{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
-- SPDX-License-Identifier: GPL-3.0-or-later
-- Native controller. All source obligations remain coupled; source selection
-- and final independent validation belong to the application boundary.
module AgdaProver.Agda28.AgendaSearch
  ( Run, Settings (..), Result (..), PauseReason (..), begin, beginSelection, beginStep, advance, withLimits, withActionLimit, withObservers, cost, frontier ) where

import Control.Concurrent (MVar, newMVar, withMVar)
import Data.Aeson (Value, object, (.=))
import Data.IORef
import Data.List.NonEmpty (NonEmpty)
import Data.List.NonEmpty qualified as NE
import Data.Set qualified as Set
import Agda.Syntax.Common (InteractionId, interactionId)
import Numeric.Natural (Natural)
import AgdaProver.Agda28.Session qualified as S
import AgdaProver.Agda28.AgendaExecution qualified as N
import AgdaProver.Symbolic.Agenda qualified as A
import AgdaProver.Symbolic.Evidence qualified as E
import AgdaProver.Symbolic.NNUE.Native (NativeScorer)
import AgdaProver.Symbolic.NNUE.Policy qualified as P
import AgdaProver.Symbolic.SessionTypes

data Settings = Settings
  { limits :: E.SearchLimits, ranking :: P.RankingMode, models :: P.Models
  , focused :: Bool, excluded :: [String]
  -- Soft priorities, not cutoffs: structural and macro alternatives stay queued.
  , structuralDelay :: Natural, macroDelay :: Natural
  , initialMacroWork :: Natural, evidenceMacro :: Bool, actionLimit :: Maybe Integer
  , dependencyOrdering :: Bool }

data Metrics = Metrics
  { schedulerSteps :: !Integer, modelItems :: !Integer, modelNanoseconds :: !Integer
  , generatedMoves :: !Integer, attemptedMoves :: !Integer, acceptedMoves :: !Integer }
data Run s = Run (S.Session s) Settings (N.Queue s) Integer
  (IORef Metrics) (MVar ()) (Value -> IO ()) (S.Transition s -> IO ()) (Maybe (S.GoalRef s, Natural))
data PauseReason = SliceEnded | AllowanceSpent | ActionsSpent | CancelledByCaller deriving (Eq, Show)
data Result s = Paused PauseReason (Run s) | Candidate (S.StateRef s) (Run s)
  | Refutation (S.RefutationProposal s) (Run s) | Exhausted | Failed Failure (Run s)

-- The initial pending query checks the source epoch. The controller never
-- accepts a malformed/stale wire key on the strength of its numeric branch ID.
begin :: S.Session s -> S.StateRef s -> Settings -> (Value -> IO ())
      -> (S.Transition s -> IO ()) -> IO (Either Failure (Run s))
begin = beginSelection Nothing

beginSelection :: Maybe (NonEmpty InteractionId) -> S.Session s -> S.StateRef s -> Settings
               -> (Value -> IO ()) -> (S.Transition s -> IO ()) -> IO (Either Failure (Run s))
beginSelection = beginWithStep False

beginStep :: Maybe (NonEmpty InteractionId) -> S.Session s -> S.StateRef s -> Settings
          -> (Value -> IO ()) -> (S.Transition s -> IO ()) -> IO (Either Failure (Run s))
beginStep = beginWithStep True

beginWithStep :: Bool -> Maybe (NonEmpty InteractionId) -> S.Session s -> S.StateRef s -> Settings
              -> (Value -> IO ()) -> (S.Transition s -> IO ()) -> IO (Either Failure (Run s))
beginWithStep oneMove selection session state supplied trace accepted = S.pending session state >>= \case
  Left failure -> pure $ Left failure
  Right _ | oneMove && maybe True ((/= 1) . length) selection ->
    pure $ Left $ KernelRejected "native-step-requires-one-selected-goal"
  Right pending | Just points <- selection,
      let ids = map interactionId $ NE.toList points,
      Set.size (Set.fromList ids) /= length ids || not (all (`elem` pendingGoals pending) ids) ->
    pure $ Left UnknownGoal
  Right pending -> do
    baseline <- nativeWork <$> S.work session
    metrics <- newIORef $ Metrics 0 0 0 0 0 0
    owner <- newMVar ()
    let settings = if oneMove then supplied { evidenceMacro = False } else supplied
        queue = case selection of
          Just points | oneMove -> N.startOneMove state (interactionId $ NE.head points) (pendingGoals pending)
          _ -> maybe (N.start state)
            (\points -> N.startSelected state (map interactionId $ NE.toList points) (pendingGoals pending)) selection
        selected = maybe (pendingGoals pending) (map interactionId . NE.toList) selection
        refutationGoal = case selected of
          [point] | not oneMove && keyBranch (S.stateKey state) == 0 -> either (const Nothing) (\goal -> Just (goal, initialMacroWork settings)) $
            S.restoreGoalReference session (S.stateKey state) (fromIntegral point)
          _ -> Nothing
    pure $ Right $ Run session settings queue baseline metrics owner trace accepted refutationGoal

-- Raising an allowance never resets accumulated work or restores spent budget.
withLimits :: E.SearchLimits -> Run s -> Run s
withLimits allowance (Run session settings queue baseline metrics owner trace accepted refutationGoal) =
  Run session settings { limits = allowance } queue baseline metrics owner trace accepted refutationGoal

withActionLimit :: Maybe Integer -> Run s -> Run s
withActionLimit limit (Run session settings queue baseline metrics owner trace accepted refutationGoal) =
  Run session settings { actionLimit = limit } queue baseline metrics owner trace accepted refutationGoal

-- A resumed protocol request has a new response channel/request ID. Do not
-- retain the callback of the request that originally created this frontier.
withObservers :: (Value -> IO ()) -> (S.Transition s -> IO ()) -> Run s -> Run s
withObservers trace accepted (Run session settings queue baseline metrics owner _ _ refutationGoal) =
  Run session settings queue baseline metrics owner trace accepted refutationGoal

cost :: Run s -> IO Value
cost (Run session settings _ baseline metrics _ _ _ _) = do
  physical <- S.work session
  measured <- readIORef metrics
  let steps = schedulerSteps measured
  pure $ object ["schema_version" .= ("agdaprover.symbolic-agenda-cost.v1" :: String),
    "scheduler_steps" .= steps, "work_units" .= (steps + nativeWork physical - baseline),
    "actions_generated" .= generatedMoves measured, "actions_attempted" .= attemptedMoves measured,
    "actions_accepted" .= acceptedMoves measured,
    "action_limit" .= actionLimit settings,
    "model_items_scored" .= modelItems measured, "model_elapsed_ns" .= modelNanoseconds measured,
    "models" .= P.modelIdentities (models settings), "session_cost" .= physical]

frontier :: Run s -> (Int, Maybe (S.StateRef s, Natural, Natural))
frontier (Run _ _ queue _ _ _ _ _ _) = N.frontier queue

-- A slice ends between native operations, retaining the exact queue. A coarse
-- evidence attempt remains atomic: its censored retry is explicitly charged
-- again. No pause claims to checkpoint the interior of an Agda checker call.
advance :: Maybe (NativeScorer n) -> Natural -> Run s -> IO (Result s)
advance native count run@(Run session settings initial baseline metrics owner trace accepted refutationGoal) =
  withMVar owner $ \_ -> if count == 0 then pure $ Paused SliceEnded run else
    case refutationGoal of
      Nothing -> go Nothing count initial
      Just (original, slice) -> allowance >>= \left ->
        if left == Just 0 then pure $ Paused AllowanceSpent run else do
          let available = maybe (toInteger slice) (min $ toInteger slice) left
          S.proposeRefutation session original (Just $ max 1 available) >>= \case
            Left Cancelled -> pure $ Paused CancelledByCaller run
            Left failure -> pure $ Failed failure run
            Right proposal -> case S.refutationKind proposal of
              S.Candidate -> pure $ Refutation proposal $ saved Nothing initial
              S.Censored -> go (Just (original, 2 * max 1 slice)) count initial
              _ -> go Nothing count initial
 where
  saved refutation queue = case run of
    Run s cfg _ base meter lock emit accept _ -> Run s cfg queue base meter lock emit accept refutation
  allowance = do
    physical <- S.work session
    steps <- schedulerSteps <$> readIORef metrics
    pure $ fmap (\limit -> max 0 $ limit - steps - nativeWork physical + baseline) $
      E.workUnitLimit $ limits settings
  moveAllowance = E.SearchLimits . fmap (max 1) <$> allowance
  recordSearch stats = modifyIORef' metrics $ \m -> m
    { modelItems = modelItems m + E.modelItems stats
    , modelNanoseconds = modelNanoseconds m + E.modelNanoseconds stats }
  recordEvent event = do
    modifyIORef' metrics $ \m -> case event of
      A.Expanded count' -> m { generatedMoves = generatedMoves m + toInteger count' }
      A.AdvancedState -> m { acceptedMoves = acceptedMoves m + 1 }
      _ -> m
    trace $ object ["schema_version" .= ("agdaprover.symbolic-agenda-event.v1" :: String),
      "event" .= show event]
  chargeAction = atomicModifyIORef' metrics $ \m ->
    if maybe False (attemptedMoves m >=) (actionLimit settings) then (m, False)
    else (m { attemptedMoves = attemptedMoves m + 1 }, True)
  planner state obligations = allowance >>= \left ->
    if left == Just 0 then pure $ Right N.PlanningCensored
    else if not (dependencyOrdering settings) || length (pendingGoals obligations) < 2 ||
        maybe False (<= toInteger (initialMacroWork settings)) left
      then planReady state obligations
      else S.dependencies session state (Just $ toInteger $ initialMacroWork settings) >>= \case
        Left failure -> pure $ Left failure
        Right snapshot -> do
          trace $ object ["schema_version" .= ("agdaprover.symbolic-agenda-event.v1" :: String),
            "event" .= ("goal-dependencies" :: String), "observation" .= S.dependencyView snapshot]
          case S.orderDependentGoals state snapshot (pendingGoals obligations) of
            Left failure -> pure $ Left failure
            Right ordered -> planReady state obligations { pendingGoals = ordered }
  planReady state obligations = case pendingGoals obligations of
    [] -> pure $ Right $ N.Moves []
    point:_ -> case S.restoreGoalReference session (S.stateKey state) (fromIntegral point) of
      Left failure -> pure $ Left failure
      Right goal -> do
        budget <- moveAllowance
        (termCost, terms) <- S.proposeTerms session goal budget (models settings)
          (ranking settings) native (excluded settings) trace
        recordSearch termCost
        case terms of
          Left failure -> pure $ Left failure
          Right S.CensoredTerms{} -> pure $ Right N.PlanningCensored
          Right (S.CompleteTerms termMoves) -> do
            remaining <- allowance
            if remaining == Just 0 then pure $ Right N.PlanningCensored else do
              nextBudget <- moveAllowance
              (clauseCost, clauses) <- S.proposeClauseActions session goal nextBudget
                (models settings) (ranking settings) native trace
              recordSearch clauseCost
              pure $ case clauses of
                Left failure -> Left failure
                Right S.CensoredClauses{} -> Right N.PlanningCensored
                Right (S.CompleteClauses clauseMoves) -> Right $ N.Moves $
                  A.rankedProposals 0 (map N.Term termMoves)
                  ++ A.rankedProposals (structuralDelay settings)
                        [N.Clause goal action | (action, _) <- clauseMoves]
                  ++ [A.Proposal (N.SlicedEvidence goal $ initialMacroWork settings)
                        (macroDelay settings) | evidenceMacro settings]
  go refutation 0 queue = pure $ Paused SliceEnded $ saved refutation queue
  go refutation remaining queue = do
    budget <- moveAllowance
    let config = N.Config budget (models settings) (ranking settings) native
          (focused settings) (excluded settings) planner
          (allowance >>= \left -> if left == Just 0 then pure False else
            modifyIORef' metrics (\m -> m { schedulerSteps = schedulerSteps m + 1 }) >> pure True)
          chargeAction recordEvent trace recordSearch accepted
    N.step session config queue >>= \case
      N.Progress next -> go refutation (remaining-1) next
      N.Candidate state next -> pure $ Candidate state $ saved refutation next
      -- A censored refutation task remains available even when the positive
      -- queue is empty. Its next larger slice is a scheduling continuation.
      N.Exhausted -> pure $ case refutation of
        Nothing -> Exhausted
        Just _ -> Paused SliceEnded $ saved refutation queue
      N.Paused next -> pure $ Paused AllowanceSpent $ saved refutation next
      N.Interrupted reason next -> pure $ case reason of
        N.PlanningAllowanceExhausted -> Paused AllowanceSpent $ saved refutation next
        N.ActionAllowanceExhausted -> Paused ActionsSpent $ saved refutation next
        N.MoveAllowanceExhausted{} -> Paused AllowanceSpent $ saved refutation next
        N.SessionFailure Cancelled -> Paused CancelledByCaller $ saved refutation next
        N.SessionFailure failure -> Failed failure $ saved refutation next

nativeWork :: Work -> Integer
nativeWork ledger = checkingAttempts ledger + symbolicActions ledger
