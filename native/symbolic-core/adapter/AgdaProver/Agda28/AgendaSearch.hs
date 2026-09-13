{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
-- SPDX-License-Identifier: GPL-3.0-or-later
-- Native controller. All source obligations remain coupled; source selection
-- and final independent validation belong to the application boundary.
module AgdaProver.Agda28.AgendaSearch
  ( Run, Settings (..), Result (..), PauseReason (..), begin, beginSelection, beginStep, advance, withLimits, withActionLimit, withDepthLimit, withObservers, cost, frontier ) where

import Control.Concurrent (MVar, newMVar, withMVar)
import Data.Aeson (Value, object, (.=))
import Data.IORef
import Data.List.NonEmpty (NonEmpty)
import Data.List.NonEmpty qualified as NE
import Data.Map.Strict qualified as Map
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
  , dependencyOrdering :: Bool, depthLimit :: Maybe Natural, progressOrdering :: Bool
  , retryWorkOrdering :: Bool, jointConstructorPropagation :: Bool, multiSubjectClauses :: Bool
  , evidenceDepthReuse :: Bool, coalesceIntroductions :: Bool, targetFunctionOperands :: Bool
  , recursiveEvidenceOperands :: Bool, contextualEvidence :: Bool, stagedPlanning :: Bool }

data Metrics = Metrics
  { schedulerSteps :: !Integer, modelItems :: !Integer, modelNanoseconds :: !Integer
  , generatedMoves :: !Integer, attemptedMoves :: !Integer, acceptedMoves :: !Integer
  , depthDeferred :: !Integer }
data Run s = Run (S.Session s) Settings (N.Queue s) Integer
  (IORef Metrics) (MVar ()) (Value -> IO ()) (S.Transition s -> IO ()) (Maybe (S.GoalRef s, Natural))
  (Maybe (JointCache s))

-- One recent assembled proposal per original entry; alternatives still belong
-- to the ordinary agenda. No TCState, checker callback or cross-run cache.
data JointCache s = JointCache (S.StateRef s) (Set.Set Int)
  (IORef (Map.Map Int (S.RetainedGoal s)))
  (IORef (Set.Set (StateKey, Int, StateKey)))
data PauseReason = SliceEnded | AllowanceSpent | ActionsSpent | DepthSpent | CancelledByCaller deriving (Eq, Show)
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
    metrics <- newIORef $ Metrics 0 0 0 0 0 0 0
    owner <- newMVar ()
    let settings = if oneMove then supplied { evidenceMacro = False } else supplied
        queue = (if progressOrdering settings then N.prioritizeProgress else id) $ case selection of
          Just points | oneMove -> N.startOneMove state (interactionId $ NE.head points) (pendingGoals pending)
          _ -> maybe (N.start state $ pendingGoals pending)
            (\points -> N.startSelected state (map interactionId $ NE.toList points) (pendingGoals pending)) selection
        selected = maybe (pendingGoals pending) (map interactionId . NE.toList) selection
        refutationGoal = case selected of
          [point] | not oneMove && keyBranch (S.stateKey state) == 0 -> either (const Nothing) (\goal -> Just (goal, initialMacroWork settings)) $
            S.restoreGoalReference session (S.stateKey state) (fromIntegral point)
          _ -> Nothing
    joint <- if not oneMove && progressOrdering settings && evidenceMacro settings &&
        stagedPlanning settings && length selected > 1
      then Just <$> (JointCache state (Set.fromList selected) <$> newIORef Map.empty <*> newIORef Set.empty)
      else pure Nothing
    let localized = maybe queue (const $ N.localizeEntries queue) joint
    pure $ Right $ Run session settings localized baseline metrics owner trace accepted refutationGoal joint

-- Raising an allowance never resets accumulated work or restores spent budget.
withLimits :: E.SearchLimits -> Run s -> Run s
withLimits allowance (Run session settings queue baseline metrics owner trace accepted refutationGoal joint) =
  Run session settings { limits = allowance } queue baseline metrics owner trace accepted refutationGoal joint

withActionLimit :: Maybe Integer -> Run s -> Run s
withActionLimit limit (Run session settings queue baseline metrics owner trace accepted refutationGoal joint) =
  Run session settings { actionLimit = limit } queue baseline metrics owner trace accepted refutationGoal joint

withDepthLimit :: Maybe Natural -> Run s -> Run s
withDepthLimit limit (Run session settings queue baseline metrics owner trace accepted refutationGoal joint) =
  Run session settings { depthLimit = limit } queue baseline metrics owner trace accepted refutationGoal joint

-- A resumed protocol request has a new response channel/request ID. Do not
-- retain the callback of the request that originally created this frontier.
withObservers :: (Value -> IO ()) -> (S.Transition s -> IO ()) -> Run s -> Run s
withObservers trace accepted (Run session settings queue baseline metrics owner _ _ refutationGoal joint) =
  Run session settings queue baseline metrics owner trace accepted refutationGoal joint

cost :: Run s -> IO Value
cost (Run session settings _ baseline metrics _ _ _ _ joint) = do
  physical <- S.work session
  measured <- readIORef metrics
  let steps = schedulerSteps measured
  pure $ object ["schema_version" .= ("agdaprover.symbolic-agenda-cost.v1" :: String),
    "scheduler_steps" .= steps, "work_units" .= (steps + nativeWork physical - baseline),
    "actions_generated" .= generatedMoves measured, "actions_attempted" .= attemptedMoves measured,
    "actions_accepted" .= acceptedMoves measured,
    "action_limit" .= actionLimit settings,
    "depth_limit" .= depthLimit settings, "depth_deferred" .= depthDeferred measured,
    "depth_unit" .= ("accepted-native-branch-transition" :: String),
    "ordering" .= (if progressOrdering settings then "fair-entry-local-v6" else "cost-only-v1" :: String),
    "entry_checkpoints" .= maybe False (const True) joint,
    "retry_ordering" .= (if retryWorkOrdering settings then "spent-work-v1" else "uniform-v1" :: String),
    "evidence_depth_reuse" .= evidenceDepthReuse settings,
    "evidence_continuation" .= (if evidenceDepthReuse settings then "operand-progress-v1" else "restart-v1" :: String),
    "coalesce_introductions" .= coalesceIntroductions settings,
    "target_function_operands" .= targetFunctionOperands settings,
    "recursive_evidence_operands" .= recursiveEvidenceOperands settings,
    "contextual_evidence" .= contextualEvidence settings,
    "staged_planning" .= (evidenceMacro settings && stagedPlanning settings),
    "local_closure_handoffs" .= (evidenceMacro settings && contextualEvidence settings),
    "joint_constructor_propagation" .= jointConstructorPropagation settings,
    "multi_subject_clauses" .= multiSubjectClauses settings,
    "model_items_scored" .= modelItems measured, "model_elapsed_ns" .= modelNanoseconds measured,
    "models" .= P.modelIdentities (models settings), "session_cost" .= physical]

frontier :: Run s -> (Int, Maybe (S.StateRef s, Natural, Natural))
frontier (Run _ _ queue _ _ _ _ _ _ _) = N.frontier queue

-- A slice ends between native operations, retaining the exact queue and coarse
-- evidence operands. Atomic catalogue/scope retries stay explicitly charged.
-- No pause claims to checkpoint the interior of an Agda checker call.
advance :: Maybe (NativeScorer n) -> Natural -> Run s -> IO (Result s)
advance native count run@(Run session settings initial baseline metrics owner trace accepted refutationGoal joint) =
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
    Run s cfg _ base meter lock emit accept _ cache -> Run s cfg queue base meter lock emit accept refutation cache
  allowance = do
    physical <- S.work session
    steps <- schedulerSteps <$> readIORef metrics
    pure $ fmap (\limit -> max 0 $ limit - steps - nativeWork physical + baseline) $
      E.workUnitLimit $ limits settings
  moveAllowance = E.SearchLimits . fmap (max 1) <$> allowance
  operands = E.PrimitiveOptions
    { E.goalFunctionOperands = targetFunctionOperands settings
    , E.recursiveEvidenceOperands = recursiveEvidenceOperands settings
    , E.contextualEvidence = contextualEvidence settings }
  recordSearch stats = modifyIORef' metrics $ \m -> m
    { modelItems = modelItems m + E.modelItems stats
    , modelNanoseconds = modelNanoseconds m + E.modelNanoseconds stats }
  recordEvent event = do
    modifyIORef' metrics $ \m -> case event of
      A.Expanded count' -> m { generatedMoves = generatedMoves m + toInteger count' }
      A.AdvancedState -> m { acceptedMoves = acceptedMoves m + 1 }
      A.DepthDeferred -> m { depthDeferred = depthDeferred m + 1 }
      _ -> m
    trace $ object ["schema_version" .= ("agdaprover.symbolic-agenda-event.v1" :: String),
      "event" .= show event]
  chargeAction = atomicModifyIORef' metrics $ \m ->
    if maybe False (attemptedMoves m >=) (actionLimit settings) then (m, False)
    else (m { attemptedMoves = attemptedMoves m + 1 }, True)
  planner state obligations = allowance >>= \left ->
    if left == Just 0 then pure $ Right N.PlanningCensored
    else if not (dependencyOrdering settings || jointConstructorPropagation settings) || length (pendingGoals obligations) < 2 ||
        maybe False (<= toInteger (initialMacroWork settings)) left
      then planReady state [] obligations
      else S.dependencies session state (Just $ toInteger $ initialMacroWork settings) >>= \case
        Left failure -> pure $ Left failure
        Right snapshot -> do
          trace $ object ["schema_version" .= ("agdaprover.symbolic-agenda-event.v1" :: String),
            "event" .= ("goal-dependencies" :: String), "observation" .= S.dependencyView snapshot]
          let selected = pendingGoals obligations
              selection = do
                ordered <- if dependencyOrdering settings
                  then S.orderDependentGoals state snapshot selected else Right selected
                constraining <- if jointConstructorPropagation settings
                  then S.constrainingGoals state snapshot selected else Right []
                Right (ordered, constraining)
          case selection of
            Left failure -> pure $ Left failure
            Right (ordered, constraining) -> planReady state constraining obligations { pendingGoals = ordered }
  planReady state constraining obligations = case pendingGoals obligations of
    [] -> pure $ Right $ N.Moves []
    point:_ -> case S.restoreGoalReference session (S.stateKey state) (fromIntegral point) of
      Left failure -> pure $ Left failure
      Right goal | evidenceMacro settings && stagedPlanning settings -> do
        reused <- reuseProposal goal
        pure $ Right $ N.Moves $ reused ++
          [A.Proposal (N.Prepare $ N.Preparation goal obligations constraining N.PrepareLocals)
            (if null reused then 0 else 1)]
      Right goal -> do
        budget <- moveAllowance
        (termCost, atomicTerms) <- S.proposeTermsWithOptions operands session goal budget (models settings)
          (ranking settings) native (excluded settings) trace
        recordSearch termCost
        constructedTerms <- case atomicTerms of
          Right (S.CompleteTerms originals) | evidenceMacro settings -> do
            compoundBudget <- moveAllowance
            (compoundCost, structures) <- S.proposeStructuresWithOptions operands session goal compoundBudget (models settings)
              (ranking settings) native (excluded settings) trace
            recordSearch compoundCost
            pure $ case structures of
              Right (S.CompleteTerms additions) -> Right $ S.CompleteTerms $ S.preferStructures additions originals
              other -> other
          other -> pure other
        equations <- case constructedTerms of
          Right S.CompleteTerms{} | evidenceMacro settings ->
            case traverse (S.restoreGoalReference session (S.stateKey state) . fromIntegral)
                (drop 1 $ pendingGoals obligations) of
              Left failure -> pure $ Left failure
              Right [] -> pure $ Right $ S.CompleteTerms []
              Right later -> do
                equationBudget <- moveAllowance
                (equationCost, proposals) <- S.proposeEquations later session goal equationBudget
                  (models settings) (ranking settings) native (excluded settings) trace
                recordSearch equationCost
                pure proposals
          _ -> pure $ Right $ S.CompleteTerms []
        case (constructedTerms, equations) of
          (Left failure, _) -> pure $ Left failure
          (_, Left failure) -> pure $ Left failure
          (Right S.CensoredTerms{}, _) -> pure $ Right N.PlanningCensored
          (_, Right S.CensoredTerms{}) -> pure $ Right N.PlanningCensored
          (Right (S.CompleteTerms termMoves), Right (S.CompleteTerms equationMoves)) -> do
            remaining <- allowance
            if remaining == Just 0 then pure $ Right N.PlanningCensored else do
              nextBudget <- moveAllowance
              (clauseCost, clauses) <- S.proposeClauseActions session goal nextBudget
                (models settings) (ranking settings) native (excluded settings) trace
              recordSearch clauseCost
              case clauses of
                Left failure -> pure $ Left failure
                Right S.CensoredClauses{} -> pure $ Right N.PlanningCensored
                Right (S.CompleteClauses clauseMoves) -> do
                  let distinctClauses = if evidenceMacro settings && coalesceIntroductions settings
                        then S.withoutResultIntroductionOverlap termMoves clauseMoves else clauseMoves
                  -- Later selected obligations can constrain earlier definitions
                  -- through Agda unification. Only target-directed constructor
                  -- closures are observed here, not whole premise catalogues or
                  -- hidden searches. Every move still owns the same parent.
                  propagated <- constructorGoals state $
                    filter (`elem` constraining) $ drop 1 $ pendingGoals obligations
                  pure $ case propagated of
                    Left failure -> Left failure
                    Right S.CensoredTerms{} -> Right N.PlanningCensored
                    Right (S.CompleteTerms closures) -> Right $ N.Moves $
                      -- An explicit clause block preserves the selected
                      -- specification's information before constructor probes
                      -- can consume its goals into suspended constraints.
                      A.rankedProposals 0 (map N.Term $ equationMoves ++ closures ++ termMoves)
                      ++ A.rankedProposals (structuralDelay settings)
                            [N.PlannedClause action | (action, _) <- distinctClauses,
                              multiSubjectClauses settings || not (S.clauseMoveIsBatch action)]
                      ++ [A.Proposal (N.SlicedEvidence goal (initialMacroWork settings) E.initialDepth)
                            (macroDelay settings) | evidenceMacro settings]
  prepareStage (N.Preparation goal obligations constraining stage) = do
    let continue next moves = N.Moves $ moves ++
          [A.Proposal (N.Prepare $ N.Preparation goal obligations constraining next) 1]
        termMoves = A.rankedProposals 0 . map N.Term
        publish generate next = do
          budget <- moveAllowance
          (stats, result) <- generate budget
          recordSearch stats
          pure $ case result of
            Left failure -> Left failure
            Right S.CensoredTerms{} -> Right N.PlanningCensored
            Right (S.CompleteTerms terms) -> Right $ next terms
        generated call budget = call session goal budget (models settings)
          (ranking settings) native (excluded settings) trace
        prepareTerms structures published quantum remaining = do
          left <- allowance
          if left == Just 0 then pure $ Right N.PlanningCensored else do
            let budget = E.SearchLimits $ Just $ maybe (toInteger quantum) (min $ toInteger quantum) left
            (stats, result) <- case remaining of
              Nothing -> S.prepareTermsSlice operands session goal budget (models settings)
                (ranking settings) native (excluded settings) trace
              Just cursor -> S.resumeTermsSlice cursor session goal budget native trace
            recordSearch stats
            trace $ object ["schema_version" .= ("agdaprover.symbolic-agenda-event.v1" :: String),
              "event" .= ("term-preparation" :: String), "parent" .= S.stateKey state,
              "goal_id" .= interactionId (S.goalId goal), "cost" .= stats]
            pure $ case result of
              Left failure -> Left failure
              Right (batch, rest) ->
                let additions = drop (length structures) $ S.preferStructures structures batch
                    combined = published ++ additions
                    -- Grow only an exhausted scheduling quantum. It is not a
                    -- theorem limit; completed work is retained, while an
                    -- unfinished atomic builder can retry with more room.
                    nextQuantum = if E.workExhausted stats then 2 * max 1 quantum else quantum
                    next = maybe (N.PrepareClauses $ structures ++ combined)
                      (N.PrepareMoreTerms structures combined nextQuantum) rest
                    -- This finishes the existing parent's catalogue; it is
                    -- not a fresh proof-search branch. Prior preparation cost
                    -- is sunk work, not an estimate of remaining proof cost.
                    -- Keep its finite preparation priority, with every query
                    -- still charged to the physical/cumulative ledger.
                in Right $ continue next $ termMoves additions
        state = S.goalState goal
        name = case stage of
          N.PrepareLocals -> "local-closure"
          N.PrepareEquations -> "equations"
          N.PreparePropagation{} -> "propagation"
          N.PrepareStructures -> "structures"
          N.PrepareTerms{} -> "terms"
          N.PrepareMoreTerms{} -> "terms-resume"
          N.PrepareClauses{} -> "clauses"
    trace $ object ["schema_version" .= ("agdaprover.symbolic-agenda-event.v1" :: String),
      "event" .= ("prepare-procedure" :: String), "procedure" .= (name :: String),
      "parent" .= S.stateKey state, "goal_id" .= interactionId (S.goalId goal)]
    case stage of
      N.PrepareLocals | not (contextualEvidence settings) -> pure $ Right $ continue N.PrepareEquations []
      N.PrepareLocals -> publish (generated S.proposeLocalClosures) $
        continue N.PrepareEquations . termMoves
      N.PrepareEquations ->
        case traverse (S.restoreGoalReference session (S.stateKey state) . fromIntegral)
            (drop 1 $ pendingGoals obligations) of
          Left failure -> pure $ Left failure
          Right later ->
            let next = N.PreparePropagation $ filter (`elem` constraining) $ drop 1 $ pendingGoals obligations
            in if null later then pure $ Right $ continue next [] else
              publish (generated $ S.proposeEquations later) $ continue next . termMoves
      N.PreparePropagation [] -> pure $ Right $ continue N.PrepareStructures []
      N.PreparePropagation (point:rest) ->
        case S.restoreGoalReference session (S.stateKey state) (fromIntegral point) of
          Left failure -> pure $ Left failure
          Right later -> publish
            (\budget -> S.proposePropagation session later budget (models settings)
              (ranking settings) native (excluded settings) trace) $
            continue (N.PreparePropagation rest) . termMoves
      N.PrepareStructures -> publish (generated $ S.proposeStructuresWithOptions operands) $ \terms ->
        continue (N.PrepareTerms terms) $ termMoves terms
      N.PrepareTerms structures -> prepareTerms structures [] (max 1 $ initialMacroWork settings) Nothing
      N.PrepareMoreTerms structures published quantum cursor ->
        prepareTerms structures published quantum (Just cursor)
      N.PrepareClauses terms -> do
        budget <- moveAllowance
        (stats, result) <- S.proposeClauseActions session goal budget
          (models settings) (ranking settings) native (excluded settings) trace
        recordSearch stats
        pure $ case result of
          Left failure -> Left failure
          Right S.CensoredClauses{} -> Right N.PlanningCensored
          Right (S.CompleteClauses clauses) ->
            let distinct = if coalesceIntroductions settings
                  then S.withoutResultIntroductionOverlap terms clauses else clauses
            in Right $ N.Moves $
              A.rankedProposals (structuralDelay settings)
                [N.PlannedClause action | (action, _) <- distinct,
                  multiSubjectClauses settings || not (S.clauseMoveIsBatch action)] ++
              [A.Proposal (N.SlicedEvidence goal (initialMacroWork settings) E.initialDepth) (macroDelay settings)]
  constructorGoals _ [] = pure $ Right $ S.CompleteTerms []
  constructorGoals state (point:rest) =
    case S.restoreGoalReference session (S.stateKey state) (fromIntegral point) of
      Left failure -> pure $ Left failure
      Right goal -> do
        budget <- moveAllowance
        (stats, proposals) <- S.proposePropagation session goal budget (models settings)
          (ranking settings) native (excluded settings) trace
        recordSearch stats
        case proposals of
          Left failure -> pure $ Left failure
          Right censored@S.CensoredTerms{} -> pure $ Right censored
          Right (S.CompleteTerms prefix) -> fmap (\case
            S.CompleteTerms suffix -> S.CompleteTerms $ prefix ++ suffix
            censored -> censored) <$> constructorGoals state rest
  go refutation 0 queue = pure $ Paused SliceEnded $ saved refutation queue
  go refutation remaining queue = do
    budget <- moveAllowance
    let config = N.Config budget (models settings) (ranking settings) native
          (focused settings) (excluded settings) planner prepareStage
          (allowance >>= \left -> if left == Just 0 then pure False else
            modifyIORef' metrics (\m -> m { schedulerSteps = schedulerSteps m + 1 }) >> pure True)
          chargeAction recordEvent trace recordSearch
          (\stats -> if retryWorkOrdering settings then fromInteger $ max 0 $ E.workUnits stats else 0)
          accepted (evidenceDepthReuse settings)
          -- Staged planning owns closure for every goal. Do not also run the
          -- legacy clause-only pass and then repeat its exact-parent probes.
          (evidenceMacro settings && contextualEvidence settings && not (stagedPlanning settings))
          (maybe False (const True) joint) rememberEntries
    N.stepWithDepth (depthLimit settings) session config queue >>= \case
      N.Progress next -> go refutation (remaining-1) next
      N.Candidate state next -> pure $ Candidate state $ saved refutation next
      -- A censored refutation task remains available even when the positive
      -- queue is empty. Its next larger slice is a scheduling continuation.
      N.Exhausted -> pure $ case refutation of
        Nothing -> Exhausted
        Just _ -> Paused SliceEnded $ saved refutation queue
      N.Paused next -> pure $ Paused AllowanceSpent $ saved refutation next
      N.DepthPaused next -> pure $ Paused DepthSpent $ saved refutation next
      N.Interrupted reason next -> pure $ case reason of
        N.PlanningAllowanceExhausted -> Paused AllowanceSpent $ saved refutation next
        N.ActionAllowanceExhausted -> Paused ActionsSpent $ saved refutation next
        N.MoveAllowanceExhausted{} -> Paused AllowanceSpent $ saved refutation next
        N.SessionFailure Cancelled -> Paused CancelledByCaller $ saved refutation next
        N.SessionFailure failure -> Failed failure $ saved refutation next

  reuseProposal goal = case joint of
    Nothing -> pure []
    Just (JointCache _ originals cache attempts) -> do
      let point = interactionId $ S.goalId goal
      candidate <- Map.lookup point <$> readIORef cache
      case candidate of
        Just retained | Set.member point originals -> do
          let key = (S.stateKey $ S.goalState goal, point, S.retainedGoalOrigin retained)
          fresh <- atomicModifyIORef' attempts $ \seen ->
            (Set.insert key seen, Set.notMember key seen)
          pure [A.Proposal (N.ReuseGoal goal retained) 0 | fresh]
        _ -> pure []
  rememberEntries state points = case joint of
    Nothing -> pure $ Right ()
    Just (JointCache root originals cache _) -> remember root cache
      (filter (`Set.member` originals) points)
   where
    remember _ _ [] = pure $ Right ()
    remember root cache (point:rest) = S.retainGoal session root (fromIntegral point) state >>= \case
      Right retained -> do
        modifyIORef' cache $ Map.insert point retained
        trace $ object ["schema_version" .= ("agdaprover.symbolic-agenda-event.v1" :: String),
          "event" .= ("entry-checkpoint" :: String), "goal_id" .= point, "state" .= S.stateKey state]
        remember root cache rest
      -- Failure to assemble a closed draft is not failure of the branch.
      -- Cancellation and invalid parent/epoch failures propagate; no failed
      -- capture is published as proof or swallowed as an ordinary rejection.
      Left KernelRejected{} -> remember root cache rest
      Left KernelBlocked{} -> remember root cache rest
      Left failure -> pure $ Left failure

nativeWork :: Work -> Integer
nativeWork ledger = checkingAttempts ledger + symbolicActions ledger
