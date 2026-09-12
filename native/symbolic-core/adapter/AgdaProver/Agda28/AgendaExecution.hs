{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE LambdaCase #-}
-- SPDX-License-Identifier: GPL-3.0-or-later
-- Coupled native moves beneath single/joint scheduling. The planner supplies
-- alternatives; it never supplies a replacement typechecker or proof authority.
module AgdaProver.Agda28.AgendaExecution
  ( Move (..), Planning (..), Config (..), Queue, Outcome (..), Interruption (..), start, startSelected, startOneMove, prioritizeProgress, frontier, step, stepWithDepth ) where

import Control.Monad.Except (ExceptT, runExceptT, throwError)
import Control.Monad.IO.Class (liftIO)
import Data.Aeson (Value)
import Data.Set qualified as Set
import Numeric.Natural (Natural)

import AgdaProver.Agda28.Session qualified as S
import AgdaProver.Symbolic.Agenda qualified as A
import AgdaProver.Symbolic.Clause (ClauseAction)
import AgdaProver.Symbolic.Evidence qualified as E
import AgdaProver.Symbolic.NNUE.Native (NativeScorer)
import AgdaProver.Symbolic.NNUE.Policy qualified as P
import AgdaProver.Symbolic.Protocol (ObservationMode)
import AgdaProver.Symbolic.SessionTypes

data Move s
  = Evidence (S.GoalRef s)
  | SlicedEvidence (S.GoalRef s) Natural
  | Term (S.TermProposal s)
  | Clause (S.GoalRef s) ClauseAction
  | Helper (S.GoalRef s) ObservationMode DraftExpression

data Planning s = Moves [A.Proposal (Move s)] | PlanningCensored

data Config s n = Config
  { moveLimits :: E.SearchLimits
  , models :: P.Models, ranking :: P.RankingMode, scorer :: Maybe (NativeScorer n)
  , focused :: Bool, excluded :: [String]
  , plan :: S.StateRef s -> Pending -> IO (Either Failure (Planning s))
  , chargeStep :: IO Bool, chargeMove :: IO Bool, observe :: A.Event -> IO ()
  , policyTrace :: Value -> IO ()
  , searchCost :: E.SearchStats -> IO ()
  , accepted :: S.Transition s -> IO () }

-- Selection is caller authority, not an independence claim. Unselected goals
-- remain in the same native state; newly created AND children inherit selection.
-- Retain the branch's AND order separately from Agda's interaction identifiers.
-- A refinement replaces one obligation with fresh identifiers, which Agda
-- appends after unrelated source goals. Those identifiers are not priorities.
data SearchState s = SearchState (S.StateRef s) (Maybe (Set.Set Int)) [Int] (Maybe StateKey)
data Continuation s = RetryEvidence (SearchState s) (S.GoalRef s) Natural
type Queue s = A.Agenda (SearchState s) (Move s) (Continuation s)

-- An exhausted coarse evidence attempt is censored, not a declined branch.
-- Its queue is retained. This API does not claim to resume inside that attempt:
-- fine-grained checker/search continuations are the separate slicing layer.
data Interruption = SessionFailure Failure | MoveAllowanceExhausted E.SearchStats | PlanningAllowanceExhausted
  | ActionAllowanceExhausted
  deriving (Eq, Show)
data Outcome s
  = Progress (Queue s) | Candidate (S.StateRef s) (Queue s)
  | Paused (Queue s) | DepthPaused (Queue s) | Interrupted Interruption (Queue s) | Exhausted

start :: S.StateRef s -> [Int] -> Queue s
start state obligations = A.start $ SearchState state Nothing obligations Nothing

startSelected :: S.StateRef s -> [Int] -> [Int] -> Queue s
startSelected state selected allGoals = A.start $
  SearchState state (Just $ Set.fromList selected) allGoals Nothing

-- A step proposes one checked transition from the original parent. Its open
-- descendants are deliberately not solved. Rejected source handoffs can resume
-- the same root alternatives; neither a fresh search nor Python planning occurs.
startOneMove :: S.StateRef s -> Int -> [Int] -> Queue s
startOneMove state selected allGoals = A.start $
  SearchState state (Just $ Set.singleton selected) allGoals (Just $ S.stateKey state)

-- An inspect/apply pair costs two agenda steps. Estimate remaining work from
-- native live obligations only; no type names, independence claim, pruning or
-- fresh checking is involved. One-step search deliberately retains its order.
prioritizeProgress :: Queue s -> Queue s
prioritizeProgress = A.prioritize $ \(SearchState _ selected order stepParent) ->
  if stepParent /= Nothing then 0 else 2 * fromIntegral
    (length $ maybe order (\chosen -> filter (`Set.member` chosen) order) selected)

frontier :: Queue s -> (Int, Maybe (S.StateRef s, Natural, Natural))
frontier queue = (A.pending queue, fmap unwrap $ A.principal queue)
 where
  unwrap (SearchState state _ _ _, priority, depth) = (state, priority, depth)

step :: S.Session s -> Config s n -> Queue s -> IO (Outcome s)
step = stepWithDepth Nothing

stepWithDepth :: Maybe Natural -> S.Session s -> Config s n -> Queue s -> IO (Outcome s)
stepWithDepth limit session config queue = runExceptT (A.stepWithDepth limit hooks queue) >>= \case
  Left problem -> pure $ Interrupted problem queue
  Right outcome -> pure $ case outcome of
    A.Progress next -> Progress next
    A.Found state next -> Candidate state next
    A.Censored next -> Paused next
    A.DepthCensored next -> DepthPaused next
    A.Exhausted -> Exhausted
 where
  hooks = A.Hooks
    { A.charge = liftIO $ chargeStep config
    , A.observe = liftIO . observe config
    , A.inspect = \(SearchState state selected order stepParent) -> do
        obligations <- require $ S.pending session state
        let live = Set.fromList $ pendingGoals obligations
            ordered = filter (`Set.member` live) order ++
              filter (`notElem` order) (pendingGoals obligations)
            selectedPending = maybe ordered (\chosen -> filter (`Set.member` chosen) ordered) selected
        if maybe False (/= S.stateKey state) stepParent then pure $ A.Candidate state
        else if null selectedPending then
          -- Partial selection is only a candidate relative to remaining source
          -- holes, never apparent global closure. Export/fresh validation must
          -- reject any unresolved selected proof or unsupported dependency.
          pure $ if selected /= Nothing ||
              (pendingMetas obligations == 0 && pendingConstraints obligations == 0)
            then A.Candidate state else A.Stuck
        else require (plan config state obligations { pendingGoals = selectedPending }) >>= \case
          Moves moves -> pure $ A.Open moves
          PlanningCensored -> throwError PlanningAllowanceExhausted
    , A.apply = execute
    , A.resume = \(RetryEvidence state goal allowance) -> execute state $ SlicedEvidence goal allowance
    -- Identical issued keys witness the same immutable branch only. Equal
    -- printed goals and equal endpoint types never authorize state merging.
    , A.sameState = \(SearchState a sa oa pa) (SearchState b sb ob pb) ->
        pure $ S.stateKey a == S.stateKey b && sa == sb && oa == ob && pa == pb }
  execute current@(SearchState state selected _ _) move = do
    allowed <- liftIO $ chargeMove config
    if not allowed then throwError ActionAllowanceExhausted else pure ()
    let goal = case move of
          Evidence g -> g
          SlicedEvidence g _ -> g
          Term proposal -> S.termProposalGoal proposal
          Clause g _ -> g
          Helper g _ _ -> g
    if S.stateKey (S.goalState goal) /= S.stateKey state ||
        maybe False (Set.notMember $ fromIntegral $ S.goalId goal) selected
      then throwError $ SessionFailure $ KernelFailure "agenda-move-parent-mismatch"
      else case move of
        Term proposal -> liftIO (S.applyTerm session proposal) >>= transition current
        Clause _ action -> liftIO (S.applyClause session goal action) >>= transition current
        Evidence _ -> search current Nothing $ S.solveEvidence session goal (moveLimits config)
          (models config) (ranking config) (scorer config) (focused config)
          (excluded config) (policyTrace config)
        SlicedEvidence _ allowance ->
          -- A soft scheduling slice, not an additional proof-search cutoff.
          -- Retry from the same immutable parent with increasing allowance.
          -- Repeated work is fully charged; no inner Agda continuation is claimed.
          let slice = max 1 $ toInteger allowance
              available = maybe slice (min slice) $ E.workUnitLimit $ moveLimits config
              again = RetryEvidence current goal (2 * max 1 allowance)
          in search current (Just again) $ S.solveEvidence session goal (E.SearchLimits $ Just available)
            (models config) (ranking config) (scorer config) (focused config)
            (excluded config) (policyTrace config)
        Helper _ view expression -> search current Nothing $ S.solveHelper session goal (moveLimits config)
          (models config) (ranking config) (scorer config) view expression (policyTrace config)
  search current continuation action = do
    (cost, result) <- liftIO action
    liftIO $ searchCost config cost
    case result of
      Left failure -> declined failure
      Right (E.WorkExhausted, _, _) -> case continuation of
        Just again -> pure $ A.Deferred again
        Nothing -> throwError $ MoveAllowanceExhausted cost
      Right (E.FragmentExhausted, Nothing, _) -> pure A.Declined
      Right (E.FoundCandidate, Just next, _) -> transition current $ Right next
      _ -> throwError $ SessionFailure $ KernelFailure "agenda-inconsistent-search-result"
  transition (SearchState parent selected previousOrder stepParent) = \case
    Left failure -> declined failure
    Right next -> do
      -- The all-goal entry point is lazy about its initial pending query. Read
      -- it once on successful root transitions, never interpret every original
      -- source goal as a newly generated child.
      before <- if null previousOrder then pendingGoals <$> require (S.pending session parent)
        else pure previousOrder
      liftIO $ accepted config next
      let current = pendingGoals $ S.transitionPending next
          previousGoals = Set.fromList before
          after = Set.fromList current
          children = filter (`Set.notMember` previousGoals) current
          order = children ++ filter (`Set.member` after) before
          chosen = fmap (\active -> Set.union (Set.intersection active after)
            (Set.difference after previousGoals)) selected
      pure $ A.Advanced $ SearchState (S.transitionState next) chosen order stepParent
  declined = \case
    KernelRejected{} -> pure A.Declined
    KernelBlocked{} -> pure A.Declined
    failure -> throwError $ SessionFailure failure

require :: IO (Either Failure a) -> ExceptT Interruption IO a
require action = liftIO action >>= either (throwError . SessionFailure) pure
