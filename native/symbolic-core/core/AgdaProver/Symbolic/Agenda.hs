{-# LANGUAGE ImportQualifiedPost #-}
-- SPDX-License-Identifier: GPL-3.0-or-later
-- A coupled state owns all its AND obligations. Alternatives never merge
-- substitutions. This module schedules opaque typed states/actions; the native
-- adapter alone observes, checks and reconstructs them.
module AgdaProver.Symbolic.Agenda
  ( Agenda, Proposal (..), Inspection (..), Transition (..), Outcome (..)
  , Event (..), Hooks (..), rankedProposals, start, prioritize, pending, principal, step, stepWithDepth ) where

import Data.Map.Strict qualified as Map
import Data.List (foldl')
import Numeric.Natural (Natural)

data Proposal action = Proposal
  { action :: action, penalty :: Natural } deriving (Eq, Show)

-- Widen an already ranked family across agenda cost tiers. Ranking only the
-- insertion order would put its entire catalogue ahead of every descendant
-- at the next depth, defeating learned guidance in a broad scope. No proposal
-- is removed: even the last has a finite, caller-visible scheduling cost.
rankedProposals :: Natural -> [action] -> [Proposal action]
rankedProposals delay = zipWith (flip Proposal) [delay..]
data Inspection action result = Open [Proposal action] | Candidate result | Stuck
  deriving (Eq, Show)
data Transition state continuation = Advanced state | Deferred continuation | Declined
  deriving (Eq, Show)
data Event = Expanded Int | Attempted | Resumed | AdvancedState | Yielded
  | Rejected | CyclePruned | Proposed | Stalled | DepthDeferred
  deriving (Eq, Show)

data Hooks m state action continuation result = Hooks
  { charge :: m Bool
  , observe :: Event -> m ()
  , inspect :: state -> m (Inspection action result)
  , apply :: state -> action -> m (Transition state continuation)
  , resume :: continuation -> m (Transition state continuation)
  -- True needs exact native ancestry evidence, never a hash/display match.
  -- Unknown equivalence must return False. Cross-branch reuse is separate.
  , sameState :: state -> state -> m Bool }

data Work state action continuation
  = Inspect state [state]
  | Apply state action [state]
  | Resume state continuation [state]

-- An immutable queue can be retained if a callback throws or checking is
-- interrupted. The adapter's transaction and external ledger own those effects.
-- Every continuation advances cost, so a zero-progress resumable action cannot
-- permanently starve a finite-cost alternative in this finitely branching queue.
-- Keep spent scheduling cost separate from the nonnegative estimate. The
-- estimate orders work; it never rebates actual work or authorizes pruning.
type Entries state action continuation =
  Map.Map (Natural, Integer) (Natural, Work state action continuation)
data Agenda state action continuation = Agenda Integer (state -> Natural)
  (Entries state action continuation) (Entries state action continuation) (Maybe Natural)

data Outcome state action continuation result
  = Progress (Agenda state action continuation)
  | Found result (Agenda state action continuation)
  | Censored (Agenda state action continuation)
  | DepthCensored (Agenda state action continuation)
  | Exhausted

start :: state -> Agenda state action continuation
start state = insert 0 (Inspect state []) $ Agenda 0 (const 0) Map.empty Map.empty Nothing

-- Reordering is explicit and deterministic, retaining serial tie breaks,
-- spent cost, held work and every alternative. No admissibility claim is made.
prioritize :: (state -> Natural) -> Agenda state action continuation -> Agenda state action continuation
prioritize estimate (Agenda serial _ queue held limit) =
  Agenda serial estimate (rekey queue) (rekey held) limit
 where
  rekey = Map.fromList . map (\((_, number), item@(spent, work)) ->
    ((spent + estimate (parentOf work), number), item)) . Map.toList

parentOf :: Work state action continuation -> state
parentOf (Inspect state _) = state
parentOf (Apply state _ _) = state
parentOf (Resume state _ _) = state

pending :: Agenda state action continuation -> Int
pending (Agenda _ _ queue held _) = Map.size queue + Map.size held

-- Read-only presentation of the next scheduled branch, not a solved path.
-- Queued applications and continuations expose their parent without forcing
-- the operation or invoking a checker. Proof authority remains elsewhere.
principal :: Agenda state action continuation -> Maybe (state, Natural, Natural)
principal (Agenda _ _ queue held _) = do
  ((priority, _), (_, work)) <- Map.lookupMin $ if Map.null queue then held else queue
  let position state ancestors = (state, priority, fromIntegral $ length ancestors)
  pure $ case work of
    Inspect state ancestors -> position state ancestors
    Apply state _ ancestors -> position state ancestors
    Resume state _ ancestors -> position state ancestors

insert :: Natural -> Work state action continuation -> Agenda state action continuation
       -> Agenda state action continuation
insert spent work (Agenda serial estimate queue held limit) =
  Agenda (serial + 1) estimate
    (Map.insert (spent + estimate (parentOf work), serial) (spent, work) queue) held limit

-- One scheduling step. Exhausted means only an empty finite frontier, never
-- logical impossibility. Found retains the other alternatives for fresh-check
-- rejection or downstream failure; it is not a verification certificate.
step :: Monad m => Hooks m state action continuation result
     -> Agenda state action continuation -> m (Outcome state action continuation result)
step = stepWithDepth Nothing

-- An explicit depth bounds accepted branch transitions, not printed proof size
-- or work performed inside a move. Park blocked work once per limit setting,
-- rather than repeatedly scanning it or discarding it as mathematical failure.
-- A changed limit restores the exact priority/serial order of all alternatives.
stepWithDepth :: Monad m => Maybe Natural -> Hooks m state action continuation result
              -> Agenda state action continuation -> m (Outcome state action continuation result)
stepWithDepth requested hooks input = case Map.minViewWithKey queue of
  Nothing -> pure $ if Map.null held then Exhausted else DepthCensored original
  Just ((key, item@(spent, work)), rest) -> do
    allowed <- charge hooks
    if not allowed then pure $ Censored original
    else if blocked work then observe hooks DepthDeferred >> pure
      (Progress $ Agenda serial estimate rest (Map.insert key item held) requested)
    else
      let remaining = Agenda serial estimate rest held requested
          event = observe hooks
          transition parent ancestors result = case result of
            Declined -> event Rejected >> pure (Progress remaining)
            Deferred continuation -> event Yielded >> pure
              (Progress $ insert (spent+1) (Resume parent continuation ancestors) remaining)
            Advanced next -> do
              cyclic <- anyM (sameState hooks next) (parent:ancestors)
              if cyclic then event CyclePruned >> pure (Progress remaining)
              else event AdvancedState >> pure
                (Progress $ insert (spent+1) (Inspect next $ parent:ancestors) remaining)
      in case work of
        Inspect state ancestors -> inspect hooks state >>= \result -> case result of
          Candidate value -> event Proposed >> pure (Found value remaining)
          Stuck -> event Stalled >> pure (Progress remaining)
          Open proposals -> do
            event $ Expanded $ length proposals
            pure $ Progress $ foldl'
              (\agenda proposal -> insert (spent + 1 + penalty proposal)
                (Apply state (action proposal) ancestors) agenda) remaining proposals
        Apply state operation ancestors -> do
          event Attempted
          result <- apply hooks state operation
          transition state ancestors result
        Resume state continuation ancestors -> do
          event Resumed
          result <- resume hooks continuation
          transition state ancestors result
 where
  original@(Agenda serial estimate queue held _) = case input of
    Agenda n estimation active parked previous | requested /= previous ->
      Agenda n estimation (Map.union active parked) Map.empty requested
    _ -> input
  blocked work = maybe False (\limit -> case work of
    Inspect _ ancestors -> fromIntegral (length ancestors) > limit
    Apply _ _ ancestors -> fromIntegral (length ancestors) >= limit
    Resume _ _ ancestors -> fromIntegral (length ancestors) >= limit) requested

anyM :: Monad m => (a -> m Bool) -> [a] -> m Bool
anyM _ [] = pure False
anyM predicate (value:rest) = predicate value >>= \matched ->
  if matched then pure True else anyM predicate rest
