{-# LANGUAGE ImportQualifiedPost #-}
-- SPDX-License-Identifier: GPL-3.0-or-later
-- A coupled state owns all its AND obligations. Alternatives never merge
-- substitutions. This module schedules opaque typed states/actions; the native
-- adapter alone observes, checks and reconstructs them.
module AgdaProver.Symbolic.Agenda
  ( Agenda, Proposal (..), Inspection (..), Transition (..), Outcome (..)
  , Event (..), Hooks (..), start, pending, step ) where

import Data.Map.Strict qualified as Map
import Data.List (foldl')
import Numeric.Natural (Natural)

data Proposal action = Proposal
  { action :: action, penalty :: Natural } deriving (Eq, Show)
data Inspection action result = Open [Proposal action] | Candidate result | Stuck
  deriving (Eq, Show)
data Transition state continuation = Advanced state | Deferred continuation | Declined
  deriving (Eq, Show)
data Event = Expanded Int | Attempted | Resumed | AdvancedState | Yielded
  | Rejected | CyclePruned | Proposed | Stalled
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
data Agenda state action continuation = Agenda Integer
  (Map.Map (Natural, Integer) (Work state action continuation))

data Outcome state action continuation result
  = Progress (Agenda state action continuation)
  | Found result (Agenda state action continuation)
  | Censored (Agenda state action continuation)
  | Exhausted

start :: state -> Agenda state action continuation
start state = insert 0 (Inspect state []) $ Agenda 0 Map.empty

pending :: Agenda state action continuation -> Int
pending (Agenda _ queue) = Map.size queue

insert :: Natural -> Work state action continuation -> Agenda state action continuation
       -> Agenda state action continuation
insert priority work (Agenda serial queue) =
  Agenda (serial + 1) $ Map.insert (priority, serial) work queue

-- One scheduling step. Exhausted means only an empty finite frontier, never
-- logical impossibility. Found retains the other alternatives for fresh-check
-- rejection or downstream failure; it is not a verification certificate.
step :: Monad m => Hooks m state action continuation result
     -> Agenda state action continuation -> m (Outcome state action continuation result)
step hooks original@(Agenda serial queue) = case Map.minViewWithKey queue of
  Nothing -> pure Exhausted
  Just (((priority, _), work), rest) -> do
    allowed <- charge hooks
    if not allowed then pure $ Censored original else
      let remaining = Agenda serial rest
          event = observe hooks
          transition parent ancestors result = case result of
            Declined -> event Rejected >> pure (Progress remaining)
            Deferred continuation -> event Yielded >> pure
              (Progress $ insert (priority+1) (Resume parent continuation ancestors) remaining)
            Advanced next -> do
              cyclic <- anyM (sameState hooks next) (parent:ancestors)
              if cyclic then event CyclePruned >> pure (Progress remaining)
              else event AdvancedState >> pure
                (Progress $ insert (priority+1) (Inspect next $ parent:ancestors) remaining)
      in case work of
        Inspect state ancestors -> inspect hooks state >>= \result -> case result of
          Candidate value -> event Proposed >> pure (Found value remaining)
          Stuck -> event Stalled >> pure (Progress remaining)
          Open proposals -> do
            event $ Expanded $ length proposals
            pure $ Progress $ foldl'
              (\agenda proposal -> insert (priority + 1 + penalty proposal)
                (Apply state (action proposal) ancestors) agenda) remaining proposals
        Apply state operation ancestors -> do
          event Attempted
          result <- apply hooks state operation
          transition state ancestors result
        Resume state continuation ancestors -> do
          event Resumed
          result <- resume hooks continuation
          transition state ancestors result

anyM :: Monad m => (a -> m Bool) -> [a] -> m Bool
anyM _ [] = pure False
anyM predicate (value:rest) = predicate value >>= \matched ->
  if matched then pure True else anyM predicate rest
