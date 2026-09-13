{-# LANGUAGE ImportQualifiedPost #-}
-- SPDX-License-Identifier: GPL-3.0-or-later
-- A coupled state owns all its AND obligations. Alternatives never merge
-- substitutions. This module schedules opaque typed states/actions; the native
-- adapter alone observes, checks and reconstructs them.
module AgdaProver.Symbolic.Agenda
  ( Agenda, Proposal (..), Inspection (..), Transition (..), Outcome (..)
  , Event (..), Hooks (..), rankedProposals, dependentFirst, start, prioritize, localize, pending, principal, step, stepWithDepth ) where

import Data.Map.Strict qualified as Map
import Data.List (foldl')
import Data.Set qualified as Set
import Numeric.Natural (Natural)

data Proposal action = Proposal
  { action :: action, penalty :: Natural } deriving (Eq, Show)

-- Widen an already ranked family across agenda cost tiers. Ranking only the
-- insertion order would put its entire catalogue ahead of every descendant
-- at the next depth, defeating learned guidance in a broad scope. No proposal
-- is removed: even the last has a finite, caller-visible scheduling cost.
rankedProposals :: Natural -> [action] -> [Proposal action]
rankedProposals delay = zipWith (flip Proposal) [delay..]

-- Order a compound elimination before the values its subjects depend on.
-- Edges point from a dependent to its prerequisites. Unselected vertices
-- retain transitive constraints but are never returned as actions. Kahn's
-- queue preserves learned preference among ready subjects, in O((V+E) log V).
-- An incomplete/cyclic ordering is not an admissibility proof: keep the
-- original alternatives, and let the adapter check every resulting proposal.
dependentFirst :: Ord a => Map.Map a (Set.Set a) -> [a] -> [a]
dependentFirst edges preferred
  | Map.size positions /= length preferred = preferred
  | otherwise = go degrees ready [] 0
 where
  positions = Map.fromList $ zip preferred [0 :: Int ..]
  vertices = Set.unions $ Map.keysSet positions : Map.keysSet edges : Map.elems edges
  degrees = Map.unionWith (+) (Map.fromSet (const (0 :: Int)) vertices) $
    Map.fromListWith (+) [(target, 1) | targets <- Map.elems edges, target <- Set.toList targets]
  key vertex = (Map.findWithDefault (-1) vertex positions, vertex)
  ready = Set.fromList [key vertex | (vertex, 0) <- Map.toList degrees]
  go remaining queue result visited = case Set.minView queue of
    Nothing | visited == Set.size vertices -> reverse result
            | otherwise -> preferred
    Just ((_, vertex), rest) ->
      let release (counts, unlocked) target =
            let count = (counts Map.! target) - 1
            in (Map.insert target count counts,
                if count == 0 then Set.insert (key target) unlocked else unlocked)
          (next, available) = foldl' release (remaining, rest) $
            Set.toList $ Map.findWithDefault Set.empty vertex edges
          chosen = if Map.member vertex positions then vertex : result else result
      in go next available chosen (visited + 1)

data Inspection action result = Open [Proposal action] | Candidate result | Stuck
  deriving (Eq, Show)
-- A deferred operation can report additional spent scheduling work. It is not
-- a second budget charge: the owner's physical ledger remains authoritative.
data Transition state action continuation
  = Advanced state
  | AdvancedWithRemainder state Natural continuation
  -- A completed original stage starts a new local priority, not a new budget
  -- or proof depth. The adapter must certify a strictly smaller finite set of
  -- original obligations; arbitrary refinements cannot request this reset.
  | Checkpoint state (Maybe (Natural, continuation))
  | Planned [Proposal action]
  | Deferred Natural continuation | Declined
  deriving (Eq, Show)
data Event = Expanded Int | Attempted | Resumed | AdvancedState | Yielded
  | Rejected | CyclePruned | Proposed | Stalled | DepthDeferred
  deriving (Eq, Show)

data Hooks m state action continuation result = Hooks
  { charge :: m Bool
  , observe :: Event -> m ()
  , inspect :: state -> m (Inspection action result)
  , apply :: state -> action -> m (Transition state action continuation)
  , resume :: continuation -> m (Transition state action continuation)
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
type Priority = (Natural, Integer)
type Scope = (Natural, Integer)
type Entry state action continuation = (Natural, Scope, Work state action continuation)
type Entries state action continuation = Map.Map Priority (Entry state action continuation)
type FocusPriority = (Natural, Integer, Natural, Integer)
data Agenda state action continuation = Agenda
  { nextSerial :: Integer
  , estimateCost :: state -> Natural
  , activeEntries :: Entries state action continuation
  , heldEntries :: Entries state action continuation
  , heldDepth :: Maybe Natural
  , entryOrder :: Maybe (state -> Natural)
  , focusedEntries :: Map.Map FocusPriority Priority
  , focusTurn :: Bool }

data Outcome state action continuation result
  = Progress (Agenda state action continuation)
  | Found result (Agenda state action continuation)
  | Censored (Agenda state action continuation)
  | DepthCensored (Agenda state action continuation)
  | Exhausted

start :: state -> Agenda state action continuation
start state = insert 0 (0, 0) (Inspect state []) $
  Agenda 0 (const 0) Map.empty Map.empty Nothing Nothing Map.empty True

-- Reordering is explicit and deterministic, retaining serial tie breaks,
-- spent cost, held work and every alternative. No admissibility claim is made.
prioritize :: (state -> Natural) -> Agenda state action continuation -> Agenda state action continuation
prioritize estimate agenda = reindex agenda
  { estimateCost = estimate, activeEntries = rekey $ activeEntries agenda,
    heldEntries = rekey $ heldEntries agenda }
 where
  rekey = Map.fromList . map (\((_, number), item@(spent, _, work)) ->
    ((spent + estimate (parentOf work), number), item)) . Map.toList

-- Alternate focused local work with the existing global cost order, using two
-- indexes over ONE queue. A checkpoint opens a new local scope. Within equally
-- advanced scopes, the oldest scope gets the focused turn; NNUE-derived local
-- penalties still order its alternatives. Global turns retain fair access to
-- every finite-cost fallback, including revisions of an unsuccessful prefix.
-- The adapter supplies progress only at original-entry boundaries, never from
-- a provisional decrease in visible holes or from a theorem's identity.
localize :: (state -> Natural) -> Agenda state action continuation -> Agenda state action continuation
localize order agenda = reindex agenda
  { entryOrder = Just order, focusTurn = True,
    activeEntries = Map.map assign $ activeEntries agenda,
    heldEntries = Map.map assign $ heldEntries agenda }
 where
  assign (spent, (_, scope), work) = (spent, (order $ parentOf work, scope), work)

focusKey :: Priority -> Entry state action continuation -> FocusPriority
focusKey (priority, number) (_, (progress, scope), _) = (progress, scope, priority, number)

reindex :: Agenda state action continuation -> Agenda state action continuation
reindex agenda = agenda { focusedEntries = case entryOrder agenda of
  Nothing -> Map.empty
  Just _ -> Map.fromList [(focusKey key item, key) | (key, item) <- Map.toList $ activeEntries agenda] }

nextEntry :: Agenda state action continuation -> Maybe (Priority, Entry state action continuation)
nextEntry agenda = do
  key <- if focusTurn agenda && entryOrderEnabled agenda
    then snd <$> Map.lookupMin (focusedEntries agenda)
    else fst <$> Map.lookupMin (activeEntries agenda)
  item <- Map.lookup key $ activeEntries agenda
  pure (key, item)

entryOrderEnabled :: Agenda state action continuation -> Bool
entryOrderEnabled = maybe False (const True) . entryOrder

parentOf :: Work state action continuation -> state
parentOf (Inspect state _) = state
parentOf (Apply state _ _) = state
parentOf (Resume state _ _) = state

pending :: Agenda state action continuation -> Int
pending agenda = Map.size (activeEntries agenda) + Map.size (heldEntries agenda)

-- Read-only presentation of the next scheduled branch, not a solved path.
-- Queued applications and continuations expose their parent without forcing
-- the operation or invoking a checker. Proof authority remains elsewhere.
principal :: Agenda state action continuation -> Maybe (state, Natural, Natural)
principal agenda = do
  ((priority, _), (_, _, work)) <- if Map.null (activeEntries agenda)
    then Map.lookupMin (heldEntries agenda) else nextEntry agenda
  let position state ancestors = (state, priority, fromIntegral $ length ancestors)
  pure $ case work of
    Inspect state ancestors -> position state ancestors
    Apply state _ ancestors -> position state ancestors
    Resume state _ ancestors -> position state ancestors

insert :: Natural -> Scope -> Work state action continuation -> Agenda state action continuation
       -> Agenda state action continuation
insert spent scope work agenda = agenda
  { nextSerial = serial + 1
  , activeEntries = Map.insert key item $ activeEntries agenda
  , focusedEntries = if entryOrderEnabled agenda
      then Map.insert (focusKey key item) key $ focusedEntries agenda
      else focusedEntries agenda }
 where
  serial = nextSerial agenda
  key = (spent + estimateCost agenda (parentOf work), serial)
  item = (spent, scope, work)

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
stepWithDepth requested hooks input = case nextEntry original of
  Nothing -> pure $ if Map.null (heldEntries original) then Exhausted else DepthCensored original
  Just (key, item@(spent, scope, work)) -> do
    let remaining = original
          { activeEntries = Map.delete key $ activeEntries original
          , focusedEntries = Map.delete (focusKey key item) $ focusedEntries original
          , focusTurn = not $ focusTurn original }
    allowed <- charge hooks
    if not allowed then pure $ Censored original
    else if blocked work then observe hooks DepthDeferred >> pure
      (Progress remaining { heldEntries = Map.insert key item $ heldEntries original })
    else
      let event = observe hooks
          transition parent ancestors result = case result of
            Declined -> event Rejected >> pure (Progress remaining)
            Planned proposals -> do
              event $ Expanded $ length proposals
              pure $ Progress $ foldl'
                (\agenda proposal -> insert (spent + 1 + penalty proposal)
                  scope (Apply parent (action proposal) ancestors) agenda) remaining proposals
            Deferred extra continuation -> event Yielded >> pure
              (Progress $ insert (spent+1+extra) scope (Resume parent continuation ancestors) remaining)
            AdvancedWithRemainder next extra continuation -> do
              let retain = insert (spent+1+extra) scope (Resume parent continuation ancestors)
              cyclic <- anyM (sameState hooks next) (parent:ancestors)
              if cyclic then event CyclePruned >> pure (Progress $ retain remaining)
              else event AdvancedState >> pure
                (Progress $ retain $ insert (spent+1) scope (Inspect next $ parent:ancestors) remaining)
            Checkpoint next remainder -> do
              let retain = maybe id (\(extra, continuation) ->
                    insert (spent+1+extra) scope (Resume parent continuation ancestors)) remainder
                  localScope = case entryOrder remaining of
                    Nothing -> scope
                    Just order -> (order next, nextSerial remaining)
              cyclic <- anyM (sameState hooks next) (parent:ancestors)
              if cyclic then event CyclePruned >> pure (Progress $ retain remaining)
              else event AdvancedState >> pure
                (Progress $ retain $ insert 0 localScope (Inspect next $ parent:ancestors) remaining)
            Advanced next -> do
              cyclic <- anyM (sameState hooks next) (parent:ancestors)
              if cyclic then event CyclePruned >> pure (Progress remaining)
              else event AdvancedState >> pure
                (Progress $ insert (spent+1) scope (Inspect next $ parent:ancestors) remaining)
      in case work of
        Inspect state ancestors -> inspect hooks state >>= \result -> case result of
          Candidate value -> event Proposed >> pure (Found value remaining)
          Stuck -> event Stalled >> pure (Progress remaining)
          Open proposals -> do
            event $ Expanded $ length proposals
            pure $ Progress $ foldl'
              (\agenda proposal -> insert (spent + 1 + penalty proposal)
                scope (Apply state (action proposal) ancestors) agenda) remaining proposals
        Apply state operation ancestors -> do
          event Attempted
          result <- apply hooks state operation
          transition state ancestors result
        Resume state continuation ancestors -> do
          event Resumed
          result <- resume hooks continuation
          transition state ancestors result
 where
  original | requested /= heldDepth input = reindex input
               { activeEntries = Map.union (activeEntries input) (heldEntries input),
                 heldEntries = Map.empty, heldDepth = requested }
           | otherwise = input
  blocked work = maybe False (\limit -> case work of
    Inspect _ ancestors -> fromIntegral (length ancestors) > limit
    Apply _ _ ancestors -> fromIntegral (length ancestors) >= limit
    Resume _ _ ancestors -> fromIntegral (length ancestors) >= limit) requested

anyM :: Monad m => (a -> m Bool) -> [a] -> m Bool
anyM _ [] = pure False
anyM predicate (value:rest) = predicate value >>= \matched ->
  if matched then pure True else anyM predicate rest
