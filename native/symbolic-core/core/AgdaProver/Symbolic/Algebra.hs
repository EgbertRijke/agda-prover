{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
-- SPDX-License-Identifier: GPL-3.0-or-later
-- Structural proof proposals from caller-supplied laws. This is neither a
-- normalizer nor an equality decision procedure. Atoms and evidence identities
-- come from the typed adapter; no declaration names or rendered terms occur.
module AgdaProver.Symbolic.Algebra
  ( Term (..), Proof (..), Edge (..), Operations (..), Event (..), Hooks (..)
  , enumerate ) where

import qualified Data.Sequence as Seq

data Term atom = Atom atom | Binary (Term atom) (Term atom)
  deriving (Eq, Ord, Show)
data Proof atom evidence
  = Given evidence
  | Commute evidence (Term atom) (Term atom)
  | Associate evidence (Term atom) (Term atom) (Term atom)
  | Invert evidence (Proof atom evidence)
  | Compose evidence (Proof atom evidence) (Proof atom evidence)
  | UnderLeft evidence (Term atom) (Proof atom evidence)
  | UnderRight evidence (Term atom) (Proof atom evidence)
  deriving (Eq, Ord, Show, Functor, Foldable)
data Edge atom evidence = Edge (Term atom) (Term atom) evidence
  deriving (Eq, Ord, Show)
data Operations evidence = Operations
  { commutativity :: [evidence], associativity :: [evidence]
  , symmetry :: [evidence], transitivity :: [evidence], congruence :: [evidence] }
  deriving (Eq, Show)
data Event = Visit | Rewrite | Deferred deriving (Eq, Show)
data Hooks m = Hooks { charge :: m Bool, observe :: Event -> m () }

-- Every traversal/rewrite is charged. Depth is supplied by the enclosing
-- widening controller, never a hard-coded theorem-size bound. A rejected
-- candidate keeps all alternatives. In particular, endpoint equality is NOT
-- evidence equality: neither a visited-term set nor a best-cost-by-term map may
-- erase a different inhabitant needed by a dependent downstream obligation.
enumerate :: (Monad m, Eq atom) => Hooks m -> Int -> Operations evidence
          -> [Edge atom evidence] -> Term atom -> Term atom
          -> (Proof atom evidence -> m (Maybe result)) -> m (Maybe result)
enumerate hooks depth ops concrete source target use =
  walk $ Seq.singleton (depth, source, Nothing)
 where
  charged event action = do
    ok <- charge hooks
    if ok then observe hooks event >> action else pure Nothing
  walk queue = case Seq.viewl queue of
    Seq.EmptyL -> pure Nothing
    (remaining, current, path) Seq.:< rest -> charged Visit $
      if remaining <= 0 then
        case steps current of
          [] -> walk rest
          _ -> observe hooks Deferred >> walk rest
      else inspect remaining path (steps current) rest
  inspect _ _ [] queue = walk queue
  inspect remaining path ((next, edge):edges) queue = charged Rewrite $
    let paths = case path of
          Nothing -> [edge]
          Just earlier -> [Compose compose earlier edge | compose <- transitivity ops]
    in combine remaining next paths queue $ inspect remaining path edges
  combine _ _ [] queue continue = continue queue
  combine remaining next (proof:proofs) queue continue = charged Rewrite $ do
    answer <- if next == target then use proof else pure Nothing
    case answer of
      Just _ -> pure answer
      Nothing -> combine remaining next proofs
        (queue Seq.|> (remaining-1, next, Just proof)) continue
  steps term = root term ++ case term of
    Atom{} -> []
    Binary left right ->
      [(Binary next right, UnderLeft lift right proof)
      | (next, proof) <- steps left, lift <- congruence ops]
      ++ [(Binary left next, UnderRight lift left proof)
         | (next, proof) <- steps right, lift <- congruence ops]
  root term =
    [(right, Given proof) | Edge left right proof <- concrete, term == left]
    ++ [(left, Invert inverse (Given proof))
       | Edge left right proof <- concrete, term == right, inverse <- symmetry ops]
    ++ case term of
      Atom{} -> []
      Binary left right ->
        [(Binary right left, Commute law left right) | law <- commutativity ops]
        ++ (case left of
          Binary a b -> [(Binary a (Binary b right), Associate law a b right)
            | law <- associativity ops]
          _ -> [])
        ++ (case right of
          Binary b c -> [(Binary (Binary left b) c, Invert inverse (Associate law left b c))
            | law <- associativity ops, inverse <- symmetry ops]
          _ -> [])
