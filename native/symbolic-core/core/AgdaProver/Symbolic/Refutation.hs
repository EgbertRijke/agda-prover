-- SPDX-License-Identifier: GPL-3.0-or-later
-- Finite Boolean witness finding for the existing abstract implication
-- fragment. No result here asserts impossibility. A typed adapter must bind
-- the complete source declaration, and Agda must check the compiled refutation.
module AgdaProver.Symbolic.Refutation
  ( ClosedType (..), Expression (..), Witness (..), Result (..)
  , findCounterexample, specialize, inhabit, refute ) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import AgdaProver.Symbolic.Focused (Formula (..))

data ClosedType = Empty | Unit | Function ClosedType ClosedType
  deriving (Eq, Ord, Show)
-- De Bruijn variables and explicitly typed lambdas/empty elimination. This
-- is a certificate recipe over newly declared empty/unit types, not evidence
-- for an arbitrary user's Empty/Unit spelling or a replacement typechecker.
data Expression = Variable Int | UnitValue | Lambda ClosedType Expression
  | Apply Expression Expression | Absurd ClosedType Expression
  deriving (Eq, Ord, Show)
data Witness = Witness
  { valuation :: Map.Map Int Bool, specialized :: ClosedType
  , refutation :: Expression }
  deriving (Eq, Show)
data Result = Counterexample Witness Integer | NoCounterexample Integer
  | Censored Integer deriving (Eq, Show)

-- Valuations are deterministic. The caller owns the assignment allowance and
-- interruption, not a fixed atom/assignment/time ceiling in this module.
-- Exhausted classical enumeration is NOT an intuitionistic proof, and a
-- censored run is neither a negative logical label nor an impossibility claim.
findCounterexample :: Monad m => m Bool -> Formula -> m Result
findCounterexample charge formula = go 0 $ assignments names
 where
  names = Set.toAscList $ atoms [formula] Set.empty
  atoms [] found = found
  atoms (Atom name:rest) found = atoms rest $ Set.insert name found
  atoms (Arrow a b:rest) found = atoms (a:b:rest) found
  assignments [] = [Map.empty]
  assignments (name:rest) = [Map.insert name value later
    | value <- [False,True], later <- assignments rest]
  go checked [] = pure $ NoCounterexample checked
  go checked (values:rest) = do
    allowed <- charge
    if not allowed then pure $ Censored checked else
      case specialize values formula >>= negative values of
        Just witness -> pure $ Counterexample witness (checked+1)
        Nothing -> go (checked+1) rest
  -- Evaluate first. Do not allocate and throw away potentially large positive
  -- argument proofs for every non-counterexample valuation.
  negative values ty
    | holds ty = Nothing
    | otherwise = Witness values ty <$> refute ty (Variable 0)

holds :: ClosedType -> Bool
holds Empty = False
holds Unit = True
holds (Function a b) = not (holds a) || holds b

specialize :: Map.Map Int Bool -> Formula -> Maybe ClosedType
specialize values (Atom name) = (\b -> if b then Unit else Empty) <$> Map.lookup name values
specialize values (Arrow a b) = Function <$> specialize values a <*> specialize values b

inhabit :: ClosedType -> Maybe Expression
inhabit Empty = Nothing
inhabit Unit = Just UnitValue
inhabit (Function a b) = case inhabit b of
  Just expression -> Just $ Lambda a expression
  Nothing -> Lambda a . Absurd b <$> refute a (Variable 0)

-- The supplied expression remains in the current context. Positive arguments
-- are closed; constructing them never captures or shifts that expression.
refute :: ClosedType -> Expression -> Maybe Expression
refute Unit _ = Nothing
refute Empty expression = Just expression
refute (Function a b) expression = do
  argument <- inhabit a
  refute b $ Apply expression argument
