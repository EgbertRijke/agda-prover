{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE LambdaCase #-}
-- SPDX-License-Identifier: GPL-3.0-or-later
module AgdaProver.Agda28.DraftAssembly (assemble) where

import Data.Map.Strict qualified as Map
import Data.Set qualified as Set
import Agda.Syntax.Abstract qualified as A
import Agda.Syntax.Abstract.Views (recurseExpr)
import Agda.Syntax.Common (InteractionId)

-- Actions are chronological on one checked branch. Splice by native interaction
-- identity, never printed question marks, binders, helper names or source text.
-- Unrelated original goals remain outside this expression; final rechecking
-- from the original parent decides whether the assembled draft can stand there.
assemble :: InteractionId -> [(InteractionId, A.Expr)] -> Either String A.Expr
assemble target actions = case dropWhile ((/= target) . fst) actions of
  [] -> Left "native-reconstruction-goal-not-assigned"
  (_, expression):rest ->
    let replacements = Map.fromList rest in
    if Map.size replacements /= length rest || Map.member target replacements
      then Left "native-reconstruction-repeated-goal-assignment"
      else replace replacements (Set.singleton target) expression
 where
  -- One structural traversal rather than rescanning a growing proof once per
  -- solved leaf. Expansion follows native draft dependencies; cycles fail
  -- before reconstruction can loop, even if an upstream invariant regresses.
  replace replacements active = recurseExpr $ \expression children -> case expression of
    A.QuestionMark _ point | Just replacement <- Map.lookup point replacements ->
      if Set.member point active then Left "native-reconstruction-cyclic-draft"
      else replace replacements (Set.insert point active) replacement
    _ -> children
