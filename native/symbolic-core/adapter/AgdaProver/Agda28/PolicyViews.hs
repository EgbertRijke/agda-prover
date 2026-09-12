{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE OverloadedStrings #-}
-- SPDX-License-Identifier: GPL-3.0-or-later
-- Legacy model feature views of native syntax, never a semantic term IR.
module AgdaProver.Agda28.PolicyViews (termView, refinementView) where

import Data.Set qualified as Set
import Data.Text (Text)
import Agda.Syntax.Abstract qualified as A
import Agda.Syntax.Common (namedArg)
import AgdaProver.Symbolic.NNUE.Features qualified as F

-- Preserve the old lambda/application vocabulary where it actually applies.
-- Richer Agda syntax is deliberately unscored, not flattened to a fake atom.
termView :: A.Expr -> Maybe F.TermView
termView = go Set.empty
 where
  atom tag = Just $ F.TermView tag 1 1 0 0
  go bound expression = case expression of
    A.ScopedExpr _ inner -> go bound inner
    A.Var name -> atom $ if Set.member name bound then "bound" else "local"
    A.Def'{} -> atom "local"
    A.Proj{} -> atom "local"
    A.Con{} -> atom "local"
    A.App _ function argument -> do
      f <- go bound function
      a <- go bound $ namedArg argument
      pure $ F.TermView "apply" (1 + F.termSize f + F.termSize a)
        (1 + max (F.termDepth f) (F.termDepth a))
        (F.termLambdas f + F.termLambdas a)
        (1 + F.termApplications f + F.termApplications a)
    A.Lam _ (A.DomainFree _ binding) body
      | A.Binder Nothing _ name <- namedArg binding -> do
      inner <- go (Set.insert (A.unBind name) bound) body
      pure inner { F.termRoot = "lambda", F.termSize = F.termSize inner + 1,
        F.termDepth = F.termDepth inner + 1, F.termLambdas = F.termLambdas inner + 1 }
    _ -> Nothing

-- Only recognize actions represented by the existing one-step model. Globals,
-- partial applications and exotic syntax remain available in symbolic order.
refinementView :: A.Expr -> Maybe (Text, Maybe A.Name)
refinementView expression = case expression of
  A.ScopedExpr _ inner -> refinementView inner
  A.Var name -> Just ("use-local", Just name)
  A.Con{} -> Just ("select-constructor", Nothing)
  A.Lam{} -> Just ("introduce-lambda", Nothing)
  A.Rec{} -> Just ("introduce-constructor", Nothing)
  _ -> Nothing
