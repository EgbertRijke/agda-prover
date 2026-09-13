{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE LambdaCase #-}
-- SPDX-License-Identifier: GPL-3.0-or-later
-- Finite clause lookahead over the shared typed application inventory. This
-- module proposes programs; source-owner termination and fresh validation are
-- still required, and ordinary open clauses remain search alternatives.
module AgdaProver.Agda28.RecursivePrograms (propose) where

import Control.Monad (filterM, forM, void)
import Control.Monad.Except (catchError, throwError)
import Data.List (sortOn)
import Data.List.NonEmpty (NonEmpty (..))
import Data.Set qualified as Set
import Agda.Syntax.Abstract qualified as A
import Agda.Syntax.Abstract.Name (QName)
import Agda.Syntax.Abstract.Views (AppView' (..), appView, foldExpr)
import Agda.Syntax.Common
import Agda.Syntax.Info qualified as Info
import Agda.Syntax.Internal qualified as I
import Agda.Syntax.Internal.MetaVars (noMetas)
import Agda.Syntax.Position (noRange)
import Agda.Syntax.Scope.Base
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Reduce (reduce)
import Agda.TypeChecking.Rules.Term (checkExpr)
import Agda.TypeChecking.Substitute (absApp, raise)
import AgdaProver.Agda28.ClauseExecution qualified as Clause
import AgdaProver.Agda28.Construction (preservingAllocations)
import AgdaProver.Agda28.Recursion qualified as Recursion

propose :: TCM Bool -> (Clause.PreparationStep -> TCM ())
        -> (InteractionId -> I.Type -> TCM [(A.Expr, a)])
        -> Set.Set QName -> Recursion.Owner -> I.Type -> TCM [(A.Expr, [a])]
propose inspect charge inventory forbidden owner = introduce []
 where
  introduce parameters ty = do
    available <- inspect
    if not available || not (noMetas ty) then pure [] else reduce ty >>= \case
      I.El _ (I.Pi domain body) -> do
        let hint = if I.absName body `elem` ["", "_"] then "x" else I.absName body
        withFreshName noRange hint $ \name -> do
          drafts <- addContext (name, domain) $
            locallyScope scopeLocals ((A.nameConcrete name, LocalVar name LambdaBound []) :) $
              introduce (parameters ++ [Arg (getArgInfo domain) name])
                (absApp (raise 1 body) $ I.Var 0 [])
          pure [(A.Lam Info.exprNoRange
            (A.mkDomainFree $ Arg (getArgInfo domain) $ unnamed $ A.mkBinder_ name) draft, evidence)
            | (draft, evidence) <- drafts]
      _ -> recursiveFamily ty >>= \eligible -> if not eligible then pure [] else do
        context <- getContext
        subjects <- filterM (recursiveFamily . snd) =<< forM (zip [0..] context)
          (\(index, entry) -> (,) (ctxEntryName entry) <$> typeOfBV index)
        fmap concat $ forM subjects $ \(name, _) -> preservingAllocations $ recover $ do
          scope <- getScope
          point <- registerInteractionPoint False noRange Nothing
          let hole = A.QuestionMark (Info.emptyMetaInfo { Info.metaScope = scope }) point
          charge Clause.CheckScaffold
          void $ checkExpr hole ty
          draft <- Clause.prepare charge point $ Clause.BoundSubjects (name :| [])
          completed <- Clause.completeDrafts charge (leaf parameters name) point draft
          pure [(expression, evidence) | (expression, evidence) <- completed,
            Recursion.usesOwner owner expression]

  leaf parameters subject point ty = do
    charge Clause.CheckContext
    recursive <- Recursion.inspect point owner
    candidates <- inventory point ty
    -- This compound lane supplies genuinely recursive alternatives. A leaf
    -- with no observed descendant supplies a base; a descendant-bearing leaf
    -- uses the sealed recursive inventory. It is only a construction profile,
    -- never a rule that nonrecursive definitions are inadmissible.
    pure $ sortOn (profile parameters subject . fst)
      [candidate | candidate@(expression, _) <- candidates,
        Recursion.usesOwner owner expression == maybe False (const True) recursive]

  -- Prefer a parameter-preserving fold before changing or erasing unrelated
  -- coordinates. These are abstract binding identities, not printed names or
  -- type-specific arithmetic rules. Keep all alternatives and use the shared
  -- inventory's order to break ties. For a partial source clause, introduced
  -- parameters are the suffix of the recursive call's explicit spine.
  profile parameters subject expression =
    let expected = [unArg parameter | parameter <- parameters, visible parameter]
        unchanged = Set.delete subject $ Set.fromList expected
        variables = foldExpr (\case A.Var name -> Set.singleton name; _ -> Set.empty) expression
        calls = foldExpr (\term -> case appView term of
          Application (A.Def function) arguments | function == Recursion.ownerName owner ->
            [[namedArg argument | argument <- arguments, visible argument]]
          _ -> []) expression
        width = maximum $ 0 : map length calls
        mismatch arguments = length
          [() | (name, argument) <- zip expected (drop (length arguments - length expected) arguments),
            name /= subject, argument /= A.Var name]
    in if null calls then
      (negate $ Set.size $ Set.intersection unchanged variables, Set.member subject variables)
    else (sum [mismatch arguments | arguments <- calls, length arguments == width], False)

  -- Positivity metadata, not a spelling or a constructor-count convention,
  -- determines whether this eager recursive-program lookahead is useful.
  -- Unknown metadata and coinduction retain ordinary search.
  recursiveFamily :: I.Type -> TCM Bool
  recursiveFamily ty = inspect >>= \available ->
    if not available then pure False else reduce ty >>= \case
      I.El _ (I.Def family _) -> do
        definition <- getConstInfo family
        scope <- getScope
        let usable name = isNameInScope name scope && Set.notMember name forbidden
        pure $ case theDef definition of
          Datatype { dataMutual = Just (_:_), dataCons = constructors } ->
            not (null constructors) && all usable constructors
          RecordDefn record | _recInduction record /= Just CoInductive,
              Just (_:_) <- _recMutual record ->
            usable (I.conName $ _recConHead record) && all (usable . I.unDom) (_recFields record)
          _ -> False
      _ -> pure False
  recover :: TCM [b] -> TCM [b]
  recover action = action `catchError` \case
    TypeError{} -> pure []
    PatternErr{} -> pure []
    failure -> throwError failure
