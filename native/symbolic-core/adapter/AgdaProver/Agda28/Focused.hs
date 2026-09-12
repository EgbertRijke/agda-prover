{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE LambdaCase #-}
-- SPDX-License-Identifier: GPL-3.0-or-later
module AgdaProver.Agda28.Focused (Fragment (..), observe, render) where

import Control.Monad.State.Strict
import Control.Monad (forM, guard, mzero)
import Control.Monad.Trans.Maybe
import Data.List (findIndex)
import Data.List.NonEmpty (NonEmpty (..))
import Data.Set qualified as Set
import Data.Text qualified as T
import Agda.Syntax.Abstract qualified as A
import Agda.Syntax.Common
import Agda.Syntax.Common.Pretty (prettyShow)
import Agda.Syntax.Info (LetInfo (..), exprNoRange)
import Agda.Syntax.Internal qualified as I
import Agda.Syntax.Internal.MetaVars (noMetas)
import Agda.Syntax.Position (noRange)
import Agda.Syntax.Translation.InternalToAbstract (reify)
import Agda.TypeChecking.Free (isBinderUsed)
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Pretty (prettyTCM)
import Agda.TypeChecking.Reduce (instantiateFull, reduceB)
import Agda.TypeChecking.Substitute (absApp)
import AgdaProver.Symbolic.Focused qualified as F
import AgdaProver.Symbolic.NNUE.Features qualified as Features

data Fragment = Fragment
  { target :: F.Formula, assumptions :: [F.Formula], expressions :: [A.Expr]
  , atoms :: [A.Expr], atomViews :: [Features.FocusedView], emptyAtoms :: Set.Set Int }

-- Only visible, relevant, nondependent functions are erased to arrows. The
-- general native path handles other binders. Unknown/blocked types are not
-- atoms, and identical printed types are never used to identify native values.
observe :: I.Type -> TCM (Maybe Fragment)
observe expected = localTCState $ dontAssignMetas $ do
  (result, table) <- runStateT (runMaybeT $ do
    result <- formula expected
    context <- lift $ lift getContext
    entries <- fmap concat $ forM (reverse $ zip [0..] context) $ \(index, entry) -> do
      ty <- lift $ lift $ typeOfBV index
      converted <- lift $ runMaybeT $ formula ty
      pure [(A.Var $ ctxEntryName entry, value) | Just value <- [converted], usableModality entry]
    pure (result, entries)) []
  case result of
    Nothing -> pure Nothing
    Just (root, entries) -> do
      views <- mapM reify table
      labels <- mapM (fmap (Features.AtomView . T.pack . prettyShow) . prettyTCM) table
      empty <- fmap Set.fromList $ fmap concat $ forM (zip [0..] table) $ \(index, ty) ->
        case ty of
          I.El _ (I.Def name _) -> getConstInfo name >>= \definition -> pure $ case theDef definition of
            Datatype { dataCons = [] } -> [index]
            _ -> []
          _ -> pure []
      pure $ Just $ Fragment root (map snd entries) (map fst entries) views labels empty
 where
  formula :: I.Type -> MaybeT (StateT [I.Type] TCM) F.Formula
  formula supplied = do
    full <- lift $ lift $ instantiateFull supplied
    guard $ noMetas full
    value <- lift (lift $ reduceB full) >>= \case
      I.Blocked{} -> mzero
      I.NotBlocked _ value -> pure value
    case value of
      I.El _ (I.Pi domain result) -> do
        guard $ visible domain && getModality domain == getModality defaultArgInfo && not (isBinderUsed result)
        F.Arrow <$> formula (I.unDom domain) <*> formula (absApp result $ I.Var 0 [])
      I.El _ I.Sort{} -> mzero
      _ -> do
        table <- lift get
        case findIndex (== value) table of
          Just index -> pure $ F.Atom index
          Nothing -> lift (put $ table ++ [value]) >> pure (F.Atom $ length table)

render :: Fragment -> F.Proof -> TCM A.Expr
render fragment = go (expressions fragment) (assumptions fragment)
 where
  typeExpression (F.Atom index) = atoms fragment !! index
  typeExpression (F.Arrow a b) = A.Fun exprNoRange (defaultArg $ typeExpression a) $ typeExpression b
  go context _ (F.Variable index) = pure $ context !! index
  go context types (F.Apply function arguments) = A.app <$> go context types function
    <*> mapM (fmap (defaultArg . unnamed) . go context types) arguments
  go context types (F.Lambda ty body) = withFreshName noRange "x" $ \name -> do
    expression <- go (context ++ [A.Var name]) (types ++ [ty]) body
    pure $ A.Lam exprNoRange (A.mkDomainFree $ defaultArg $ unnamed $ A.mkBinder_ name) expression
  go context types (F.Absurd result subject) = do
    expression <- go context types subject
    let source = proofType types subject
    withFreshName noRange "eliminate" $ \name -> do
      let signature = A.Fun exprNoRange (defaultArg $ typeExpression source) $ typeExpression result
          binding = A.LetBind (LetRange noRange) defaultArgInfo (A.mkBindName name)
            signature (A.AbsurdLam exprNoRange NotHidden)
      pure $ A.Let exprNoRange (binding :| []) $ A.app (A.Var name) [defaultArg $ unnamed expression]
  proofType context (F.Variable index) = context !! index
  proofType context (F.Lambda ty body) = F.Arrow ty $ proofType (context ++ [ty]) body
  proofType context (F.Apply function arguments) = dropDomains (length arguments) $ proofType context function
  proofType _ (F.Absurd result _) = result
  dropDomains 0 ty = ty
  dropDomains n (F.Arrow _ rest) = dropDomains (n-1) rest
  dropDomains _ ty = ty
