{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE LambdaCase #-}
-- SPDX-License-Identifier: GPL-3.0-or-later
module AgdaProver.Agda28.ObservedEquations (propose) where

import Control.Monad (guard)
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.Maybe
import Data.IntSet qualified as IntSet
import Data.List (sortOn)
import Data.List.NonEmpty (NonEmpty (..))
import Data.Set qualified as Set

import Agda.Syntax.Abstract qualified as A
import Agda.Syntax.Abstract.Name (Name, QName, nameConcrete, qualify)
import Agda.Syntax.Abstract.Views (foldExpr)
import Agda.Syntax.Common hiding (Unrelated)
import Agda.Syntax.Info qualified as Info
import Agda.Syntax.Internal qualified as I
import Agda.Syntax.Internal.MetaVars (noMetas)
import Agda.Syntax.Position (noRange, rEnd', rStart', rangeFile)
import Agda.Syntax.Scope.Base (isNameInScope)
import Agda.Syntax.Translation.InternalToAbstract (reify, reifyPatterns)
import Agda.TypeChecking.Free (allFreeVars)
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Patterns.Internal (termToPattern)
import Agda.TypeChecking.Reduce (reduce)
import Agda.Utils.Null (empty)

-- These observations are clause proposals, not equations asserted by search.
-- Only the selected later goals contribute; their proofs are never premises.
-- Agda checks coverage, indices, recursive termination and every later law.
data Observation = Unrelated | Boundary | Equation [NamedArg A.Pattern] A.Expr

propose :: TCM Bool -> Set.Set QName -> QName -> InteractionId -> [InteractionId] -> TCM (Maybe A.Expr)
propose charge forbidden owner point later = do
  scope <- getScope
  ambient <- Set.fromList . map ctxEntryName <$> getContext
  parameters <- getDefFreeVars owner
  location <- ipRange <$> lookupInteractionPoint point
  ordered <- sourceOrder location [] later
  let visibleName name = name == owner ||
        (isNameInScope name scope && not (Set.member name forbidden))
  observed <- collect ambient visibleName parameters [] $ map snd $ sortOn fst ordered
  case observed of
    [] -> pure Nothing
    first:rest -> do
      allowed <- charge
      if not allowed then pure Nothing else do
        signature <- reify =<< typeOfConst owner
        withFreshName noRange "defined" $ \binding -> do
          helper <- qualify <$> currentModule <*> freshName_ "equations"
          let info = Info.mkDefInfo (nameConcrete binding) empty PublicAccess ConcreteDef noRange
              clause (patterns, rhs) = A.Clause (A.LHS empty $ A.LHSHead helper patterns) []
                (A.RHS rhs Nothing) A.noWhereDecls empty
          pure $ Just $ A.Let Info.exprNoRange
            (A.LetBind (Info.LetRange noRange) defaultArgInfo (A.mkBindName binding) signature
              (A.ExtendedLam Info.exprNoRange info defaultErased helper
                (clause first :| map clause rest)) :| [])
            (A.Var binding)
 where
  -- Joint readiness may reorder the agenda. Observations retain source order,
  -- and generated helpers without later source ranges are not statements.
  sourceOrder _ found [] = pure found
  sourceOrder location found (next:rest) = do
    allowed <- charge
    if not allowed then pure [] else do
      nextRange <- ipRange <$> lookupInteractionPoint next
      let found' = case (rEnd' location, rStart' nextRange) of
            (Just end, Just start) | rangeFile location == rangeFile nextRange, end <= start ->
              (start, next):found
            _ -> found
      sourceOrder location found' rest
  collect _ _ _ found [] = pure $ reverse found
  collect ambient visibleName parameters found (next:rest) = do
    allowed <- charge
    if not allowed then pure [] else do
      observed <- withInteractionId next $ do
        ty <- getMetaTypeInContext =<< lookupInteractionId next
        inspect ambient visibleName parameters ty
      case observed of
        Equation patterns rhs -> collect ambient visibleName parameters ((patterns, rhs):found) rest
        Unrelated | null found -> collect ambient visibleName parameters found rest
        _ -> pure $ reverse found
  inspect ambient visibleName parameters ty = do
    allowed <- charge
    if not allowed then pure Boundary else reduce ty >>= \case
      I.El _ (I.Pi domain body) -> underAbstraction domain body $
        inspect ambient visibleName parameters
      I.El _ (I.Def _ eliminations) -> case I.allApplyElims eliminations of
        Just args -> case reverse $ map unArg args of
          right:left:_ -> case (application left, application right) of
            (Just _, Just _) -> pure Boundary
            (Just lhs, Nothing) -> equation ambient visibleName parameters lhs right
            (Nothing, Just lhs) -> equation ambient visibleName parameters lhs left
            _ -> pure Unrelated
          _ -> pure Unrelated
        Nothing -> pure Unrelated
      _ -> pure Unrelated
  application (I.Def name eliminations) | name == owner = I.allApplyElims eliminations
  application _ = Nothing
  equation :: Set.Set Name -> (QName -> Bool) -> Int -> [Arg I.Term] -> I.Term -> TCM Observation
  equation ambient visibleName parameters lhs rhs = do
    found <- runMaybeT $ do
      let operands = drop parameters lhs
      guard $ not (null operands) && noMetas operands && noMetas rhs
      patterns <- lift $ termToPattern operands
      variables <- MaybeT $ pure $ traverse linearPattern (patterns :: [Arg I.DeBruijnPattern])
      let bindings = concat variables
      guard $ length bindings == IntSet.size (IntSet.fromList bindings)
      guard $ any (rigid . unArg) patterns
      guard $ all visibleName $ foldMap (patternNames . unArg) patterns
      let captured = IntSet.toList $ allFreeVars rhs `IntSet.difference` IntSet.fromList bindings
      capturedNames <- lift $ mapM nameOfBV captured
      guard $ all (`Set.member` ambient) capturedNames
      abstractPatterns <- lift $ withShowAllArguments $ reifyPatterns $ map (fmap unnamed) patterns
      expression <- lift $ withShowAllArguments $ reify rhs
      let names = foldExpr referenced expression
      guard $ all visibleName names
      pure $ Equation abstractPatterns expression
    pure $ maybe Boundary id found
  linearPattern argument = case unArg argument of
    I.VarP _ variable -> Just [I.dbPatVarIndex variable]
    I.ConP _ _ patterns -> concat <$> mapM (linearPattern . fmap namedThing) patterns
    I.LitP{} -> Just []
    _ -> Nothing
  rigid I.ConP{} = True
  rigid I.LitP{} = True
  rigid _ = False
  patternNames (I.ConP constructor _ patterns) = Set.insert (I.conName constructor) $
    foldMap (patternNames . namedArg) patterns
  patternNames _ = Set.empty
  referenced (A.Def name) = Set.singleton name
  referenced (A.Con (I.AmbQ names)) = Set.fromList $ foldr (:) [] names
  referenced (A.Proj _ (I.AmbQ names)) = Set.fromList $ foldr (:) [] names
  referenced _ = Set.empty
