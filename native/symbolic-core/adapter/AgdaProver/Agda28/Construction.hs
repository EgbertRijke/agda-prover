{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE LambdaCase #-}
-- SPDX-License-Identifier: GPL-3.0-or-later
module AgdaProver.Agda28.Construction
  ( recordPlan, recordExpression, projectedEvidence, omittedField, absurdLambda, eliminateEmpty
  , constructorClosures, constructionScaffold ) where

import Control.Monad (filterM)
import Control.Monad.Except (catchError)
import Data.Maybe (catMaybes)
import Data.List.NonEmpty (NonEmpty (..))
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set

import Agda.Syntax.Abstract qualified as A
import Agda.Syntax.Abstract.Name (QName)
import Agda.Syntax.Abstract.Views (traverseExpr)
import Agda.Syntax.Common
import Agda.Syntax.Concrete (FieldAssignment' (..))
import Agda.Syntax.Concrete.Name qualified as C
import Agda.Syntax.Info (LetInfo (..), exprNoRange)
import Agda.Syntax.Info qualified as Info
import Agda.Syntax.Internal qualified as I
import Agda.Syntax.Internal.MetaVars (noMetas)
import Agda.Syntax.Position (noRange)
import Agda.Syntax.Scope.Base (isNameInScope, LocalVar (..), BindingSource (..), scopeLocals)
import Agda.Syntax.Translation.InternalToAbstract (reify)
import Agda.Interaction.BasicOps (give_)
import Agda.Interaction.Base (UseForce (WithoutForce))
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Constraints (noConstraints)
import Agda.TypeChecking.Conversion (compareType)
import Agda.TypeChecking.Records (isRecordType, recordFieldNames)
import Agda.TypeChecking.Reduce (instantiateFull, reduce)
import Agda.TypeChecking.Rules.Term (checkExpr, inferExpr')
import Agda.TypeChecking.Substitute (apply, absApp, raise)
import Agda.Utils.Null (empty)

-- Focused introductions ending in a visible nullary constructor. These are
-- proposals, not assertions that a dependent result index matches. Checking
-- the whole expression can propagate that index into other open definitions.
-- No proof-specific family, spelling or reference implementation is involved.
constructorClosures :: TCM Bool -> Set.Set QName -> I.Type -> TCM [A.Expr]
constructorClosures charge forbidden target = charge >>= \allowed ->
  if not allowed then pure [] else reduce target >>= \case
    I.El _ (I.Pi domain body) -> do
      let hint = if I.absName body `elem` ["", "_"] then "x" else I.absName body
      withFreshName noRange hint $ \name -> do
        bodies <- addContext (name, domain) $ constructorClosures charge forbidden
          (absApp (raise 1 body) $ I.Var 0 [])
        pure [A.Lam exprNoRange
          (A.mkDomainFree $ Arg (getArgInfo domain) $ unnamed $ A.mkBinder_ name) expression
          | expression <- bodies]
    I.El _ (I.Def family _) -> do
      scope <- getScope
      definition <- getConstInfo family
      let constructors = case theDef definition of
            Datatype { dataCons = names } -> names
            RecordDefn record | _recInduction record /= Just CoInductive ->
              [I.conName $ _recConHead record]
            _ -> []
          availableName name = isNameInScope name scope && not (Set.member name forbidden)
      names <- filterM (\name -> charge >>= \available ->
        if not available then pure False else getConstInfo name >>= \entry -> pure $
          case theDef entry of Constructor { conArity = 0 } -> True; _ -> False)
        (filter availableName constructors)
      pure [A.Con $ I.AmbQ (name :| []) | name <- names]
    _ -> pure []

-- Expose a finite introduction tree, closing uniquely matching local leaves.
-- Unresolved types, nondecreasing repeated families and genuine choices remain
-- explicit goals; the ordinary agenda retains all alternatives. Each hole is
-- created in its native context, and the finished draft is kernel-checked.
-- This is not used by the cheap later-goal constructor-closure probe.
constructionScaffold :: TCM Bool -> TCM Bool -> Set.Set QName -> I.Type -> TCM (Maybe A.Expr)
constructionScaffold inspect charge forbidden target = do
  (expression, introduced) <- build Map.empty target
  pure $ if introduced then Just expression else Nothing
 where
  hole ty = do
    scope <- getScope
    point <- registerInteractionPoint False noRange Nothing
    let expression = A.QuestionMark (Info.emptyMetaInfo { Info.metaScope = scope }) point
    value <- check expression ty
    pure (expression, value)
  build seen ty = do
    allowed <- inspect
    if not allowed then genericError "native-construction-allowance-spent"
    -- This eager optimization needs an established dependent type. Expanding
    -- a constructor telescope against unresolved indices can multiply Agda's
    -- postponed substitutions before control returns to the agenda. Leave an
    -- ordinary obligation instead: atomic refinement can still instantiate
    -- those indices, and a later invocation can build their resolved shape.
    -- Inspect the native tree before reducing/instantiating it; this is not a
    -- size limit or a rejection of the branch's mathematical goal.
    else if not (noMetas ty) then unresolved ty else reduce ty >>= \case
      I.El _ (I.Pi domain body) -> do
        let hint = if I.absName body `elem` ["", "_"] then "x" else I.absName body
        withFreshName noRange hint $ \name -> do
          -- Adding a typed binder does not add it to Agda's syntactic scope.
          -- Every nested hole must see the same native name as its enclosing
          -- lambda, including hidden/instance binders and captured prefixes.
          (expression, _) <- addContext (name, domain) $
            locallyScope scopeLocals ((A.nameConcrete name, LocalVar name LambdaBound []) :) $
              build seen (absApp (raise 1 body) $ I.Var 0 [])
          pure (A.Lam exprNoRange
            (A.mkDomainFree $ Arg (getArgInfo domain) $ unnamed $ A.mkBinder_ name) expression, True)
      normalHead@(I.El _ (I.Def family _))
        | let size = I.termSize $ I.unEl normalHead
        , maybe True (size <) (Map.lookup family seen) -> do
        definition <- getConstInfo family
        let next = Map.insert family size seen
        case theDef definition of
          RecordDefn record | _recInduction record /= Just CoInductive ->
            recordPlan forbidden ty >>= \case
              Just (names, telescope) -> do
                assignments <- fields next names telescope
                pure (recordExpression assignments, True)
              Nothing -> unresolved ty
          Datatype { dataCons = names } -> do
            scope <- getScope
            compatible <- filterM (\name -> localTCState $
              (prepare name ty >> pure True) `catchError` (\_ -> pure False))
              [name | name <- names, isNameInScope name scope, not $ Set.member name forbidden]
            case compatible of
              [name] -> do
                (expression, holes) <- prepare name ty
                completed <- fill next expression holes Map.empty
                pure (completed, True)
              _ -> unresolved ty
          _ -> unresolved ty
      _ -> unresolved ty
  unresolved ty = do
    locals <- if not (noMetas ty) then pure [] else do
      context <- getContext
      fmap catMaybes $ mapM (\entry -> localTCState $
        (do allowed <- charge
            if not allowed then pure Nothing else do
              let expression = A.Var $ ctxEntryName entry
              value <- noConstraints $ dontAssignMetas $ checkExpr expression ty
              pure $ if noMetas value then Just expression else Nothing)
        `catchError` (\_ -> pure Nothing)) context
    case locals of
      [expression] -> pure (expression, True)
      _ -> do
        (expression, _) <- hole ty
        pure (expression, False)
  checked seen ty = do
    (expression, _) <- build seen ty
    value <- check expression ty
    pure (expression, value)
  prepare name ty = do
    let headExpression = A.Con $ I.AmbQ (name :| [])
    available <- inspect
    if not available then genericError "native-construction-allowance-spent" else do
      -- Infer the actual application head, including constructor parameters.
      -- A parameter-stripped constructor type is not the telescope accepted
      -- by an abstract application with explicit hidden field operands.
      (_, constructorType) <- inferExpr' DontExpandLast headExpression
      (expression, holes, resultType) <- skeleton headExpression constructorType []
      allowed <- charge
      if not allowed then genericError "native-construction-allowance-spent" else
        compareType CmpLeq resultType ty
      _ <- check expression ty
      pure (expression, holes)
  check expression ty = do
    allowed <- charge
    if not allowed then genericError "native-construction-allowance-spent"
      else checkExpr expression ty
  skeleton expression ty holes = reduce ty >>= \case
    I.El _ (I.Pi domain body) -> do
      (operand, value) <- hole (I.unDom domain)
      case operand of
        A.QuestionMark _ point -> skeleton
          (A.app expression [Arg (getArgInfo domain) $ unnamed operand]) (absApp body value)
          (holes ++ [(point, value, getHiding domain)])
        _ -> genericError "native-constructor-hole-unavailable"
    _ -> pure (expression, holes, ty)
  fill _ expression [] completed = traverseExpr (\case
    old@(A.QuestionMark _ point) -> pure $ Map.findWithDefault old point completed
    old -> pure old) expression
  fill seen expression ((point, value, visibility):rest) completed = do
    resolved <- instantiateFull value
    if noMetas resolved then do
      supplied <- reify resolved
      fill seen expression rest (Map.insert point supplied completed)
    else if visibility /= NotHidden then fill seen expression rest completed
    else do
      ty <- getMetaTypeInContext =<< lookupInteractionId point
      (supplied, _) <- build seen =<< instantiateFull ty
      allowed <- charge
      if not allowed then genericError "native-construction-allowance-spent" else do
        _ <- give_ False WithoutForce point Nothing supplied
        fill seen expression rest (Map.insert point supplied completed)
  fields _ [] I.EmptyTel = pure []
  fields seen (name:names) (I.ExtendTel domain body) = do
    (expression, value) <- if visible domain then checked seen (I.unDom domain)
      else hole (I.unDom domain)
    rest <- fields seen names (absApp body value)
    pure $ (name, expression):rest
  fields _ _ _ = genericError "native-record-telescope-mismatch"

-- The telescope comes from Agda, already instantiated with this record's
-- parameters. Search substitutes checked field values into it, never names or
-- printed types. Coinductive construction is a separate H5.4 clause action.
recordPlan :: Set.Set QName -> I.Type -> TCM (Maybe ([C.Name], I.Telescope))
recordPlan forbidden target = do
  observed <- isRecordType target
  pure $ case observed of
    Just (_, parameters, definition)
      | _recInduction definition /= Just CoInductive
      , not $ Set.member (I.conName $ _recConHead definition) forbidden ->
      Just (map I.unDom $ recordFieldNames definition, _recTel definition `apply` parameters)
    _ -> Nothing

recordExpression :: [(C.Name, A.Expr)] -> A.Expr
recordExpression fields = A.Rec empty exprNoRange
  [Left $ FieldAssignment name expression | (name, expression) <- fields]

-- Expose visible fields of an existing typed record as ordinary evidence heads.
-- In particular, a function-valued field should not require resynthesizing its
-- record operand each time it is used in a composition. No record is consumed,
-- no eta law is assumed, and private/excluded fields are not made visible.
projectedEvidence :: Set.Set QName -> A.Expr -> I.Type -> TCM [A.Expr]
projectedEvidence visibleFields expression ty = isRecordType ty >>= \case
  Nothing -> pure []
  Just (_, _, definition) -> pure
    [A.app (A.Proj ProjPrefix $ I.AmbQ (name :| [])) [defaultArg $ unnamed expression]
    | field <- _recFields definition, let name = I.unDom field
    , Set.member name visibleFields]

-- Omitted hidden fields are inferred in the same branch as subsequent fields.
-- Instance fields use Agda's instance metavariables, not unification substitutes.
-- The reconstructed record omits this assignment so Agda repeats that operation.
omittedField :: Hiding -> TCM A.Expr
omittedField visibility = do
  scope <- getScope
  let kind = case visibility of Instance{} -> Info.InstanceMeta; _ -> Info.UnificationMeta
  pure $ A.Underscore $ Info.MetaInfo noRange scope Nothing "" kind

absurdLambda :: Hiding -> A.Expr
absurdLambda = A.AbsurdLam exprNoRange

-- An absurd lambda needs a known domain. Keep the annotation and application as
-- native syntax in the replayable draft, rather than retaining Agda's temporary
-- generated helper name. Agda decides emptiness (including impossible indices).
eliminateEmpty :: A.Expr -> I.Type -> I.Type -> TCM A.Expr
eliminateEmpty subject domain target = do
  sourceType <- reify domain
  resultType <- reify target
  withFreshName noRange "eliminate" $ \name -> do
    let signature = A.Fun exprNoRange (defaultArg sourceType) resultType
        binding = A.LetBind (LetRange noRange) defaultArgInfo (A.mkBindName name)
          signature (absurdLambda NotHidden)
    pure $ A.Let exprNoRange (binding :| []) $
      A.app (A.Var name) [defaultArg $ unnamed subject]
