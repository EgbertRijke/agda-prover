{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE LambdaCase #-}
-- SPDX-License-Identifier: GPL-3.0-or-later
module AgdaProver.Agda28.Construction
  ( recordPlan, recordExpression, projectedEvidence, omittedField, absurdLambda, eliminateEmpty
  , constructorClosures, localEliminationClosures, constructionScaffold, emptyResultApplication, completeLocalOperands
  , determinedOperands, ArgumentWrapper (..), argumentWrappers, preservingAllocations ) where

import Control.Monad (filterM, forM)
import Control.Monad.Except (catchError, throwError)
import Data.Maybe (catMaybes)
import Data.Monoid (Any (..))
import Data.List.NonEmpty (NonEmpty (..))
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set

import Agda.Syntax.Abstract qualified as A
import Agda.Syntax.Abstract.Name (QName)
import Agda.Syntax.Abstract.Views (foldExpr, traverseExpr)
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
import Agda.TypeChecking.Empty (isEmptyType)
import Agda.TypeChecking.Records (isRecordType, recordFieldNames)
import Agda.TypeChecking.Reduce (instantiateFull, reduce)
import Agda.TypeChecking.Rules.Term (checkExpr, inferExpr')
import Agda.TypeChecking.Substitute (apply, absApp, raise)
import Agda.Utils.Null (empty)
import AgdaProver.Agda28.ClauseExecution qualified as ClauseExecution

-- A shallow constructor context for an actual argument domain. Only native
-- names and field metadata escape telescope inspection, never types containing
-- the temporary binders introduced by underAbstraction.
data ArgumentWrapper
  = ConstructorWrapper QName Int
  | RecordWrapper [(C.Name, ArgInfo)]

argumentWrappers :: TCM Bool -> Set.Set QName -> I.Type -> TCM [(Int, ArgumentWrapper)]
argumentWrappers charge forbidden = domains 0
 where
  domains :: Int -> I.Type -> TCM [(Int, ArgumentWrapper)]
  domains index ty = charge >>= \allowed ->
    if not allowed then pure [] else reduce ty >>= \case
      I.El _ (I.Pi domain body) -> do
        wrapper <- argumentWrapper charge forbidden $ I.unDom domain
        rest <- underAbstraction domain body $ domains (index + 1)
        pure $ maybe rest (\value -> (index, value):rest) wrapper
      _ -> pure []

argumentWrapper :: TCM Bool -> Set.Set QName -> I.Type -> TCM (Maybe ArgumentWrapper)
argumentWrapper charge forbidden ty = charge >>= \allowed ->
  if not allowed then pure Nothing else reduce ty >>= \case
    I.El _ (I.Def family _) -> do
      definition <- getConstInfo family
      scope <- getScope
      let available name = isNameInScope name scope && not (Set.member name forbidden)
      case theDef definition of
        Datatype { dataCons = [name] } | available name ->
          getConstInfo name >>= \entry -> pure $ case theDef entry of
            Constructor { conArity = arity } | arity > 0 -> Just $ ConstructorWrapper name arity
            _ -> Nothing
        RecordDefn record
          | _recInduction record /= Just CoInductive
          , not $ Set.member (I.conName $ _recConHead record) forbidden
          , all (available . I.unDom) (_recFields record) ->
              pure $ Just $ RecordWrapper
                [(I.unDom field, getArgInfo field) | field <- recordFieldNames record]
        _ -> pure Nothing
    _ -> pure Nothing

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

-- A closed elimination is different from publishing arbitrary case branches.
-- Introduce the actual telescope and try one single-constructor argument at a
-- time. Only local or nullary-constructor leaf closures escape; no recursive
-- search or later specification is used. This gives the
-- agenda a computationally useful definition before speculative equations,
-- while all ordinary introductions, equations and eliminations remain available.
localEliminationClosures :: TCM Bool -> TCM Bool
                        -> (ClauseExecution.PreparationStep -> TCM ())
                        -> Set.Set QName -> I.Type -> TCM [A.Expr]
localEliminationClosures inspect charge clauseStep forbidden = introduce []
 where
  introduce inputs ty = do
    allowed <- inspect
    if not allowed || not (noMetas ty) then pure [] else reduce ty >>= \case
      I.El _ (I.Pi domain body) -> do
        let hint = if I.absName body `elem` ["", "_"] then "x" else I.absName body
        withFreshName noRange hint $ \name -> do
          drafts <- addContext (name, domain) $
            locallyScope scopeLocals ((A.nameConcrete name, LocalVar name LambdaBound []) :) $
              introduce (inputs ++ [name]) (absApp (raise 1 body) $ I.Var 0 [])
          pure [A.Lam exprNoRange
            (A.mkDomainFree $ Arg (getArgInfo domain) $ unnamed $ A.mkBinder_ name) draft
            | draft <- drafts]
      _ -> firstClosure inputs ty
  -- This is the same deterministic local-closure lane as ClosingSubjects, not
  -- a second enumeration of case choices. Stop after useful computation;
  -- ordinary clause proposals retain every other subject and the full batch.
  firstClosure [] _ = pure []
  firstClosure (name:rest) ty = do
      found <- preservingAllocations $
        (do
          context <- getContext
          case [index | (index, entry) <- zip [0..] context, ctxEntryName entry == name] of
            [index] -> do
              available <- inspect
              eligible <- if not available then pure False else typeOfBV index >>= reduce >>= \case
                I.El _ (I.Def family _) -> do
                  scope <- getScope
                  definition <- getConstInfo family
                  let usable constructor = isNameInScope constructor scope && not (Set.member constructor forbidden)
                  pure $ case theDef definition of
                    Datatype { dataCons = [constructor] } -> usable constructor
                    RecordDefn record -> _recInduction record /= Just CoInductive &&
                      usable (I.conName $ _recConHead record) &&
                      all (usable . I.unDom) (_recFields record)
                    _ -> False
                _ -> pure False
              if not eligible then pure Nothing else do
                scope <- getScope
                point <- registerInteractionPoint False noRange Nothing
                let hole = A.QuestionMark (Info.emptyMetaInfo { Info.metaScope = scope }) point
                checked <- charge
                if not checked then pure Nothing else do
                  _ <- checkExpr hole ty
                  Just <$> ClauseExecution.prepareClosing clauseStep
                    (constructorClosures inspect forbidden) point (name :| [])
            _ -> pure Nothing)
        `catchError` (\case
          TypeError{} -> pure Nothing
          PatternErr{} -> pure Nothing
          problem -> throwError problem)
      maybe (firstClosure rest ty) (pure . pure) found

-- Expose a finite introduction tree, closing uniquely matching local leaves.
-- Unresolved types, nondecreasing repeated families and genuine choices remain
-- explicit goals; the ordinary agenda retains all alternatives. Each hole is
-- created in its native context, and the finished draft is kernel-checked.
-- This is not used by the cheap later-goal constructor-closure probe.
constructionScaffold :: TCM Bool -> TCM Bool -> (ClauseExecution.PreparationStep -> TCM ())
                     -> Set.Set QName -> I.Type -> TCM (Maybe A.Expr)
constructionScaffold inspect charge clauseStep forbidden target = do
  (expression, introduced) <- build Map.empty Set.empty target
  pure $ if introduced then Just expression else Nothing
 where
  hole ty = do
    scope <- getScope
    point <- registerInteractionPoint False noRange Nothing
    let expression = A.QuestionMark (Info.emptyMetaInfo { Info.metaScope = scope }) point
    value <- check expression ty
    pure (expression, value)
  build seen inputs ty = do
    allowed <- inspect
    if not allowed then genericError "native-construction-allowance-spent"
    -- This eager optimization needs an established dependent type. Expanding
    -- a constructor telescope against unresolved indices can multiply Agda's
    -- postponed substitutions before control returns to the agenda. Leave an
    -- ordinary obligation instead: atomic refinement can still instantiate
    -- those indices, and a later invocation can build their resolved shape.
    -- Inspect the native tree before reducing/instantiating it; this is not a
    -- size limit or a rejection of the branch's mathematical goal.
    else if not (noMetas ty) then unresolved inputs ty else reduce ty >>= \case
      I.El _ (I.Pi domain body) -> do
        let hint = if I.absName body `elem` ["", "_"] then "x" else I.absName body
        withFreshName noRange hint $ \name -> do
          -- Adding a typed binder does not add it to Agda's syntactic scope.
          -- Every nested hole must see the same native name as its enclosing
          -- lambda, including hidden/instance binders and captured prefixes.
          (expression, _) <- addContext (name, domain) $
            locallyScope scopeLocals ((A.nameConcrete name, LocalVar name LambdaBound []) :) $
              build seen (Set.insert name inputs) (absApp (raise 1 body) $ I.Var 0 [])
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
                assignments <- fields next inputs names telescope
                pure (recordExpression assignments, True)
              Nothing -> unresolved inputs ty
          Datatype { dataCons = names } -> do
            scope <- getScope
            compatible <- filterM (\name -> localTCState $
              (prepare name ty >> pure True) `catchError` (\_ -> pure False))
              [name | name <- names, isNameInScope name scope, not $ Set.member name forbidden]
            case compatible of
              [name] -> do
                (expression, holes) <- prepare name ty
                completed <- fill next inputs expression holes Map.empty
                pure (completed, True)
              _ -> unresolved inputs ty
          _ -> unresolved inputs ty
      _ -> unresolved inputs ty
  unresolved inputs ty = do
    uniqueLocal charge ty >>= \case
      Just expression -> pure (expression, True)
      Nothing -> do
        projected <- uniqueProjection inputs ty
        case projected of
          Just expression -> pure (expression, True)
          Nothing -> do
            (expression, _) <- hole ty
            pure (expression, False)
  -- A single-constructor input may contain the desired leaf even when it has
  -- no projection function. Reuse Agda's case operation and the shared local
  -- completion check; do not synthesize patterns or infer field types here.
  -- Only one shallow elimination is tried per introduced argument; ambient
  -- inputs belong to ordinary shared elimination. Projecting an ambient
  -- field separately can hide its connection to dependent sibling operands.
  -- The introduction's native binding identities distinguish these cases.
  -- Ambiguous results
  -- remain for the ordinary agenda. Completion does not recurse into this rule.
  uniqueProjection inputs ty | Set.null inputs || not (noMetas ty) = pure Nothing
  uniqueProjection inputs ty = do
    context <- getContext
    matches <- fmap catMaybes $ forM
      [(index, entry) | (index, entry) <- zip [0..] context,
        Set.member (ctxEntryName entry) inputs] $ \(index, entry) -> do
      candidate <- preservingAllocations $ (do
        subjectType <- typeOfBV index
        wrapper <- argumentWrapper inspect forbidden subjectType
        case wrapper of
          Nothing -> pure Nothing
          Just _ -> do
            (expression, _) <- hole ty
            case expression of
              A.QuestionMark _ point -> do
                draft <- ClauseExecution.prepare clauseStep point $
                  ClauseExecution.BoundSubjects (ctxEntryName entry :| [])
                completeLocalOperands inspect charge draft ty
              _ -> pure Nothing) `catchError` (\case
                TypeError{} -> pure Nothing
                PatternErr{} -> pure Nothing
                problem -> throwError problem)
      pure candidate
    pure $ case matches of [expression] -> Just expression; _ -> Nothing
  checked seen inputs ty = do
    (expression, _) <- build seen inputs ty
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
  fill _ _ expression [] completed = traverseExpr (\case
    old@(A.QuestionMark _ point) -> pure $ Map.findWithDefault old point completed
    old -> pure old) expression
  fill seen inputs expression ((point, value, visibility):rest) completed = do
    resolved <- instantiateFull value
    if noMetas resolved then do
      supplied <- reify resolved
      fill seen inputs expression rest (Map.insert point supplied completed)
    else if visibility /= NotHidden then fill seen inputs expression rest completed
    else do
      ty <- getMetaTypeInContext =<< lookupInteractionId point
      (supplied, _) <- build seen inputs =<< instantiateFull ty
      allowed <- charge
      if not allowed then genericError "native-construction-allowance-spent" else do
        _ <- give_ False WithoutForce point Nothing supplied
        fill seen inputs expression rest (Map.insert point supplied completed)
  fields _ _ [] I.EmptyTel = pure []
  fields seen inputs (name:names) (I.ExtendTel domain body) = do
    (expression, value) <- if visible domain then checked seen inputs (I.unDom domain)
      else hole (I.unDom domain)
    rest <- fields seen inputs names (absApp body value)
    pure $ (name, expression):rest
  fields _ _ _ _ = genericError "native-record-telescope-mismatch"

-- A local is unambiguous only under Agda conversion without new constraints
-- or meta assignments. Distinct inhabitants of one type remain alternatives.
-- Unresolved types are not approximated by their heads or printed forms.
uniqueLocal :: TCM Bool -> I.Type -> TCM (Maybe A.Expr)
uniqueLocal charge ty
  | not (noMetas ty) = pure Nothing
  | otherwise = do
      context <- getContext
      matches <- fmap catMaybes $ forM context $ \entry -> localTCState $
        (do allowed <- charge
            if not allowed then pure Nothing else do
              let expression = A.Var $ ctxEntryName entry
              value <- noConstraints $ dontAssignMetas $ checkExpr expression ty
              pure $ if noMetas value then Just expression else Nothing)
        `catchError` (\case
          TypeError{} -> pure Nothing
          PatternErr{} -> pure Nothing
          problem -> throwError problem)
      pure $ case matches of [expression] -> Just expression; _ -> Nothing

-- Complete a proposed application's coupled holes from unambiguous locals.
-- Check the whole spine first so expected results and later operands constrain
-- earlier dependent domains. Each successful pass retires at least one hole;
-- no recursive argument synthesis or arbitrary iteration cap is hidden here.
-- Only a closed native expression escapes this transaction. The caller keeps
-- the original open proposal and still checks/validates any completed one.
completeLocalOperands :: TCM Bool -> TCM Bool -> A.Expr -> I.Type -> TCM (Maybe A.Expr)
completeLocalOperands inspect charge expression target = preservingAllocations $ do
  allowed <- charge
  if not allowed then pure Nothing else do
    value <- checkExpr expression target
    complete value $ Set.toList $ foldExpr (\case
      A.QuestionMark _ point -> Set.singleton point
      _ -> Set.empty) expression
 where
  complete value points = do
    allowed <- inspect
    if not allowed then pure Nothing else do
      resolved <- instantiateFull value
      if noMetas resolved && not retainsHelpers then Just <$> reify resolved
      else if null points then if not (noMetas resolved) then pure Nothing else do
        -- Reifying only the result can leave references to temporary helper
        -- definitions after rollback. Keep the original scoped syntax and
        -- reify each solved hole in its own checked context. Editor-oriented
        -- blanking of names outside the old scope would erase newly exposed
        -- pattern variables. Native names, not their spellings, bind the draft.
        Just <$> traverseExpr (\case
          A.QuestionMark _ point -> withInteractionId point $ do
            meta <- lookupInteractionId point
            arguments <- getContextArgs
            supplied <- instantiateFull $ I.MetaV meta $ map I.Apply arguments
            if noMetas supplied then reify supplied
              else genericError "native-local-completion-incomplete-solution"
          part -> pure part) expression
      else do
        -- A checked head can be a fresh helper definition whose body still
        -- contains interaction holes. noMetas on its application does not
        -- inspect that body. Retire the draft's holes before reifying it.
        retired <- forM points $ \point -> lookupInteractionMeta point >>= \case
          Nothing -> pure False -- Postponed elaboration has not connected it.
          Just meta -> do
            variable <- lookupLocalMeta meta
            case mvInstantiation variable of
              InstV{} -> pure True
              _ -> withInteractionId point $ do
                ty <- instantiateFull =<< getMetaTypeInContext meta
                uniqueLocal charge ty >>= \case
                  Nothing -> pure False
                  Just supplied -> do
                    available <- charge
                    if not available then pure False else do
                      _ <- give_ False WithoutForce point Nothing supplied
                      pure True
        let remaining = [point | (point, False) <- zip points retired]
        if length remaining == length points then pure Nothing
          else complete value remaining
  -- Ordinary application values can be reified directly, including Agda's
  -- omission of inferred operands. Extended lambdas introduce declarations:
  -- their checked Def head alone is not a self-contained replayable term.
  retainsHelpers = getAny $ foldExpr (\case
    A.ExtendedLam{} -> Any True
    _ -> Any False) expression

-- A composition hint is useful when its known operands and expected result
-- determine the remaining obligations. Do not promote a speculative spine
-- with extra unification metas or blocked domains. This is only an additional
-- proposal filter; the ordinary application remains available, and acceptance
-- still goes through the normal source-owner/termination boundary.
determinedOperands :: TCM Bool -> TCM Bool -> A.Expr -> I.Type -> TCM (Maybe A.Expr)
determinedOperands inspect charge expression target = preservingAllocations $ do
  allowed <- charge
  if not allowed then pure Nothing else do
    before <- Set.fromList <$> getOpenMetas
    _ <- noConstraints $ checkExpr expression target
    let points = Set.toList $ foldExpr (\case
          A.QuestionMark _ point -> Set.singleton point
          _ -> Set.empty) expression
    holes <- forM points $ \point -> do
      available <- inspect
      if not available then pure Nothing else lookupInteractionMeta point >>= \case
        Nothing -> pure Nothing
        Just meta -> withInteractionId point $ do
          ty <- instantiateFull =<< getMetaTypeInContext meta
          pure $ if noMetas ty then Just meta else Nothing
    remaining <- Set.fromList <$> getOpenMetas
    pure $ if all (/= Nothing) holes &&
      (remaining `Set.difference` before) `Set.isSubsetOf` Set.fromList (catMaybes holes)
      then Just expression else Nothing

-- Reified drafts can bind freshly allocated names. Retain only their small
-- allocation watermarks, never the speculative checking state or assignments.
preservingAllocations :: TCM a -> TCM a
preservingAllocations action = do
  (result, names, points) <- localTCState $ do
    result <- action
    names <- useTC stFreshNameId
    points <- useTC stFreshInteractionId
    pure (result, names, points)
  stFreshNameId `modifyTCLens` max names
  stFreshInteractionId `modifyTCLens` max points
  pure result

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

-- Expose elimination of computed empty evidence as an ordinary application
-- with operand goals. Inspect the dependent codomain under its own telescope;
-- Agda, including its indexed/record emptiness check, decides applicability.
-- Typed lambdas retain the argument domains when the eliminator is applied.
-- No provisional native metas or generated helper names escape reification.
emptyResultApplication :: TCM Bool -> TCM Bool -> A.Expr -> I.Type -> I.Type
                       -> TCM (Maybe A.Expr)
emptyResultApplication inspect charge expression ty target
  | not (noMetas ty && noMetas target) = pure Nothing
  | otherwise = build expression ty target >>= \case
      Nothing -> pure Nothing
      Just (eliminator, infos) -> do
        scope <- getScope
        arguments <- mapM (\info -> do
          point <- registerInteractionPoint False noRange Nothing
          pure $ Arg info $ unnamed $ A.QuestionMark
            (Info.emptyMetaInfo { Info.metaScope = scope }) point) infos
        pure $ Just $ A.app eliminator arguments
 where
  build subject domain result = inspect >>= \allowed ->
    if not allowed then pure Nothing else reduce domain >>= \case
      I.El _ (I.Pi argument body) -> do
        argumentType <- reify $ I.unDom argument
        withFreshName noRange (if I.absName body `elem` ["", "_"] then "x" else I.absName body) $ \name -> do
          next <- addContext (name, argument) $
            build (A.app subject [Arg (getArgInfo argument) $ unnamed $ A.Var name])
              (absApp (raise 1 body) $ I.Var 0 []) (raise 1 result)
          let binding = A.TBind noRange (empty { A.tbFinite = I.domIsFinite argument })
                (Arg (getArgInfo argument) (unnamed $ A.mkBinder_ name) :| []) argumentType
          pure $ fmap (\(term, infos) ->
            (A.Lam exprNoRange (A.DomainFull binding) term, getArgInfo argument : infos)) next
      leaf@(I.El _ I.Def{}) -> do
        checkAllowed <- charge
        emptyResult <- if checkAllowed then localTCState $ dontAssignMetas $ isEmptyType leaf else pure False
        if not emptyResult then pure Nothing else do
          eliminated <- eliminateEmpty subject leaf result
          pure $ Just (eliminated, [])
      _ -> pure Nothing

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
