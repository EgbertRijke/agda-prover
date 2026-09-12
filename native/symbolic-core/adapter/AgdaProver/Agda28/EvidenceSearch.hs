{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
-- SPDX-License-Identifier: GPL-3.0-or-later
module AgdaProver.Agda28.EvidenceSearch (run, Result (..)) where

import Control.Monad (forM)
import Control.Monad.Except (catchError, runExceptT, throwError)
import Control.Monad.IO.Class (liftIO)
import Data.Aeson (Value)
import Data.Foldable (toList)
import Data.IORef
import Data.List (nub)
import Data.List.NonEmpty (NonEmpty (..))
import Data.Map.Strict qualified as Map
import Data.Maybe (catMaybes)
import Data.Set qualified as Set
import Data.Text qualified as T

import Agda.Syntax.Abstract qualified as A
import Agda.Syntax.Abstract.Name (QName)
import Agda.Syntax.Abstract.Views (traverseExpr)
import Agda.Syntax.Common
import Agda.Syntax.Common.Pretty (prettyShow)
import Agda.Syntax.Concrete.Name qualified as C
import Agda.Syntax.Info (exprNoRange)
import Agda.Syntax.Info qualified as Info
import Agda.Syntax.Internal qualified as I
import Agda.Syntax.Internal.MetaVars (noMetas)
import Agda.Syntax.Position (noRange)
import Agda.Syntax.Scope.Base
import Agda.Syntax.Scope.Monad (tryResolveName)
import Agda.Syntax.Translation.InternalToAbstract (reify)
import Agda.Interaction.BasicOps (give_)
import Agda.Interaction.Base (UseForce (WithoutForce))
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Conversion (compareType)
import Agda.TypeChecking.Pretty (prettyTCM)
import Agda.TypeChecking.Reduce (instantiateFull, reduce)
import Agda.TypeChecking.Rules.Term (checkExpr, inferExpr, inferExpr')
import Agda.TypeChecking.Substitute (absApp, apply, raise)
import Agda.Utils.Impossible (impossible)

import AgdaProver.Symbolic.Evidence
import AgdaProver.Agda28.Construction qualified as Construction
import AgdaProver.Agda28.Recursion qualified as Recursion
import AgdaProver.Symbolic.NNUE.Features qualified as F
import AgdaProver.Symbolic.NNUE.Native (NativeScorer)
import AgdaProver.Symbolic.NNUE.Policy qualified as P

-- This module is private to the versioned adapter. Drafts remain Agda abstract
-- syntax; checked values/types remain Agda internal syntax under the live TCM.
-- A continuation keeps dependent argument choices and all their constraints in
-- the same branch. No inferred type containing fresh metas escapes rollback.
data Result = Result SearchStatus (Maybe A.Expr) [(T.Text, T.Text)]
data Runtime s = Runtime SearchLimits (IORef SearchStats) (IORef Bool)
  P.Models P.RankingMode (Maybe (NativeScorer s)) (Value -> IO ()) T.Text
data Seed = Seed A.Expr String String
data GlobalInventory = GlobalInventory [A.Expr] (Set.Set QName) (Maybe Recursion.CallContext)

run :: IORef SearchStats -> SearchLimits -> P.Models -> P.RankingMode -> Maybe (NativeScorer s)
    -> (Value -> IO ()) -> String -> [String] -> InteractionId -> Maybe Recursion.Owner
    -> (A.Expr -> TCM ()) -> I.Type -> TCM Result
run stats limits models mode native emit namespace excluded point owner validate target = do
  pruned <- liftIO $ newIORef False
  let runtime = Runtime limits stats pruned models mode native emit (T.pack namespace)
  (currentForbidden, userExcluded) <- excludedGlobals excluded
  inheritedGroup <- maybe (pure Set.empty) Recursion.ownerGroup owner
  let forbidden = Set.union currentForbidden inheritedGroup
  globals <- visibleGlobals forbidden
  recursion <- case owner of
    Just root | not $ Set.member (Recursion.ownerName root) userExcluded -> attempt runtime $ do
      allowed <- charge runtime $ \s -> s { recursiveContextQueries = recursiveContextQueries s + 1 }
      if allowed then Recursion.inspect point root else pure Nothing
    _ -> pure Nothing
  let iterateDepth depth = do
        liftIO $ writeIORef pruned False
        modify runtime $ \s -> s { depthIterations = depthIterations s + 1, currentDepth = depth }
        found <- search runtime (GlobalInventory globals forbidden recursion) depth target [] $ \expression term selected -> do
          closed <- instantiateFull term
          if not (noMetas closed) then pure Nothing else do
            admissible <- if maybe False (`Recursion.usesOwner` expression) owner then do
              allowed <- charge runtime $ \s -> s
                { checkerQueries = checkerQueries s + 1, recursiveValidationQueries = recursiveValidationQueries s + 1 }
              if not allowed then pure False else validate expression >> pure True
              else pure True
            pure $ if admissible then Just (expression, selected) else Nothing
        observed <- liftIO $ readIORef stats
        widened <- liftIO $ readIORef pruned
        case found of
          Just (term, selected) -> pure $ Result FoundCandidate (Just term) selected
          Nothing | workExhausted observed -> pure $ Result WorkExhausted Nothing []
          Nothing | not widened -> pure $ Result FragmentExhausted Nothing []
          Nothing -> iterateDepth (depth + 1)
  iterateDepth 0

modify :: Runtime s -> (SearchStats -> SearchStats) -> TCM ()
modify (Runtime _ ref _ _ _ _ _ _) f = liftIO $ atomicModifyIORef' ref $ \s -> (f s, ())
stopped :: Runtime s -> TCM Bool
stopped (Runtime _ ref _ _ _ _ _ _) = workExhausted <$> liftIO (readIORef ref)
charge :: Runtime s -> (SearchStats -> SearchStats) -> TCM Bool
charge (Runtime limits ref _ _ _ _ _ _) f = liftIO $ atomicModifyIORef' ref $ \s ->
  if workExhausted s || maybe False (workUnits s >=) (workUnitLimit limits)
    then (s { workExhausted = True }, False)
    else (f s { workUnits = workUnits s + 1 }, True)
deferDepth :: Runtime s -> TCM (Maybe a)
deferDepth (Runtime _ _ ref _ _ _ _ _) = liftIO (writeIORef ref True) >> pure Nothing

-- Only ordinary type rejection/postponement are search outcomes. Internal,
-- parser or IO failures propagate to the session's precise failure boundary.
attempt :: Runtime s -> TCM (Maybe a) -> TCM (Maybe a)
attempt runtime action = do
  initial <- getTC
  result <- action `catchError` \err -> case err of
    TypeError{} -> modify runtime (\s -> s { rejectedQueries = rejectedQueries s + 1 }) >> pure Nothing
    PatternErr{} -> modify runtime (\s -> s { blockedQueries = blockedQueries s + 1 }) >> pure Nothing
    _ -> throwError err
  case result of
    Nothing -> putTC initial >> pure Nothing
    Just _ -> pure result

choices :: Runtime s -> [TCM (Maybe a)] -> TCM (Maybe a)
choices _ [] = pure Nothing
choices runtime (action:rest) = do
  done <- stopped runtime
  if done then pure Nothing else attempt runtime action >>= \case
    Just result -> pure $ Just result
    Nothing -> choices runtime rest

queryCheck :: Runtime s -> A.Expr -> I.Type -> (I.Term -> TCM (Maybe a)) -> TCM (Maybe a)
queryCheck runtime expression target use = do
  allowed <- charge runtime $ \s -> s { checkerQueries = checkerQueries s + 1 }
  if allowed then checkExpr expression target >>= use else pure Nothing

queryInfer :: Runtime s -> A.Expr -> ((I.Term, I.Type) -> TCM (Maybe a)) -> TCM (Maybe a)
queryInfer = queryInferWith ExpandLast

queryInferWith :: ExpandHidden -> Runtime s -> A.Expr -> ((I.Term, I.Type) -> TCM (Maybe a)) -> TCM (Maybe a)
queryInferWith expansion runtime expression use = do
  allowed <- charge runtime $ \s -> s { inferenceQueries = inferenceQueries s + 1 }
  if allowed then inferExpr' expansion expression >>= use else pure Nothing

-- Current recursive definitions are never ordinary evidence. Agda supplies
-- the exact mutual group; dedicated calls below carry clause descent context.
-- User exclusions are resolved before any premise typing or ranking.
excludedGlobals :: [String] -> TCM (Set.Set QName, Set.Set QName)
excludedGlobals names = do
  group <- asksTC envMutualBlock >>= maybe (pure Set.empty) (fmap mutualNames . lookupMutualBlock)
  scope <- getScope
  resolutions <- forM (Set.toAscList $ concreteNamesInScope scope) $ \alias ->
    if prettyShow alias `elem` names then do
      resolved <- runExceptT $ tryResolveName allKindsOfNames Nothing alias
      pure $ either (const []) globalsOf resolved
    else pure []
  let userExcluded = Set.fromList $ concat resolutions
  pure (Set.union group userExcluded, userExcluded)
 where
  globalsOf (DefinedName _ name _) = [anameName name]
  globalsOf (FieldName fields) = map anameName $ toList fields
  globalsOf (ConstructorName _ constructors) = map anameName $ toList constructors
  globalsOf _ = []

visibleGlobals :: Set.Set QName -> TCM [A.Expr]
visibleGlobals forbidden = do
  scope <- getScope
  resolved <- forM (Set.toAscList $ concreteNamesInScope scope) $ \alias ->
    if not (all (\n -> not (C.isNoName n) && C.isInScope n == C.InScope) $ C.qnameParts alias)
      then pure Nothing else do
        meaning <- runExceptT $ tryResolveName allKindsOfNames Nothing alias
        pure $ case meaning of
          Right value@(DefinedName _ name _)
            | not (Set.member (anameName name) forbidden) -> case A.nameToExpr value of
                expression@A.Def'{} -> Just expression
                _ -> Nothing
          Right (FieldName fields) -> case filter (not . (`Set.member` forbidden) . anameName) (toList fields) of
            [] -> Nothing
            -- This is a prefix function head, not a postfix projection
            -- elimination. Preserve that distinction through reconstruction.
            name:names -> Just $ A.Proj ProjPrefix $ I.AmbQ (anameName name :| map anameName names)
          Right (ConstructorName _ constructors) ->
            case filter (not . (`Set.member` forbidden) . anameName) (toList constructors) of
              [] -> Nothing
              name:names -> Just $ A.Con $ I.AmbQ (anameName name :| map anameName names)
          Right value@VarName{} -> Just $ A.nameToExpr value
          _ -> Nothing
  -- An overloaded constructor head cannot always be inferred without its
  -- operands. Preserve each resolved, visible QName as a distinct proposal;
  -- Agda still checks its result indices and the final printed expression.
  pure $ nub $ concatMap expandConstructors $ catMaybes resolved
 where
  expandConstructors (A.Con (I.AmbQ names)) =
    [A.Con $ I.AmbQ (name :| []) | name <- toList names]
  expandConstructors expression = [expression]

-- No inferred Agda term/type is retained by describe. Its presentation is used
-- solely by the unchanged NNUE feature vocabulary. Actual use re-elaborates in
-- the appropriate branch with native operands and expected dependent types.
describe :: Runtime s -> String -> A.Expr -> TCM Seed
describe runtime origin expression = do
  info <- localTCState $ attempt runtime $ do
    allowed <- charge runtime $ \s -> s { inferenceQueries = inferenceQueries s + 1 }
    if not allowed then pure Nothing else do
      (_, ty) <- inferExpr expression
      Just . prettyShow <$> prettyTCM ty
  pure $ Seed expression origin (maybe "unknown" id info)

rankSeeds :: Runtime s -> I.Type -> [A.Expr] -> TCM [(Seed, [(T.Text, T.Text)])]
rankSeeds runtime@(Runtime _ ref _ models mode native emit namespace) target globals = do
  locals <- map (A.Var . ctxEntryName) <$> getContext
  seeds <- mapM (uncurry $ describe runtime) $
    [("local", expression) | expression <- locals] ++ [("visible", expression) | expression <- globals, expression `notElem` locals]
  targetText <- T.pack . prettyShow <$> prettyTCM target
  stats <- liftIO $ readIORef ref
  let ordinal = policyDecisions stats
      decision = namespace <> ":evidence:" <> T.pack (show ordinal)
      contextText = [T.pack typeText | Seed _ "local" typeText <- seeds]
      goal = F.GoalView targetText contextText Nothing
  candidates <- forM (zip [0 :: Int ..] seeds) $ \(index, seed@(Seed expression origin typeText)) -> do
    display <- T.pack . prettyShow <$> prettyTCM expression
    let view = F.CandidateView "evidence-application-v1" "native-evidence" (T.pack typeText) display 1 [("origin", T.pack origin)]
    pure $ P.Candidate (T.pack $ show index) display 0 (Right $ F.candidateTokens goal view) seed
  ranked <- liftIO $ P.rankBatch native models mode (P.ORFamily "evidence-application-v1") decision
    (F.policyStateTokens goal F.unknownClassification) candidates
  -- The router counts inference; this ledger also retains preparation work on
  -- interrupted/rejected attempts through the surrounding session dispatch.
  case ranked of
    Left reason -> genericError $ "native-policy-batch:" ++ reason
    Right batch -> do
      modify runtime $ \s -> s { policyDecisions = ordinal + 1
        , modelItems = modelItems s + fromIntegral (P.traceItemsScored $ P.decisionTrace batch)
        , modelNanoseconds = modelNanoseconds s + P.traceModelNanoseconds (P.decisionTrace batch) }
      liftIO $ emit $ P.traceView $ P.decisionTrace batch
      pure [(P.candidateValue candidate, if length candidates > 1 then [(decision, P.candidateId candidate)] else [])
            | candidate <- P.rankedCandidates batch]

-- Continuations implement the AND part: if a later argument or final check
-- fails, search revisits earlier argument choices with the original TCState.
search :: Runtime s -> GlobalInventory -> Int -> I.Type -> [(T.Text,T.Text)]
       -> (A.Expr -> I.Term -> [(T.Text,T.Text)] -> TCM (Maybe a)) -> TCM (Maybe a)
search runtime inventory@(GlobalInventory globals forbidden recursion) depth target selected use = do
  done <- stopped runtime
  if done then pure Nothing else do
    modify runtime $ \s -> s { searchNodes = searchNodes s + 1 }
    seeds <- rankSeeds runtime target globals
    choices runtime $
      [queryCheck runtime expression target $ \term -> use expression term (selected ++ picked)
       | (Seed expression _ _, picked) <- seeds]
      ++ [recursiveCall inferredArguments context | Just context <- [recursion]]
      ++ [constructRecord, introduce]
      ++ [queryInferWith DontExpandLast runtime expression $ \(_, ty) ->
            guidedApplication expression ty depth [] (selected ++ picked)
         | (Seed expression _ _, picked) <- seeds]
      ++ [recursiveCall arguments context | Just context <- [recursion]]
      ++ [produce expression picked | (Seed expression _ _, picked) <- seeds]
 where
  -- The recursive head is sealed away from ordinary argument search. Only a
  -- fully applied call using a descent seed or a real coinductive copattern
  -- context is offered as evidence.
  -- This covers direct children, applications of function-valued children and
  -- reconstructed wrappers through the same typed argument generator. Descent
  -- is a proposal condition, not a replacement for Agda's termination checker;
  -- unresolved with-ancestry remains an explicitly uncertain fallback.
  recursiveCall generate context = do
    allowed <- charge runtime $ \s -> s { inferenceQueries = inferenceQueries s + 1 }
    if not allowed then pure Nothing else do
      let headExpression = Recursion.callHead context
      (_, ty) <- inferExpr headExpression
      generate context headExpression ty depth selected
  -- Infer operands from the expected dependent result before enumerating them.
  -- All placeholders are native Agda metas in this speculative branch. Only a
  -- fully instantiated term is reified/retained; otherwise ordinary argument
  -- search remains available. No textual result-index matching is involved.
  inferredArguments context expression ty remaining picked
    | remaining <= 0 = deferDepth runtime
    | otherwise = inferExpected context expression ty picked
  -- This is one expected-type inference proposal, not a choice for every
  -- parameter. Its actual checker work is charged for each supplied meta.
  inferExpected context expression ty picked = reduce ty >>= \case
    I.El _ (I.Pi domain codomain)
      -> do
          omitted <- Construction.omittedField $ getHiding domain
          queryCheck runtime omitted (I.unDom domain) $ \value ->
            inferExpected context
              (A.app expression [Arg (getArgInfo domain) $ unnamed omitted])
              (absApp codomain value) picked
    _ -> queryCheck runtime expression target $ \value -> do
      instantiated <- instantiateFull value
      if not (noMetas instantiated) then pure Nothing else do
        nativeExpression <- reify instantiated
        if not (Recursion.eligibleCall context nativeExpression) then pure Nothing else do
          noteCall context
          use nativeExpression instantiated picked
  arguments context expression ty remaining picked = reduce ty >>= \case
    I.El _ (I.Pi domain codomain)
      | remaining <= 0 -> deferDepth runtime
      | otherwise -> choices runtime $
          [do omitted <- Construction.omittedField $ getHiding domain
              queryCheck runtime omitted (I.unDom domain) $ \value -> advance omitted value
          | notVisible domain]
          ++ [search runtime (GlobalInventory globals forbidden Nothing) (remaining-1)
                (I.unDom domain) picked $ \argument value selected' ->
                  next argument value selected']
       where
        next argument value selected' =
          arguments context (A.app expression [Arg (getArgInfo domain) $ unnamed argument])
            (absApp codomain value) (remaining - if visible domain then 1 else 0) selected'
        advance argument value = next argument value picked
    _ | Recursion.eligibleCall context expression -> do
          noteCall context
          queryCheck runtime expression target $ \term -> use expression term picked
      | otherwise -> pure Nothing
  noteCall context = modify runtime $ \s -> s
    { recursiveProposals = recursiveProposals s + 1
    , copatternProposals = copatternProposals s + if Recursion.copatternCall context then 1 else 0 }
  constructRecord = Construction.recordPlan forbidden target >>= \case
    Nothing -> pure Nothing
    Just (names, telescope)
      | depth <= 0 && not (null names) -> deferDepth runtime
      | otherwise -> do
          modify runtime $ \s -> s { recordProposals = recordProposals s + 1 }
          fields names telescope [] selected
  fields [] I.EmptyTel assignments picked = do
    let expression = Construction.recordExpression assignments
    queryCheck runtime expression target $ \term -> use expression term picked
  fields (name:names) (I.ExtendTel domain rest) assignments picked = choices runtime $
    [do expression <- Construction.omittedField $ getHiding domain
        queryCheck runtime expression (I.unDom domain) $ \value ->
          fields names (absApp rest value) assignments picked
    | notVisible domain]
    ++ [search runtime inventory (depth-1) (I.unDom domain) picked $ \expression value selected' ->
          fields names (absApp rest value) (assignments ++ [(name, expression)]) selected']
  fields _ _ _ _ = genericError "native-record-telescope-mismatch"
  introduce = reduce target >>= \case
    I.El _ (I.Pi domain codomain)
      -> choices runtime
        [do modify runtime $ \s -> s { absurdProposals = absurdProposals s + 1 }
            let expression = Construction.absurdLambda $ getHiding domain
            queryCheck runtime expression target $ \term -> use expression term selected
        ,if depth <= 0 then deferDepth runtime else do
          modify runtime $ \s -> s { lambdaProposals = lambdaProposals s + 1 }
          let hint = if I.absName codomain `elem` ["", "_"] then "x" else I.absName codomain
          withFreshName noRange hint $ \name ->
            addContext (name, domain) $ search runtime inventory (depth-1)
              (absApp (raise 1 codomain) $ I.Var 0 []) selected $ \body term picked ->
                escapeContext impossible 1 $
                  let info = getArgInfo domain
                      expression = A.Lam exprNoRange (A.mkDomainFree $ Arg info $ unnamed $ A.mkBinder_ name) body
                      value = I.Lam info $ I.Abs hint term
                  in use expression value picked]
    _ -> pure Nothing
  produce expression picked = queryInfer runtime expression $ \(term, ty) ->
    choices runtime
      [eliminate expression ty (selected ++ picked)
      ,applyMore expression term ty depth (selected ++ picked)]
  -- Elaborate a native application skeleton against the expected result before
  -- searching its operands. Re-elaborating a constructor may instantiate its
  -- hidden head parameters afresh: compare the inferred result as well, so the
  -- operand types keep the constraints belonging to this application spine.
  -- Keep the chosen abstract operands (including generated helpers); reifying
  -- the completed internal term would lose their declaration structure.
  guidedApplication expression ty remaining holes picked = reduce ty >>= \case
    I.El _ (I.Pi domain codomain)
      | remaining <= 0 && visible domain -> deferDepth runtime
      | otherwise -> do
          scope <- getScope
          point' <- registerInteractionPoint False noRange Nothing
          let hole = A.QuestionMark (Info.emptyMetaInfo { Info.metaScope = scope }) point'
          queryCheck runtime hole (I.unDom domain) $ \value ->
            guidedApplication (A.app expression [Arg (getArgInfo domain) $ unnamed hole])
              (absApp codomain value) (remaining - if visible domain then 1 else 0)
              (holes ++ [(point', value)]) picked
    _ | null holes -> pure Nothing
      | otherwise -> do
          allowed <- charge runtime $ \s -> s { checkerQueries = checkerQueries s + 1 }
          if not allowed then pure Nothing else do
            compareType CmpLeq ty target
            queryCheck runtime expression target $ \_ ->
              fillArguments expression holes Map.empty picked
  fillArguments expression [] filled picked = do
    completed <- traverseExpr (\case
      old@(A.QuestionMark _ point') -> pure $ Map.findWithDefault old point' filled
      old -> pure old) expression
    queryCheck runtime completed target $ \term -> use completed term picked
  fillArguments expression ((point', value):rest) filled picked = do
    instantiated <- instantiateFull value
    if noMetas instantiated then do
      supplied <- reify instantiated
      fillArguments expression rest (Map.insert point' supplied filled) picked
    else do
      ty <- getMetaTypeInContext =<< lookupInteractionId point'
      search runtime inventory (depth-1) ty picked $ \argument _ selected' -> do
        allowed <- charge runtime $ \s -> s { checkerQueries = checkerQueries s + 1 }
        if not allowed then pure Nothing else do
          _ <- give_ False WithoutForce point' Nothing argument
          fillArguments expression rest (Map.insert point' argument filled) selected'
  eliminate expression ty picked = do
    modify runtime $ \s -> s { absurdProposals = absurdProposals s + 1 }
    proposal <- Construction.eliminateEmpty expression ty target
    queryCheck runtime proposal target $ \term -> use proposal term picked
  applyMore expression term ty remaining picked = reduce ty >>= \case
    I.El _ (I.Pi domain codomain)
      | remaining <= 0 -> deferDepth runtime
      | otherwise -> search runtime inventory (remaining-1) (I.unDom domain) picked $ \argument value selected' -> do
          modify runtime $ \s -> s { applicationProposals = applicationProposals s + 1 }
          let info = getArgInfo domain
              applied = A.app expression [Arg info $ unnamed argument]
              nativeTerm = apply term [Arg info value]
              resultType = absApp codomain value
          choices runtime
            [queryCheck runtime applied target $ \checked -> use applied checked selected'
            ,eliminate applied resultType selected'
            ,reduce resultType >>= \case
               -- Hidden/instance arguments may occur between explicit ones.
               -- Agda inserts their metas and infers them from later operands;
               -- do not replace that operation with guessing universe values.
               I.El _ (I.Pi nextDomain _) | notVisible nextDomain ->
                 queryInfer runtime applied $ \(continued, continuedType) ->
                   applyMore applied continued continuedType (remaining-1) selected'
               _ -> applyMore applied nativeTerm resultType (remaining-1) selected']
    _ -> pure Nothing
