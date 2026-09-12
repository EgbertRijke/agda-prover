{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
-- SPDX-License-Identifier: GPL-3.0-or-later
module AgdaProver.Agda28.EvidenceSearch (run, runHelper, primitiveProposals, structuralProposals, constructorProposals, clauseProposals, Result (..)) where

import Control.Monad (forM)
import Control.Monad.Except (catchError, runExceptT, throwError)
import Control.Monad.IO.Class (liftIO)
import Data.Aeson (Value (..), toJSON)
import Data.Aeson.KeyMap qualified as KM
import Data.Foldable (toList)
import Data.IORef
import Data.List (nub, sortOn)
import Data.List.NonEmpty (NonEmpty (..))
import Data.List.NonEmpty qualified as NE
import Data.Map.Strict qualified as Map
import Data.Maybe (catMaybes)
import Data.Set qualified as Set
import Data.Text qualified as T

import Agda.Syntax.Abstract qualified as A
import Agda.Syntax.Abstract.Name (QName)
import Agda.Syntax.Abstract.Views (AppView' (..), appView, traverseExpr)
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
import Agda.Interaction.BasicOps qualified as Basic
import Agda.Interaction.Base (UseForce (WithoutForce), Rewrite (AsIs))
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
import AgdaProver.Agda28.Scheduling qualified as Scheduling
import AgdaProver.Agda28.PolicyViews qualified as PolicyViews
import AgdaProver.Agda28.Focused qualified as NativeFocused
import AgdaProver.Agda28.Algebra qualified as NativeAlgebra
import AgdaProver.Symbolic.Algebra qualified as Algebra
import AgdaProver.Agda28.HelperConstruction qualified as Helper
import AgdaProver.Agda28.ClauseExecution qualified as ClauseExecution
import AgdaProver.Symbolic.Focused qualified as Focused
import AgdaProver.Symbolic.Classification qualified as Classification
import AgdaProver.Symbolic.Clause qualified as Clause
import AgdaProver.Symbolic.NNUE.Features qualified as F
import AgdaProver.Symbolic.NNUE.Native (NativeScorer)
import AgdaProver.Symbolic.NNUE.Policy qualified as P
import AgdaProver.Symbolic.Protocol (ObservationMode)
import AgdaProver.Symbolic.SessionTypes (DraftExpression)

-- This module is private to the versioned adapter. Drafts remain Agda abstract
-- syntax; checked values/types remain Agda internal syntax under the live TCM.
-- A continuation keeps dependent argument choices and all their constraints in
-- the same branch. No inferred type containing fresh metas escapes rollback.
data Result = Result SearchStatus (Maybe A.Expr) [(T.Text, T.Text)]
data Runtime s = Runtime SearchLimits (IORef SearchStats) (IORef Bool)
  P.Models P.RankingMode (Maybe (NativeScorer s)) (Value -> IO ()) T.Text Bool
data Seed = Seed A.Expr String String
data GlobalInventory = GlobalInventory [A.Expr] (Set.Set QName) (Maybe Recursion.CallContext)

-- Only rigid type heads can witness a mismatch. A stuck definition, newly
-- introduced telescope variable or meta is unknown. LocalShape identifies a
-- binder in the original goal context, never a printed name. Argument/index
-- conversion and universe comparison remain Agda's responsibility.
data ExpectedShape = FunctionShape | SortShape | FamilyShape QName | LocalShape Int deriving Eq

run :: IORef SearchStats -> SearchLimits -> P.Models -> P.RankingMode -> Maybe (NativeScorer s)
    -> Bool -> (Value -> IO ()) -> String -> [String] -> InteractionId -> Maybe Recursion.Owner
    -> (A.Expr -> TCM ()) -> I.Type -> TCM Result
run stats limits models mode native enableFocused emit namespace excluded point owner validate target = do
  pruned <- liftIO $ newIORef False
  let runtime = Runtime limits stats pruned models mode native emit (T.pack namespace) enableFocused
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

-- Finite typed helper proposals use the same policy/checking boundary as
-- ordinary evidence. Scheduling which application to generalize belongs to
-- the agenda; the caller supplies that scoped task input here.
runHelper :: IORef SearchStats -> SearchLimits -> P.Models -> P.RankingMode -> Maybe (NativeScorer s)
          -> (Value -> IO ()) -> String -> InteractionId -> ObservationMode -> DraftExpression
          -> (A.Expr -> TCM ()) -> I.Type -> TCM Result
runHelper stats limits models mode native emit namespace point view application validate target = do
  pruned <- liftIO $ newIORef False
  let runtime = Runtime limits stats pruned models mode native emit (T.pack namespace) False
      allow step = charge runtime $ \s -> case step of
        Helper.InferSignature -> s { inferenceQueries = inferenceQueries s + 1,
          helperInferenceQueries = helperInferenceQueries s + 1 }
        Helper.InspectSignature -> s { inferenceQueries = inferenceQueries s + 1 }
        Helper.CheckScaffold -> s { checkerQueries = checkerQueries s + 1 }
        Helper.GenerateClauses -> s { checkerQueries = checkerQueries s + 1,
          helperClauseQueries = helperClauseQueries s + 1 }
      rejected = modify runtime $ \s -> s { rejectedQueries = rejectedQueries s + 1 }
  proposals <- Helper.generate allow rejected point view application
  let expressions = maybe [] id proposals
  modify runtime $ \s -> s { helperProposals = helperProposals s + fromIntegral (length expressions) }
  seeds <- mapM (describe runtime "helper") expressions
  ranked <- rankDescribed runtime Classification.unknownClassification target seeds
  found <- choices runtime
    [queryCheck runtime expression target $ \term -> do
      closed <- instantiateFull term
      if not (noMetas closed) then pure Nothing else do
        allowed <- charge runtime $ \s -> s { checkerQueries = checkerQueries s + 1 }
        if not allowed then pure Nothing else validate expression >> pure (Just (expression, picked))
    | (Seed expression _ _, picked) <- ranked]
  exhausted <- stopped runtime
  pure $ case found of
    Just (expression, picked) -> Result FoundCandidate (Just expression) picked
    Nothing -> Result (if exhausted then WorkExhausted else FragmentExhausted) Nothing []

-- One-move forms of the existing generators. Agda infers the telescope;
-- native holes retain dependencies for the shared agenda instead of recursing
-- through every operand before other actions get a turn. No arity cap and no
-- printed type matching. Rechecking each proposal owns all meta assignments.
primitiveProposals :: IORef SearchStats -> SearchLimits -> P.Models -> P.RankingMode
                   -> Maybe (NativeScorer s) -> (Value -> IO ()) -> String -> [String]
                   -> Maybe Recursion.Owner -> InteractionId -> I.Type
                   -> TCM [(A.Expr, [(T.Text, T.Text)])]
primitiveProposals stats limits models mode native emit namespace excluded owner point target = do
  pruned <- liftIO $ newIORef False
  originalSize <- getContextSize
  let runtime = Runtime limits stats pruned models mode native emit (T.pack namespace) False
      freshHole scope = do
        freshPoint <- registerInteractionPoint False noRange Nothing
        pure $ A.QuestionMark (Info.emptyMetaInfo { Info.metaScope = scope }) freshPoint
      explicitHole info = do
        freshPoint <- registerInteractionPoint False noRange Nothing
        pure $ A.QuestionMark (info { Info.metaNumber = Nothing, Info.metaRange = noRange }) freshPoint
      signature ty = do
        allowed <- charge runtime $ \s -> s { inferenceQueries = inferenceQueries s + 1 }
        if not allowed then pure (Nothing, []) else reduce ty >>= \case
          I.El _ (I.Pi domain body) -> do
            (result, rest) <- underAbstraction domain body signature
            pure (if visible domain then Just FunctionShape else result,
              (getArgInfo domain, result):rest)
          I.El _ (I.Sort _) -> pure (Just SortShape, [])
          I.El _ (I.Var index _) -> do
            -- Parameters from the original goal are rigid, but variables
            -- introduced while inspecting a function's telescope can be
            -- instantiated by its application. Account for actual context
            -- extension: Agda's NoAbs does not introduce a new binder.
            introduced <- subtract originalSize <$> getContextSize
            pure (if index >= introduced
              then Just $ LocalShape (index - introduced) else Nothing, [])
          I.El _ (I.Def name _) -> getConstInfo name >>= \definition -> pure
            (case theDef definition of
              Datatype{} -> Just $ FamilyShape name
              RecordDefn{} -> Just $ FamilyShape name
              _ -> Nothing, [])
          _ -> pure (Nothing, [])
      compatible Nothing _ = True
      compatible _ Nothing = True
      compatible (Just wanted) (Just offered) = wanted == offered
      applications expected scope expression infos = go expression infos
       where
        go _ [] = pure []
        go function ((info, result):rest) = do
          operand <- if getHiding info == NotHidden then freshHole scope
            else Construction.omittedField (getHiding info)
          let applied = A.app function [Arg info $ unnamed operand]
          suffix <- go applied rest
          pure $ if getHiding info == NotHidden && compatible expected result
            then applied:suffix else suffix
  -- Unification in a sibling can solve a meta without retiring its source
  -- interaction. Use Agda's own scoped solution (including its permutation)
  -- as a proposal, rather than searching for that assignment a second time.
  -- Still check it through the normal transition and retain ordinary fallbacks.
  assigned <- attempt runtime $ do
    allowed <- charge runtime $ \s -> s { inferenceQueries = inferenceQueries s + 1 }
    if not allowed then pure Nothing else do
      meta <- lookupInteractionId point
      variable <- lookupLocalMeta meta
      case mvInstantiation variable of
        InstV{} -> do
          arguments <- getContextArgs
          value <- instantiateFull $ I.MetaV meta $ map I.Apply arguments
          -- Retain Agda's inferred structure, but never its anonymous meta
          -- identities in a replayable draft. Its elaboration presentation
          -- exposes missing values as holes; each occurrence gets a fresh
          -- interaction so normal checking records explicit obligations.
          solutions <- locallyTC ePrintMetasBare (const $ not $ noMetas value) $
            Basic.getSolvedInteractionPoints False AsIs
          case lookup point [(p, expression) | (p, _, expression) <- solutions] of
            Nothing -> pure Nothing
            Just expression | noMetas value -> pure $ Just expression
            Just expression -> Just <$> traverseExpr (\case
              A.QuestionMark info _ -> explicitHole info
              A.Underscore info -> explicitHole info
              part -> pure part) expression
        _ -> pure Nothing
  let assignedProposals = maybe [] (\expression -> [(expression, [])]) assigned
  (forbiddenHere, _) <- excludedGlobals excluded
  inherited <- maybe (pure Set.empty) Recursion.ownerGroup owner
  let forbidden = Set.union forbiddenHere inherited
  closures <- Construction.constructorClosures
    (charge runtime $ \s -> s { inferenceQueries = inferenceQueries s + 1 }) forbidden target
  globals <- visibleGlobals forbidden
  classified <- attempt runtime $ do
    allowed <- charge runtime $ \s -> s
      { inferenceQueries = inferenceQueries s + 1, classificationQueries = classificationQueries s + 1 }
    let constructors = Set.fromList [name | A.Con (I.AmbQ names) <- globals, name <- toList names]
    if allowed then Just <$> Scheduling.classify forbidden constructors Nothing target else pure Nothing
  let classification = maybe Classification.unknownClassification id classified
  ranked <- rankSeeds runtime classification target globals
  scope <- getScope
  (expected, _) <- localTCState $ signature target
  heads <- fmap concat $ forM ranked $ \(Seed expression _ _, picked) -> do
    observed <- localTCState $ attempt runtime $
      queryInferWith DontExpandLast runtime expression $ \(_, ty) -> Just <$> signature ty
    let (result, infos) = maybe (Nothing, []) id observed
    variants <- applications expected scope expression infos
    modify runtime $ \s -> s { applicationProposals = applicationProposals s + fromIntegral (length variants) }
    pure [(variant, picked) | variant <- [expression | compatible expected result] ++ variants]
  construction <- localTCState $ do
    allowed <- charge runtime $ \s -> s { inferenceQueries = inferenceQueries s + 1 }
    if allowed then Construction.recordPlan forbidden target else pure Nothing
  record <- case construction of
    Nothing -> pure []
    Just (names, telescope) -> do
      let fields :: [C.Name] -> I.Telescope -> TCM [(C.Name, A.Expr)]
          fields [] I.EmptyTel = pure []
          fields (name:rest) (I.ExtendTel domain body) = do
            if visible domain then do
              hole <- freshHole scope
              restFields <- fields rest (I.unAbs body)
              pure $ (name, hole):restFields
            else fields rest (I.unAbs body)
          fields _ _ = genericError "native-record-telescope-mismatch"
      assignments <- fields names telescope
      modify runtime $ \s -> s { recordProposals = recordProposals s + 1 }
      pure [(Construction.recordExpression assignments, [])]
  introduction <- reduce target >>= \case
    I.El _ (I.Pi domain body) ->
      let hint = if I.absName body `elem` ["", "_"] then "x" else I.absName body in
      withFreshName noRange hint $ \name -> do
        let inner = setScopeLocals ((A.nameConcrete name, LocalVar name LambdaBound []) : _scopeLocals scope) scope
        hole <- freshHole inner
        modify runtime $ \s -> s { lambdaProposals = lambdaProposals s + 1 }
        pure [(A.Lam exprNoRange (A.mkDomainFree $ Arg (getArgInfo domain) $ unnamed $ A.mkBinder_ name) hole, [])]
    _ -> pure []
  let constructed = [(expression, []) | expression <- closures,
        expression `notElem` map fst heads] ++ introduction ++ record
      constructorHead expression = case appView expression of
        Application A.Con{} _ -> True
        _ -> False
      -- Constructor-headed applications are introductions just as record
      -- literals are. Keep their model order within the construction tier;
      -- otherwise a datatype's constructor fields are scheduled as arbitrary
      -- eliminations, while the equivalent record fields get precedence.
      constructorHeads = [item | item@(expression, _) <- heads, constructorHead expression]
      eliminationHeads = [item | item@(expression, _) <- heads, not $ constructorHead expression]
      ordered = if Classification.constructionFirst classification
        then [(0, item) | item <- constructed ++ constructorHeads] ++ [(1, item) | item <- eliminationHeads]
        else [(0, item) | item <- heads] ++ [(1, item) | item <- constructed]
  if not (P.hasDomain models P.Refinements) || mode == P.Symbolic
    then pure $ assignedProposals ++ map snd ordered else do
    context <- getContext
    localTypes <- forM (zip [0..] context) $ \(index, entry) -> do
      ty <- typeOfBV index
      text <- T.pack . prettyShow <$> prettyTCM ty
      pure (ctxEntryName entry, text)
    targetText <- T.pack . prettyShow <$> prettyTCM target
    let goal = F.GoalView targetText (map snd localTypes) Nothing
        features expression = do
          (tag, local) <- PolicyViews.refinementView expression
          pure $ F.refinementTokens goal tag (local >>= (`lookup` localTypes))
    (assignedProposals ++) <$> rankCompatible runtime P.Refinements goal
      [(tier, features expression, item) | (tier, item@(expression, _)) <- ordered]

-- Compound introductions are a whole-search operation, separate from the
-- ordinary one-step catalogue and the cheap later-goal closure probe.
structuralProposals :: IORef SearchStats -> SearchLimits -> P.Models -> P.RankingMode
                    -> Maybe (NativeScorer s) -> (Value -> IO ()) -> String -> [String]
                    -> Maybe Recursion.Owner -> InteractionId -> I.Type
                    -> TCM [(A.Expr, [(T.Text, T.Text)])]
structuralProposals stats limits models mode native emit namespace excluded owner point target = do
  pruned <- liftIO $ newIORef False
  let runtime = Runtime limits stats pruned models mode native emit (T.pack namespace) False
  (forbiddenHere, _) <- excludedGlobals excluded
  inherited <- maybe (pure Set.empty) Recursion.ownerGroup owner
  proposal <- attempt runtime $ do
    allowed <- charge runtime $ \s -> s { inferenceQueries = inferenceQueries s + 1 }
    if not allowed then pure Nothing else do
      variable <- lookupLocalMeta =<< lookupInteractionId point
      case mvInstantiation variable of
        -- The ordinary catalogue already preserves Agda's assigned structure.
        -- Do not offer a new construction in front of that exact assignment.
        InstV{} -> pure Nothing
        _ -> Construction.constructionScaffold
          (charge runtime $ \s -> s { inferenceQueries = inferenceQueries s + 1 })
          (charge runtime $ \s -> s { checkerQueries = checkerQueries s + 1 })
          (Set.union forbiddenHere inherited) target
  pure [(expression, []) | expression <- maybe [] pure proposal]

-- A cheap target-directed slice for other selected joint obligations. It does
-- not enumerate their premise catalogues or perform a hidden whole-goal search.
constructorProposals :: IORef SearchStats -> SearchLimits -> P.Models -> P.RankingMode
                     -> Maybe (NativeScorer s) -> (Value -> IO ()) -> String -> [String]
                     -> Maybe Recursion.Owner -> InteractionId -> I.Type
                     -> TCM [(A.Expr, [(T.Text, T.Text)])]
constructorProposals stats limits models mode native emit namespace excluded owner _ target = do
  pruned <- liftIO $ newIORef False
  let runtime = Runtime limits stats pruned models mode native emit (T.pack namespace) False
  (forbiddenHere, _) <- excludedGlobals excluded
  inherited <- maybe (pure Set.empty) Recursion.ownerGroup owner
  proposals <- Construction.constructorClosures
    (charge runtime $ \s -> s { inferenceQueries = inferenceQueries s + 1 })
    (Set.union forbiddenHere inherited) target
  seeds <- mapM (describe runtime "constructor-closure") proposals
  ranked <- rankDescribed runtime Classification.unknownClassification target seeds
  pure [(expression, picked) | (Seed expression _ _, picked) <- ranked]

-- Clause subjects come from native context identities and datatype/record
-- metadata. Generated actions retain those identities through the session;
-- Agda decides whether splitting, coverage and without-K are admissible.
clauseProposals :: IORef SearchStats -> SearchLimits -> P.Models -> P.RankingMode
                -> Maybe (NativeScorer s) -> (Value -> IO ()) -> String -> [String] -> I.Type
                -> TCM [(ClauseExecution.Intent, [(T.Text, T.Text)])]
clauseProposals stats limits models mode native emit namespace excluded target = do
  pruned <- liftIO $ newIORef False
  let runtime = Runtime limits stats pruned models mode native emit (T.pack namespace) False
  (forbidden, _) <- excludedGlobals excluded
  context <- getContext
  observed <- fmap catMaybes $ forM (zip [0..] context) $ \(index, entry) -> attempt runtime $ do
    allowed <- charge runtime $ \s -> s { inferenceQueries = inferenceQueries s + 1 }
    if not allowed then pure Nothing else do
      ty <- typeOfBV index
      splitting <- reduce ty >>= \case
        I.El _ (I.Def name _) -> getConstInfo name >>= \definition -> pure $ case theDef definition of
          Datatype { dataCons = constructors }
            | not $ any (`Set.member` forbidden) constructors -> Just $ length constructors == 1
          RecordDefn record | _recInduction record /= Just CoInductive,
            not $ any (`Set.member` forbidden) (I.conName (_recConHead record) : map I.unDom (_recFields record)) -> Just True
          _ -> Nothing
        _ -> pure Nothing
      rendered <- prettyShow <$> prettyTCM ty
      let name = prettyShow $ A.nameConcrete $ ctxEntryName entry
          subject = fmap (\single -> (name, rendered, single,
            ClauseExecution.BoundSubjects (ctxEntryName entry :| []))) splitting
      pure $ Just (rendered, subject)
  targetText <- T.pack . prettyShow <$> prettyTCM target
  let subjects = catMaybes $ map snd observed
      goal = F.GoalView targetText (map (T.pack . fst) observed) Nothing
      decision = T.pack namespace <> ":case"
      candidates = [P.Candidate (T.pack $ show index) (T.pack name) 0
        (Right $ F.candidateTokens goal $ F.CandidateView "case-variable" "split"
          (T.pack ty) (T.pack name) 1 []) action
        | (index, (name, ty, _, action)) <- zip [0 :: Int ..] subjects]
  ordered <- if null candidates then pure [] else do
    ranked <- liftIO $ P.rankBatch native models mode (P.ORFamily "case-variable") decision
      (F.policyStateTokens goal Classification.unknownClassification) candidates
    case ranked of
      Left reason -> genericError $ "native-policy-batch:" ++ reason
      Right batch -> do
        modify runtime $ \s -> s { policyDecisions = policyDecisions s + 1,
          modelItems = modelItems s + fromIntegral (P.traceItemsScored $ P.decisionTrace batch),
          modelNanoseconds = modelNanoseconds s + P.traceModelNanoseconds (P.decisionTrace batch) }
        liftIO $ emit $ P.traceView $ P.decisionTrace batch
        pure [(P.candidateValue candidate, [(decision, P.candidateId candidate)])
          | candidate <- P.rankedCandidates batch]
  -- A single finite batch exposes the existing multi-subject Agda operation
  -- to autonomous search. Positive one-constructor metadata avoids a product
  -- of case branches; admissibility and dependent substitution remain Agda's
  -- responsibility. Preserve every single-subject alternative.
  let linearNames = Set.fromList [name | (_, _, True, ClauseExecution.BoundSubjects names) <- subjects,
        name <- NE.toList names]
      linearSubjects = [name | (ClauseExecution.BoundSubjects names, _) <- ordered,
        name <- NE.toList names, Set.member name linearNames]
      batches = case linearSubjects of
        first:second:rest -> [(ClauseExecution.BoundSubjects (first :| (second:rest)), [])]
        _ -> []
      features action = case [(ty) | (_, ty, _, proposed) <- subjects, proposed == action] of
        ty:_ -> Just $ F.refinementTokens goal "case-split" (Just $ T.pack ty)
        [] -> Just $ F.refinementTokens goal "case-split" Nothing
  refinements <- rankCompatible runtime P.Refinements goal
    [(0, features action, item) | item@(action, _) <- batches ++ ordered]
  -- Result splitting also exposes binders that are absent from the local
  -- context. Keep that Agda operation; do not guess a telescope from text.
  resultAvailable <- attempt runtime $ do
    allowed <- charge runtime $ \s -> s { inferenceQueries = inferenceQueries s + 1 }
    if not allowed then pure Nothing else reduce target >>= \case
      I.El _ (I.Def name _) -> getConstInfo name >>= \definition -> pure $ case theDef definition of
        Datatype{} -> Just False
        _ -> Just True
      I.El _ I.Sort{} -> pure $ Just False
      _ -> pure $ Just True
  -- A rigid datatype/sort result has no fields or trailing arguments. Asking
  -- make_case to expose the already-generated helper's hidden parameters only
  -- wraps the same obligation again. Explicit user commands remain available.
  pure $ [(ClauseExecution.UserAction Clause.splitResult, []) | resultAvailable /= Just False] ++ refinements

-- Optional legacy roles only see compatible native feature views. Unmodelled
-- actions keep their original slots, and structural tiers are never crossed.
-- The terms themselves remain native values throughout; text is scoring only.
rankCompatible :: Runtime s -> P.RankingDomain -> F.GoalView
               -> [(Int, Maybe (Either String [T.Text]), (a, [(T.Text, T.Text)]))]
               -> TCM [(a, [(T.Text, T.Text)])]
rankCompatible runtime@(Runtime _ ref _ models mode native emit namespace _) domain goal entries
  | not (P.hasDomain models domain) || mode == P.Symbolic = pure $ map (\(_, _, item) -> item) entries
  | otherwise = do
    stats <- liftIO $ readIORef ref
    let ordinal = policyDecisions stats
        decision = namespace <> ":primary:" <> T.pack (show ordinal)
        candidates = [P.Candidate (T.pack $ show index) "native-action" tier tokens item
          | (index, (tier, Just tokens, item)) <- zip [0 :: Int ..] entries]
    ranked <- liftIO $ P.rankBatch native models mode domain decision (F.stateTokens goal) candidates
    case ranked of
      Left reason -> genericError $ "native-primary-policy-batch:" ++ reason
      Right batch -> do
        modify runtime $ \s -> s { policyDecisions = ordinal + 1,
          modelItems = modelItems s + fromIntegral (P.traceItemsScored $ P.decisionTrace batch),
          modelNanoseconds = modelNanoseconds s + P.traceModelNanoseconds (P.decisionTrace batch) }
        liftIO $ emit $ P.traceView $ P.decisionTrace batch
        let reordered = [(value, chosen ++ [(decision, P.candidateId candidate)])
              | candidate <- P.rankedCandidates batch, let (value, chosen) = P.candidateValue candidate]
            merge :: [(Int, Maybe (Either String [T.Text]), b)] -> [b] -> TCM [b]
            merge [] [] = pure []
            merge ((_, Nothing, item):rest) values = (item :) <$> merge rest values
            merge ((_, Just _, _):rest) (item:values) = (item :) <$> merge rest values
            merge _ _ = genericError "native-primary-policy-cardinality"
        merge entries reordered

modify :: Runtime s -> (SearchStats -> SearchStats) -> TCM ()
modify (Runtime _ ref _ _ _ _ _ _ _) f = liftIO $ atomicModifyIORef' ref $ \s -> (f s, ())
stopped :: Runtime s -> TCM Bool
stopped (Runtime _ ref _ _ _ _ _ _ _) = workExhausted <$> liftIO (readIORef ref)
charge :: Runtime s -> (SearchStats -> SearchStats) -> TCM Bool
charge (Runtime limits ref _ _ _ _ _ _ _) f = liftIO $ atomicModifyIORef' ref $ \s ->
  if workExhausted s || maybe False (workUnits s >=) (workUnitLimit limits)
    then (s { workExhausted = True }, False)
    else (f s { workUnits = workUnits s + 1 }, True)
deferDepth :: Runtime s -> TCM (Maybe a)
deferDepth (Runtime _ _ ref _ _ _ _ _ _) = liftIO (writeIORef ref True) >> pure Nothing

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
        case meaning of
          Right value@(DefinedName _ name _)
            | not (Set.member (anameName name) forbidden) -> do
                definition <- getConstInfo $ anameName name
                available <- case theDef definition of
                  -- Generalizable names describe binders, not closed global
                  -- terms. Agda's inferDef requires a live generalization
                  -- binding; invoking it outside that context is invalid.
                  -- Generalized local parameters remain ordinary local heads.
                  GeneralizableVar{} -> Map.member (anameName name) <$> viewTC eGeneralizedVars
                  _ -> pure True
                pure $ if not available then Nothing else case A.nameToExpr value of
                  expression@A.Def'{} -> Just expression
                  _ -> Nothing
          Right (FieldName fields) -> pure $ case filter (not . (`Set.member` forbidden) . anameName) (toList fields) of
            [] -> Nothing
            -- This is a prefix function head, not a postfix projection
            -- elimination. Preserve that distinction through reconstruction.
            name:names -> Just $ A.Proj ProjPrefix $ I.AmbQ (anameName name :| map anameName names)
          Right (ConstructorName _ constructors) -> pure $
            case filter (not . (`Set.member` forbidden) . anameName) (toList constructors) of
              [] -> Nothing
              name:names -> Just $ A.Con $ I.AmbQ (anameName name :| map anameName names)
          Right value@VarName{} -> pure $ Just $ A.nameToExpr value
          _ -> pure Nothing
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

rankSeeds :: Runtime s -> Classification.Classification -> I.Type -> [A.Expr] -> TCM [(Seed, [(T.Text, T.Text)])]
rankSeeds runtime classification target globals = do
  context <- getContext
  let locals = map (A.Var . ctxEntryName) context
      visibleFields = Set.fromList [name | A.Proj _ (I.AmbQ names) <- globals, name <- toList names]
  observed <- if Set.null visibleFields then pure Nothing else localTCState $ attempt runtime $ do
    allowed <- charge runtime $ \s -> s
      { inferenceQueries = inferenceQueries s + 1, recordObservationQueries = recordObservationQueries s + 1 }
    if not allowed then pure Nothing else Just . concat <$> forM (zip [0..] locals) (\(index, expression) ->
      typeOfBV index >>= Construction.projectedEvidence visibleFields expression)
  let projections = nub $ maybe [] id observed
  appliedFields <- fmap concat $ forM projections $ \function -> do
    admissible <- localTCState $ attempt runtime $
      queryInfer runtime function $ \(_, ty) -> reduce ty >>= \case
        I.El _ (I.Pi domain _) | visible domain -> pure $ Just ()
        _ -> pure Nothing
    case admissible of
      Nothing -> pure []
      Just () -> fmap catMaybes $ forM locals $ \argument -> localTCState $ attempt runtime $ do
        let expression = A.app function [defaultArg $ unnamed argument]
        modify runtime $ \s -> s { applicationProposals = applicationProposals s + 1 }
        queryInfer runtime expression $ \(value, ty) -> do
          completeValue <- instantiateFull value
          completeType <- instantiateFull ty
          pure $ if noMetas completeValue && noMetas completeType then Just expression else Nothing
  let recordSeeds = nub $ projections ++ appliedFields
  modify runtime $ \s -> s { projectedSeeds = projectedSeeds s + fromIntegral (length recordSeeds) }
  seeds <- mapM (uncurry $ describe runtime) $
    [("local", expression) | expression <- locals]
    ++ [("projected-field", expression) | expression <- recordSeeds]
    ++ [("visible", expression) | expression <- globals, expression `notElem` locals]
  rankDescribed runtime classification target seeds

rankDescribed :: Runtime s -> Classification.Classification -> I.Type -> [Seed]
              -> TCM [(Seed, [(T.Text, T.Text)])]
rankDescribed _ _ _ [] = pure []
rankDescribed runtime@(Runtime _ ref _ models mode native emit namespace _) classification target seeds = do
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
    (F.policyStateTokens goal classification) candidates
  -- The router counts inference; this ledger also retains preparation work on
  -- interrupted/rejected attempts through the surrounding session dispatch.
  case ranked of
    Left reason -> genericError $ "native-policy-batch:" ++ reason
    Right batch -> do
      modify runtime $ \s -> s { policyDecisions = ordinal + 1
        , modelItems = modelItems s + fromIntegral (P.traceItemsScored $ P.decisionTrace batch)
        , modelNanoseconds = modelNanoseconds s + P.traceModelNanoseconds (P.decisionTrace batch) }
      let view = case P.traceView $ P.decisionTrace batch of
            Object fields -> Object $ KM.insert "structural_classification" (toJSON classification) fields
            other -> other
      liftIO $ emit view
      rankCompatible runtime P.ProofTerms goal
        [(0, F.termTokens goal <$> PolicyViews.termView expression,
          (seed, if length candidates > 1 then [(decision, P.candidateId candidate)] else []))
        | candidate <- P.rankedCandidates batch, let seed@(Seed expression _ _) = P.candidateValue candidate]

-- Continuations implement the AND part: if a later argument or final check
-- fails, search revisits earlier argument choices with the original TCState.
rankFocused :: Runtime s -> NativeFocused.Fragment -> Focused.Formula -> [Focused.Formula]
            -> [Focused.Action] -> TCM [(Focused.Action, [(T.Text, T.Text)])]
rankFocused _ _ _ _ [] = pure []
rankFocused runtime@(Runtime _ ref _ models mode native emit namespace _) fragment target context actions = do
  stats <- liftIO $ readIORef ref
  let view (Focused.Atom index) = NativeFocused.atomViews fragment !! index
      view (Focused.Arrow a b) = F.ArrowView (view a) (view b)
      goal = view target
      assumptions = [F.FocusedAssumption (view ty) index | (index, ty) <- zip [0..] context]
      ordinal = policyDecisions stats
      decision = namespace <> ":focused:" <> T.pack (show ordinal)
      candidates = [P.Candidate (T.pack $ show index) ("focus-" <> T.pack (show $ Focused.assumption action)) 0
          (Right $ F.focusedActionTokens goal assumptions (assumptions !! Focused.assumption action)
            (map view $ Focused.domains action)) action
        | (index, action) <- zip [0 :: Int ..] actions]
  result <- liftIO $ P.rankBatch native models mode P.FocusedBranches decision
    (Right $ F.focusedStateTokens goal assumptions) candidates
  case result of
    Left reason -> genericError $ "native-focused-policy-batch:" ++ reason
    Right batch -> do
      modify runtime $ \s -> s { policyDecisions = ordinal + 1
        , modelItems = modelItems s + fromIntegral (P.traceItemsScored $ P.decisionTrace batch)
        , modelNanoseconds = modelNanoseconds s + P.traceModelNanoseconds (P.decisionTrace batch) }
      liftIO $ emit $ P.traceView $ P.decisionTrace batch
      pure [(P.candidateValue candidate, if length candidates > 1 then [(decision, P.candidateId candidate)] else [])
        | candidate <- P.rankedCandidates batch]

search :: Runtime s -> GlobalInventory -> Int -> I.Type -> [(T.Text,T.Text)]
       -> (A.Expr -> I.Term -> [(T.Text,T.Text)] -> TCM (Maybe a)) -> TCM (Maybe a)
search runtime@(Runtime _ _ _ _ _ _ _ _ enableFocused) inventory@(GlobalInventory globals forbidden recursion) depth target selected use = do
  done <- stopped runtime
  if done then pure Nothing else do
    modify runtime $ \s -> s { searchNodes = searchNodes s + 1 }
    choices runtime $ [focused | enableFocused] ++ [ordinary]
 where
  focused = do
    allowed <- charge runtime $ \s -> s
      { inferenceQueries = inferenceQueries s + 1, focusedObservationQueries = focusedObservationQueries s + 1 }
    if not allowed then pure Nothing else NativeFocused.observe target >>= \case
      Nothing -> pure Nothing
      Just fragment -> Focused.enumerate
        (Focused.Hooks
          (charge runtime $ \s -> s { focusedActions = focusedActions s + 1 })
          noteFocused
          (rankFocused runtime fragment))
        (NativeFocused.emptyAtoms fragment) depth (NativeFocused.assumptions fragment)
        (NativeFocused.target fragment) $ \solution -> attempt runtime $ do
          modify runtime $ \s -> s { focusedCandidates = focusedCandidates s + 1 }
          expression <- NativeFocused.render fragment $ Focused.proof solution
          queryCheck runtime expression target $ \term -> use expression term (selected ++ Focused.decisions solution)
  noteFocused event = case event of
    Focused.Node -> modify runtime $ \s -> s { focusedNodes = focusedNodes s + 1 }
    Focused.CacheHit -> modify runtime $ \s -> s { focusedCacheHits = focusedCacheHits s + 1 }
    Focused.CyclePruned -> modify runtime $ \s -> s { focusedCycles = focusedCycles s + 1 }
    Focused.Deferred -> deferDepth runtime >> pure ()
    Focused.Rule -> pure ()
  ordinary = do
    classified <- attempt runtime $ do
      allowed <- charge runtime $ \s -> s
        { inferenceQueries = inferenceQueries s + 1, classificationQueries = classificationQueries s + 1 }
      let constructors = Set.fromList [name | A.Con (I.AmbQ names) <- globals, name <- toList names]
      if allowed then Just <$> Scheduling.classify forbidden constructors recursion target else pure Nothing
    let classification = maybe Classification.unknownClassification id classified
    seeds <- rankSeeds runtime classification target globals
    let construction = [constructRecord, introduce]
        application = [queryInferWith DontExpandLast runtime expression $ \(_, ty) ->
            guidedApplication expression ty depth [] (selected ++ picked)
          | (Seed expression _ _, picked) <- seeds]
    choices runtime $
      [queryCheck runtime expression target $ \term -> use expression term (selected ++ picked)
       | (Seed expression _ _, picked) <- seeds]
      ++ [algebraic seeds]
      ++ [recursiveCall inferredArguments context | Just context <- [recursion]]
      ++ (if Classification.constructionFirst classification
            then construction ++ application else application ++ construction)
      ++ [recursiveCall arguments context | Just context <- [recursion]]
      ++ [produce expression picked | (Seed expression _ _, picked) <- seeds]
  -- Recognizers consume native types; ranked visible/local evidence supplies
  -- every law and relation operation. Pure rewrite paths preserve distinct
  -- proofs, and a downstream rejection resumes alternative paths. This does
  -- not confer commutativity, equality elimination or proof irrelevance.
  algebraic seeds = do
    allowed <- charge runtime $ \s -> s
      { inferenceQueries = inferenceQueries s + 1, algebraObservationQueries = algebraObservationQueries s + 1 }
    if not allowed then pure Nothing else do
      views <- NativeAlgebra.inspectGoal target
      choices runtime [rewriteView view | view <- views]
   where
      rewriteView view = do
        observed <- fmap catMaybes $ forM seeds $ \(Seed expression _ _, picked) -> localTCState $ attempt runtime $
          queryInferWith DontExpandLast runtime expression $ \(_, ty) ->
            fmap (\role -> (role,(expression,picked))) <$> NativeAlgebra.inspectEvidence view ty
        let (ops, edges) = NativeAlgebra.operations observed
            (left,right) = NativeAlgebra.endpoints view
            note Algebra.Deferred = deferDepth runtime >> pure ()
            note _ = pure ()
        wrappers <- NativeAlgebra.contexts view
        let finish [] expression picked = do
              modify runtime $ \s -> s { algebraCandidates = algebraCandidates s + 1 }
              queryCheck runtime expression target $ \term -> use expression term picked
            finish (f:rest) expression picked = choices runtime
              [finish rest (A.app lift [defaultArg $ unnamed f, defaultArg $ unnamed expression])
                (picked ++ labels) | (lift,labels) <- Algebra.congruence ops]
        Algebra.enumerate (Algebra.Hooks
          (charge runtime $ \s -> s { algebraActions = algebraActions s + 1 }) note)
          depth ops edges left right $ \proof -> attempt runtime $ do
            expression <- NativeAlgebra.render view (fmap fst proof)
            finish wrappers expression (selected ++ concatMap snd (toList proof))
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
              -- A supplied operation is one AND step, regardless of its
              -- arity. The operands recurse at depth-1 below; every generated
              -- placeholder/check is still charged to the work allowance.
              (absApp codomain value) remaining
              (holes ++ [(point', value, getHiding domain)]) picked
    _ | null holes -> pure Nothing
      | otherwise -> do
          allowed <- charge runtime $ \s -> s { checkerQueries = checkerQueries s + 1 }
          if not allowed then pure Nothing else do
            compareType CmpLeq ty target
            queryCheck runtime expression target $ \_ ->
              -- Explicit operands carry the evidence that determines hidden
              -- endpoints, carriers and families. Do not guess those hidden
              -- values before giving Agda the operands that constrain them.
              -- The final pass still checks every unresolved obligation.
              fillArguments expression (sortOn (\(_, _, visibility) -> visibility /= NotHidden) holes) Map.empty picked
  fillArguments expression [] filled picked = do
    completed <- traverseExpr (\case
      old@(A.QuestionMark _ point') -> pure $ Map.findWithDefault old point' filled
      old -> pure old) expression
    queryCheck runtime completed target $ \term -> use completed term picked
  fillArguments expression ((point', value, _):rest) filled picked = do
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
