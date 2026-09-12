{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE LambdaCase #-}
-- SPDX-License-Identifier: GPL-3.0-or-later
module AgdaProver.Agda28.ClauseExecution (Intent (..), PreparationStep (..), prepare, prepareClosing, prepareAbstraction, registerDraft, patternLocals) where

import Control.Monad (forM, void, when)
import Control.Monad.Except (catchError, throwError)
import Data.List (elemIndex)
import Data.List.NonEmpty (NonEmpty (..))
import Data.List.NonEmpty qualified as NE
import Data.Maybe (isNothing)

import Agda.Interaction.BasicOps (give_, parseExprIn)
import Agda.Interaction.Base (UseForce (WithoutForce))
import Agda.Interaction.MakeCase (makeCase, parseVariables, recheckAbstractClause)
import Agda.Syntax.Abstract qualified as A
import Agda.Syntax.Abstract.Name (Name, nameConcrete, qualify)
import Agda.Syntax.Abstract.Pattern (lhsToSpine)
import Agda.Syntax.Abstract.Views (deepUnscope, traverseExpr)
import Agda.Syntax.Common
import Agda.Syntax.Common.Pretty (prettyShow)
import Agda.Syntax.Concrete.Name qualified as C
import Agda.Syntax.Info qualified as Info
import Agda.Syntax.Internal qualified as I
import Agda.Syntax.Internal.MetaVars (noMetas)
import Agda.Syntax.Position (noRange)
import Agda.Syntax.Scope.Base
import Agda.Syntax.Translation.InternalToAbstract (reify)
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Constraints (reallyNoConstraints)
import Agda.TypeChecking.Reduce (instantiateFull, reduce)
import Agda.TypeChecking.Rules.Term (checkExpr)
import Agda.TypeChecking.Substitute (telePi)
import Agda.TypeChecking.Telescope (splitTelescopeAt)
import Agda.Utils.Null (empty)
import Agda.Utils.Lens ((^.))
import Agda.Utils.BiMap qualified as BiMap

import AgdaProver.Symbolic.Clause (ClauseAction, command)
import AgdaProver.Agda28.Clauses qualified as Clauses

data PreparationStep = GenerateClauses | CheckContext | CheckScaffold

-- Search already has Agda binding identities; round-tripping their base names
-- loses shadowing and disambiguation. User commands deliberately retain Agda's
-- own resolution/exposure behavior. Session seals either intent to its goal.
data Intent = UserAction ClauseAction | BoundSubjects (NonEmpty Name)
  | ClosingSubjects (NonEmpty Name)
  | AdaptiveSubjects (NonEmpty Name)
  deriving Eq

-- A split is implemented as a local, dependent eliminator, not by mutating an
-- already checked global definition. The helper and its case clauses are native
-- syntax. Ordinary give checks the final draft again from the unsplit parent.
prepare :: (PreparationStep -> TCM ()) -> InteractionId -> Intent -> TCM A.Expr
prepare = prepareTarget False

prepareTarget :: Bool -> (PreparationStep -> TCM ()) -> InteractionId -> Intent -> TCM A.Expr
prepareTarget introduced chargeStep point action = withInteractionId point $ do
  chargeStep CheckContext
  target <- getMetaTypeInContext =<< lookupInteractionId point
  reduce target >>= \case
    I.El _ (I.Pi domain body) | notVisible domain -> do
      -- Ordinary checking inserts these lambdas even around a let-bound
      -- helper. They must be syntax in the retained draft: later child proofs
      -- can refer to their exact native identities. Let Agda establish the
      -- child context, including the binder's hiding and modality.
      before <- getTC
      name <- C.setNotInScope <$> freshName_ (I.absName body)
      scope <- getScope
      temporary <- registerInteractionPoint False noRange Nothing
      let hole = A.QuestionMark (Info.emptyMetaInfo { Info.metaScope = scope }) temporary
          wrap = A.Lam Info.exprNoRange $
            A.mkDomainFree $ Arg (getArgInfo domain) $ unnamed $ A.mkBinder_ name
      chargeStep CheckScaffold
      void $ give_ False WithoutForce point Nothing $ wrap hole
      expression <- prepareTarget True chargeStep temporary action
      restoreAllocations before
      registerDraft $ wrap expression
    I.El _ I.Pi{} -> prepareBody chargeStep point action
    _ | introduced, UserAction requested <- action, null (command requested) -> do
      -- Agda's result split stops after introducing arguments; it does not
      -- also split the resulting record. Hidden-only functions likewise leave
      -- their codomain as an ordinary obligation, even when it is rigid.
      scope <- getScope
      pure $ A.QuestionMark (Info.emptyMetaInfo { Info.metaScope = scope }) point
    _ -> prepareBody chargeStep point action

-- The caller may add finite terminal inhabitants, but cannot accept them.
-- All leaves still require non-instantiating, constraint-free native checks.
-- The ordinary ClosingSubjects action supplies no extra candidates.
prepareClosing :: (PreparationStep -> TCM ()) -> (I.Type -> TCM [A.Expr])
               -> InteractionId -> NonEmpty Name -> TCM A.Expr
prepareClosing chargeStep terminal point chosen = trySubjects $ NE.toList chosen
 where
  -- A bounded lookahead for an existing inhabitant after one elimination.
  -- The full batch and ordinary single-subject moves remain alternatives.
  -- Do not inspect further subjects once a branch can reuse its context: an
  -- unnecessary pattern can destroy computation useful to later obligations.
  trySubjects [] = genericError "native-clause-no-local-closure"
  trySubjects (name:rest) = do
    before <- getTC
    existing <- getInteractionPoints
    let probe = do
          draft <- prepare chargeStep point $ BoundSubjects (name :| [])
          chargeStep CheckScaffold
          void $ give_ False WithoutForce point Nothing draft
          result <- traverseExpr (\case
            A.QuestionMark _ child | child `notElem` existing ->
              withInteractionId child $ do
                target <- getMetaTypeInContext =<< lookupInteractionId child
                context <- getContext
                close target (map (A.Var . ctxEntryName) context) >>= \case
                  Just expression -> pure expression
                  Nothing -> terminal target >>= close target >>= \case
                    Just expression -> pure expression
                    Nothing -> genericError "native-clause-no-local-inhabitant"
            expression -> pure expression) draft
          restoreAllocations before
          pure result
    probe `catchError` \err -> case err of
      TypeError{} -> restoreAllocations before >> trySubjects rest
      PatternErr{} -> restoreAllocations before >> trySubjects rest
      _ -> throwError err
  close _ [] = pure Nothing
  close target (expression:rest) = do
    chargeStep CheckContext
    found <- localTCState $ (do
      term <- reallyNoConstraints $ dontAssignMetas $ checkExpr expression target
      noMetas <$> instantiateFull term) `catchError` \err -> case err of
        TypeError{} -> pure False
        PatternErr{} -> pure False
        _ -> throwError err
    if found then pure $ Just expression else close target rest

prepareBody :: (PreparationStep -> TCM ()) -> InteractionId -> Intent -> TCM A.Expr
prepareBody chargeStep point (ClosingSubjects chosen) =
  prepareClosing chargeStep (const $ pure []) point chosen
prepareBody chargeStep point action = withInteractionId point $ do
  context <- getContext
  target <- getMetaTypeInContext =<< lookupInteractionId point
  telescope <- getContextTelescope
  originalScope <- getScope
  names <- forM (zip [0 :: Int ..] context) $ \(i, _) ->
    freshName_ $ "argument" ++ show i
  (selected, indices) <- subjects chargeStep point action (map ctxEntryName context) names
  let width = maximum $ 0 : map (+ 1) indices
  before <- getTC
  let build count = do
        let (_, suffix) = splitTelescopeAt (length context - count) telescope
        -- Reification must retain the actual meta argument spines. Reusing a
        -- checkpoint strengthened past the abstracted variables would leave
        -- impossible entries in Agda's identity-substitution comparison.
        signature <- withShowAllArguments $ inTopContext $ addContext (reverse $ drop count context) $
          reify $ telePi suffix target
        let entries = reverse $ take count $ zip context names
        prepareHelperUsing generateClauses chargeStep point originalScope signature selected
          [(getArgInfo entry, name, A.Var $ ctxEntryName entry) | (entry, name) <- entries]
      -- Start with just the subjects and their dependent suffix. Free-variable
      -- scans of indices also include hidden carrier arguments of local
      -- operations, incorrectly pulling ambient types into the helper.
      -- Let Agda determine which older binders must actually be generalized.
      attempt count = build count `catchError` \err -> case err of
        TypeError{} | count < length context -> retry count
        PatternErr{} | count < length context -> retry count
        _ -> throwError err
      retry count = restoreAllocations before >> attempt (count + 1)
      generateClauses = case action of
        AdaptiveSubjects{} -> Clauses.extendHelper (chargeStep CheckContext) (chargeStep GenerateClauses)
        _ -> standardClauses chargeStep
  attempt $ min width $ length context

-- A with-helper has an Agda-inferred closed telescope and an application in
-- the current context. Reuse the same checked clause preparation as ordinary
-- elimination; only the telescope/application origin differs.
prepareAbstraction :: (PreparationStep -> TCM ()) -> InteractionId -> I.Type
                   -> [Arg A.Expr] -> Int -> TCM A.Expr
prepareAbstraction chargeStep point ty arguments selected = withInteractionId point $ do
  chargeStep CheckContext
  -- This is re-elaborated syntax, not a compact display. A hidden family
  -- parameter may not be recoverable from its explicit indices.
  signature <- withShowAllArguments $ inTopContext $ reify ty
  scope <- getScope
  entries <- forM (zip [0 :: Int ..] arguments) $ \(index, argument) -> do
    name <- freshName_ $ "withArgument" ++ show index
    pure (getArgInfo argument, name, unArg argument)
  case drop selected entries of
    (_, subject, _):_ | selected >= 0 ->
      prepareHelper chargeStep point scope signature (prettyShow $ nameConcrete subject) entries
    _ -> genericError "native-generalization-invalid-subject"

prepareHelper :: (PreparationStep -> TCM ()) -> InteractionId -> ScopeInfo
              -> A.Expr -> String -> [(ArgInfo, Name, A.Expr)] -> TCM A.Expr
prepareHelper chargeStep = prepareHelperUsing (standardClauses chargeStep) chargeStep

standardClauses :: (PreparationStep -> TCM ()) -> InteractionId -> String -> TCM [A.Clause]
standardClauses chargeStep point selected = do
  chargeStep GenerateClauses
  (_, _, clauses) <- withShowAllArguments $ makeCase point noRange selected
  pure clauses

prepareHelperUsing :: (InteractionId -> String -> TCM [A.Clause])
                   -> (PreparationStep -> TCM ()) -> InteractionId -> ScopeInfo
                   -> A.Expr -> String -> [(ArgInfo, Name, A.Expr)] -> TCM A.Expr
prepareHelperUsing generateClauses chargeStep point originalScope signature selected arguments = do
  let patterns = [Arg info $ unnamed $ A.VarP $ A.mkBindName name
                 | (info, name, _) <- arguments]
      operands = [Arg info $ unnamed expression | (info, _, expression) <- arguments]
      scope = setScopeLocals (concatMap patternLocals patterns ++ _scopeLocals originalScope) originalScope
  withFreshName noRange "eliminate" $ \binding -> do
    helper <- qualify <$> currentModule <*> freshName_ "clauses"
    let info = Info.mkDefInfo (nameConcrete binding) empty PublicAccess ConcreteDef noRange
        build cs = A.Let Info.exprNoRange
          (A.LetBind (Info.LetRange noRange) defaultArgInfo (A.mkBindName binding)
            signature (A.ExtendedLam Info.exprNoRange info defaultErased helper cs) :| [])
          (A.app (A.Var binding) operands)
    before <- getTC
    temporary <- registerInteractionPoint False noRange Nothing
    let hole = A.QuestionMark (Info.emptyMetaInfo { Info.metaScope = scope }) temporary
        clause = A.Clause (A.LHS empty $ A.LHSHead helper patterns) []
          (A.RHS hole Nothing) A.noWhereDecls empty
    chargeStep CheckScaffold
    void $ give_ False WithoutForce point Nothing $ build (clause :| [])
    -- Retained drafts are syntax, not a compact display. Hidden patterns must
    -- bind the exact names used by later refinements; otherwise rechecking an
    -- omitted pattern invents fresh identities and leaves spliced terms free.
    generated <- generateClauses temporary selected
    instantiated <- mapM (freshClause originalScope) generated
    restoreAllocations before
    case instantiated of
      [] -> genericError "native-clause-execution-empty-proposal"
      first:rest -> registerDraft $ build (first :| rest)

-- Only allocation high-water marks survive speculative preparation. No
-- helper definition, original-goal assignment or constraint may leak back.
restoreAllocations :: TCState -> TCM ()
restoreAllocations before = do
  allocation <- getTC
  putTC before
  stFreshNameId `setTCLens` (allocation ^. stFreshNameId)
  stFreshInteractionId `setTCLens` (allocation ^. stFreshInteractionId)

-- Keep each native binder's hiding, including nested constructor and record
-- patterns. Only pattern-bound names become splittable in the helper scope.
patternLocals :: NamedArg A.Pattern -> LocalVars
patternLocals argument = case namedArg argument of
  A.VarP name -> local name
  A.AsP _ name pattern -> local name ++ recurse pattern
  A.ConP _ _ patterns -> concatMap patternLocals patterns
  A.DefP _ _ patterns -> concatMap patternLocals patterns
  A.PatternSynP _ _ patterns -> concatMap patternLocals patterns
  A.RecP _ _ fields -> concatMap (foldMap recurse) fields
  A.WithP _ pattern -> recurse pattern
  _ -> []
 where
  local bound = let name = A.unBind bound in
    [(nameConcrete name, LocalVar name (PatternBound $ getHiding argument) [])]
  recurse pattern = patternLocals $ setNamedArg argument pattern

-- Ask Agda to resolve subjects (including hidden and as-bound variables). The
-- resulting identities, not printed type/name comparisons, map to helper args.
subjects :: (PreparationStep -> TCM ()) -> InteractionId -> Intent -> [Name] -> [Name]
         -> TCM (String, [Int])
subjects chargeStep _ (BoundSubjects chosen) originals renamed = do
  chargeStep CheckContext
  mapped <- forM (NE.toList chosen) $ \name -> case elemIndex name originals of
    Nothing -> genericError "native-clause-execution-foreign-binding"
    Just index -> case drop index renamed of
      replacement:_ -> pure (prettyShow $ nameConcrete replacement, index)
      [] -> genericError "native-clause-execution-invalid-subject-index"
  pure (unwords $ map fst mapped, map snd mapped)
subjects _ _ ClosingSubjects{} _ _ = genericError "native-clause-unprepared-closure"
subjects chargeStep point (AdaptiveSubjects chosen) originals renamed =
  subjects chargeStep point (BoundSubjects chosen) originals renamed
subjects chargeStep point (UserAction action) originals renamed
  | command action `elem` ["", "."] = pure (command action, [])
  | otherwise = do
      -- A generalized helper can eliminate module parameters and lambda-bound
      -- variables that make_case cannot split in the original source clause.
      -- Resolve Agda binding identities first; the helper's make_case remains
      -- the authority on admissibility. Missing hidden binders still use Agda's
      -- source-clause exposure operation below.
      chargeStep CheckContext
      direct <- localTCState $ (do
        expressions <- mapM (parseExprIn point noRange) (words $ command action)
        pure $ traverse (\expression -> case deepUnscope expression of
          A.Var name -> elemIndex name originals
          _ -> Nothing) expressions) `catchError` \err -> case err of
            TypeError{} -> pure Nothing
            PatternErr{} -> pure Nothing
            _ -> throwError err
      case direct of
        Just indices -> do
          mapped <- mapM (fmap showName . (`at` renamed)) indices
          pure (unwords mapped, indices)
        Nothing -> originalSubjects
 where
  originalSubjects = do
      interaction <- lookupInteractionPoint point
      chargeStep GenerateClauses
      _ <- makeCase point (ipRange interaction) (command action)
      case ipClause interaction of
        IPNoClause -> genericError "native-clause-execution-no-clause"
        IPClause function _ ty sub clause closure -> do
          chargeStep CheckContext
          (_, context, bindings) <- enterClosure closure $ \_ -> locallyTC eMakeCase (const True) $
            recheckAbstractClause ty sub clause
          indices <- parseVariables function context bindings point (ipRange interaction)
            (words $ command action)
          mapped <- forM indices $ \(index, visibility) ->
            if visibility == C.NotInScope then pure [] else do
              entry <- at index context
              case elemIndex (ctxEntryName entry) originals of
                Nothing -> genericError "native-clause-execution-missing-subject"
                Just i -> do
                  replacement <- at i renamed
                  pure [(showName replacement, i)]
          pure $ case concat mapped of
            [] -> (".", [])
            values -> (unwords $ map fst values, map snd values)
  showName = prettyShow . nameConcrete
  at :: Int -> [a] -> TCM a
  at index values = case drop index values of
    value:_ | index >= 0 -> pure value
    _ -> genericError "native-clause-execution-invalid-subject-index"

freshClause :: ScopeInfo -> A.Clause -> TCM A.Clause
freshClause base clause = do
  let scope = setScopeLocals (concatMap patternLocals (A.spLhsPats $ A.clauseLHS $ lhsToSpine clause)
                             ++ _scopeLocals base) base
  rhs <- traverseExpr (\case
    A.QuestionMark{} -> do
      point <- registerInteractionPoint False noRange Nothing
      pure $ A.QuestionMark (Info.emptyMetaInfo { Info.metaScope = scope }) point
    A.ScopedExpr _ expression -> pure expression
    expression -> pure expression) (A.clauseRHS clause)
  pure clause { A.clauseRHS = rhs }

-- Replay registers the retained native holes; no display parsing or fabricated
-- types are needed. All checking and scope validation still belongs to Agda.
registerDraft :: A.Expr -> TCM A.Expr
registerDraft = traverseExpr $ \case
  expression@(A.QuestionMark info point) -> do
    checkMeta info
    -- Reified types can reference an existing interaction while their meta
    -- presentation carries a different range. The native identity still
    -- denotes that exact obligation. Preserve its original registration;
    -- Agda's registration operation asserts on a second, conflicting range.
    -- Only newly introduced draft holes need registration during replay.
    missing <- isNothing . BiMap.lookup point <$> useTC stInteractionPoints
    when missing $ void $ registerInteractionPoint False (Info.metaRange info) (Just $ interactionId point)
    stFreshInteractionId `modifyTCLens` max (point + 1)
    pure expression
  expression@(A.Underscore info) -> checkMeta info >> pure expression
  expression -> pure expression
 where
  checkMeta :: Info.MetaInfo -> TCM ()
  checkMeta info = case Info.metaNumber info of
    Nothing -> pure ()
    Just meta -> do
      missing <- isNothing <$> lookupMeta meta
      when missing $ genericError "native-draft-stale-metavariable"
