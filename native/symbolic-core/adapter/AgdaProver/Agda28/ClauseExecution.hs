{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE LambdaCase #-}
-- SPDX-License-Identifier: GPL-3.0-or-later
module AgdaProver.Agda28.ClauseExecution (Intent (..), PreparationStep (..), prepare, registerDraft, patternLocals) where

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
import Agda.Syntax.Position (noRange)
import Agda.Syntax.Scope.Base
import Agda.Syntax.Translation.InternalToAbstract (reify)
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Substitute (telePi)
import Agda.Utils.Null (empty)
import Agda.Utils.Lens ((^.))

import AgdaProver.Symbolic.Clause (ClauseAction, command)

data PreparationStep = GenerateClauses | CheckContext | CheckScaffold

-- Search already has Agda binding identities; round-tripping their base names
-- loses shadowing and disambiguation. User commands deliberately retain Agda's
-- own resolution/exposure behavior. Session seals either intent to its goal.
data Intent = UserAction ClauseAction | BoundSubjects (NonEmpty Name)
  deriving Eq

-- A split is implemented as a local, dependent eliminator, not by mutating an
-- already checked global definition. The helper and its case clauses are native
-- syntax. Ordinary give checks the final draft again from the unsplit parent.
prepare :: (PreparationStep -> TCM ()) -> InteractionId -> Intent -> TCM A.Expr
prepare chargeStep point action = withInteractionId point $ do
  context <- getContext
  target <- getMetaTypeInContext =<< lookupInteractionId point
  telescope <- getContextTelescope
  signature <- inTopContext $ reify $ telePi telescope target
  originalScope <- getScope
  names <- forM (zip [0 :: Int ..] context) $ \(i, _) ->
    freshName_ $ "argument" ++ show i
  selected <- subjects chargeStep point action (map ctxEntryName context) names
  let entries = reverse $ zip context names
      patterns = [Arg (getArgInfo entry) $ unnamed $ A.VarP $ A.mkBindName name
                 | (entry, name) <- entries]
      operands = [Arg (getArgInfo entry) $ unnamed $ A.Var $ ctxEntryName entry
                 | (entry, _) <- entries]
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
    chargeStep GenerateClauses
    -- Retained drafts are syntax, not a compact display. Hidden patterns must
    -- bind the exact names used by later refinements; otherwise rechecking an
    -- omitted pattern invents fresh identities and leaves spliced terms free.
    (_, _, generated) <- withShowAllArguments $ makeCase temporary noRange selected
    instantiated <- mapM (freshClause originalScope) generated
    allocation <- getTC
    putTC before
    -- Only allocation high-water marks survive speculative preparation. No
    -- helper definition, original-goal assignment or constraint may leak back.
    stFreshNameId `setTCLens` (allocation ^. stFreshNameId)
    stFreshInteractionId `setTCLens` (allocation ^. stFreshInteractionId)
    case instantiated of
      [] -> genericError "native-clause-execution-empty-proposal"
      first:rest -> registerDraft $ build (first :| rest)

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
subjects :: (PreparationStep -> TCM ()) -> InteractionId -> Intent -> [Name] -> [Name] -> TCM String
subjects chargeStep _ (BoundSubjects chosen) originals renamed = do
  chargeStep CheckContext
  mapped <- forM (NE.toList chosen) $ \name -> case elemIndex name originals of
    Nothing -> genericError "native-clause-execution-foreign-binding"
    Just index -> case drop index renamed of
      replacement:_ -> pure $ prettyShow $ nameConcrete replacement
      [] -> genericError "native-clause-execution-invalid-subject-index"
  pure $ unwords mapped
subjects chargeStep point (UserAction action) originals renamed
  | command action `elem` ["", "."] = pure $ command action
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
        Just indices -> unwords <$> mapM (fmap showName . (`at` renamed)) indices
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
                Just i -> (:[]) . showName <$> at i renamed
          pure $ case concat mapped of [] -> "."; values -> unwords values
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
    void $ registerInteractionPoint False (Info.metaRange info) (Just $ interactionId point)
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
