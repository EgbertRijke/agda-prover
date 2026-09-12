{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
-- SPDX-License-Identifier: GPL-3.0-or-later
module AgdaProver.Agda28.Clauses (ClauseSnapshot, generate, extendHelper, view) where

import Control.Monad (forM, unless)
import Control.Monad.Except (catchError, throwError)
import Data.Aeson (Value, object, (.=))
import Data.Maybe (isJust, mapMaybe)

import Agda.Interaction.InteractionTop (decorate, extlam_dropName)
import Agda.Interaction.MakeCase (CaseContext, makeCase, getClauseZipperForIP,
  recheckAbstractClause, parseVariables, makeAbstractClause, makeAbsurdClause)
import Agda.Interaction.Options (optUseUnicode)
import Agda.Syntax.Abstract qualified as A
import Agda.Syntax.Abstract.Name (QName, qnameModule, qnameName)
import Agda.Syntax.Abstract.Pretty (prettyAUnqualify)
import Agda.Syntax.Common (InteractionId)
import Agda.Syntax.Common.Pretty (prettyShow)
import Agda.Syntax.Concrete qualified as C
import Agda.Syntax.Internal qualified as I
import Agda.Syntax.Position (Range, getRange, noRange)
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Coverage (SplitClause, scSubst, clauseToSplitClause,
  splitClauseWithAbsurd, splitClauses)
import Agda.TypeChecking.Coverage.Match (applySplitPSubst)
import Agda.Utils.Lens ((^.))

import AgdaProver.Symbolic.Clause (ClauseAction, command)
import Structure qualified as S

-- The original source clause and Agda's generated clauses stay native. The
-- owner retains the generation TCState with this snapshot, not a text-derived
-- substitute. Rendering is a view for reconstruction/conformance, not checking.
data ClauseSnapshot = ClauseSnapshot ClauseAction QName CaseContext [A.Clause]
  [String] Range Range

generate :: InteractionId -> ClauseAction -> TCM ClauseSnapshot
generate point action = do
  interaction <- lookupInteractionPoint point
  let goalRange = ipRange interaction
      sourceRange = case ipClause interaction of
        IPClause { ipcClause = clause } -> getRange clause
        IPNoClause -> noRange
  (name, context, clauses) <- makeCase point goalRange (command action)
  -- Use the very same renderer/context as Cmd_make_case, including extended
  -- lambdas and the user's glyph preference. No local syntax surgery.
  rendered <- withInteractionId point $ do
    telescope <- lookupSection $ qnameModule name
    unicode <- optUseUnicode <$> pragmaOptions
    docs <- inTopContext $ addContext telescope $ mapM prettyAUnqualify clauses
    pure $ map (extlam_dropName unicode context . decorate) docs
  pure $ ClauseSnapshot action name context clauses rendered sourceRange goalRange

-- Adaptive search operates on a fresh local helper, not on an existing user's
-- clause group. Retain Agda's telescope, patterns, target and substitutions
-- while extending its split tree. No earlier helper is rebuilt after a split.
-- The caller still checks the assembled helper from its original parent.
extendHelper :: TCM () -> TCM () -> InteractionId -> String -> TCM [A.Clause]
extendHelper chargeContext chargeSplit point selected = withInteractionId point $
  locallyTC eMakeCase (const True) $ withShowAllArguments $ do
    interaction <- lookupInteractionPoint point
    case ipClause interaction of
      IPNoClause -> genericError "native-clause-extension-without-helper"
      IPClause name number ty sub abstract closure -> do
        (_, (previous, _, following)) <- getClauseZipperForIP name number
        unless (null previous && null following) $
          genericError "native-clause-extension-requires-fresh-helper"
        chargeContext
        (clause, context, aliases) <- enterClosure closure $ \_ ->
          locallyTC eMakeCase (const True) $ recheckAbstractClause ty sub abstract
        variables <- parseVariables name context aliases point noRange (words selected)
        unless (all ((== C.InScope) . snd) variables) $
          genericError "native-clause-extension-requires-bound-subjects"
        (progress, leaves) <- grow (clauseToSplitClause clause) (map fst variables) []
        unless progress $ genericError "native-clause-no-admissible-subject"
        forM leaves $ \case
          OpenLeaf leaf -> makeAbstractClause name (A.clauseRHS abstract) (I.clauseEllipsis clause) leaf
          AbsurdLeaf leaf -> makeAbsurdClause name (I.clauseEllipsis clause) leaf
 where
  -- Retrying an inadmissible subject is justified only by a successful split.
  -- Agda's substitution maps both waiting and deferred indices into each new
  -- telescope; a subject already forced to a nonvariable is no longer split.
  grow clause [] _ = pure (False, [OpenLeaf clause])
  grow clause (subject:rest) deferred = attempt clause subject >>= \case
    Nothing -> grow clause rest (subject:deferred)
    Just (Left absurd) -> pure (True, [AbsurdLeaf absurd])
    Just (Right covering) -> do
      children <- forM (splitClauses covering) $ \child ->
        grow child (mapMaybe (remaining child) $ reverse deferred ++ rest) []
      pure (True, concatMap snd children)
  remaining clause index = case applySplitPSubst (scSubst clause) (I.var index) of
    I.Var next [] -> Just next
    _ -> Nothing
  attempt clause subject = do
    before <- getTC
    chargeSplit
    let restore = do
          after <- getTC
          putTC before
          stFreshNameId `setTCLens` (after ^. stFreshNameId)
          stFreshInteractionId `setTCLens` (after ^. stFreshInteractionId)
    (dontAssignMetas (splitClauseWithAbsurd clause subject) >>= \case
      Left _ -> restore >> pure Nothing
      Right result -> pure $ Just result) `catchError` \err -> case err of
        TypeError{} -> restore >> pure Nothing
        PatternErr{} -> restore >> pure Nothing
        _ -> throwError err

data Leaf = OpenLeaf SplitClause | AbsurdLeaf SplitClause

view :: ClauseSnapshot -> Value
view (ClauseSnapshot action name context clauses rendered sourceRange goalRange) = object
  ["schema_version" .= ("agdaprover.symbolic-clauses.v1" :: String)
  ,"status" .= ("proposed" :: String), "action" .= action
  ,"variant" .= (if isJust context then "ExtendedLambda" else "Function" :: String)
  ,"function" .= object ["id" .= S.nameKey (qnameName name),
      "module" .= S.moduleView (qnameModule name), "display" .= prettyShow name]
  ,"clause_count" .= length clauses, "clauses" .= rendered
  ,"source_range" .= S.spanOf sourceRange, "goal_range" .= S.spanOf goalRange
  ,"applied" .= False, "proof_authority" .= False]
