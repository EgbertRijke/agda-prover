{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
-- SPDX-License-Identifier: GPL-3.0-or-later
module AgdaProver.Agda28.Source (Snapshot, render, view) where

import Control.Monad (forM, unless)
import Data.Aeson (Value, object, (.=))
import Data.Map.Strict qualified as Map
import Data.Maybe (isNothing)
import Data.Set qualified as Set

import Agda.Interaction.MakeCase (makeCase, recheckAbstractClause)
import Agda.Syntax.Abstract qualified as A
import Agda.Syntax.Abstract.Name (qnameModule)
import Agda.Syntax.Abstract.Pattern (lhsToSpine)
import Agda.Syntax.Abstract.Pretty (prettyAUnqualify)
import Agda.Syntax.Abstract.Views (deepUnscope, foldExpr, mapExpr)
import Agda.Syntax.Common (InteractionId)
import Agda.Syntax.Common.Pretty (prettyShow)
import Agda.Syntax.Internal qualified as I
import Agda.Syntax.Position (Range, getRange, fuseRange)
import Agda.Syntax.Scope.Base
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Pretty (prettyTCM)

import Structure qualified as S

-- Presentation of a checked native draft, never proof authority. The caller
-- pins original source and validates any resulting edit independently.
data Snapshot = Expression Range String | Clause Range Range String

render :: TCM () -> InteractionId -> A.Expr -> TCM Snapshot
render charge point expression = withInteractionId point $ do
  interaction <- lookupInteractionPoint point
  context <- getContext
  scope <- getScope
  let referenced = foldExpr (\case A.Var name -> Set.singleton name; _ -> Set.empty) expression
      visible = Set.fromList $ map snd $ notShadowedLocals $ _scopeLocals scope
      missing = [(index, ctxEntryName entry) | (index, entry) <- zip [0..] context,
        Set.member (ctxEntryName entry) referenced,
        not $ Set.member (ctxEntryName entry) visible]
  if null missing then Expression (ipRange interaction) <$> (prettyShow <$> prettyTCM expression)
  else case ipClause interaction of
    IPNoClause -> genericError "native-source-hidden-binder-without-clause"
    IPClause _ _ ty sub original closure -> do
      -- Do not replace surrounding record fields, local lambdas or sibling
      -- goals with a generated clause. Direct term edits still work
      -- in those contexts; wider authorized edits belong to format integration.
      case A.clauseRHS original of
        A.RHS rhs _ | A.QuestionMark _ p <- deepUnscope rhs, p == point -> pure ()
        _ -> genericError "native-source-exposure-requires-whole-clause-hole"
      names <- forM missing $ \(index, _) -> prettyShow <$> prettyTCM (I.var index)
      charge
      (name, variant, generated) <- makeCase point (ipRange interaction) (unwords names)
      unless (isNothing variant) $
        genericError "native-source-exposure-extended-lambda-needs-source-context"
      clause <- case generated of
        [single] -> pure single
        _ -> genericError "native-source-exposure-changed-branch-count"
      -- Agda reifies a fresh LHS telescope when exposing omitted binders. Its
      -- binding identities, not coincidentally equal spellings, must also bind
      -- the retained RHS. No elimination was requested, so order is unchanged.
      charge
      (_, renamed, _) <- enterClosure closure $ \_ -> locallyTC eMakeCase (const True) $
        recheckAbstractClause ty sub (lhsToSpine clause)
      unless (length context == length renamed) $
        genericError "native-source-exposure-context-mismatch"
      let renaming = Map.fromList $ zip (map ctxEntryName context) (map ctxEntryName renamed)
          rhs = mapExpr (\case
            A.Var old -> A.Var $ Map.findWithDefault old old renaming
            A.ScopedExpr _ inner -> inner
            e -> e) expression
          -- The source keeps its original where block, including comments and
          -- scopes. Only the LHS and selected RHS are rendered/replaced.
          completed = clause { A.clauseRHS = A.RHS rhs Nothing,
            A.clauseWhereDecls = A.noWhereDecls }
      telescope <- lookupSection $ qnameModule name
      printed <- inTopContext $ addContext telescope $ prettyAUnqualify completed
      pure $ Clause (fuseRange (getRange $ A.clauseLHS original) $ ipRange interaction)
        (ipRange interaction) $ prettyShow printed

view :: Snapshot -> Value
view snapshot = object $
  ["schema_version" .= ("agdaprover.symbolic-source.v1" :: String),
   "proof_authority" .= False] ++ case snapshot of
    Expression goal body -> ["kind" .= ("expression" :: String),
      "goal_range" .= S.spanOf goal, "body" .= body]
    Clause clause goal body -> ["kind" .= ("clause" :: String),
      "source_range" .= S.spanOf clause, "goal_range" .= S.spanOf goal, "body" .= body]
