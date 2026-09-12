{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE OverloadedStrings #-}
-- SPDX-License-Identifier: GPL-3.0-or-later
module AgdaProver.Agda28.Clauses (ClauseSnapshot, generate, view) where

import Data.Aeson (Value, object, (.=))
import Data.Maybe (isJust)

import Agda.Interaction.InteractionTop (decorate, extlam_dropName)
import Agda.Interaction.MakeCase (CaseContext, makeCase)
import Agda.Interaction.Options (optUseUnicode)
import Agda.Syntax.Abstract qualified as A
import Agda.Syntax.Abstract.Name (QName, qnameModule, qnameName)
import Agda.Syntax.Abstract.Pretty (prettyAUnqualify)
import Agda.Syntax.Common (InteractionId)
import Agda.Syntax.Common.Pretty (prettyShow)
import Agda.Syntax.Position (Range, getRange, noRange)
import Agda.TypeChecking.Monad

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
