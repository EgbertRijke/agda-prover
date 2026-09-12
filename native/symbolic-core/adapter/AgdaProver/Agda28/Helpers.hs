{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE OverloadedStrings #-}
-- SPDX-License-Identifier: GPL-3.0-or-later
module AgdaProver.Agda28.Helpers (Snapshot, infer, signature, view) where

import Data.Aeson (Value, object, (.=))
import Agda.Interaction.BasicOps (metaHelperType)
import Agda.Interaction.Base (OutputConstraint' (OfType'))
import Agda.Syntax.Abstract qualified as A
import Agda.Syntax.Abstract.Pretty (prettyATop)
import Agda.Syntax.Common (InteractionId)
import Agda.Syntax.Common.Pretty (prettyShow)
import Agda.Syntax.Position (noRange)
import Agda.TypeChecking.Monad
import AgdaProver.Agda28.Observation (rewrite)
import AgdaProver.Symbolic.Protocol (ObservationMode, modeName)
import AgdaProver.Symbolic.SessionTypes (DraftExpression (..))

-- Agda owns abstraction over compound arguments, section parameters, hiding
-- and dependent telescope order. Keep its abstract syntax, not a parsed display
-- of that telescope. The session brands the snapshot and retains its TCState.
data Snapshot = Snapshot ObservationMode A.Expr String

signature :: Snapshot -> A.Expr
signature (Snapshot _ expression _) = expression

infer :: InteractionId -> ObservationMode -> DraftExpression -> TCM Snapshot
infer point mode (DraftExpression source) = do
  result <- withInteractionId point $ inTopContext $
    metaHelperType (rewrite mode) point noRange source
  case result of
    OfType' _ expression -> Snapshot mode expression . prettyShow <$> inTopContext (prettyATop result)

view :: Snapshot -> Value
view (Snapshot mode _ display) = object
  ["schema_version" .= ("agdaprover.symbolic-helper.v1" :: String)
  ,"status" .= ("proposed" :: String), "mode" .= modeName mode
  ,"signature" .= display, "applied" .= False, "proof_authority" .= False]
