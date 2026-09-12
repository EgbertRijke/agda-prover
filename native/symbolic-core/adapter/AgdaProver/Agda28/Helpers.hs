{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE OverloadedStrings #-}
-- SPDX-License-Identifier: GPL-3.0-or-later
module AgdaProver.Agda28.Helpers (Snapshot, infer, signature, view, abstractOperands) where

import Control.Monad (forM)
import Data.Aeson (Value, object, (.=))
import Data.List.NonEmpty (NonEmpty)
import Data.List.NonEmpty qualified as NE
import Agda.Interaction.BasicOps (metaHelperType)
import Agda.Interaction.Base (OutputConstraint' (OfType'))
import Agda.Syntax.Abstract qualified as A
import Agda.Syntax.Abstract.Pretty (prettyATop)
import Agda.Syntax.Common
import Agda.Syntax.Common.Pretty (prettyShow)
import Agda.Syntax.Internal qualified as I
import Agda.Syntax.Position (noRange)
import Agda.Syntax.Translation.InternalToAbstract (reify)
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Rules.Term (inferExpr)
import Agda.TypeChecking.With (splitTelForWith, withFunctionType)
import Agda.Utils.Null (empty)
import Agda.Utils.Permutation (permute)
import Agda.Utils.Size (size)
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

-- The same with-abstraction operation used by Agda's helper command, with
-- native operands rather than a generated string. Keep the complete context
-- telescope and its permutation: no display cleanup or binder guessing is
-- needed for an internal helper. All operands are ordinary with-expressions,
-- not a special identity/rewrite operation.
abstractOperands :: TCM () -> InteractionId -> NonEmpty A.Expr
                 -> TCM (I.Type, [Arg A.Expr], Int)
abstractOperands charge point expressions = withInteractionId point $ do
  telescope <- getContextTelescope
  target <- getMetaTypeInContext =<< lookupInteractionId point
  typed <- forM expressions $ \expression -> do
    charge
    (value, ty) <- inferExpr expression
    pure $ defaultArg (value, I.OtherType ty)
  let (before, after, permutation, result, operands) = splitTelForWith telescope target typed
  charge
  (signatureType, _) <- inTopContext $ withFunctionType before operands after result empty
  context <- permute permutation <$> getContextArgs
  arguments <- forM context $ \argument -> charge >> traverse reify argument
  let (prefix, suffix) = splitAt (size before) arguments
  pure (signatureType, prefix ++ map defaultArg (NE.toList expressions) ++ suffix,
    length prefix + length expressions - 1)

view :: Snapshot -> Value
view (Snapshot mode _ display) = object
  ["schema_version" .= ("agdaprover.symbolic-helper.v1" :: String)
  ,"status" .= ("proposed" :: String), "mode" .= modeName mode
  ,"signature" .= display, "applied" .= False, "proof_authority" .= False]
