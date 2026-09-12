{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE LambdaCase #-}
-- SPDX-License-Identifier: GPL-3.0-or-later
module AgdaProver.Agda28.Construction
  ( recordPlan, recordExpression, projectedEvidence, omittedField, absurdLambda, eliminateEmpty ) where

import Data.List.NonEmpty (NonEmpty (..))
import Data.Set qualified as Set

import Agda.Syntax.Abstract qualified as A
import Agda.Syntax.Abstract.Name (QName)
import Agda.Syntax.Common
import Agda.Syntax.Concrete (FieldAssignment' (..))
import Agda.Syntax.Concrete.Name qualified as C
import Agda.Syntax.Info (LetInfo (..), exprNoRange)
import Agda.Syntax.Info qualified as Info
import Agda.Syntax.Internal qualified as I
import Agda.Syntax.Position (noRange)
import Agda.Syntax.Translation.InternalToAbstract (reify)
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Records (isRecordType, recordFieldNames)
import Agda.TypeChecking.Substitute (apply)
import Agda.Utils.Null (empty)

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
