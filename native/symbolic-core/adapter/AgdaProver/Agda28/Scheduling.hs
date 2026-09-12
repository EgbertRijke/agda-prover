{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE LambdaCase #-}
-- SPDX-License-Identifier: GPL-3.0-or-later
module AgdaProver.Agda28.Scheduling (classify) where

import Control.Monad (forM)
import Data.Set qualified as Set
import Agda.Syntax.Abstract.Name (QName)
import Agda.Syntax.Common
import Agda.Syntax.Internal qualified as I
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Records (isRecordType)
import Agda.TypeChecking.Reduce (reduce, reduceB)
import AgdaProver.Agda28.Recursion qualified as Recursion
import AgdaProver.Symbolic.Classification

data Head = Global QName | Local Int deriving (Eq)

-- Compare result *heads*, not types. Enter native abstractions so outer locals
-- keep their identity; a result depending on a new binder remains unknown.
resultHead :: Int -> I.Type -> TCM (Maybe Head)
resultHead extra ty = reduceB ty >>= \case
  I.Blocked{} -> pure Nothing
  I.NotBlocked _ value -> case value of
    I.El _ (I.Pi domain body) -> underAbstraction domain body $ resultHead
      (extra + case body of I.Abs{} -> 1; I.NoAbs{} -> 0)
    I.El _ (I.Def name _) -> pure $ Just $ Global name
    I.El _ (I.Var index _) | index >= extra -> pure $ Just $ Local (index-extra)
    _ -> pure Nothing

goalHead :: I.Type -> TCM (Maybe Head)
goalHead target = reduce target >>= \case
  I.El _ I.Pi{} -> pure Nothing
  value -> resultHead 0 value

-- This metadata query is read-only and does not instantiate user metas. It is
-- deliberately conservative: unavailable classification is not unavailability
-- of an action. Remaining relational/dependency facts belong to later slices.
classify :: Set.Set QName -> Set.Set QName -> Maybe Recursion.CallContext -> I.Type -> TCM Classification
classify forbidden constructors recursion target = localTCState $ dontAssignMetas $ do
  shape <- reduce target
  headOfGoal <- goalHead shape
  record <- isRecordType shape
  construction <- case (shape, record) of
    (_, Just (_, _, definition)) -> pure $ Just $
      _recInduction definition /= Just CoInductive &&
      not (Set.member (I.conName $ _recConHead definition) forbidden)
    (I.El _ I.Pi{}, _) -> pure $ Just True
    (I.El _ (I.Def name _), _) -> getConstInfo name >>= \definition -> case theDef definition of
      Datatype { dataCons = names } -> pure $ Just $ any (`Set.member` constructors) names
      _ -> pure Nothing
    (I.El _ I.Sort{}, _) -> pure $ Just False
    _ -> pure Nothing
  context <- getContext
  locals <- forM (zip [0..] context) $ \(index, _) -> do
    ty <- typeOfBV index
    reduce ty >>= \case
      I.El _ I.Pi{} -> resultHead 0 ty
      _ -> pure Nothing
  recursiveHead <- case recursion of
    Nothing -> pure Nothing
    Just call -> resultHead 0 =<< Recursion.callType call
  (descent, higher) <- maybe (pure (Nothing, Nothing)) Recursion.descentFacts recursion
  let matches left right = (==) <$> left <*> right
      elimination = if any ((== Just True) . matches headOfGoal) locals then Just True else Nothing
  pure $ deriveCompetition unknownClassification
    { recursiveResultMatch = matches recursiveHead headOfGoal
    , constructionResultMatch = case construction of Just True -> Just True; _ -> Nothing
    , constructionAvailable = construction, productiveElimination = elimination
    , structuralDescent = descent, higherOrderDescent = higher }
