{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE OverloadedStrings #-}
-- SPDX-License-Identifier: GPL-3.0-or-later
module AgdaProver.Symbolic.Classification
  ( Classification (..), unknownClassification, deriveCompetition, constructionFirst ) where

import Control.Monad (unless)
import Data.Aeson
import Data.Aeson.KeyMap qualified as KM
import Data.Set qualified as Set

-- Model-independent scheduling observations, never acceptance certificates.
-- Nothing is unknown, not false. Keep the existing public vocabulary/encoding.
data Classification = Classification
  { recursiveResultMatch :: Maybe Bool, constructionResultMatch :: Maybe Bool
  , constructionAvailable :: Maybe Bool, productiveElimination :: Maybe Bool
  , structuralDescent :: Maybe Bool, higherOrderDescent :: Maybe Bool
  , dependenciesReady :: Maybe Bool, coordinatePermutation :: Maybe Bool
  , reflexiveRelation :: Maybe Bool, relationalElimination :: Maybe Bool
  , constructionEliminationCompete :: Maybe Bool }
  deriving (Eq, Show)

unknownClassification :: Classification
unknownClassification = Classification Nothing Nothing Nothing Nothing Nothing Nothing Nothing Nothing Nothing Nothing Nothing

deriveCompetition :: Classification -> Classification
deriveCompetition facts = facts { constructionEliminationCompete =
  (&&) <$> constructionAvailable facts <*> productiveElimination facts }

-- An ordering preference only. Both continuations must remain on the agenda.
constructionFirst :: Classification -> Bool
constructionFirst facts = constructionAvailable facts == Just True &&
  (productiveElimination facts /= Just True || recursiveResultMatch facts == Just True)

version :: String
version = "agdaprover.structural-classification.v2"

fields :: [(Key, Classification -> Maybe Bool)]
fields =
  [("recursive_result_head_matches_goal", recursiveResultMatch)
  ,("construction_result_head_matches_goal", constructionResultMatch)
  ,("structural_construction_available", constructionAvailable)
  ,("productive_elimination_available", productiveElimination)
  ,("structural_descent_available", structuralDescent)
  ,("higher_order_structural_descent_available", higherOrderDescent)
  ,("dependencies_ready", dependenciesReady)
  ,("homogeneous_coordinate_permutation", coordinatePermutation)
  ,("reflexive_relation_target", reflexiveRelation)
  ,("relational_elimination_available", relationalElimination)
  ,("construction_elimination_compete", constructionEliminationCompete)]

instance ToJSON Classification where
  toJSON facts = object $ ("schema_version" .= version) : [key .= get facts | (key, get) <- fields]

instance FromJSON Classification where
  parseJSON = withObject "structural classification" $ \o -> do
    unless (Set.fromList (KM.keys o) == Set.fromList ("schema_version" : map fst fields)) $
      fail "invalid structural classification fields"
    actual <- o .: "schema_version"
    unless (actual == version) $ fail "unsupported structural classification version"
    Classification <$> o .: "recursive_result_head_matches_goal"
      <*> o .: "construction_result_head_matches_goal" <*> o .: "structural_construction_available"
      <*> o .: "productive_elimination_available" <*> o .: "structural_descent_available"
      <*> o .: "higher_order_structural_descent_available" <*> o .: "dependencies_ready"
      <*> o .: "homogeneous_coordinate_permutation" <*> o .: "reflexive_relation_target"
      <*> o .: "relational_elimination_available" <*> o .: "construction_elimination_compete"
