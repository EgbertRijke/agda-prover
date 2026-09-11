{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE OverloadedStrings #-}
-- SPDX-License-Identifier: GPL-3.0-or-later
module AgdaProver.Symbolic.NNUE.Policy
  ( Models, models, RankingDomain (..), RankingMode (..), Candidate (..)
  , RankedBatch (..), DecisionTrace, traceView, rankBatch ) where

import Control.Monad (unless)
import Data.Aeson (Value, object, (.=))
import Data.List (sort, sortOn)
import Data.Map.Strict qualified as M
import Data.Set qualified as S
import Data.Text (Text)
import Data.Text qualified as T
import GHC.Clock (getMonotonicTimeNSec)
import AgdaProver.Symbolic.NNUE.Model
import AgdaProver.Symbolic.NNUE.Native
import AgdaProver.Symbolic.NNUE.Score
import AgdaProver.Symbolic.NNUE.Sparse

newtype Models = Models (M.Map ModelRole Model)
models :: [Model] -> Either String Models
models values = do
  unless (S.size (S.fromList $ map modelRole values) == length values) $ Left "duplicate-model-role"
  pure $ Models $ M.fromList [(modelRole model, model) | model <- values]

data RankingDomain = ProofTerms | Refinements | FocusedBranches | ORFamily Text deriving (Eq, Show)
data RankingMode = Symbolic | Learned deriving (Eq, Show)
data Candidate a = Candidate
  { candidateId :: Text, expressionView :: Text, priorityTier :: Int
  , actionTokens :: Either String [Text], candidateValue :: a }
data RankedBatch a = RankedBatch { rankedCandidates :: [Candidate a], decisionTrace :: DecisionTrace }

-- A trace records ordering, not successful proof steps. There is deliberately
-- no native API to assign proof credit: the application must first freshly
-- validate the reconstructed selected proof, then bind these IDs to that
-- result using the existing validated-policy-proof contract.
data DecisionTrace = DecisionTrace
  { decisionName :: Text, domain :: RankingDomain, selectedModel :: Maybe Model
  , fallbackReason :: Maybe String, symbolicOrder :: [Text], rankedOrder :: [Text]
  , priorities :: [Int], scoring :: Maybe ScoredBatch, rankingElapsedNanoseconds :: Integer }

roleFor :: RankingDomain -> ModelRole
roleFor ProofTerms = ProofTerm
roleFor Refinements = OneStep
roleFor FocusedBranches = FocusedBranch
roleFor (ORFamily _) = ORDecision
familyName :: RankingDomain -> Text
familyName ProofTerms = "proof-term-v2"
familyName Refinements = "one-step-refinement-v2"
familyName FocusedBranches = "focused-hypothesis"
familyName (ORFamily family) = family

-- Rank a complete, already-generated OR batch. Structural tiers are supplied
-- in symbolic order. Opt-out, absent/unsupported weights and scoring failures
-- preserve that exact order. Invalid batches are caller errors, never pruning.
rankBatch :: Maybe (NativeScorer s) -> Models -> RankingMode -> RankingDomain -> Text
          -> Either String [Text] -> [Candidate a] -> IO (Either String (RankedBatch a))
rankBatch native (Models table) mode requested decision state candidates = do
  let keys = map candidateId candidates
      tiers = map priorityTier candidates
      expressions = map expressionView candidates
      valid = do
        unless (not $ T.null decision) $ Left "empty-decision-id"
        unless (all (not . T.null) keys && S.size (S.fromList keys) == length keys
                && S.size (S.fromList expressions) == length expressions) $ Left "duplicate-or-empty-candidate"
        unless (all (>= 0) tiers && sort tiers == tiers) $ Left "invalid-structural-tiers"
      model = M.lookup (roleFor requested) table
      usable = case requested of
        ORFamily family -> maybe True (`supportsFamily` T.unpack family) model
        _ -> True
      trace reason chosen score order = DecisionTrace decision requested chosen reason keys order tiers score 0
      fallback reason chosen = Right $ RankedBatch candidates (trace reason chosen Nothing keys)
  case valid of
    Left reason -> pure $ Left reason
    Right () | length candidates <= 1 -> pure $ fallback (Just "deterministic") Nothing
    Right () | mode == Symbolic -> pure $ fallback (Just "symbolic-opt-out") Nothing
    Right () | not usable -> pure $ fallback (Just "unsupported-decision-family") model
    Right () -> case model of
      Nothing -> pure $ fallback (Just "model-unavailable") Nothing
      Just chosen -> do
        started <- getMonotonicTimeNSec
        let prepared = do
              tokens <- state
              initial <- hashSparse (inputSize chosen) tokens >>= accumulator chosen
              actions <- traverse (actionTokens >=> hashSparse (inputSize chosen)) candidates
              pure (initial, actions)
        result <- case prepared of
          Left reason -> pure $ fallback (Just $ "feature-error:" ++ reason) model
          Right (initial, actions) -> do
            scored <- scoreBatch native chosen initial actions
            pure $ case scored of
              Left reason -> fallback (Just $ "scoring-error:" ++ reason) model
              Right batch ->
                let ordered = map (\(_, _, candidate) -> candidate) $ sortOn
                      (\(index, value, candidate) -> (priorityTier candidate, -value, index))
                      (zip3 [0 :: Int ..] (batchScores batch) candidates)
                in Right $ RankedBatch ordered $ trace Nothing model (Just batch) (map candidateId ordered)
        finished <- getMonotonicTimeNSec
        pure $ fmap (\batch -> batch { decisionTrace = (decisionTrace batch)
          { rankingElapsedNanoseconds = toInteger $ finished - started } }) result
 where (>=>) f g x = f x >>= g

traceView :: DecisionTrace -> Value
traceView trace = object
  [ "schema_version" .= ("agdaprover.symbolic-policy-decision.v1" :: String)
  , "decision_id" .= decisionName trace, "role" .= roleName (roleFor $ domain trace)
  , "family" .= familyName (domain trace)
  , "model_id" .= fmap modelId (selectedModel trace)
  , "model_seed" .= fmap modelSeed (selectedModel trace)
  , "feature_family" .= featureFamily (roleFor $ domain trace)
  , "fallback_reason" .= fallbackReason trace
  , "symbolic_order" .= symbolicOrder trace, "model_order" .= rankedOrder trace
  , "priority_tiers" .= priorities trace
  , "scores_in_symbolic_order" .= maybe [] batchScores (scoring trace)
  , "backend" .= fmap scoringBackend (scoring trace)
  , "native_fallback" .= (scoring trace >>= nativeFallback)
  , "model_items_scored" .= maybe 0 itemsScored (scoring trace)
  , "model_elapsed_ns" .= rankingElapsedNanoseconds trace
  , "scoring_elapsed_ns" .= maybe 0 scoringNanoseconds (scoring trace)
  , "validated_proof" .= False ]
