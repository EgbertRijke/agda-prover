{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE OverloadedStrings #-}
-- SPDX-License-Identifier: GPL-3.0-or-later
module AgdaProver.Symbolic.Evidence
  ( SearchLimits (..), SearchStats (..), emptyStats, SearchStatus (..), statusName
  , IterationDepth, initialDepth, retryDepth, iterationDepth ) where

import Control.Monad (unless)
import Data.Aeson
import Data.Aeson.KeyMap qualified as KM
import Data.Set qualified as S

-- Caller-supplied work allowance, not a hard proof-size/depth bound. Nothing
-- means supervised/cancellable search without a work-unit cap. Depth widens.
newtype SearchLimits = SearchLimits { workUnitLimit :: Maybe Integer } deriving (Eq, Show)
instance FromJSON SearchLimits where
  parseJSON = withObject "evidence search limits" $ \o -> do
    unless (S.fromList (KM.keys o) == S.fromList ["work_units"]) $ fail "invalid search limits"
    limit <- o .: "work_units"
    unless (maybe True (> 0) limit) $ fail "work allowance must be positive or null"
    pure $ SearchLimits limit

data SearchStatus = FoundCandidate | FragmentExhausted | WorkExhausted deriving (Eq, Show)
statusName :: SearchStatus -> String
statusName FoundCandidate = "candidate"
statusName FragmentExhausted = "unsolved"
statusName WorkExhausted = "resource-exhausted"

-- A restarting iteration bound, not a proof or cached substitution. The
-- unfinished iteration must run again; only earlier completed iterations are
-- omitted. The agenda retains this value with its immutable parent and goal.
newtype IterationDepth = IterationDepth Int deriving (Eq, Show)

initialDepth :: IterationDepth
initialDepth = IterationDepth 0

iterationDepth :: IterationDepth -> Int
iterationDepth (IterationDepth depth) = depth

retryDepth :: SearchStats -> IterationDepth
retryDepth stats
  | workExhausted stats = IterationDepth $ max 0 $ currentDepth stats
  | otherwise = initialDepth

data SearchStats = SearchStats
  { workUnits :: !Integer, checkerQueries :: !Integer, inferenceQueries :: !Integer
  , rejectedQueries :: !Integer, blockedQueries :: !Integer
  , lambdaProposals :: !Integer, applicationProposals :: !Integer, applicationGenerationSteps :: !Integer
  , recordProposals :: !Integer, absurdProposals :: !Integer
  , recursiveContextQueries :: !Integer, recursiveProposals :: !Integer, recursiveValidationQueries :: !Integer
  , copatternProposals :: !Integer
  , classificationQueries :: !Integer
  , focusedObservationQueries :: !Integer, focusedActions :: !Integer
  , focusedNodes :: !Integer, focusedCacheHits :: !Integer, focusedCycles :: !Integer
  , focusedCandidates :: !Integer
  , algebraObservationQueries :: !Integer, algebraActions :: !Integer, algebraCandidates :: !Integer
  , recordObservationQueries :: !Integer, projectedSeeds :: !Integer
  , helperInferenceQueries :: !Integer, helperClauseQueries :: !Integer, helperProposals :: !Integer
  , searchNodes :: !Integer, depthIterations :: !Integer, currentDepth :: !Int
  , modelItems :: !Integer, modelNanoseconds :: !Integer, policyDecisions :: !Integer
  , workExhausted :: !Bool }
  deriving (Eq, Show)
emptyStats :: SearchStats
emptyStats = SearchStats
  { workUnits = 0, checkerQueries = 0, inferenceQueries = 0
  , rejectedQueries = 0, blockedQueries = 0
  , lambdaProposals = 0, applicationProposals = 0, applicationGenerationSteps = 0
  , recordProposals = 0, absurdProposals = 0
  , recursiveContextQueries = 0, recursiveProposals = 0, recursiveValidationQueries = 0
  , copatternProposals = 0
  , classificationQueries = 0
  , focusedObservationQueries = 0, focusedActions = 0
  , focusedNodes = 0, focusedCacheHits = 0, focusedCycles = 0, focusedCandidates = 0
  , algebraObservationQueries = 0, algebraActions = 0, algebraCandidates = 0
  , recordObservationQueries = 0, projectedSeeds = 0
  , helperInferenceQueries = 0, helperClauseQueries = 0, helperProposals = 0
  , searchNodes = 0, depthIterations = 0, currentDepth = 0
  , modelItems = 0, modelNanoseconds = 0, policyDecisions = 0
  , workExhausted = False }
instance ToJSON SearchStats where
  toJSON s = object
    ["schema_version" .= ("agdaprover.symbolic-evidence-cost.v2" :: String)
    ,"work_units" .= workUnits s, "checker_queries" .= checkerQueries s
    ,"inference_queries" .= inferenceQueries s, "rejected_queries" .= rejectedQueries s
    ,"blocked_queries" .= blockedQueries s, "lambda_proposals" .= lambdaProposals s
    ,"application_proposals" .= applicationProposals s, "nodes" .= searchNodes s
    ,"application_generation_steps" .= applicationGenerationSteps s
    ,"record_proposals" .= recordProposals s, "absurd_proposals" .= absurdProposals s
    ,"recursive_context_queries" .= recursiveContextQueries s
    ,"recursive_proposals" .= recursiveProposals s
    ,"recursive_validation_queries" .= recursiveValidationQueries s
    ,"copattern_proposals" .= copatternProposals s
    ,"classification_queries" .= classificationQueries s
    ,"focused_observation_queries" .= focusedObservationQueries s
    ,"focused_actions" .= focusedActions s, "focused_nodes" .= focusedNodes s
    ,"focused_cache_hits" .= focusedCacheHits s, "focused_cycles" .= focusedCycles s
    ,"focused_candidates" .= focusedCandidates s
    ,"algebra_observation_queries" .= algebraObservationQueries s
    ,"algebra_actions" .= algebraActions s, "algebra_candidates" .= algebraCandidates s
    ,"record_observation_queries" .= recordObservationQueries s
    ,"projected_seeds" .= projectedSeeds s
    ,"helper_inference_queries" .= helperInferenceQueries s
    ,"helper_clause_queries" .= helperClauseQueries s, "helper_proposals" .= helperProposals s
    ,"depth_iterations" .= depthIterations s, "current_depth" .= currentDepth s
    ,"model_items_scored" .= modelItems s, "model_elapsed_ns" .= modelNanoseconds s
    ,"policy_decisions" .= policyDecisions s, "work_exhausted" .= workExhausted s]
