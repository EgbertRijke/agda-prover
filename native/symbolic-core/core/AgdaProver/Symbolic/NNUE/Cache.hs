{-# LANGUAGE ImportQualifiedPost #-}
-- SPDX-License-Identifier: GPL-3.0-or-later
module AgdaProver.Symbolic.NNUE.Cache
  ( Cache, CacheMetrics (..), newCache, stateAccumulator, cacheMetrics ) where

import Control.Monad (unless)
import Data.Map.Strict qualified as M
import Data.Text (Text)
import AgdaProver.Symbolic.NNUE.Model
import AgdaProver.Symbolic.NNUE.Sparse
import AgdaProver.Symbolic.NNUE.Score

data CacheMetrics = CacheMetrics
  { cacheHits :: Integer, fullRefreshes :: Integer, incrementalUpdates :: Integer
  , incrementalFeaturesTouched :: Integer, cachedStates :: Int }
  deriving (Eq, Show)

data Cache = Cache
  { owner :: Model, capacity :: Int, clock :: Integer
  , byTokens :: M.Map [Text] (Integer, Accumulator)
  , byAge :: M.Map Integer [Text], previous :: Maybe (Sparse, Accumulator)
  , cacheMetrics :: CacheMetrics }

newCache :: Model -> Int -> Either String Cache
newCache model limit = do
  unless (limit > 0) $ Left "invalid-accumulator-cache-capacity"
  pure $ Cache model limit 0 M.empty M.empty Nothing (CacheMetrics 0 0 0 0 0)

-- Exact feature-token identity only. Eviction affects speed, not search
-- completeness, state validity or accepted proofs. Instances cannot change model.
stateAccumulator :: [Text] -> Cache -> Either String (Accumulator, Cache)
stateAccumulator tokens cache = do
  features <- hashSparse (inputSize $ owner cache) tokens
  let metrics = cacheMetrics cache
      tick = clock cache + 1
  (value, metrics', ages) <- case M.lookup tokens (byTokens cache) of
    Just (age, value) -> pure
      (value, metrics { cacheHits = cacheHits metrics + 1 }, M.delete age $ byAge cache)
    Nothing -> case previous cache of
      Nothing -> do
        value <- accumulator (owner cache) features
        pure (value, metrics { fullRefreshes = fullRefreshes metrics + 1 }, byAge cache)
      Just (oldFeatures, oldAccumulator) -> do
        (remove, add) <- sparseDelta oldFeatures features
        value <- updateAccumulator (owner cache) oldAccumulator (Just remove) (Just add)
        pure (value, metrics
          { incrementalUpdates = incrementalUpdates metrics + 1
          , incrementalFeaturesTouched = incrementalFeaturesTouched metrics
              + fromIntegral (length (entries remove) + length (entries add)) }, byAge cache)
  let table = M.insert tokens (tick, value) (byTokens cache)
      ages' = M.insert tick tokens ages
      (table', ages'') = if M.size table <= capacity cache then (table, ages')
        else case M.minViewWithKey ages' of
          Just ((_, oldest), rest) -> (M.delete oldest table, rest)
          Nothing -> (table, ages')
  pure (value, cache { clock = tick, byTokens = table', byAge = ages''
    , previous = Just (features, value), cacheMetrics = metrics' { cachedStates = M.size table' } })
