{-# LANGUAGE ImportQualifiedPost #-}
-- SPDX-License-Identifier: GPL-3.0-or-later
module AgdaProver.Symbolic.NNUE.Score
  ( Accumulator, accumulator, restoreAccumulator, accumulatorValues
  , updateAccumulator, scoreAccumulator, referenceBatch ) where

import Control.Monad (forM_, unless)
import Control.Monad.ST (runST)
import Data.Vector.Storable qualified as V
import Data.Vector.Storable.Mutable qualified as MV
import AgdaProver.Symbolic.NNUE.Model
import AgdaProver.Symbolic.NNUE.Sparse

-- Model identity prevents accidental accumulator reuse across weight updates.
-- This cache is numerical only, never proof-state equality or proof evidence.
data Accumulator = Accumulator String (V.Vector Double)

accumulatorValues :: Accumulator -> V.Vector Double
accumulatorValues (Accumulator _ values) = values

restoreAccumulator :: Model -> V.Vector Double -> Either String Accumulator
restoreAccumulator model values = do
  unless (V.length values == hiddenSize model && V.all finite values) $
    Left "invalid-accumulator"
  pure $ Accumulator (modelId model) values

finite :: Double -> Bool
finite x = not (isNaN x || isInfinite x)

accumulator :: Model -> Sparse -> Either String Accumulator
accumulator model features = do
  initial <- restoreAccumulator model (V.map realToFrac $ hiddenBias model)
  updateAccumulator model initial Nothing (Just features)

updateAccumulator :: Model -> Accumulator -> Maybe Sparse -> Maybe Sparse
                  -> Either String Accumulator
updateAccumulator model (Accumulator identity original) remove add = do
  unless (identity == modelId model) $ Left "accumulator-model-mismatch"
  let steps = [(features, direction) | (Just features, direction) <- [(remove, -1), (add, 1)]]
  unless (all ((== inputSize model) . dimension . fst) steps) $ Left "feature-dimension-mismatch"
  let result = runST $ do
        values <- V.thaw original
        forM_ steps $ \(features, direction) ->
          forM_ (entries features) $ \(index, value) ->
            forM_ [0 .. hiddenSize model - 1] $ \hidden -> do
              old <- MV.read values hidden
              let weight = realToFrac $ embeddings model V.! (index * hiddenSize model + hidden)
              MV.write values hidden $! old + direction * value * weight
        V.freeze values
  restoreAccumulator model result

scoreAccumulator :: Model -> Accumulator -> Either String Double
scoreAccumulator model (Accumulator identity values) = do
  unless (identity == modelId model) $ Left "accumulator-model-mismatch"
  let activate x = min 1 (max 0 x)
      products = V.zipWith (\w x -> realToFrac w * activate x) (outputWeights model) values
      score = realToFrac (outputBias model) + V.foldl' (+) 0 products
  unless (finite score) $ Left "nonfinite-model-score"
  pure score

referenceBatch :: Model -> Accumulator -> [Sparse] -> Either String [Double]
referenceBatch model base features = traverse score features
 where
  score feature = updateAccumulator model base Nothing (Just feature) >>= scoreAccumulator model
