{-# LANGUAGE ImportQualifiedPost #-}
-- SPDX-License-Identifier: GPL-3.0-or-later
module AgdaProver.Symbolic.NNUE.Sparse
  ( Sparse, sparse, hashSparse, entries, dimension, mergeSparse, sparseDelta ) where

import Control.Monad (unless)
import Data.Bits (testBit)
import Data.IntMap.Strict qualified as M
import Data.List (foldl')
import Data.Text (Text)
import AgdaProver.Symbolic.NNUE.Hash (featureHash)

-- Retain first-insertion order, including zero-valued hash collisions. The
-- reference scorer sums in this order; the Rust ABI sorts the same entries.
data Sparse = Sparse { dimension :: Int, entries :: [(Int, Double)] }
  deriving (Eq, Show)

sparse :: Int -> [(Int, Double)] -> Either String Sparse
sparse size values = do
  unless (size > 0 && all valid values) $ Left "invalid-sparse-features"
  let (order, table) = foldl' insert ([], M.empty) values
      result = [(key, table M.! key) | key <- reverse order]
  unless (all (finite . snd) result) $ Left "nonfinite-sparse-sum"
  pure $ Sparse size result
 where
  valid (index, value) = index >= 0 && index < size && finite value
  insert (order, table) (index, value) =
    (if M.member index table then order else index : order,
     M.insertWith (+) index value table)

finite :: Double -> Bool
finite x = not (isNaN x || isInfinite x)

hashSparse :: Int -> [Text] -> Either String Sparse
hashSparse size tokens
  | size <= 0 = Left "invalid-feature-dimension"
  | otherwise = sparse size
      [(fromIntegral $ raw `mod` fromIntegral size, if testBit raw 63 then -1 else 1)
      | token <- tokens, let raw = featureHash token]

mergeSparse :: Int -> [Sparse] -> Either String Sparse
mergeSparse size sets = do
  unless (all ((== size) . dimension) sets) $ Left "feature-dimension-mismatch"
  combined <- sparse size (concatMap entries sets)
  pure combined { entries = filter ((/= 0) . snd) $ entries combined }

sparseDelta :: Sparse -> Sparse -> Either String (Sparse, Sparse)
sparseDelta previous current = do
  unless (dimension previous == dimension current) $ Left "feature-dimension-mismatch"
  let difference = M.unionWith (+) (M.fromList $ entries current)
        (M.map negate $ M.fromList $ entries previous)
  remove <- sparse (dimension current) [(i, -v) | (i, v) <- M.toAscList difference, v < 0]
  add <- sparse (dimension current) [(i, v) | (i, v) <- M.toAscList difference, v > 0]
  pure (remove, add)
