{-# LANGUAGE CPP #-}
{-# LANGUAGE ForeignFunctionInterface #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RoleAnnotations #-}
-- SPDX-License-Identifier: GPL-3.0-or-later
module AgdaProver.Symbolic.NNUE.Native
  ( NativeScorer, ScoredBatch (..), withNativeScorer, scoreBatch ) where

import Control.Monad (unless)
import Data.Kind (Type)
import GHC.Clock (getMonotonicTimeNSec)
import System.Environment (lookupEnv)
import AgdaProver.Symbolic.NNUE.Model
import AgdaProver.Symbolic.NNUE.Sparse
import AgdaProver.Symbolic.NNUE.Score
#ifndef mingw32_HOST_OS
import Control.Exception (bracket)
import Control.Concurrent.MVar (MVar, modifyMVar_, newMVar, withMVar)
import Data.List (sortOn)
import Data.Vector.Storable qualified as V
import Data.Word (Word32)
import Foreign.C.Types (CFloat (..), CInt (..), CSize (..))
import Foreign.ForeignPtr (mallocForeignPtrArray, withForeignPtr)
import Foreign.Marshal.Array (peekArray, withArray)
import Foreign.Ptr (FunPtr, Ptr, castPtr)
import System.IO.Error (tryIOError)
import System.Posix.DynamicLinker

type Batch = Ptr CFloat -> Ptr CFloat -> CSize -> CSize -> Ptr CFloat -> CFloat
          -> Ptr CSize -> Ptr Word32 -> Ptr CFloat -> CSize -> CSize -> Ptr CFloat -> IO CInt
foreign import ccall "dynamic" callABI :: FunPtr (IO Word32) -> IO Word32
foreign import ccall safe "dynamic" callBatch :: FunPtr Batch -> Batch
data NativeScorer (s :: Type) = NativeScorer (MVar (Maybe (FunPtr Batch)))
#else
data NativeScorer (s :: Type) = NativeUnavailable
#endif
type role NativeScorer nominal

data ScoredBatch = ScoredBatch
  { batchScores :: [Double], scoringBackend :: String
  , nativeFallback :: Maybe String, scoringNanoseconds :: Integer, itemsScored :: Int }
  deriving (Eq, Show)

-- A trusted installation/custom-library path is supplied by the application,
-- never by a model or proof. Keep the handle live for the entire callback.
-- The OS-specific loader is optional: the reference path works offline alone.
withNativeScorer :: Maybe FilePath -> (forall s. Maybe (NativeScorer s) -> IO a) -> IO a
withNativeScorer path use = do
  disabled <- (== Just "1") <$> lookupEnv "AGDAPROVER_DISABLE_NATIVE"
  if disabled then use Nothing else case path of
    Nothing -> use Nothing
#ifndef mingw32_HOST_OS
    Just file -> do
      loaded <- tryIOError $ dlopen file [RTLD_NOW, RTLD_LOCAL]
      case loaded of
        Left _ -> use Nothing
        Right handle -> bracket (pure handle) dlclose $ \library -> do
          found <- tryIOError $ do
            version <- dlsym library "agdaprover_native_abi_version" >>= callABI
            unless (version == 3) $ ioError $ userError "unsupported-native-ABI"
            dlsym library "agdaprover_nnue_score_batch"
          case found of
            Left _ -> use Nothing
            Right function -> bracket (newMVar $ Just function)
              (\owner -> modifyMVar_ owner $ const $ pure Nothing)
              (use . Just . NativeScorer)
#else
    Just _ -> use Nothing
#endif

scoreBatch :: Maybe (NativeScorer s) -> Model -> Accumulator -> [Sparse]
           -> IO (Either String ScoredBatch)
scoreBatch backend model base features = do
  started <- getMonotonicTimeNSec
  -- Validate dimensions/identity before exposing any pointer to native code.
  let valid = do
        _ <- scoreAccumulator model base
        unless (all ((== inputSize model) . dimension) features) $ Left "feature-dimension-mismatch"
  result <- case valid of
    Left failure -> pure $ Left failure
    Right () -> case backend of
      Just scorer | length features > 1 -> do
        native <- nativeBatch scorer model base features
        pure $ case native of
          Right values -> Right (values, "rust-abi3", Nothing)
          Left reason -> (\values -> (values, "haskell-reference", Just reason))
            <$> referenceBatch model base features
      _ -> pure $ (\values -> (values, "haskell-reference", Nothing))
        <$> referenceBatch model base features
  -- Force the complete batch inside the timing boundary, including fallback.
  case result of
    Right (scores, _, _) -> unless (all finite scores) $ ioError $ userError "nonfinite-scoring-result"
    Left _ -> pure ()
  finished <- getMonotonicTimeNSec
  pure $ fmap (\(scores, name, reason) -> ScoredBatch scores name reason
    (toInteger $ finished - started) (length scores)) result
 where finite x = not (isNaN x || isInfinite x)

nativeBatch :: NativeScorer s -> Model -> Accumulator -> [Sparse] -> IO (Either String [Double])
#ifndef mingw32_HOST_OS
nativeBatch (NativeScorer owner) model base features = withMVar owner $ \live -> case live of
  Nothing -> pure $ Left "native-scorer-closed"
  Just function -> borrowedBatch function model base features

-- The owner lock serializes unload with in-flight calls. Even an IO closure
-- improperly retained beyond withNativeScorer fails rather than using a
-- dangling function pointer. Waiting callers remain cancellable.
borrowedBatch :: FunPtr Batch -> Model -> Accumulator -> [Sparse] -> IO (Either String [Double])
borrowedBatch function model base features = do
  let rows = map (sortOn fst . entries) features
      offsets = scanl (+) 0 (map (toInteger . length) rows)
      flat = concat rows
      floats = V.map realToFrac (accumulatorValues base) :: V.Vector Float
      values = V.fromList (map (realToFrac . snd) flat) :: V.Vector Float
      finite x = not (isNaN x || isInfinite x)
  if not (V.all finite floats && V.all finite values)
      || last offsets > toInteger (maxBound :: CSize)
    then pure $ Left "native-buffer-range"
    else do
      output <- mallocForeignPtrArray (length features)
      V.unsafeWith floats $ \basePtr ->
        V.unsafeWith (embeddings model) $ \embeddingPtr ->
          V.unsafeWith (outputWeights model) $ \weightPtr ->
            withArray (map fromInteger offsets) $ \offsetPtr ->
              withArray (map (fromIntegral . fst) flat) $ \indexPtr ->
                V.unsafeWith values $ \valuePtr ->
                  withForeignPtr output $ \outputPtr -> do
                    status <- callBatch function (castPtr basePtr) (castPtr embeddingPtr)
                      (fromIntegral $ inputSize model) (fromIntegral $ hiddenSize model)
                      (castPtr weightPtr) (realToFrac $ outputBias model)
                      offsetPtr indexPtr (castPtr valuePtr) (fromIntegral $ length features)
                      (fromInteger $ last offsets) outputPtr
                    if status /= 0 then pure $ Left $ "native-score-status:" ++ show status
                    else do
                      scores <- map realToFrac <$> peekArray (length features) outputPtr
                      pure $ if all finite scores then Right scores else Left "native-nonfinite-score"
#else
nativeBatch NativeUnavailable _ _ _ = pure $ Left "native-platform-unavailable"
#endif
