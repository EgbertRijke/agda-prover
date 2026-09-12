{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
-- SPDX-License-Identifier: GPL-3.0-or-later
module AgdaProver.Symbolic.NNUE.Model
  ( Model, ModelRole (..), roleName, featureFamily, parseRole
  , modelRole, modelId, inputSize, hiddenSize, modelSeed, policyFamilies
  , hiddenBias, embeddings, outputWeights, outputBias
  , decodeModel, loadModel, requireRole, supportsFamily, legacyFamilies
  , ModelCache, newModelCache, loadModelCached
  ) where

import Control.Exception qualified as E
import Control.Concurrent.MVar (MVar, newMVar, modifyMVar)
import Control.Monad (unless)
import Data.Aeson
import Data.Aeson.KeyMap qualified as KM
import Data.Aeson.Types (Parser, parseEither)
import Data.Bits ((.|.), shiftL)
import Data.ByteString qualified as BS
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set
import Data.Vector.Storable qualified as V
import Data.Word (Word32)
import GHC.Float (castWord32ToFloat)
import System.IO (IOMode (ReadMode), withBinaryFile)
import AgdaProver.Symbolic.NNUE.Hash (sha256)

data ModelRole = ProofTerm | OneStep | FocusedBranch | ORDecision
  deriving (Eq, Ord, Show, Enum, Bounded)

roleName :: ModelRole -> String
roleName ProofTerm = "proof-term-ranking"
roleName OneStep = "one-step-refinement-ranking"
roleName FocusedBranch = "focused-search-branch-policy"
roleName ORDecision = "or-decision-ranking"

parseRole :: String -> Maybe ModelRole
parseRole text = case filter ((== text) . roleName) [minBound .. maxBound] of
  [role] -> Just role
  _ -> Nothing

featureFamily :: ModelRole -> String
featureFamily ProofTerm = "proof-term-v2"
featureFamily OneStep = "one-step-refinement-v2"
featureFamily FocusedBranch = "focused-branch-v2"
featureFamily ORDecision = "or-decision-v4"

-- Parameters are immutable and constructors private. Every model visible to
-- inference has validated sizes, layout, role/domain and finite float32 values.
data Model = Model
  { modelRole :: ModelRole, modelId :: String, inputSize :: Int, hiddenSize :: Int
  , modelSeed :: Integer, policyFamilies :: Maybe [String]
  , hiddenBias :: V.Vector Float, embeddings :: V.Vector Float
  , outputWeights :: V.Vector Float, outputBias :: Float }

legacyFamilies :: Set.Set String
legacyFamilies = Set.fromList ["case-variable", "constructor-choice", "recursive-call", "visible-premise"]

supportsFamily :: Model -> String -> Bool
supportsFamily model family = Set.member family $
  maybe legacyFamilies Set.fromList (policyFamilies model)

requireRole :: ModelRole -> Model -> Either String ()
requireRole role model = unless (role == modelRole model) $ Left "model-role-mismatch"

maxHeader, maxParameters, maxFile :: Int
maxHeader = 64 * 1024
maxParameters = 16 * 1024 * 1024
maxFile = 12 + maxHeader + maxParameters

-- Limits are the existing artifact-format allocation limits. They are not
-- search budgets and cannot truncate a proof. Validate before vector allocation.
decodeModel :: Maybe ModelRole -> Maybe Value -> BS.ByteString -> Either String Model
decodeModel expected legacyManifest bytes = do
  unless (BS.length bytes <= maxFile) $ Left "model-file-too-large"
  version <- case BS.take 8 bytes of
    "APNNUE1\0" -> Right (1 :: Int)
    "APNNUE2\0" -> Right 2
    "APNNUE3\0" -> Right 3
    _ -> Left "invalid-model-magic"
  unless (BS.length bytes >= 12) $ Left "truncated-model-header"
  let headerSize = toInteger (word32LE bytes 8)
  unless (headerSize <= toInteger maxHeader) $ Left "model-header-too-large"
  let end = 12 + fromInteger headerSize
  unless (BS.length bytes >= end) $ Left "truncated-model-header"
  header <- either (const $ Left "invalid-model-header") Right $
    eitherDecodeStrict' (BS.take (fromInteger headerSize) $ BS.drop 12 bytes)
  (role, size, hidden, seed, families) <- parseEither (parseHeader version legacyManifest) header
  unless (maybe True (== role) expected) $ Left "model-role-mismatch"
  let count = hidden + size * hidden + hidden + 1
      payload = BS.drop end bytes
  unless (BS.length payload == count * 4) $ Left "model-payload-size-mismatch"
  let values = V.generate count (castWord32ToFloat . word32LE payload . (* 4))
  unless (V.all (\x -> not (isNaN x || isInfinite x)) values) $ Left "nonfinite-model-weight"
  pure $ Model role (sha256 bytes) size hidden seed families
    (V.take hidden values) (V.slice hidden (size * hidden) values)
    (V.slice (hidden + size * hidden) hidden values) (V.last values)

parseHeader :: Int -> Maybe Value -> Value -> Parser (ModelRole, Int, Int, Integer, Maybe [String])
parseHeader version legacyManifest = withObject "NNUE header" $ \header -> do
  schema <- header .: "schema_version"
  unless (schema == "agdaprover.nnue.p0.v" ++ show version) $ fail "model-schema-magic-mismatch"
  featureSchema <- header .: "feature_schema_version"
  unless (featureSchema == ("agdaprover.features.p0.v2" :: String)) $ fail "unsupported-feature-schema"
  size <- header .: "input_size" :: Parser Integer
  hidden <- header .: "hidden_size" :: Parser Integer
  seed <- header .: "seed"
  unless (size >= 1 && size <= 1048576 && hidden >= 1 && hidden <= 4096) $ fail "invalid-model-dimensions"
  unless (4 * (hidden + size * hidden + hidden + 1) <= toInteger maxParameters) $ fail "model-parameters-too-large"
  explicit <- header .:? "role"
  named <- case explicit of
    Just name -> pure name
    Nothing | version == 1 -> case legacyManifest of
      Just value -> withObject "legacy manifest" (\o -> o .: "training" >>= withObject "training" (.: "role")) value
      Nothing -> fail "legacy-model-role-missing"
    Nothing -> fail "model-role-missing"
  role <- maybe (fail "unsupported-model-role") pure (parseRole named)
  unless (version == 1) $ do
    family <- header .: "feature_family"
    unless (family == featureFamily role) $ fail "model-feature-family-mismatch"
  families <- if version == 3 then do
    values <- header .: "policy_families"
    let known = Set.insert "evidence-application-v1" legacyFamilies
    unless (role == ORDecision && not (null values) && Set.toAscList (Set.fromList values) == values
            && all (`Set.member` known) values) $ fail "invalid-model-policy-domain"
    pure $ Just values
    else do
      unless (not $ KM.member "policy_families" header) $ fail "unexpected-model-policy-domain"
      pure Nothing
  pure (role, fromInteger size, fromInteger hidden, seed, families)

-- Called only after the corresponding byte bounds have been checked.
word32LE :: BS.ByteString -> Int -> Word32
word32LE bytes start = foldr (\offset rest ->
  fromIntegral (BS.index bytes $ start + offset) .|. shiftL rest 8) 0 [0..3]

-- Explicit provisioning supplies paths; loading never downloads or executes a
-- model. A caller may cancel loading through normal IO interruption.
loadModel :: Maybe ModelRole -> FilePath -> IO (Either String Model)
loadModel expected path = fmap (>>= decodeSource expected) $ readSource path

-- A session retains at most one decoded model per supported role. Running
-- searches own their immutable models independently; replacing a cache slot
-- cannot change their weights. A new request still reads bounded exact bytes,
-- including the legacy sidecar, so paths and timestamps are never witnesses.
data ModelSource = ModelSource !BS.ByteString !(Maybe BS.ByteString)
  deriving Eq
newtype ModelCache = ModelCache (MVar (Map.Map ModelRole (ModelSource, Model)))

newModelCache :: IO ModelCache
newModelCache = ModelCache <$> newMVar Map.empty

loadModelCached :: ModelCache -> Maybe ModelRole -> FilePath -> IO (Either String Model)
loadModelCached (ModelCache cache) expected path = do
  source <- readSource path
  case source of
    Left failure -> pure $ Left failure
    Right witness -> modifyMVar cache $ \entries -> do
      let matches = [model | (saved, model) <- Map.elems entries, saved == witness]
      case matches of
        -- Identical bytes do not replace the long-lived source witness with
        -- a newly read buffer. Keep the cache's original allocation as well
        -- as its model; the temporary read becomes collectible immediately.
        model:_ -> pure (entries, model <$ maybe (Right ()) (`requireRole` model) expected)
        [] -> case decodeSource expected witness of
          -- Force validation before publishing the slot. Cancellation/decoding
          -- failure leaves the previous cache intact, never a suspended decoder.
          Left failure -> pure (entries, Left failure)
          Right model -> pure (Map.insert (modelRole model) (witness, model) entries, Right model)

decodeSource :: Maybe ModelRole -> ModelSource -> Either String Model
decodeSource expected (ModelSource bytes sidecar) = decodeModel expected
  (sidecar >>= either (const Nothing) Just . eitherDecodeStrict') bytes

readSource :: FilePath -> IO (Either String ModelSource)
readSource path = do
  loaded <- E.try $ boundedRead maxFile path
  case loaded of
    Left (_ :: E.IOException) -> pure $ Left "model-read-failed"
    Right (Left failure) -> pure $ Left failure
    Right (Right bytes) -> do
      manifest <- if BS.take 8 bytes == "APNNUE1\0" then do
        result <- E.try $ boundedRead maxHeader (path ++ ".json")
        pure $ case result of
          Right (Right value) -> Just value
          Left (_ :: E.IOException) -> Nothing
          _ -> Nothing
        else pure Nothing
      pure $ Right $ ModelSource bytes manifest

boundedRead :: Int -> FilePath -> IO (Either String BS.ByteString)
boundedRead limit path = withBinaryFile path ReadMode $ \handle -> go handle 0 []
 where
  go handle size chunks = do
    block <- BS.hGet handle (min (1024 * 1024) (limit - size + 1))
    if BS.null block then pure $ Right $ BS.concat (reverse chunks)
    else if BS.length block > limit - size then pure $ Left "model-file-too-large"
    else go handle (size + BS.length block) (block : chunks)
