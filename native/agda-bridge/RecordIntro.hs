{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE OverloadedStrings #-}

-- SPDX-License-Identifier: GPL-3.0-or-later AND MIT
-- Record literal rendering adapted from Agda 2.8.0's BasicOps.introRec (MIT).
-- Copyright (c) 2005-2025 Agda authors; modifications (C) 2026 contributors.
-- See ../../THIRD_PARTY_NOTICES.md and ../../licenses/Agda-MIT.txt.
module RecordIntro (request, emit) where

import Control.Monad (unless)
import Control.Monad.IO.Class (liftIO)
import Data.Aeson (FromJSON (parseJSON), eitherDecodeStrict', encode, object, withObject, (.:), (.=))
import Data.Aeson.KeyMap qualified as KeyMap
import Data.ByteString.Lazy.Char8 qualified as BL
import Data.List (stripPrefix)
import Data.Text qualified as Text
import Data.Text.Encoding qualified as Text

import Agda.Syntax.Common
import Agda.Syntax.Common.Pretty (prettyShow)
import Agda.Syntax.Concrete qualified as C
import Agda.Syntax.Internal
import Agda.Syntax.Position (noRange)
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Records (getRecordFieldNames)
import Agda.TypeChecking.Reduce (reduce)
import Agda.Utils.Null (empty)

request :: String -> Maybe String
request = stripPrefix "agdaprover:record-introduction:v1:"

newtype Request = Request Integer
instance FromJSON Request where
  parseJSON = withObject "record introduction request" $ \o -> do
    unless (KeyMap.keys o == ["output_bytes"]) $ fail "invalid request fields"
    limit <- o .: "output_bytes"
    unless (limit > 0) $ fail "invalid output reservation"
    pure $ Request limit

-- The caller encloses this observation in localStateCommandM. Do not unfold
-- abstract definitions, assign metas, or look up a rendered qualified name.
-- Include hidden/instance fields too: unresolved fields must remain explicit
-- obligations, not be mistaken for a completed record with internal metas.
emit :: InteractionId -> String -> TCM ()
emit point payload = do
  Request limit <- either (const $ genericError "invalid-record-introduction-request") pure $
    eitherDecodeStrict' (Text.encodeUtf8 (Text.pack payload))
  expression <- withInteractionId point $ dontAssignMetas $ do
    meta <- lookupInteractionId point
    target <- reduce =<< getMetaTypeInContext meta
    case unEl target of
      Def name _ -> do
        definition <- getConstInfo name
        case theDef definition of
          Record{} -> do
            fields <- getRecordFieldNames name
            pure $ Just $ prettyShow $ C.Rec empty noRange
              [Left $ C.FieldAssignment (unDom field) $ C.QuestionMark noRange Nothing
              | field <- fields]
          _ -> pure Nothing
      _ -> pure Nothing
  let response status term required = encode $ object
        ["kind" .= ("AgdaProverRecordIntroduction" :: String),
         "schema_version" .= ("agdaprover.record-introduction.v1" :: String),
         "interaction_id" .= interactionId point, "output_bytes" .= limit,
         "status" .= (status :: String), "expression" .= (term :: Maybe String),
         "required_bytes" .= (required :: Maybe Integer)]
      bytes = response (maybe "not-record" (const "record") expression) expression Nothing
      size = toInteger (BL.length bytes)
  liftIO $ BL.putStrLn $ if size <= limit then bytes
    else response "output-limited" Nothing (Just size)
