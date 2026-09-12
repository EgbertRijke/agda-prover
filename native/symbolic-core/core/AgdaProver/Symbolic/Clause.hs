{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE OverloadedStrings #-}
-- SPDX-License-Identifier: GPL-3.0-or-later
module AgdaProver.Symbolic.Clause
  ( ClauseAction, splitSubjects, splitResult, expandEllipsis, command ) where

import Control.Monad (unless)
import Data.Aeson
import Data.Aeson.KeyMap qualified as KM
import Data.Aeson.Types (Parser)
import Data.Char (isSpace)
import Data.List.NonEmpty (NonEmpty (..), toList)
import Data.Set qualified as Set

-- The same versioned intent as the public interaction boundary. Constructors
-- are private: a variable batch cannot accidentally become result/ellipsis
-- splitting through whitespace or an empty string. Agda resolves actual names.
data ClauseAction = Subjects (NonEmpty String) | Result | Ellipsis
  deriving (Eq, Show)

splitSubjects :: [String] -> Either String ClauseAction
splitSubjects names = case names of
  [] -> Left "empty-clause-subjects"
  name:rest
    | all valid names -> Right $ Subjects (name :| rest)
    | otherwise -> Left "invalid-clause-subject"
 where
  valid name = not (null name) && name /= "." && not (any whitespace name)
  -- Python's public isspace contract also excludes these separator controls.
  whitespace c = isSpace c || c `elem` ['\x1c' .. '\x1f']

splitResult, expandEllipsis :: ClauseAction
splitResult = Result
expandEllipsis = Ellipsis

command :: ClauseAction -> String
command (Subjects names) = unwords $ toList names
command Result = ""
command Ellipsis = "."

instance FromJSON ClauseAction where
  parseJSON = withObject "clause action" $ \o -> do
    unless (Set.fromList (KM.keys o) == Set.fromList ["schema_version", "kind", "subjects"]) $
      fail "invalid clause action fields"
    version <- o .: "schema_version"
    unless (version == ("agdaprover.clause-action.v1" :: String)) $ fail "unsupported clause action version"
    kind <- o .: "kind" :: Parser String
    names <- o .: "subjects"
    case (kind, names) of
      ("variables", _) -> either fail pure $ splitSubjects names
      ("result", []) -> pure Result
      ("ellipsis", []) -> pure Ellipsis
      _ -> fail "invalid clause action intent"

instance ToJSON ClauseAction where
  toJSON action = object
    ["schema_version" .= ("agdaprover.clause-action.v1" :: String)
    ,"kind" .= kind, "subjects" .= names]
   where
    (kind, names) = case action of
      Subjects values -> ("variables" :: String, toList values)
      Result -> ("result", [])
      Ellipsis -> ("ellipsis", [])
