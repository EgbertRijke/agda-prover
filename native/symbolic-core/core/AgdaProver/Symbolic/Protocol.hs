{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE CPP #-}
#if __GLASGOW_HASKELL__ != 906 || __GLASGOW_HASKELL_PATCHLEVEL1__ != 7
#error The symbolic core requires GHC 9.6.7
#endif
-- SPDX-License-Identifier: GPL-3.0-or-later
module AgdaProver.Symbolic.Protocol
  ( ObservationMode (..), modeName, parseMode, capabilities ) where

import Data.Aeson (Value, object, (.=))

-- These are distinct requests, not aliases for full normalization.
data ObservationMode = Raw | Instantiated | HeadNormal | Simplified | Normalized
  deriving (Eq, Ord, Show, Enum, Bounded)

modeName :: ObservationMode -> String
modeName Raw = "raw"
modeName Instantiated = "instantiated"
modeName HeadNormal = "head-normal"
modeName Simplified = "simplified"
modeName Normalized = "normalized"

parseMode :: String -> Maybe ObservationMode
parseMode name = case filter ((== name) . modeName) [minBound .. maxBound] of
  [mode] -> Just mode
  _ -> Nothing

capabilities :: Value
capabilities = object
  [ "schema_version" .= ("agdaprover.symbolic-capabilities.v1" :: String)
  , "engine" .= ("haskell-symbolic-core" :: String)
  , "package_version" .= ("0.1.0.0" :: String)
  , "agda_version" .= ("2.8.0" :: String)
  , "ghc_version" .= ("9.6.7" :: String)
  , "operations" .= (["capabilities", "observe-goal", "resident-session"] :: [String])
  , "session_operations" .=
      (["pending", "observe", "give", "evict", "replay", "cost", "cancel", "close"] :: [String])
  , "observation_modes" .= map modeName [minBound .. maxBound]
  , "search_available" .= False
  , "proof_authority" .= False
  ]
