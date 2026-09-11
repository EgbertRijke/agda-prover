{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE OverloadedStrings #-}

-- Runtime declaration-boundary proposals; fresh Agda decides acceptance.
module Main (main) where

import Control.Monad (when)
import Data.Aeson (encode, object, (.=))
import Data.ByteString qualified as BS
import Data.ByteString.Lazy.Char8 qualified as BL
import Data.Text qualified as T
import Data.Text.Encoding (decodeUtf8')
import System.Environment (getArgs)
import System.Exit (exitFailure)
import System.IO (IOMode (ReadMode), withBinaryFile)
import Text.Read (readMaybe)
import Agda.Syntax.Parser qualified as P
import Agda.Syntax.Position (mkRangeFile)
import Agda.Utils.FileName (absolute)
import Agda.Version (version)
import Prefix qualified
import Entries qualified

failure :: String -> IO a
failure diagnostic = do
  -- Retain the established error wire tag for client compatibility.
  BL.putStrLn $ encode $ object
    [ "schema_version" .= ("agdaprover.corpus-prefix.v1" :: String)
    , "status" .= ("prefix-rejected" :: String)
    , "diagnostic" .= take 4096 diagnostic
    ]
  exitFailure

main :: IO ()
main = do
  arguments <- getArgs
  (position, path) <- case arguments of
    ["--prefix", offset, file] | Just n <- readMaybe offset, n >= 0 -> pure (Just n, file)
    ["--entries", file] -> pure (Nothing, file)
    _ -> failure "expected-prefix-or-entries-and-source-file"
  bytes <- withBinaryFile path ReadMode $ \handle -> BS.hGet handle (4 * 1024 * 1024 + 1)
  when (BS.length bytes > 4 * 1024 * 1024) $ failure "source-size-limit"
  text <- either (failure . show) pure (decodeUtf8' bytes)
  let source = T.unpack text
  absolutePath <- absolute path
  let file = mkRangeFile absolutePath Nothing
  (parsed, warnings) <- P.runPMIO $ P.parseFile P.moduleParser file source
  ((modul, _), _) <- either (failure . show) pure parsed
  case position of
    Nothing -> do
      entries <- either failure pure (Entries.inventory source modul)
      BL.putStrLn $ encode $ object
        [ "schema_version" .= ("agdaprover.source-entries.v1" :: String)
        , "parser_version" .= version
        , "source_characters" .= length source
        , "parse_warning_count" .= length warnings
        , "entries" .= entries
        ]
    Just offset -> do
      end <- either failure pure (Prefix.boundary source modul offset)
      omissions <- either failure pure (Prefix.omissions modul)
      when (length omissions > 4096) $ failure "prefix-declaration-count-limit"
      BL.putStrLn $ encode $ object
        [ "schema_version" .= ("agdaprover.source-prefix.v1" :: String)
        , "parser_version" .= version
        , "source_characters" .= length source
        , "position" .= offset
        , "prefix_end" .= end
        , "parse_warning_count" .= length warnings
        , "omission_candidates" .=
            [ object ["name" .= name, "start" .= start, "end" .= stop]
            | (name, start, stop) <- omissions, stop < offset ]
        ]
