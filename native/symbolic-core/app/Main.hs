{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE LambdaCase #-}
-- SPDX-License-Identifier: GPL-3.0-or-later
module Main (main) where

import Control.Monad (unless, when)
import Control.Monad.IO.Class (liftIO)
import Control.Exception (Exception, Handler (..), IOException, bracket, catches, throwIO)
import Data.Aeson (Value, encode, object, (.=))
import Data.ByteString.Lazy.Char8 qualified as BL
import Data.IORef (newIORef, readIORef, writeIORef)
import Data.List (isPrefixOf, stripPrefix)
import Data.Maybe (mapMaybe, isJust)
import System.Directory (doesFileExist)
import System.Environment (getArgs, getProgName)
import System.Exit (ExitCode (..), exitFailure)
import System.FilePath (isAbsolute, takeDirectory)
import System.IO (stdout, stderr, Handle, hClose, hFlush)
import GHC.IO.Handle (hDuplicate, hDuplicateTo)
import Text.Read (readMaybe)

import Agda.Interaction.Imports
  ( Mode (TypeCheck), crMode, crWarnings, crInterface, parseSource, typeCheckMain )
import Agda.Interaction.Options (CommandLineOptions (..), defaultOptions, runOptM, parsePragmaOptions)
import Agda.Interaction.Library (OptionsPragma (..))
import Agda.Main (Interactor, runAgdaWithOptions, runTCMPrettyErrors)
import Agda.Setup qualified
import Agda.Syntax.Common (InteractionId)
import Agda.Syntax.Position (noRange)
import Agda.TypeChecking.Monad
import Agda.Utils.FileName (absolute)
import Agda.Version (version)
import AgdaProver.Agda28.Observation (observeGoal, encodeGoal, openInteractionPoints)
import AgdaProver.Agda28.Session qualified as Session
import AgdaProver.Symbolic.Protocol qualified as P
import SessionProtocol qualified

main :: IO ()
main = bracket (hDuplicate stdout) hClose $ \protocol -> do
  -- Agda owns its reporting machinery. Route it as a whole to stderr rather
  -- than assuming verbosity flags silence every successful/error code path.
  hDuplicateTo stderr stdout
  args <- getArgs
  if take 1 args == ["session"] then live protocol else single protocol

single :: Handle -> IO ()
single protocol = do
  pending <- newIORef Nothing
  let collect value = do
        old <- readIORef pending
        case old of
          Nothing -> writeIORef pending (Just $ Right value)
          Just _ -> reject "duplicate-response"
      failure reason = writeIORef pending (Just $ Left reason)
  -- Agda's top-level driver exits even on success. Buffer the observation until
  -- that driver finishes; a late failure must never follow a published success.
  run collect reject `catches`
    [ Handler $ \(ObservationFailure reason) -> failure reason
    , Handler $ \case
        ExitSuccess -> pure ()
        ExitFailure _ -> failure "agda-checking-failed"
    , Handler $ \(_ :: IOException) -> failure "native-io-failure"
    ]
  response <- maybe (Left "missing-response") id <$> readIORef pending
  case response of
    Right value -> BL.hPutStrLn protocol (encode value)
    Left reason -> do
      BL.hPutStrLn protocol $ encode $ object
        ["schema_version" .= ("agdaprover.symbolic-error.v1" :: String),
         "status" .= ("observation-rejected" :: String), "reason" .= reason]
      exitFailure

live :: Handle -> IO ()
live protocol = do
  failed <- newIORef False
  let failure :: String -> IO ()
      failure reason = do
        already <- readIORef failed
        unless already $ do
          writeIORef failed True
          emit $ object ["schema_version" .= ("agdaprover.symbolic-session-event.v1" :: String),
            "event" .= ("session-error" :: String), "reason" .= reason]
  run emit failure `catches`
    [ Handler $ \(ObservationFailure reason) -> failure reason
    , Handler $ \case
        ExitSuccess -> pure ()
        ExitFailure _ -> failure "agda-checking-failed"
    , Handler $ \(_ :: IOException) -> failure "native-io-failure"
    ]
  readIORef failed >>= (`when` exitFailure)
 where
  emit value = BL.hPutStrLn protocol (encode value) >> hFlush protocol

run :: (Value -> IO ()) -> (String -> IO ()) -> IO ()
run emit sessionFailure = do
  unless (version == "2.8.0") $
    reject "toolchain-mismatch"
  args <- getArgs
  case args of
    ["capabilities"] -> emit P.capabilities
    "session" : file : arguments
      | let (configuration, suffix) = break (== "--") arguments
            registries = mapMaybe (stripPrefix "--library-file=") configuration
            pins = mapMaybe (stripPrefix "--pin-config=") configuration
            includes = filter (not . isPrefixOf "--") configuration
      , isAbsolute file, all isAbsolute (includes ++ registries ++ pins)
      , length configuration == length includes + length registries + length pins
      , length registries <= 1 -> do
        let registry = case registries of [path] -> Just path; _ -> Nothing
        unless (all (`elem` pins) registries) $ reject "unpinned-library-registry"
        filesExist <- and <$> mapM doesFileExist pins
        unless filesExist $ reject "missing-configuration-input"
        projectPins <- Session.pinConfiguration pins
        Agda.Setup.setup False
        pinned <- if isJust registry then Session.pinRuntimeConfiguration projectPins else pure projectPins
        program <- getProgName
        let initial = defaultOptions
              { optUseLibs = isJust registry, optDefaultLibs = False
              , optOverrideLibrariesFile = registry
              , optIgnoreInterfaces = True
              , optIncludePaths = takeDirectory file : includes }
        opts <- case runOptM $ parsePragmaOptions (OptionsPragma (drop 1 suffix) noRange) initial of
          (Right pragmas, []) -> pure initial { optPragmaOptions = pragmas }
          _ -> reject "unsupported-checking-options"
        runTCMPrettyErrors $ runAgdaWithOptions (session emit sessionFailure file pinned) program opts
    "observe" : file : goal : mode : includes
      | isAbsolute file, all isAbsolute includes
      , Just point <- readGoal goal, Just policy <- P.parseMode mode -> do
        Agda.Setup.setup False
        program <- getProgName
        let opts = defaultOptions
              { optUseLibs = False, optDefaultLibs = False
              , optIgnoreInterfaces = True
              , optIncludePaths = takeDirectory file : includes
              }
        runTCMPrettyErrors $ runAgdaWithOptions (observe emit file point policy) program opts
    _ -> reject "usage: capabilities | observe ABSOLUTE-FILE GOAL MODE [ABSOLUTE-INCLUDE ...] | session ABSOLUTE-FILE [ABSOLUTE-INCLUDE ...]"

readGoal :: String -> Maybe InteractionId
readGoal text = do
  n <- readMaybe text :: Maybe Integer
  if n >= 0 && n <= toInteger (maxBound :: Int)
    then Just (fromInteger n) else Nothing

observe :: (Value -> IO ()) -> FilePath -> InteractionId -> P.ObservationMode -> Interactor ()
observe emit file point mode setup _ = do
  setup
  path <- liftIO $ absolute file
  result <- typeCheckMain TypeCheck =<< parseSource =<< srcFromPath path
  unless (crMode result == ModuleTypeChecked && all expected (crWarnings result)) $
    liftIO $ reject "unsupported-checker-warning"
  points <- openInteractionPoints
  unless (point `elem` points) $ liftIO $ reject "unknown-goal"
  snapshot <- observeGoal point mode
  either (liftIO . reject) (liftIO . emit) (encodeGoal snapshot)
 where
  expected warning = case tcWarning warning of
    UnsolvedInteractionMetas{} -> True
    UnsolvedMetaVariables{} -> True
    UnsolvedConstraints{} -> True
    _ -> False

session :: (Value -> IO ()) -> (String -> IO ()) -> FilePath -> Session.Configuration -> Interactor ()
session emit failure file pinned setup _ = do
  setup
  path <- liftIO $ absolute file
  result <- typeCheckMain TypeCheck =<< parseSource =<< srcFromPath path
  unless (crMode result == ModuleTypeChecked && all expected (crWarnings result)) $
    liftIO $ reject "unsupported-checker-warning"
  -- Handle protocol exceptions before they cross TCM's liftIO boundary, which
  -- would otherwise relabel them as Agda checking errors. Exit outside Agda's
  -- driver after its own success exit; publish only the precise error once.
  Session.withSessionConfiguration pinned (crInterface result) $ \owner root ->
    SessionProtocol.serve emit owner root `catches`
      [ Handler $ \err -> failure (SessionProtocol.protocolFailureName err)
      , Handler $ \(_ :: IOException) -> failure "native-io-failure"
      ]
 where
  expected warning = case tcWarning warning of
    UnsolvedInteractionMetas{} -> True
    UnsolvedMetaVariables{} -> True
    UnsolvedConstraints{} -> True
    _ -> False

data ObservationFailure = ObservationFailure String deriving Show
instance Exception ObservationFailure

reject :: String -> IO a
reject = throwIO . ObservationFailure
