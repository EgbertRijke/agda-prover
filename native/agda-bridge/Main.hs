{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE OverloadedStrings #-}

-- SPDX-License-Identifier: GPL-3.0-or-later AND MIT
-- Copyright (C) 2026 Egbert Rijke and contributors (AgdaProver modifications).
-- Interaction loop and command reader adapted from Agda 2.8.0 (MIT).
-- Copyright (c) 2005-2025 remains with the Agda authors.
-- See ../../THIRD_PARTY_NOTICES.md and ../../licenses/Agda-MIT.txt.
--
-- A deliberately narrow Agda 2.8 interaction adapter for AgdaProver.
--
-- The ordinary interaction protocol uses the highlighting method `Direct`.
-- AgdaProver marks speculative commands with `Indirect`; those commands run
-- under Agda's own localStateCommandM and therefore restore both TCState and
-- CommandState after emitting their response.  Committed commands retain the
-- standard behaviour.  This keeps the wire response compatible with
-- --interaction-json while avoiding reload/replay after rejected candidates.
module Main (main) where

import Control.Monad ((<=<), unless)
import Control.Monad.IO.Class (liftIO)
import Control.Monad.State (evalStateT, gets, runStateT)
import Control.Monad.Trans (lift)
import Data.Aeson (encode)
import Data.ByteString.Lazy.Char8 qualified as BS
import Data.Char (isSpace)
import Data.List (sort, stripPrefix)
import System.Environment (getArgs, getProgName)
import System.IO
  ( BufferMode (LineBuffering)
  , hFlush
  , hSetBuffering
  , hSetEncoding
  , hPutStrLn
  , isEOF
  , stderr
  , stdin
  , stdout
  , utf8
  )

import Agda.Interaction.AgdaTop ()
import Agda.Interaction.Base
import Agda.Interaction.Command (CommandM, localStateCommandM)
import Agda.Interaction.ExitCode (AgdaError (CommandError), exitAgdaWith)
import Agda.Interaction.InteractionTop
  ( handleCommand_
  , initialiseCommandQueue
  , maybeAbort
  , runInteraction
  )
import Agda.Interaction.JSON (EncodeTCM (encodeTCM))
import Agda.Interaction.JSONTop ()
import Agda.Interaction.Options
  ( commandLineOptions
  , defaultOptions
  , optAbsoluteIncludePaths
  , optExitOnError
  , optIgnoreInterfaces
  , optJSONInteraction
  , optUseLibs
  )
import Agda.Interaction.Response (InteractionOutputCallback)
import Agda.Main (Interactor, runAgdaWithOptions, runTCMPrettyErrors)
import Agda.Setup qualified
import Agda.TypeChecking.Monad
  ( HighlightingMethod (Direct, Indirect)
  , TCM
  , genericError
  , setInteractionOutputCallback
  )
import Agda.TypeChecking.Monad.Benchmark qualified as Bench
import Agda.Utils.FileName (absolute)
import ScopeQuery qualified

main :: IO ()
main = do
  -- This private adapter has one startup profile, matching its transport.
  -- Agda 2.8's runAgdaWithOptions expects *parsed* options: passing defaults
  -- silently discards argv, including isolation and interaction settings.
  arguments <- getArgs
  unless (sort arguments == sort ["--no-libraries", "--ignore-interfaces", "--interaction-json"]) $ do
    hPutStrLn stderr "AgdaProver bridge requires --no-libraries --ignore-interfaces --interaction-json; other startup options are unsupported"
    exitAgdaWith CommandError
  Agda.Setup.setup False
  program <- getProgName
  let options = defaultOptions
        { optUseLibs = False
        , optIgnoreInterfaces = True
        , optJSONInteraction = True
        }
  runTCMPrettyErrors $ runAgdaWithOptions transactionalInteractor program options

transactionalInteractor :: Interactor ()
transactionalInteractor setup _check = transactionalJSONREPL setup

transactionalJSONREPL :: TCM () -> TCM ()
transactionalJSONREPL = repl jsonCallback "JSON> "

jsonCallback :: InteractionOutputCallback
jsonCallback = liftIO . BS.putStrLn <=< (pure . encode <=< encodeTCM)

repl :: InteractionOutputCallback -> String -> TCM () -> TCM ()
repl callback prompt setup = do
  liftIO $ do
    hSetBuffering stdout LineBuffering
    hSetBuffering stdin LineBuffering
    hSetEncoding stdout utf8
    hSetEncoding stdin utf8

  setInteractionOutputCallback callback
  commands <- liftIO $ initialiseCommandQueue readCommand
  handleCommand_ (lift setup) `evalStateT` initCommandState commands
  opts <- commandLineOptions
  _ <- interactLoop `runStateT`
    (initCommandState commands)
      { optionsOnReload = opts {optAbsoluteIncludePaths = []}
      }
  pure ()
 where
  interactLoop :: CommandM ()
  interactLoop = do
    Bench.reset
    done <- Bench.billTo [] $ do
      liftIO $ putStr prompt >> hFlush stdout
      result <- maybeAbort runTransactionalInteraction
      case result of
        Done -> pure True
        Command _ -> pure False
        Error message -> do
          shouldExit <- optExitOnError <$> commandLineOptions
          if shouldExit
            then liftIO $ exitAgdaWith CommandError
            else liftIO (putStrLn message) >> pure False
    lift Bench.print
    unless done interactLoop

-- `Indirect` is otherwise only a highlighting delivery choice.  The Python
-- transport reserves it as the transaction bit for this adapter; ordinary
-- Agda clients and all committed AgdaProver commands continue to use Direct.
runTransactionalInteraction :: IOTCM -> CommandM ()
runTransactionalInteraction command =
  case command Nothing of
    IOTCM current _ _ (Cmd_show_module_contents _ point _ payload)
      | Just (withDependencies, exclusions) <- ScopeQuery.request payload ->
        handleCommand_ $ localStateCommandM $ do
          path <- liftIO $ absolute current
          loaded <- gets theCurrentFile
          unless (Just path == (currentFilePath <$> loaded)) $
            lift $ genericError "live-scope-current-file-mismatch"
          lift $ ScopeQuery.emit withDependencies point exclusions
    IOTCM _ _ Indirect _ ->
      localStateCommandM (runInteraction (forceDirect command))
    IOTCM _ _ Direct _ -> runInteraction command

-- Do not let the transaction marker reach Agda's highlighting machinery:
-- genuine Indirect highlighting can write auxiliary files and is much slower.
forceDirect :: IOTCM -> IOTCM
forceDirect command moduleName =
  case command moduleName of
    IOTCM current highlighting _ action ->
      IOTCM current highlighting Direct action

readCommand :: IO Command
readCommand = do
  done <- isEOF
  if done
    then pure Done
    else do
      input <- getLine
      _ <- pure $! length input
      case dropWhile isSpace input of
        "" -> readCommand
        ('-' : '-' : _) -> readCommand
        _ -> case parseIOTCM input of
          Right command -> pure $ Command command
          Left message -> pure $ Error message
