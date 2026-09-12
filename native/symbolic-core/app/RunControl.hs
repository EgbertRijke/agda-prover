{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
-- SPDX-License-Identifier: GPL-3.0-or-later
-- Resident run handles and protocol lifecycle only. Search decisions remain
-- in the typed native controller; no heap or proof authority crosses the wire.
module RunControl (Store, Key, newStore, start, advance, snapshot, discard) where

import Control.Concurrent (MVar, newMVar, modifyMVar, withMVar)
import Control.Monad (unless)
import Data.Aeson hiding (Key)
import Data.Aeson.KeyMap qualified as KM
import Data.Map.Strict qualified as Map
import Data.List.NonEmpty (NonEmpty)
import Data.List.NonEmpty qualified as NE
import Agda.Syntax.Common (InteractionId, interactionId)
import Data.Set qualified as Set
import Numeric.Natural (Natural)
import AgdaProver.Agda28.AgendaSearch qualified as G
import AgdaProver.Agda28.Session qualified as S
import AgdaProver.Symbolic.Evidence qualified as E
import AgdaProver.Symbolic.NNUE.Native (withNativeScorer)
import AgdaProver.Symbolic.SessionTypes

data Key = Key String Integer Integer Integer
data Entry s = Entry Integer (S.StateRef s) (Maybe FilePath) (Maybe [Int]) (G.Run s)
data Store s = Store (S.Session s) StateKey (MVar (Integer, Map.Map Integer (Entry s)))

instance FromJSON Key where
  parseJSON = withObject "native run key" $ \o -> do
    unless (Set.fromList (KM.keys o) == Set.fromList ["session", "epoch", "run", "revision"]) $
      fail "invalid run key fields"
    key@(Key session epoch number revision) <- Key <$> o .: "session" <*> o .: "epoch"
      <*> o .: "run" <*> o .: "revision"
    unless (not (null session) && epoch >= 0 && number >= 0 && revision >= 0) $
      fail "invalid run key"
    pure key

instance ToJSON Key where
  toJSON (Key session epoch number revision) = object
    ["session" .= session, "epoch" .= epoch, "run" .= number, "revision" .= revision]

newStore :: S.Session s -> S.StateRef s -> IO (Store s)
newStore session root = Store session (S.stateKey root) <$> newMVar (0, Map.empty)

start :: Store s -> S.StateRef s -> G.Settings -> Maybe FilePath -> Maybe (NonEmpty InteractionId) -> IO Value
start (Store session identity store) root settings nativePath selection = modifyMVar store $ \(serial, entries) ->
  G.beginSelection selection session root settings (const $ pure ()) (const $ pure ()) >>= \case
    Left failure -> pure ((serial, entries), failureView failure)
    Right run -> do
      measured <- G.cost run
      let key = Key (keySession identity) (keyEpoch $ S.stateKey root) serial 0
          chosen = fmap (map interactionId . NE.toList) selection
      pure ((serial+1, Map.insert serial (Entry 0 root nativePath chosen run) entries),
        object ["status" .= ("ready" :: String), "run" .= key, "cost" .= measured,
          "goal_ids" .= chosen, "proof_authority" .= False])

-- Consume a revision only when the operation returns. An interruption outside
-- a native call restores the prior queue; its shared ledger still charges work.
-- Successful advancement issues a new revision, preventing accidental replay
-- of a stale frontend request against a different frontier.
advance :: Store s -> Key -> Natural -> E.SearchLimits -> Maybe (Maybe Integer) -> (Value -> IO ()) -> IO Value
advance (Store session identity store) key@(Key nonce epoch number revision) quantum limits actionLimit emit =
  modifyMVar store $ \(serial, entries) -> case resolve identity entries key of
    Left reason -> pure ((serial, entries), rejected reason)
    Right (Entry _ root nativePath chosen run) -> S.pending session root >>= \case
      Left failure -> pure ((serial, entries), failureView failure)
      Right _ -> do
        let progress t = emit $ object
              ["schema_version" .= ("agdaprover.symbolic-progress.v1" :: String),
               "state" .= S.stateKey (S.transitionState t), "pending" .= S.transitionPending t,
               "goal_ids" .= chosen,
               "status" .= kindName (S.transitionKind t), "proof_authority" .= False]
            current = G.withObservers emit progress $ G.withLimits limits $
              maybe run (`G.withActionLimit` run) actionLimit
        outcome <- withNativeScorer nativePath $ \native -> G.advance native quantum current
        measured <- G.cost current
        let nextKey = Key nonce epoch number (revision+1)
            retained next status extra =
              ((serial, Map.insert number (Entry (revision+1) root nativePath chosen next) entries),
               object (["status" .= (status :: String), "run" .= nextKey,
                 "cost" .= measured, "goal_ids" .= chosen, "proof_authority" .= False] ++ extra))
        case outcome of
          G.Refutation proposal next -> pure $ retained next "refutation-candidate"
            ["refutation" .= S.refutationView proposal]
          G.Candidate state next -> S.pending session state >>= \case
            Left failure -> pure $ retained next "failed" ["failure" .= failureView failure]
            Right pending -> pure $ retained next "candidate"
              ["state" .= S.stateKey state, "pending" .= pending]
          G.Paused reason next -> pure $ retained next "paused" ["reason" .= pauseName reason]
          G.Failed failure next -> pure $ retained next "failed" ["failure" .= failureView failure]
          G.Exhausted -> pure ((serial, Map.delete number entries), object
            ["status" .= ("unsolved" :: String), "cost" .= measured,
             "goal_ids" .= chosen, "proof_authority" .= False])

snapshot :: Store s -> Key -> IO Value
snapshot (Store session identity store) key = withMVar store $ \(_, entries) ->
  case resolve identity entries key of
    Left reason -> pure $ rejected reason
    Right (Entry _ root _ chosen run) -> S.pending session root >>= \case
      Left failure -> pure $ failureView failure
      Right _ -> do
        let (size, focus) = G.frontier run
        viewed <- case focus of
          Nothing -> pure $ Right Null
          Just (state, priority, depth) -> fmap (fmap $ \pending -> object
            ["state" .= S.stateKey state, "priority" .= priority,
             "depth" .= depth, "pending" .= pending, "proof_authority" .= False]) $
            S.pending session state
        measured <- G.cost run
        pure $ either failureView (\principal -> object
          ["status" .= ("retained" :: String), "run" .= key,
           "goal_ids" .= chosen, "cost" .= measured, "principal" .= principal,
           "frontier_size" .= size, "proof_authority" .= False]) viewed

discard :: Store s -> Key -> IO Value
discard (Store _ identity store) key@(Key _ _ number _) = modifyMVar store $ \(serial, entries) ->
  case resolve identity entries key of
    Left reason -> pure ((serial, entries), rejected reason)
    Right (Entry _ _ _ chosen run) -> do
      measured <- G.cost run
      pure ((serial, Map.delete number entries), object
        ["status" .= ("discarded" :: String), "cost" .= measured,
         "goal_ids" .= chosen, "proof_authority" .= False])

resolve :: StateKey -> Map.Map Integer (Entry s) -> Key -> Either String (Entry s)
resolve identity entries (Key nonce epoch number revision)
  | nonce /= keySession identity = Left "foreign-session"
  | epoch /= keyEpoch identity = Left "stale-epoch"
  | otherwise = case Map.lookup number entries of
      Nothing -> Left "unknown-run"
      Just entry@(Entry current _ _ _ _) | revision == current -> Right entry
      _ -> Left "stale-run"

pauseName :: G.PauseReason -> String
pauseName G.SliceEnded = "slice-ended"
pauseName G.AllowanceSpent = "allowance-spent"
pauseName G.ActionsSpent = "action-allowance-spent"
pauseName G.CancelledByCaller = "cancelled"

rejected :: String -> Value
rejected reason = object ["status" .= ("rejected" :: String), "reason" .= reason]

failureView :: Failure -> Value
failureView failure = object
  ["status" .= ("rejected" :: String), "reason" .= failureName failure,
   "detail" .= show failure]
