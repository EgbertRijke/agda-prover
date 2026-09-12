{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
-- SPDX-License-Identifier: GPL-3.0-or-later
-- Transport only. Native checking and branch ownership live in the adapter;
-- no proof or benchmark policy belongs in this module.
module SessionProtocol (serve, ProtocolFailure, protocolFailureName) where

import Control.Concurrent
import Control.Exception qualified as E
import Control.Monad (unless, when)
import Data.Aeson
import Data.Aeson.KeyMap qualified as KM
import Data.Aeson.Types (Parser, Pair, parseEither)
import Data.ByteString qualified as BS
import Data.IORef
import Data.List.NonEmpty (NonEmpty (..))
import Data.List.NonEmpty qualified as NE
import Data.Set qualified as Set
import Numeric.Natural (Natural)
import System.Environment (lookupEnv)
import System.IO (stdin)
import Text.Read (readMaybe)
import Agda.Syntax.Common (InteractionId, interactionId)
import AgdaProver.Agda28.Session qualified as S
import AgdaProver.Agda28.AgendaSearch qualified as G
import AgdaProver.Symbolic.Protocol qualified as P
import AgdaProver.Symbolic.SessionTypes hiding (Pending)
import AgdaProver.Symbolic.Evidence qualified as Search
import AgdaProver.Symbolic.Clause (ClauseAction)
import AgdaProver.Symbolic.NNUE.Model qualified as Model
import AgdaProver.Symbolic.NNUE.Policy qualified as Policy
import AgdaProver.Symbolic.NNUE.Native (withNativeScorer)
import RunControl qualified as Run

data Operation = Pending StateKey | Observe StateKey InteractionId P.ObservationMode
  | Give StateKey InteractionId DraftExpression | Evict StateKey | Replay StateKey
  | SolveEvidence StateKey InteractionId Search.SearchLimits Policy.RankingMode (Maybe FilePath) (Maybe FilePath) (Maybe FilePath) Bool [String]
  | MakeClause StateKey InteractionId ClauseAction
  | ApplyClause StateKey InteractionId ClauseAction
  | ReconstructGoal StateKey InteractionId StateKey
  | ReconstructGoals StateKey (NonEmpty InteractionId) StateKey
  | ExportGoals StateKey (NonEmpty InteractionId) StateKey
  | StartSearch StateKey Search.SearchLimits Policy.RankingMode (Maybe FilePath)
      (Maybe FilePath) (Maybe FilePath) Bool [String] Scheduling
  | AdvanceSearch Run.Key Natural Search.SearchLimits
  | RunCost Run.Key | DiscardSearch Run.Key
  | InferHelper StateKey InteractionId P.ObservationMode DraftExpression
  | SolveHelper StateKey InteractionId Search.SearchLimits Policy.RankingMode (Maybe FilePath) (Maybe FilePath)
      P.ObservationMode DraftExpression
  | Cost | Cancel | Close
data Request = Request Integer Operation
data Active = Active Integer ThreadId (MVar ())
data ProtocolFailure = InvalidFrameBudget | UnterminatedFrame | FrameBudgetExhausted
  deriving Show
instance E.Exception ProtocolFailure

-- Soft ordering/slice settings, not proof-size or depth restrictions.
data Scheduling = Scheduling Natural Natural Natural Bool
instance FromJSON Scheduling where
  parseJSON = withObject "scheduling" $ \o -> do
    unless (Set.fromList (KM.keys o) == Set.fromList
      ["structural_delay", "macro_delay", "initial_macro_work", "evidence_macro"]) $ fail "invalid scheduling fields"
    scheduling@(Scheduling _ _ initial _) <- Scheduling <$> o .: "structural_delay"
      <*> o .: "macro_delay" <*> o .: "initial_macro_work" <*> o .: "evidence_macro"
    unless (initial > 0) $ fail "initial macro allowance must be positive"
    pure scheduling

protocolFailureName :: ProtocolFailure -> String
protocolFailureName InvalidFrameBudget = "invalid-frame-budget"
protocolFailureName UnterminatedFrame = "unterminated-frame"
protocolFailureName FrameBudgetExhausted = "transport-frame-budget-exhausted"

parseRequest :: Value -> Parser Request
parseRequest = withObject "session request" $ \o -> do
  schema <- o .: "schema_version"
  unless (schema == ("agdaprover.symbolic-session-request.v1" :: String)) $
    fail "unsupported request version"
  number <- o .: "request_id"
  unless (number >= 0) $ fail "negative request id"
  operation <- o .: "operation" :: Parser String
  let fields extra = unless
        (Set.fromList (KM.keys o) == Set.fromList (["schema_version", "request_id", "operation"] ++ extra)) $
        fail "unexpected or missing request fields"
      goal = do
        n <- o .: "goal_id" :: Parser Integer
        unless (n >= 0 && n <= toInteger (maxBound :: Int)) $ fail "invalid goal id"
        pure (fromInteger n)
  op <- case operation of
    "pending" -> fields ["state"] >> Pending <$> o .: "state"
    "observe" -> do
      fields ["state", "goal_id", "mode"]
      mode <- o .: "mode" >>= maybe (fail "unknown observation mode") pure . P.parseMode
      Observe <$> o .: "state" <*> goal <*> pure mode
    "give" -> do
      fields ["state", "goal_id", "expression"]
      Give <$> o .: "state" <*> goal <*> (DraftExpression <$> o .: "expression")
    "make-clause" -> do
      fields ["state", "goal_id", "action"]
      MakeClause <$> o .: "state" <*> goal <*> o .: "action"
    "infer-helper" -> do
      fields ["state", "goal_id", "mode", "application"]
      mode <- o .: "mode" >>= maybe (fail "unknown observation mode") pure . P.parseMode
      InferHelper <$> o .: "state" <*> goal <*> pure mode <*> (DraftExpression <$> o .: "application")
    "apply-clause" -> do
      fields ["state", "goal_id", "action"]
      ApplyClause <$> o .: "state" <*> goal <*> o .: "action"
    "reconstruct-goal" -> do
      fields ["state", "goal_id", "descendant"]
      ReconstructGoal <$> o .: "state" <*> goal <*> o .: "descendant"
    opName | opName `elem` ["reconstruct-goals", "export-goals"] -> do
      fields ["state", "goal_ids", "descendant"]
      ids <- o .: "goal_ids" :: Parser [Integer]
      unless (all (\n -> n >= 0 && n <= toInteger (maxBound :: Int)) ids
              && Set.size (Set.fromList ids) == length ids) $ fail "invalid goal ids"
      case ids of
        [] -> fail "empty goal selection"
        first:rest -> (if opName == "export-goals" then ExportGoals else ReconstructGoals) <$> o .: "state"
          <*> pure (fmap fromInteger $ first :| rest) <*> o .: "descendant"
    "start-search" -> do
      fields $ ["state", "limits", "ranker", "model_path", "focused_model_path",
        "native_path", "focused_search", "exclude_names"] ++ filter (`KM.member` o) ["scheduling"]
      mode <- o .: "ranker" >>= \case
        ("nnue" :: String) -> pure Policy.Learned
        "symbolic" -> pure Policy.Symbolic
        _ -> fail "unknown ranker"
      scheduling <- if KM.member "scheduling" o then o .: "scheduling" else pure $ Scheduling 2 8 64 True
      StartSearch <$> o .: "state" <*> o .: "limits" <*> pure mode <*> o .: "model_path"
        <*> o .: "focused_model_path" <*> o .: "native_path" <*> o .: "focused_search"
        <*> o .: "exclude_names" <*> pure scheduling
    "advance-search" -> do
      fields ["run", "steps", "limits"]
      AdvanceSearch <$> o .: "run" <*> o .: "steps" <*> o .: "limits"
    "search-cost" -> fields ["run"] >> RunCost <$> o .: "run"
    "discard-search" -> fields ["run"] >> DiscardSearch <$> o .: "run"
    "solve-helper" -> do
      fields ["state", "goal_id", "limits", "ranker", "model_path", "native_path", "mode", "application"]
      mode <- o .: "ranker" >>= \case
        ("nnue" :: String) -> pure Policy.Learned
        "symbolic" -> pure Policy.Symbolic
        _ -> fail "unknown ranker"
      view <- o .: "mode" >>= maybe (fail "unknown observation mode") pure . P.parseMode
      SolveHelper <$> o .: "state" <*> goal <*> o .: "limits" <*> pure mode
        <*> o .: "model_path" <*> o .: "native_path" <*> pure view <*> (DraftExpression <$> o .: "application")
    "solve-evidence" -> do
      fields $ ["state", "goal_id", "limits", "ranker", "model_path", "native_path", "exclude_names"]
        ++ filter (`KM.member` o) ["focused_model_path", "focused_search"]
      mode <- o .: "ranker" >>= \case
        ("nnue" :: String) -> pure Policy.Learned
        "symbolic" -> pure Policy.Symbolic
        _ -> fail "unknown ranker"
      SolveEvidence <$> o .: "state" <*> goal <*> o .: "limits" <*> pure mode
        <*> o .: "model_path" <*> o .:? "focused_model_path" <*> o .: "native_path"
        <*> (if KM.member "focused_search" o then o .: "focused_search" else pure True)
        <*> o .: "exclude_names"
    "evict" -> fields ["state"] >> Evict <$> o .: "state"
    "replay" -> fields ["state"] >> Replay <$> o .: "state"
    "cost" -> fields [] >> pure Cost
    "cancel" -> fields [] >> pure Cancel
    "close" -> fields [] >> pure Close
    _ -> fail "unknown operation"
  pure $ Request number op

event :: String -> [Pair] -> Value
event name fields = object
  (["schema_version" .= ("agdaprover.symbolic-session-event.v1" :: String), "event" .= name] ++ fields)

failureView :: Failure -> Value
failureView failure = object
  (["status" .= ("rejected" :: String), "reason" .= failureName failure] ++ details)
 where
  details = case failure of
    KernelRejected message -> ["detail" .= message]
    KernelBlocked message -> ["detail" .= message]
    KernelFailure message -> ["detail" .= message]
    ReplayRejected message -> ["detail" .= message]
    _ -> []

-- One active request, no accumulating worker queue. A reader remains available
-- for cancellation while Agda works. A dispatch receipt is published first;
-- a killed process leaves its completion/cost *unknown*, never an invented zero.
serve :: (Value -> IO ()) -> S.Session s -> S.StateRef s -> IO ()
serve output session root = do
  runs <- Run.newStore session root
  outputLock <- newMVar ()
  active <- newMVar Nothing
  serial <- newIORef (-1)
  dispatched <- newIORef (0 :: Integer)
  buffered <- newIORef BS.empty
  limit <- frameLimit
  let emit value = withMVar outputLock $ const (output value)
      control number outcome = do
        cost <- S.work session
        emit $ event "control-result" ["request_id" .= number, "outcome" .= outcome, "cost" .= cost]
      stop = readMVar active >>= mapM_ (\(Active _ thread done) ->
        E.throwTo thread E.ThreadKilled >> readMVar done)
      launch number operation = E.mask_ $ modifyMVar_ active $ \current -> case current of
        Just _ -> control number (object ["status" .= ("busy" :: String)]) >> pure current
        Nothing -> do
          done <- newEmptyMVar
          gate <- newEmptyMVar
          count <- atomicModifyIORef' dispatched (\n -> (n + 1, n + 1))
          emit $ event "operation-start"
            ["request_id" .= number, "dispatched_requests" .= count,
             "completion_known" .= False]
          let retire currentWorker = case currentWorker of
                Just (Active target _ _) | target == number -> Nothing
                _ -> currentWorker
          thread <- forkIOWithUnmask $ \unmask ->
            E.finally (do
              let emitSearch trace = emit $ event "search-policy"
                    ["request_id" .= number, "trace" .= trace]
                  emitRun payload = emit $ event "search-progress"
                    ["request_id" .= number, "payload" .= payload]
              outcome <- (takeMVar gate >> unmask (perform session runs emitSearch emitRun operation)) `E.catches`
                [ E.Handler $ \(err :: E.AsyncException) -> case err of
                    E.ThreadKilled -> pure (failureView Cancelled)
                    _ -> E.throwIO err
                , E.Handler $ \(_ :: E.IOException) -> pure $ failureView (KernelFailure "native-io-failure")
                , E.Handler $ \(_ :: E.SomeException) -> do
                    S.close session
                    pure $ failureView (KernelFailure "native-internal-failure")
                ]
              cost <- S.work session
              modifyMVar_ active $ \currentActive -> do
                emit $ event "operation-result"
                  ["request_id" .= number, "outcome" .= outcome, "cost" .= cost]
                pure (retire currentActive))
              (modifyMVar_ active (pure . retire) >> putMVar done ())
          putMVar gate ()
          pure $ Just (Active number thread done)
      loop = nextFrame limit buffered >>= \case
        Nothing -> pure ()
        Just frame -> case eitherDecodeStrict' frame >>= parseEither parseRequest of
          Left _ -> emit (event "request-rejected" ["reason" .= ("invalid-request" :: String)]) >> loop
          Right (Request number operation) -> do
            previous <- readIORef serial
            if number <= previous then
              emit (event "request-rejected" ["request_id" .= number,
                "reason" .= ("nonincreasing-request-id" :: String)]) >> loop
            else do
              writeIORef serial number
              case operation of
                Close -> stop >> control number (object ["status" .= ("closed" :: String)])
                Cancel -> do
                  victim <- readMVar active
                  case victim of
                    Nothing -> control number (object ["status" .= ("idle" :: String)])
                    Just (Active target thread done) -> do
                      E.throwTo thread E.ThreadKilled
                      readMVar done
                      control number (object ["status" .= ("cancelled" :: String), "target_request_id" .= target])
                  loop
                Cost -> S.work session >>= control number . toJSON >> loop
                _ -> launch number operation >> loop
  emit $ event "session-start" ["state" .= S.stateKey root, "proof_authority" .= False]
  E.finally loop stop
  S.close session
  cost <- S.work session
  emit $ event "session-end" ["cost" .= cost]

perform :: S.Session s -> Run.Store s -> (Value -> IO ()) -> (Value -> IO ()) -> Operation -> IO Value
perform session runs emit emitRun operation = case operation of
  StartSearch key limits mode modelPath focusedPath nativePath focused excluded (Scheduling structural macro initial enabled) ->
    resolved key $ \root -> do
      loaded <- maybe (pure $ Right []) (fmap (fmap (:[])) . Model.loadModel (Just Model.ORDecision)) modelPath
      focusedModel <- maybe (pure $ Right []) (fmap (fmap (:[])) . Model.loadModel (Just Model.FocusedBranch)) focusedPath
      case ((++) <$> loaded <*> focusedModel) >>= Policy.models of
        Left reason -> pure $ failureView $ KernelFailure ("model-configuration:" ++ reason)
        Right models -> Run.start runs root (G.Settings limits mode models focused excluded structural macro initial enabled) nativePath
  AdvanceSearch key steps limits -> Run.advance runs key steps limits emitRun
  RunCost key -> Run.snapshot runs key
  DiscardSearch key -> Run.discard runs key
  Pending key -> resolved key $ \ref -> result toJSON <$> S.pending session ref
  Observe key goal mode -> resolvedGoal key goal $ \ref -> result id <$> S.inspect session ref mode
  MakeClause key goal action -> resolvedGoal key goal $ \ref ->
    result S.clauseView <$> S.makeClauses session ref action
  InferHelper key goal mode expression -> resolvedGoal key goal $ \ref ->
    result S.helperView <$> S.inferHelper session ref mode expression
  ApplyClause key goal action -> resolvedGoal key goal $ \ref -> do
    answer <- S.applyClause session ref action
    checkedResult answer
  ReconstructGoal key goal child -> resolvedGoal key goal $ \ref -> resolved child $ \descendant ->
    S.reconstructGoal session ref descendant >>= checkedResult
  ReconstructGoals key goals child -> resolved key $ \ref -> resolved child $ \descendant -> do
    batch <- S.reconstructGoals session ref goals descendant
    pure $ batchResult $ fmap (fmap $ \(point, checked) -> (point, checked, [])) batch
  ExportGoals key goals child -> resolved key $ \ref -> resolved child $ \descendant -> do
    batch <- S.exportGoals session ref goals descendant
    pure $ batchResult $ fmap (fmap $ \(point, checked, source) -> (point, checked, ["source" .= source])) batch
  Give key goal expression -> resolvedGoal key goal $ \ref -> do
    answer <- S.tryExpression session ref expression
    checkedResult answer
  SolveEvidence key goal limits mode modelPath focusedPath nativePath enableFocused excluded ->
    solve key goal limits mode modelPath focusedPath nativePath enableFocused excluded Nothing
  SolveHelper key goal limits mode modelPath nativePath view expression ->
    solve key goal limits mode modelPath Nothing nativePath False [] (Just (view, expression))
  Evict key -> resolved key $ \ref -> result (const $ object ["status" .= ("evicted" :: String)]) <$> S.evict session ref
  Replay key -> resolved key $ \ref -> result (\state -> object ["state" .= S.stateKey state]) <$> S.replay session ref
  _ -> pure $ failureView (KernelFailure "control-dispatched-as-work")
 where
  batchResult = either failureView $ \transitions ->
    let (_, final, _) = NE.last transitions
        entries = traverse (\(point, checked, extra) -> do
          evidence <- S.evidenceView $ S.transitionEvidence checked
          pure $ object $ ["goal_id" .= interactionId point, "evidence" .= evidence] ++ extra) transitions
    in case entries of
      Left reason -> failureView $ KernelFailure reason
      Right values -> object ["state" .= S.stateKey (S.transitionState final),
        "status" .= kindName (S.transitionKind final), "pending" .= S.transitionPending final,
        "entries" .= values, "proof_authority" .= False]
  solve key goal limits mode modelPath focusedPath nativePath enableFocused excluded helper = resolvedGoal key goal $ \ref -> do
    loaded <- maybe (pure $ Right []) (fmap (fmap (:[])) . Model.loadModel (Just Model.ORDecision)) modelPath
    focused <- maybe (pure $ Right []) (fmap (fmap (:[])) . Model.loadModel (Just Model.FocusedBranch)) focusedPath
    case ((++) <$> loaded <*> focused) >>= Policy.models of
      Left reason -> pure $ failureView $ KernelFailure ("model-configuration:" ++ reason)
      Right models -> withNativeScorer nativePath $ \native -> do
        (stats, answer) <- case helper of
          Nothing -> S.solveEvidence session ref limits models mode native enableFocused excluded emit
          Just (view, expression) -> S.solveHelper session ref limits models mode native view expression emit
        case answer of
          Left failure -> pure $ object ["search_cost" .= stats, "failure" .= failureView failure]
          Right (status, candidate, selected) -> do
            value <- case candidate of
              Nothing -> pure Null
              Just checked -> case S.evidenceView (S.transitionEvidence checked) of
                Left reason -> S.close session >> pure (failureView $ KernelFailure reason)
                Right evidence -> pure $ transition checked evidence
            pure $ object ["status" .= Search.statusName status, "search_cost" .= stats,
              "candidate" .= value, "selected_choices" .= selected,
              "model_id" .= either (const Nothing) (fmap Model.modelId . safeHead) loaded,
              "focused_model_id" .= either (const Nothing) (fmap Model.modelId . safeHead) focused,
              "proof_authority" .= False]
  resolved key action = either (pure . failureView) action (S.restoreReference session key)
  resolvedGoal key goal action = either (pure . failureView) action (S.restoreGoalReference session key goal)
  result encodeResult = either failureView encodeResult
  safeHead [] = Nothing
  safeHead (x:_) = Just x
  checkedResult = either (pure . failureView) $ \checked ->
    case S.evidenceView (S.transitionEvidence checked) of
      Left reason -> S.close session >> pure (failureView $ KernelFailure reason)
      Right evidence -> pure $ transition checked evidence
  transition t evidence = object
      ["status" .= kindName (S.transitionKind t), "state" .= S.stateKey (S.transitionState t),
       "pending" .= S.transitionPending t, "evidence" .= evidence, "proof_authority" .= False]

-- A configurable transport envelope, not a proof-size/depth search policy.
-- Read bounded chunks so an unterminated oversized line cannot allocate without
-- limit. The external supervisor remains responsible for process resources.
frameLimit :: IO Int
frameLimit = lookupEnv "AGDAPROVER_SYMBOLIC_FRAME_BYTES" >>= \case
  Nothing -> pure (16 * 1024 * 1024)
  Just text -> case readMaybe text :: Maybe Integer of
    Just n | n > 0 && n <= toInteger (maxBound :: Int) -> pure (fromInteger n)
    _ -> E.throwIO InvalidFrameBudget

nextFrame :: Int -> IORef BS.ByteString -> IO (Maybe BS.ByteString)
nextFrame limit buffered = readIORef buffered >>= go [] 0
 where
  go chunks size bytes = case BS.elemIndex 10 bytes of
    Just offset -> do
      when (offset > limit - size) oversized
      let (line, rest) = BS.splitAt offset bytes
      writeIORef buffered (BS.drop 1 rest)
      pure $ Just $ BS.concat (reverse (line : chunks))
    Nothing -> do
      when (BS.length bytes > limit - size) oversized
      let total = size + BS.length bytes
      new <- BS.hGetSome stdin (1 + min 65535 (limit - total))
      if BS.null new then
        if total == 0 then pure Nothing else
          E.throwIO UnterminatedFrame
      else go (bytes : chunks) total new
  oversized = E.throwIO FrameBudgetExhausted
