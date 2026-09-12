{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
-- SPDX-License-Identifier: GPL-3.0-or-later
module AgdaProver.Agda28.Session
  ( Session, StateRef, GoalRef, CheckedEvidence, Transition
  , withSession, stateKey, restoreReference, restoreGoalReference, goalState, goalId
  , inspect, pending, tryExpression
  , solveEvidence
  , ClauseProposal, makeClauses, clauseView, applyClause
  , transitionState, transitionKind, transitionPending, transitionEvidence
  , evict, replay, close, cancel, work, evidenceView
  ) where

import Control.Concurrent (MVar, ThreadId, myThreadId, newMVar, modifyMVar, readMVar)
import Control.Exception qualified as E
import Control.Monad (unless, forM)
import Control.Monad.Except (catchError)
import Control.Monad.IO.Class (liftIO)
import Control.Monad.State.Strict (runStateT)
import Data.Aeson (Value, object, (.=))
import Data.ByteString qualified as BS
import Data.IORef
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set
import Data.Text qualified as T
import Data.Text.Lazy qualified as TL
import Data.Word (Word64)
import GHC.Clock (getMonotonicTimeNSec)
import Numeric (showHex)
import System.CPUTime (getCPUTime)
import System.Directory (canonicalizePath)
import System.Random (randomIO)

import Agda.Interaction.BasicOps (parseExprIn, give_)
import Agda.Interaction.Base (UseForce (WithoutForce))
import Agda.Syntax.Abstract qualified as A
import Agda.Syntax.Common (InteractionId, interactionId, NameId)
import Agda.Syntax.Common.Pretty (prettyShow)
import Agda.Syntax.Internal qualified as I
import Agda.Syntax.Position (noRange)
import Agda.TypeChecking.Errors (prettyError)
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Pretty (prettyTCM)
import Agda.TypeChecking.Reduce (instantiateFull)
import Agda.Utils.FileName (filePath)
import Agda.Utils.IO.UTF8 qualified as UTF8
import Agda.Utils.Lens ((^.))
import AgdaProver.Agda28.Observation (observeGoal, encodeGoal, openInteractionPoints)
import AgdaProver.Agda28.EvidenceSearch qualified as Search
import AgdaProver.Agda28.Clauses qualified as Clauses
import AgdaProver.Agda28.ClauseExecution qualified as ClauseExecution
import AgdaProver.Agda28.Recursion qualified as Recursion
import AgdaProver.Symbolic.Clause (ClauseAction)
import AgdaProver.Symbolic.Evidence qualified as Search
import AgdaProver.Symbolic.NNUE.Native (NativeScorer)
import AgdaProver.Symbolic.NNUE.Policy qualified as Policy
import AgdaProver.Symbolic.Protocol (ObservationMode)
import AgdaProver.Symbolic.SessionTypes
import Structure qualified as S

-- The phantom is nominal, not coercible: a native term has meaning only in its
-- owner's epoch and branch. Wire keys cannot construct these values directly.
type role Session nominal
data Session s = Session
  { sessionNonce :: String, sessionOwner :: MVar Owner, sessionEnv :: TCEnv
  , sessionInputs :: [SourceWitness], sessionWork :: IORef Work
  , sessionActive :: IORef (Maybe ThreadId)
  }
type role StateRef nominal
newtype StateRef s = StateRef StateKey
type role GoalRef nominal
data GoalRef s = GoalRef { goalState :: StateRef s, goalId :: InteractionId }
type role CheckedEvidence nominal
data CheckedEvidence s = CheckedEvidence
  { evidenceState :: StateRef s, evidenceDisplay :: String
  , evidenceTerm :: I.Term, evidenceType :: I.Type, evidenceContext :: I.Telescope
  }
type role Transition nominal
data Transition s = Transition
  { transitionState :: StateRef s, transitionKind :: TransitionKind
  , transitionPending :: Pending, transitionEvidence :: CheckedEvidence s }

-- A planning snapshot is not an accepted child state. Native syntax and the
-- state in which it was generated travel together under the parent's brand.
type role ClauseProposal nominal
data ClauseProposal s = ClauseProposal (GoalRef s) Clauses.ClauseSnapshot TCState

-- Preserve checked-source abstract syntax as well as internal evidence. Agda's
-- display reifier may use postfix projections: display syntax is not a draft
-- to send straight back to checkExpr without scope elaboration.
data Allocation = Allocation NameId InteractionId
data Draft = TextDraft DraftExpression | NativeDraft A.Expr Allocation
data DraftAction = DraftAction InteractionId Draft
data Branch = Branch
  { branchState :: Maybe TCState, branchTrail :: Maybe (Integer, DraftAction)
  , branchOrigins :: Map.Map InteractionId (Maybe Recursion.Owner) }
data Owner = Owner
  { ownerEpoch :: Integer, ownerClosed :: Bool, ownerNext :: Integer
  , ownerBranches :: Map.Map Integer Branch }
data SourceWitness = SourceWitness FilePath FilePath BS.ByteString

stateKey :: StateRef s -> StateKey
stateKey (StateRef key) = key

-- This conversion checks the session brand only. Every operation additionally
-- checks the epoch, branch residency and pinned inputs while holding the owner.
restoreReference :: Session s -> StateKey -> Either Failure (StateRef s)
restoreReference session key
  | keySession key /= sessionNonce session = Left ForeignSession
  | otherwise = Right (StateRef key)

restoreGoalReference :: Session s -> StateKey -> InteractionId -> Either Failure (GoalRef s)
restoreGoalReference session key point = GoalRef <$> restoreReference session key <*> pure point

-- Agda's loaded interface carries the source it actually checked, including
-- imported modules. Pin that text and the current exact bytes/path together;
-- neither a filesystem timestamp nor a hash collision can validate an epoch.
withSession :: Interface -> (forall s. Session s -> StateRef s -> IO a) -> TCM a
withSession root use = do
  visited <- useTC stVisitedModules
  mapping <- moduleToSourceId <$> useTC stModuleToSource
  let interfaces = Map.insert (iTopLevelModuleName root) root $
        Map.map miInterface visited
  sources <- forM (Map.toAscList interfaces) $ \(name, iface) ->
    case Map.lookup name mapping of
      Nothing -> genericError "symbolic-session-missing-source"
      Just source -> (, iSource iface) . filePath <$> srcFilePath source
  env <- askTC
  points <- openInteractionPoints
  origins <- Map.fromList <$> forM points (\point -> (point,) <$> Recursion.owner point)
  initial <- getTC
  liftIO $ do
    ledger <- newIORef emptyWork
    witnesses <- mapM (pin ledger) sources
    a <- randomIO :: IO Word64
    b <- randomIO :: IO Word64
    owner <- newMVar $ Owner 0 False 1 (Map.singleton 0 $ Branch (Just initial) Nothing origins)
    active <- newIORef Nothing
    let nonce = showHex a "-" ++ showHex b ""
        session = Session nonce owner env witnesses ledger active
        rootRef = StateRef $ StateKey nonce 0 0
    E.finally (use session rootRef) (close session)

pin :: IORef Work -> (FilePath, TL.Text) -> IO SourceWitness
pin ledger (path, expected) = do
  canonical <- canonicalizePath path
  before <- readCharged ledger path
  actual <- UTF8.readTextFile path
  -- UTF8 reads a second time; force it before the second byte witness.
  same <- E.evaluate (actual == expected)
  charge ledger $ \w -> w { inputBytesRead = inputBytesRead w + toInteger (BS.length before) }
  after <- readCharged ledger path
  canonicalAfter <- canonicalizePath path
  unless (same && before == after && canonical == canonicalAfter) $
    E.throwIO $ userError "symbolic-session-source-changed-during-load"
  pure $ SourceWitness path canonical after

charge :: IORef Work -> (Work -> Work) -> IO ()
charge ref f = atomicModifyIORef' ref (\w -> (f w, ()))

readCharged :: IORef Work -> FilePath -> IO BS.ByteString
readCharged ledger path = do
  bytes <- BS.readFile path
  charge ledger $ \w -> w { inputBytesRead = inputBytesRead w + toInteger (BS.length bytes) }
  pure bytes

inputsMatch :: Session s -> IO Bool
inputsMatch session = go (sessionInputs session) `E.catch` \(_ :: E.IOException) -> pure False
 where
  go [] = pure True
  go (SourceWitness path canonical bytes : rest) = do
    pathNow <- canonicalizePath path
    bytesNow <- readCharged (sessionWork session) path
    if pathNow == canonical && bytesNow == bytes then go rest else pure False

work :: Session s -> IO Work
work = readIORef . sessionWork

-- All restorable Agda state lives in the MVar value. The ledger and active
-- thread do not: modifyMVar restores the original owner if checking is cancelled
-- or raises an IO exception. No speculative TCState is then published.
request :: Session s -> StateRef s
        -> (Owner -> TCState -> IO (Owner, Either Failure a))
        -> IO (Either Failure a)
request session ref action = recover $ modifyMVar (sessionOwner session) $ \owner ->
  E.bracket begin finish $ \_ -> do
    case lookupState session ref owner of
      Left failure -> pure (owner, Left failure)
      Right state -> do
        valid <- inputsMatch session
        if not valid then pure (invalidate owner, Left StaleInputs)
        else do
          result <- action owner state
          stillValid <- inputsMatch session
          pure $ if stillValid then result else (invalidate owner, Left StaleInputs)
 where
  ledger = sessionWork session
  begin = do
    wall <- getMonotonicTimeNSec
    cpu <- getCPUTime
    thread <- myThreadId
    writeIORef (sessionActive session) (Just thread)
    charge ledger $ \w -> w { requests = requests w + 1 }
    pure (wall, cpu)
  finish (wall, cpu) = do
    writeIORef (sessionActive session) Nothing
    end <- getMonotonicTimeNSec
    endCPU <- getCPUTime
    charge ledger $ \w -> w
      { elapsedNanoseconds = elapsedNanoseconds w + toInteger (end - wall)
      , cpuPicoseconds = cpuPicoseconds w + endCPU - cpu }
  recover io = io `E.catches`
    [ E.Handler $ \(e :: E.AsyncException) -> case e of
        E.ThreadKilled -> do
          charge ledger $ \w -> w { cancelledRequests = cancelledRequests w + 1 }
          pure (Left Cancelled)
        _ -> E.throwIO e
    , E.Handler $ \(_ :: E.IOException) -> pure $ Left (KernelFailure "native-io-failure")
    ]

lookupState :: Session s -> StateRef s -> Owner -> Either Failure TCState
lookupState session (StateRef key) owner
  | keySession key /= sessionNonce session = Left ForeignSession
  | ownerClosed owner = Left ClosedSession
  | keyEpoch key /= ownerEpoch owner = Left StaleEpoch
  | otherwise = case Map.lookup (keyBranch key) (ownerBranches owner) of
      Nothing -> Left UnknownState
      Just branch -> maybe (Left EvictedState) Right (branchState branch)

invalidate :: Owner -> Owner
invalidate owner = owner { ownerEpoch = ownerEpoch owner + 1, ownerBranches = Map.empty }

close :: Session s -> IO ()
close session = modifyMVar (sessionOwner session) $ \owner ->
  pure ((invalidate owner) { ownerClosed = True }, ())

-- No lock on the owner: cancellation must work while the checker owns it.
cancel :: Session s -> IO Bool
cancel session = readIORef (sessionActive session) >>= \case
  Nothing -> pure False
  Just thread -> E.throwTo thread E.ThreadKilled >> pure True

kernel :: Session s -> TCState -> TCM a -> IO (Either Failure a, TCState)
kernel session initial action = runTCM (sessionEnv session) initial $
  (Right <$> action) `catchError` (fmap Left . failure)
 where
  failure err = case err of
    PatternErr{} -> pure $ KernelBlocked "checker-postponed"
    TypeError{} -> KernelRejected . prettyShow <$> prettyError err
    ParserError{} -> KernelRejected . prettyShow <$> prettyError err
    GenericException message -> pure $ KernelFailure message
    IOException{} -> pure $ KernelFailure "checker-io-failure"

pendingTC :: TCM Pending
pendingTC = Pending <$> (map interactionId <$> openInteractionPoints)
                    <*> (length <$> getOpenMetas) <*> (length <$> getAllConstraints)

pending :: Session s -> StateRef s -> IO (Either Failure Pending)
pending session ref = request session ref $ \owner state -> do
  (result, _) <- kernel session state pendingTC
  pure (owner, result)

inspect :: Session s -> GoalRef s -> ObservationMode -> IO (Either Failure Value)
inspect session goal mode = request session (goalState goal) $ \owner state -> do
  let point = goalId goal
  (result, _) <- kernel session state $ do
    exists <- elem point <$> openInteractionPoints
    if not exists then pure $ Left UnknownGoal else do
      snapshot <- observeGoal point mode
      pure $ either (Left . KernelFailure) Right (encodeGoal snapshot)
  pure (owner, result >>= id)

tryExpression :: Session s -> GoalRef s -> DraftExpression
              -> IO (Either Failure (Transition s))
tryExpression session goal expression = request session (goalState goal) $ \owner state ->
  check session owner (goalState goal) state (DraftAction (goalId goal) $ TextDraft expression) False

makeClauses :: Session s -> GoalRef s -> ClauseAction -> IO (Either Failure (ClauseProposal s))
makeClauses session goal action = request session (goalState goal) $ \owner state -> do
  charge (sessionWork session) $ \w -> w
    { checkingAttempts = checkingAttempts w + 1, clauseQueries = clauseQueries w + 1 }
  let point = goalId goal
  (generated, planningState) <- kernel session state $ do
    exists <- elem point <$> openInteractionPoints
    if not exists then pure $ Left UnknownGoal else Right <$> Clauses.generate point action
  let result = generated >>= id
  case result of
    Left _ -> charge (sessionWork session) $ \w -> w { rejectedChecks = rejectedChecks w + 1 }
    Right _ -> pure ()
  pure (owner, (\snapshot -> ClauseProposal goal snapshot planningState) <$> result)

clauseView :: ClauseProposal s -> Value
clauseView (ClauseProposal goal snapshot _) = object
  ["parent" .= stateKey (goalState goal), "goal_id" .= interactionId (goalId goal)
  ,"proposal" .= Clauses.view snapshot, "proof_authority" .= False]

applyClause :: Session s -> GoalRef s -> ClauseAction -> IO (Either Failure (Transition s))
applyClause session goal action = request session (goalState goal) $ \owner state -> do
  let chargeStep step = liftIO $ charge (sessionWork session) $ \w -> w
        { checkingAttempts = checkingAttempts w + 1
        , clauseQueries = clauseQueries w + case step of
            ClauseExecution.GenerateClauses -> 1
            _ -> 0 }
  (prepared, allocation) <- kernel session state $ do
    exists <- elem (goalId goal) <$> openInteractionPoints
    if not exists then pure $ Left UnknownGoal
      else Right <$> ClauseExecution.prepare chargeStep (goalId goal) action
  case prepared >>= id of
    Left failure -> do
      charge (sessionWork session) $ \w -> w { rejectedChecks = rejectedChecks w + 1 }
      pure (owner, Left failure)
    Right expression -> check session owner (goalState goal) allocation
      (DraftAction (goalId goal) $ nativeDraft expression allocation) False

nativeDraft :: A.Expr -> TCState -> Draft
nativeDraft expression state = NativeDraft expression $
  Allocation (state ^. stFreshNameId) (state ^. stFreshInteractionId)

reserveAllocation :: Allocation -> TCM ()
reserveAllocation (Allocation name point) = do
  stFreshNameId `modifyTCLens` max name
  stFreshInteractionId `modifyTCLens` max point

-- One coarse request owns all speculative choices. Costs live outside TCM and
-- survive cancellation. A winning native term is rechecked from the ORIGINAL
-- parent: no speculative constraints or warnings are silently published.
solveEvidence :: Session s -> GoalRef s -> Search.SearchLimits -> Policy.Models
              -> Policy.RankingMode -> Maybe (NativeScorer n) -> [String]
              -> (Value -> IO ())
              -> IO (Search.SearchStats, Either Failure
                   (Search.SearchStatus, Maybe (Transition s), [(T.Text,T.Text)]))
solveEvidence session goal limits models mode native excluded emit = do
  stats <- newIORef Search.emptyStats
  outcome <- request session (goalState goal) $ \owner state -> do
    ledger <- work session
    let point = goalId goal
        namespace = show (stateKey $ goalState goal) ++ ":" ++ show (requests ledger)
        origin = Map.lookup (keyBranch $ stateKey $ goalState goal) (ownerBranches owner)
          >>= Map.findWithDefault Nothing point . branchOrigins
    (searched, allocation) <- kernel session state $ do
      exists <- elem point <$> openInteractionPoints
      if not exists then pure $ Left UnknownGoal else withInteractionId point $ do
        meta <- lookupInteractionId point
        target <- getMetaTypeInContext meta
        let validate expression = do
              warnings <- useTC stTCWarnings
              _ <- give_ False WithoutForce point Nothing expression
              maybe (pure ()) (`Recursion.checkOwner` expression) origin
              changed <- Set.difference <$> useTC stTCWarnings <*> pure warnings
              let bad = filter (not . expectedWarning) (Set.toAscList changed)
              unless (null bad) $ genericError $ unlines $ map tcWarningString bad
        Right <$> Search.run stats limits models mode native emit namespace excluded point origin validate target
    case searched >>= id of
      Left failure -> pure (owner, Left failure)
      Right (Search.Result status Nothing selected) -> pure (owner, Right (status, Nothing, selected))
      Right (Search.Result status (Just term) selected) -> do
        (next, checked) <- check session owner (goalState goal) state
          (DraftAction point $ nativeDraft term allocation) False
        pure (next, (\transition -> (status, Just transition, selected)) <$> checked)
  observed <- readIORef stats
  charge (sessionWork session) $ \w -> w
    { checkingAttempts = checkingAttempts w + Search.workUnits observed
    , rejectedChecks = rejectedChecks w + Search.rejectedQueries observed }
  pure (observed, outcome)

check :: Session s -> Owner -> StateRef s -> TCState -> DraftAction -> Bool
      -> IO (Owner, Either Failure (Transition s))
check session owner parent initial draft@(DraftAction point expression) isReplay = do
  let previous = maybe Map.empty branchOrigins $
        Map.lookup (keyBranch $ stateKey parent) (ownerBranches owner)
      origin = Map.findWithDefault Nothing point previous
  charge (sessionWork session) $ \w -> w
    { checkingAttempts = checkingAttempts w + 1
    , replayedActions = replayedActions w + if isReplay then 1 else 0 }
  (result, child) <- kernel session initial $ do
    exists <- elem point <$> openInteractionPoints
    if not exists then pure (Left UnknownGoal) else withInteractionId point $ do
      warnings <- useTC stTCWarnings
      meta <- lookupInteractionId point
      target <- getMetaTypeInContext meta
      telescope <- getContextTelescope
      scoped <- case expression of
        TextDraft text -> parseExprIn point noRange (draftSource text)
        NativeDraft scoped allocation -> reserveAllocation allocation >> ClauseExecution.registerDraft scoped
      -- Same transition as Agda's give, retaining its *returned* internal term
      -- rather than guessing how the meta's context permutation applies.
      checked <- give_ False WithoutForce point Nothing scoped
      maybe (pure ()) (`Recursion.checkOwner` scoped) origin
      removeInteractionPoint point
      display <- prettyShow <$> prettyTCM scoped
      term <- instantiateFull checked
      obligations <- pendingTC
      newWarnings <- Set.difference <$> useTC stTCWarnings <*> pure warnings
      let bad = filter (not . expectedWarning) (Set.toAscList newWarnings)
      pure $ if null bad then Right (display, term, target, telescope, obligations)
        else Left $ KernelRejected $ unlines (map tcWarningString bad)
  case result >>= id of
    Left failure -> do
      charge (sessionWork session) $ \w -> w { rejectedChecks = rejectedChecks w + 1 }
      pure (owner, Left failure)
    Right (abstract, term, target, telescope, obligations) -> do
      charge (sessionWork session) $ \w -> w { acceptedChecks = acceptedChecks w + 1 }
      let number = ownerNext owner
          ref = StateRef $ StateKey (sessionNonce session) (ownerEpoch owner) number
          origins = Map.fromList
            [(p, Map.findWithDefault origin p previous)
            | number' <- pendingGoals obligations, let p = fromIntegral number']
          branch = Branch (Just child) (Just (keyBranch $ stateKey parent, draft)) origins
          next = owner { ownerNext = number + 1,
                         ownerBranches = Map.insert number branch (ownerBranches owner) }
          kind | not (null $ pendingGoals obligations) = AcceptedPartial
               | pendingMetas obligations > 0 || pendingConstraints obligations > 0 = AcceptedBlocked
               | otherwise = ApparentlyClosed
      pure (next, Right $ Transition ref kind obligations $
        CheckedEvidence ref abstract term target telescope)

expectedWarning :: TCWarning -> Bool
expectedWarning warning = case tcWarning warning of
  UnsolvedInteractionMetas{} -> True
  UnsolvedMetaVariables{} -> True
  UnsolvedConstraints{} -> True
  _ -> False

-- Rendering is only a presentation. The native tree, telescope, and its branch
-- brand remain in the opaque evidence for the future in-process search.
evidenceView :: CheckedEvidence s -> Either String Value
evidenceView evidence = do
  ((term, target, context), encoded) <- flip runStateT S.withAtoms $
    (,,) <$> S.term 0 (evidenceTerm evidence) <*> S.typ 0 (evidenceType evidence)
         <*> S.telescope 0 (evidenceContext evidence)
  pure $ object ["state" .= stateKey (evidenceState evidence),
    "term" .= term, "type" .= target, "context" .= context,
    "names" .= S.names encoded, "display" .= evidenceDisplay evidence,
    "proof_authority" .= False]

evict :: Session s -> StateRef s -> IO (Either Failure ())
evict session ref = request session ref $ \owner _ ->
  let number = keyBranch (stateKey ref) in
  if number == 0 then pure (owner, Left CannotEvictRoot) else
  pure (owner { ownerBranches = Map.adjust (\b -> b { branchState = Nothing })
                 number (ownerBranches owner) }, Right ())

-- Replay deliberately creates new branch identities. Even equal-looking
-- observations cannot witness equality of arbitrary TCStates or old evidence.
-- The root is retained; replay walks to the nearest resident ancestor.
replay :: Session s -> StateRef s -> IO (Either Failure (StateRef s))
replay session ref = do
  owner <- readMVar (sessionOwner session)
  let key = stateKey ref
      rootRef = StateRef key { keyBranch = 0 }
  -- Use the ordinary serialized operation/epoch/input checks, but permit the
  -- requested child to be evicted. Resolve its trail only *inside* the lock.
  if ownerClosed owner then pure (Left ClosedSession) else
    request session rootRef $ \current _ -> case trail current (keyBranch key) [] of
      Left failure -> pure (current, Left failure)
      Right (ancestor, state, actions) ->
        go current (StateRef key { keyBranch = ancestor }) state actions
 where
  trail owner number actions = case Map.lookup number (ownerBranches owner) of
    Nothing -> Left UnknownState
    Just branch -> case branchState branch of
      Just state -> Right (number, state, actions)
      Nothing -> case branchTrail branch of
        Just (parent, draft) -> trail owner parent (draft : actions)
        Nothing -> Left EvictedState
  go owner parent _ [] = pure (owner, Right parent)
  go owner parent state (draft : rest) = do
    (next, outcome) <- check session owner parent state draft True
    case outcome of
      Left failure -> pure (owner, Left $ ReplayRejected (failureName failure))
      Right transition -> case lookupState session (transitionState transition) next of
        Left failure -> pure (owner, Left failure)
        Right child -> go next (transitionState transition) child rest
