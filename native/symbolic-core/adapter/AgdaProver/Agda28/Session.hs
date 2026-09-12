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
  , Configuration, pinConfiguration, pinRuntimeConfiguration, withSessionConfiguration
  , withSessionConfigurationReuse
  , inspect, pending, tryExpression
  , DependencySnapshot, dependencies, dependencyView, orderDependentGoals, constrainingGoals
  , solveEvidence, solveEvidenceAtDepth, solveHelper, RefutationProposal, proposeRefutation, refutationView, refutationKind
  , Refutation.Kind (..)
  , ClauseProposal, makeClauses, clauseView, applyClause
  , reconstructGoal, reconstructGoals, exportGoals
  , TermProposal, TermProposals (..), termProposalGoal, termProposalChoices, preferStructures, withoutResultIntroductionOverlap, proposeTerms, proposeTermsWithTargetOperands, proposeStructures, proposeEquations, proposeConstructors, applyTerm
  , ClauseMove, clauseMoveGoal, clauseMoveIsBatch, applyClauseMove, ClauseProposals (..), proposeClauseActions
  , HelperProposal, inferHelper, helperView
  , transitionState, transitionKind, transitionPending, transitionEvidence
  , evict, replay, close, cancel, work, evidenceView
  ) where

import Control.Concurrent (MVar, ThreadId, myThreadId, newMVar, modifyMVar, readMVar)
import Control.Exception qualified as E
import Control.Monad (unless, when, forM)
import Control.Monad.Except (catchError)
import Control.Monad.IO.Class (liftIO)
import Control.Monad.State.Strict (runStateT)
import Data.Aeson (Value, object, (.=))
import Data.ByteString qualified as BS
import Data.IORef
import Data.List.NonEmpty (NonEmpty (..))
import Data.List.NonEmpty qualified as NE
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
import Agda.Interaction.Library (getPrimitiveLibDir, getAgdaLibFile, AgdaLibFile (..))
import Agda.Interaction.Library.Base (agdaLibFiles, runLibM)
import Agda.Syntax.Abstract qualified as A
import Agda.Syntax.Abstract.Views (unScope)
import Agda.Syntax.Common (InteractionId, interactionId, NameId, ArgInfo, Arg (..), Named (..))
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
import Agda.Utils.Null (empty)
import AgdaProver.Agda28.Observation (observeGoal, encodeGoal, openInteractionPoints)
import AgdaProver.Agda28.EvidenceSearch qualified as Search
import AgdaProver.Agda28.Clauses qualified as Clauses
import AgdaProver.Agda28.Helpers qualified as Helpers
import AgdaProver.Agda28.ClauseExecution qualified as ClauseExecution
import AgdaProver.Agda28.Recursion qualified as Recursion
import AgdaProver.Agda28.DraftAssembly qualified as Assembly
import AgdaProver.Agda28.Source qualified as Source
import AgdaProver.Agda28.Refutation qualified as Refutation
import AgdaProver.Agda28.Dependencies qualified as Dependencies
import AgdaProver.Symbolic.Clause (ClauseAction)
import AgdaProver.Symbolic.Clause qualified as Clause
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
  { sessionNonce :: String, sessionOwner :: MVar (Owner s), sessionEnv :: TCEnv
  , sessionInputs :: [SourceWitness], sessionWork :: IORef Work
  , sessionActive :: IORef (Maybe ThreadId)
  , sessionReuse :: ReusePolicy
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

type role HelperProposal nominal
data HelperProposal s = HelperProposal (GoalRef s) Helpers.Snapshot TCState

type role RefutationProposal nominal
data RefutationProposal s = RefutationProposal (GoalRef s) Refutation.Snapshot

type role DependencySnapshot nominal
data DependencySnapshot s = DependencySnapshot (StateRef s) Dependencies.Snapshot

dependencyView :: DependencySnapshot s -> Value
dependencyView (DependencySnapshot parent snapshot) = object
  ["parent" .= stateKey parent, "dependencies" .= Dependencies.view snapshot]

orderDependentGoals :: StateRef s -> DependencySnapshot s -> [Int] -> Either Failure [Int]
orderDependentGoals parent (DependencySnapshot original snapshot) selected
  | stateKey parent /= stateKey original = Left $ KernelFailure "dependency-parent-mismatch"
  | otherwise = Right $ Dependencies.orderGoals snapshot selected

constrainingGoals :: StateRef s -> DependencySnapshot s -> [Int] -> Either Failure [Int]
constrainingGoals parent (DependencySnapshot original snapshot) selected
  | stateKey parent /= stateKey original = Left $ KernelFailure "dependency-parent-mismatch"
  | otherwise = Right $ Dependencies.constrainingGoals snapshot selected

refutationKind :: RefutationProposal s -> Refutation.Kind
refutationKind (RefutationProposal _ snapshot) = Refutation.kind snapshot

refutationView :: RefutationProposal s -> Value
refutationView (RefutationProposal goal snapshot) = object $
  ("parent" .= stateKey (goalState goal)) : Refutation.viewFields (goalId goal) snapshot

type role TermProposal nominal
data TermProposal s = TermProposal (GoalRef s) Draft [(T.Text, T.Text)] ActionIdentity

data TermProposals s = CompleteTerms [TermProposal s] | CensoredTerms [TermProposal s]

type role ClauseMove nominal
data ClauseMove s = ClauseMove (GoalRef s) ClauseExecution.Intent
data ClauseProposals s = CompleteClauses [(ClauseMove s, [(T.Text, T.Text)])]
  | CensoredClauses [(ClauseMove s, [(T.Text, T.Text)])]

clauseMoveGoal :: ClauseMove s -> GoalRef s
clauseMoveGoal (ClauseMove goal _) = goal

clauseMoveIsBatch :: ClauseMove s -> Bool
clauseMoveIsBatch (ClauseMove _ (ClauseExecution.BoundSubjects (_ :| (_:_)))) = True
clauseMoveIsBatch _ = False

termProposalGoal :: TermProposal s -> GoalRef s
termProposalGoal (TermProposal goal _ _ _) = goal

termProposalChoices :: TermProposal s -> [(T.Text, T.Text)]
termProposalChoices (TermProposal _ _ choices _) = choices

-- Prefer the compound catalogue's position without enqueuing a second copy
-- of the ordinary lambda-to-fresh-hole move. Both come from the same sealed
-- parent and goal, with the same binder modality. This narrowly witnessed
-- action overlap does not identify arbitrary alpha-equivalent proof states,
-- populated bodies, repeated holes or helper definitions.
preferStructures :: [TermProposal s] -> [TermProposal s] -> [TermProposal s]
preferStructures structures ordinary = structures ++ filter (not . duplicate) ordinary
 where
  duplicate proposal = case lambdaIntroduction proposal of
    Nothing -> False
    Just key -> any ((== Just key) . lambdaIntroduction) structures

lambdaIntroduction :: TermProposal s -> Maybe (StateKey, InteractionId, ArgInfo)
lambdaIntroduction (TermProposal goal (NativeDraft expression _) _ _) = case unScope expression of
  A.Lam _ (A.DomainFree tactic (Arg info (Named Nothing (A.Binder Nothing _ _)))) body
    | tactic == empty, A.QuestionMark{} <- unScope body ->
        Just (stateKey $ goalState goal, goalId goal, info)
  _ -> Nothing
lambdaIntroduction _ = Nothing

-- Autonomous search uses its existing scoped lambda to expose a function
-- binder instead of also opening a result-split helper for the same goal.
-- This chooses an introduction route, not equality of the resulting states.
-- Keep all subject eliminations, actual record-result splits, and unknown
-- cases. The command catalogue and one-step interaction remain unchanged.
withoutResultIntroductionOverlap :: [TermProposal s] -> [(ClauseMove s, a)] -> [(ClauseMove s, a)]
withoutResultIntroductionOverlap terms = filter $ \(ClauseMove goal intent, _) ->
  intent /= ClauseExecution.UserAction Clause.splitResult ||
    not (Set.member (stateKey $ goalState goal, goalId goal) introduced)
 where
  introduced = Set.fromList [(state, point) | Just (state, point, _) <- map lambdaIntroduction terms]

-- Preserve checked-source abstract syntax as well as internal evidence. Agda's
-- display reifier may use postfix projections: display syntax is not a draft
-- to send straight back to checkExpr without scope elaboration.
-- A replay recipe must not retain a suspended lens read of the entire TCState.
-- Force the small allocation watermark when sealing the recipe, not only when
-- it is replayed: its source checkpoint may be evicted long before then.
data Allocation = Allocation !NameId !InteractionId
data Draft = TextDraft DraftExpression | NativeDraft A.Expr !Allocation
data DraftAction = DraftAction !InteractionId !Draft
-- Agda's A.Expr equality deliberately ignores some scope/presentation fields.
-- Do not use it (or a rendered/hashed type) as an exact application witness.
-- An issued identity seals the original proposal's full native draft/allocation.
data ActionIdentity = SourceAction String | IssuedAction Integer Integer
  deriving (Eq, Ord)
data ApplicationKey = ApplicationKey StateKey InteractionId ActionIdentity
  deriving (Eq, Ord)
data Branch = Branch
  { branchState :: Maybe TCState, branchTrail :: Maybe (Integer, DraftAction)
  -- Building this map consults the previous Owner. Leaving it suspended keeps
  -- that owner's pre-eviction snapshot map alive through an unrelated recipe.
  , branchOrigins :: !(Map.Map InteractionId (Maybe Recursion.Owner))
  , branchApplication :: Maybe ApplicationKey }
type role Owner nominal
data Owner s = Owner
  { ownerEpoch :: Integer, ownerClosed :: Bool, ownerNext :: Integer
  , ownerBranches :: Map.Map Integer Branch
  , ownerApplications :: Map.Map ApplicationKey (Transition s) }
data SourceWitness = SourceWitness FilePath FilePath BS.ByteString
-- Captured before Agda setup/load, not after an option file may have changed.
newtype Configuration = Configuration [SourceWitness]

pinConfiguration :: [FilePath] -> IO Configuration
pinConfiguration paths = Configuration <$> mapM capture paths
 where
  capture path = do
    canonical <- canonicalizePath path
    bytes <- BS.readFile path
    pure $ SourceWitness path canonical bytes

-- Agda owns its runtime location and manifest discovery. Do not encode an
-- installed path or a built-in library filename in the solver.
pinRuntimeConfiguration :: Configuration -> IO Configuration
pinRuntimeConfiguration (Configuration project) = do
  directory <- getPrimitiveLibDir
  ((result, warnings), _) <- runLibM (getAgdaLibFile $ filePath directory) empty
  case result of
    Right manifests | null warnings -> do
      Configuration runtime <- pinConfiguration $ map _libFile manifests
      pure $ Configuration $ runtime ++ project
    _ -> E.throwIO $ userError "symbolic-session-invalid-runtime-library-configuration"

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
withSession = withSessionConfiguration (Configuration [])

withSessionConfiguration :: Configuration -> Interface
                         -> (forall s. Session s -> StateRef s -> IO a) -> TCM a
withSessionConfiguration = withSessionConfigurationReuse ExactReuse

-- Retain an explicit ablation path without changing the checked-transition API.
withSessionConfigurationReuse :: ReusePolicy -> Configuration -> Interface
                             -> (forall s. Session s -> StateRef s -> IO a) -> TCM a
withSessionConfigurationReuse reuse (Configuration configuration) root use = do
  libraries <- Map.keys . agdaLibFiles <$> useTC stLibCache
  -- Never retain a branch loaded with an unpinned project configuration. The
  -- caller's prepared overlay supplies these paths; Agda supplies actual usage.
  known <- liftIO $ mapM canonicalizePath libraries
  let pinnedPaths = Set.fromList [canonical | SourceWitness _ canonical _ <- configuration]
      unpinned = filter (`Set.notMember` pinnedPaths) known
  unless (null unpinned) $
    genericError $ "symbolic-session-unpinned-library-configuration: " ++ unwords unpinned
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
    ledger <- newIORef emptyWork { inputBytesRead = sum
      [toInteger $ BS.length bytes | SourceWitness _ _ bytes <- configuration] }
    witnesses <- mapM (pin ledger) sources
    a <- randomIO :: IO Word64
    b <- randomIO :: IO Word64
    owner <- newMVar $ Owner 0 False 1
      (Map.singleton 0 $ Branch (Just initial) Nothing origins Nothing) Map.empty
    active <- newIORef Nothing
    let nonce = showHex a "-" ++ showHex b ""
        session = Session nonce owner env (configuration ++ witnesses) ledger active reuse
        rootRef = StateRef $ StateKey nonce 0 0
    stable <- inputsMatch session
    unless stable $ E.throwIO $ userError "symbolic-session-configuration-changed-during-load"
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
        -> (Owner s -> TCState -> IO (Owner s, Either Failure a))
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

lookupState :: Session s -> StateRef s -> Owner s -> Either Failure TCState
lookupState session (StateRef key) owner
  | keySession key /= sessionNonce session = Left ForeignSession
  | ownerClosed owner = Left ClosedSession
  | keyEpoch key /= ownerEpoch owner = Left StaleEpoch
  | otherwise = case Map.lookup (keyBranch key) (ownerBranches owner) of
      Nothing -> Left UnknownState
      Just branch -> maybe (Left EvictedState) Right (branchState branch)

invalidate :: Owner s -> Owner s
invalidate owner = owner { ownerEpoch = ownerEpoch owner + 1,
  ownerBranches = Map.empty, ownerApplications = Map.empty }

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

-- Read-only native dependencies. The bounded traversal may be incomplete;
-- that is a fallback observation, never proof of absent dependencies.
dependencies :: Session s -> StateRef s -> Maybe Integer -> IO (Either Failure (DependencySnapshot s))
dependencies session parent limit = request session parent $ \owner state -> do
  used <- newIORef (0 :: Integer)
  let step kind = liftIO $ do
        allowed <- atomicModifyIORef' used $ \n ->
          if maybe False (n >=) limit then (n, False) else (n+1, True)
        when allowed $ charge (sessionWork session) $ \w -> case kind of
          Dependencies.ReadDependency -> w { symbolicActions = symbolicActions w + 1,
            dependencyQueries = dependencyQueries w + 1 }
          Dependencies.WalkDependency -> w { symbolicActions = symbolicActions w + 1,
            dependencyNodes = dependencyNodes w + 1 }
        pure allowed
  (result, _) <- kernel session state $ Dependencies.observe step
  pure (owner, DependencySnapshot parent <$> result)

-- Negative certificates are only proposed for an original source obligation,
-- never an assigned prefix, a case branch or a speculative helper. The command
-- is read-only and its allowance includes both observation and valuations.
proposeRefutation :: Session s -> GoalRef s -> Maybe Integer -> IO (Either Failure (RefutationProposal s))
proposeRefutation session goal limit = request session (goalState goal) $ \owner state -> do
  used <- newIORef (0 :: Integer)
  let step update = liftIO $ do
        allowed <- atomicModifyIORef' used $ \n ->
          if maybe False (n >=) limit then (n, False) else (n+1, True)
        if allowed then charge (sessionWork session) update >> pure True else pure False
      query = step $ \w -> w { checkingAttempts = checkingAttempts w + 1,
        refutationQueries = refutationQueries w + 1 }
      assignment = step $ \w -> w { symbolicActions = symbolicActions w + 1,
        refutationAssignments = refutationAssignments w + 1 }
  (result, _) <- kernel session state $ do
    exists <- elem (goalId goal) <$> openInteractionPoints
    if not exists then pure $ Left UnknownGoal
    else if keyBranch (stateKey $ goalState goal) /= 0
      then pure $ Left $ KernelRejected "refutation-requires-original-source-state"
      else do
        snapshot <- Refutation.propose query assignment (goalId goal)
        liftIO $ charge (sessionWork session) $ \w -> w
          { refutationCandidates = refutationCandidates w + if Refutation.kind snapshot == Refutation.Candidate then 1 else 0 }
        pure $ Right $ RefutationProposal goal snapshot
  pure (owner, result >>= id)

tryExpression :: Session s -> GoalRef s -> DraftExpression
              -> IO (Either Failure (Transition s))
tryExpression session goal expression = request session (goalState goal) $ \owner state ->
  checkApplication session owner goal state (SourceAction $ draftSource expression) (TextDraft expression)

inferHelper :: Session s -> GoalRef s -> ObservationMode -> DraftExpression
            -> IO (Either Failure (HelperProposal s))
inferHelper session goal mode expression = request session (goalState goal) $ \owner state -> do
  charge (sessionWork session) $ \w -> w
    { checkingAttempts = checkingAttempts w + 1, helperQueries = helperQueries w + 1 }
  (inferred, planningState) <- kernel session state $ do
    exists <- elem (goalId goal) <$> openInteractionPoints
    if not exists then pure $ Left UnknownGoal
      else Right <$> Helpers.infer (goalId goal) mode expression
  let result = inferred >>= id
  case result of
    Left _ -> charge (sessionWork session) $ \w -> w { rejectedChecks = rejectedChecks w + 1 }
    Right _ -> pure ()
  pure (owner, (\snapshot -> HelperProposal goal snapshot planningState) <$> result)

helperView :: HelperProposal s -> Value
helperView (HelperProposal goal snapshot _) = object
  ["parent" .= stateKey (goalState goal), "goal_id" .= interactionId (goalId goal)
  ,"proposal" .= Helpers.view snapshot, "proof_authority" .= False]

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
applyClause session goal action = applyClauseMove session $
  ClauseMove goal $ ClauseExecution.UserAction action

applyClauseMove :: Session s -> ClauseMove s -> IO (Either Failure (Transition s))
applyClauseMove session (ClauseMove goal action) = request session (goalState goal) $ \owner state -> do
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
              -> Policy.RankingMode -> Maybe (NativeScorer n) -> Bool -> [String]
              -> (Value -> IO ())
              -> IO (Search.SearchStats, Either Failure
                   (Search.SearchStatus, Maybe (Transition s), [(T.Text,T.Text)]))
solveEvidence = solveEvidenceAtDepth Search.initialDepth

solveEvidenceAtDepth :: Search.IterationDepth -> Session s -> GoalRef s -> Search.SearchLimits -> Policy.Models
                     -> Policy.RankingMode -> Maybe (NativeScorer n) -> Bool -> [String]
                     -> (Value -> IO ())
                     -> IO (Search.SearchStats, Either Failure
                          (Search.SearchStatus, Maybe (Transition s), [(T.Text,T.Text)]))
solveEvidenceAtDepth depth session goal limits models mode native enableFocused excluded emit =
  runGoalSearch session goal $ \stats namespace point origin validate target ->
    Search.run depth stats limits models mode native enableFocused emit namespace excluded point origin validate target

solveHelper :: Session s -> GoalRef s -> Search.SearchLimits -> Policy.Models
            -> Policy.RankingMode -> Maybe (NativeScorer n) -> ObservationMode -> DraftExpression
            -> (Value -> IO ())
            -> IO (Search.SearchStats, Either Failure
                 (Search.SearchStatus, Maybe (Transition s), [(T.Text,T.Text)]))
solveHelper session goal limits models mode native view expression emit =
  runGoalSearch session goal $ \stats namespace point _ validate target ->
    Search.runHelper stats limits models mode native emit namespace point view expression validate target

proposeTerms :: Session s -> GoalRef s -> Search.SearchLimits -> Policy.Models
             -> Policy.RankingMode -> Maybe (NativeScorer n) -> [String] -> (Value -> IO ())
             -> IO (Search.SearchStats, Either Failure (TermProposals s))
proposeTerms = proposeTermsWithTargetOperands True

proposeTermsWithTargetOperands :: Bool -> Session s -> GoalRef s -> Search.SearchLimits -> Policy.Models
                             -> Policy.RankingMode -> Maybe (NativeScorer n) -> [String] -> (Value -> IO ())
                             -> IO (Search.SearchStats, Either Failure (TermProposals s))
proposeTermsWithTargetOperands enabled = proposeTermsUsing $ Search.primitiveProposals enabled

proposeStructures :: Session s -> GoalRef s -> Search.SearchLimits -> Policy.Models
                  -> Policy.RankingMode -> Maybe (NativeScorer n) -> [String] -> (Value -> IO ())
                  -> IO (Search.SearchStats, Either Failure (TermProposals s))
proposeStructures = proposeTermsUsing Search.structuralProposals

proposeEquations :: [GoalRef s] -> Session s -> GoalRef s -> Search.SearchLimits -> Policy.Models
                 -> Policy.RankingMode -> Maybe (NativeScorer n) -> [String] -> (Value -> IO ())
                 -> IO (Search.SearchStats, Either Failure (TermProposals s))
proposeEquations later session goal = proposeTermsUsing generate session goal
 where
  generate stats limits models mode native emit namespace excluded owner point target = do
    available <- openInteractionPoints
    if any (\ref -> stateKey (goalState ref) /= stateKey (goalState goal)
          || goalId ref `notElem` available) later
      then genericError "native-observation-goal-state-mismatch"
      else Search.equationProposals (map goalId later) stats limits models mode native emit
        namespace excluded owner point target

proposeConstructors :: Session s -> GoalRef s -> Search.SearchLimits -> Policy.Models
                    -> Policy.RankingMode -> Maybe (NativeScorer n) -> [String] -> (Value -> IO ())
                    -> IO (Search.SearchStats, Either Failure (TermProposals s))
proposeConstructors = proposeTermsUsing Search.constructorProposals

type TermGenerator n = IORef Search.SearchStats -> Search.SearchLimits -> Policy.Models
  -> Policy.RankingMode -> Maybe (NativeScorer n) -> (Value -> IO ()) -> String -> [String]
  -> Maybe Recursion.Owner -> InteractionId -> I.Type -> TCM [(A.Expr, [(T.Text, T.Text)])]

proposeTermsUsing :: TermGenerator n -> Session s -> GoalRef s -> Search.SearchLimits -> Policy.Models
                 -> Policy.RankingMode -> Maybe (NativeScorer n) -> [String] -> (Value -> IO ())
                 -> IO (Search.SearchStats, Either Failure (TermProposals s))
proposeTermsUsing generate session goal limits models mode native excluded emit = do
  stats <- newIORef Search.emptyStats
  outcome <- request session (goalState goal) $ \owner state -> do
    ledger <- work session
    let point = goalId goal
        namespace = show (stateKey $ goalState goal) ++ ":moves:" ++ show (requests ledger)
        origin = Map.lookup (keyBranch $ stateKey $ goalState goal) (ownerBranches owner)
          >>= Map.findWithDefault Nothing point . branchOrigins
    (result, allocation) <- kernel session state $ do
      exists <- elem point <$> openInteractionPoints
      if not exists then pure $ Left UnknownGoal else withInteractionId point $ do
        target <- getMetaTypeInContext =<< lookupInteractionId point
        Right <$> generate stats limits models mode native emit namespace excluded origin point target
    -- The queue deliberately leaves many proposal payloads unevaluated. Seal
    -- their small allocation watermark now: mapping nativeDraft lazily over
    -- the catalogue would retain the entire speculative TCState until the
    -- last alternative is tried or discarded.
    let watermark = Allocation (allocation ^. stFreshNameId) (allocation ^. stFreshInteractionId)
    watermark `seq` pure (owner, fmap (zipWith (\ordinal (expression, selected) -> TermProposal goal
      (NativeDraft expression watermark) selected (IssuedAction (requests ledger) ordinal)) [0..]) $ result >>= id)
  observed <- readIORef stats
  recordSearchWork session observed
  pure (observed, (if Search.workExhausted observed then CensoredTerms else CompleteTerms) <$> outcome)

applyTerm :: Session s -> TermProposal s -> IO (Either Failure (Transition s))
applyTerm session (TermProposal goal draft _ identity) = request session (goalState goal) $ \owner state ->
  checkApplication session owner goal state identity draft

-- Only exact applications with an accepted, still-resident child are reused.
-- Parent epoch/residency and pinned source bytes are checked by request before
-- and after this operation. Failures and interrupted/blocked searches are never
-- memoized, and reconstruction/replay deliberately call check directly.
checkApplication :: Session s -> Owner s -> GoalRef s -> TCState -> ActionIdentity -> Draft
                 -> IO (Owner s, Either Failure (Transition s))
checkApplication session owner goal initial identity draft
  | sessionReuse session == NoReuse = recheck owner
  | otherwise = do
      charge (sessionWork session) $ \w -> w
        { exactReuseQueries = exactReuseQueries w + 1, symbolicActions = symbolicActions w + 1 }
      case Map.lookup key (ownerApplications owner) of
        Just transition | Right _ <- lookupState session (transitionState transition) owner -> do
          charge (sessionWork session) $ \w -> w { exactReuseHits = exactReuseHits w + 1 }
          pure (owner, Right transition)
        _ -> do
          (next, result) <- recheck owner
          pure $ case result of
            Left _ -> (next, result)
            Right transition -> (next
              { ownerApplications = Map.insert key transition (ownerApplications next)
              , ownerBranches = Map.adjust (\b -> b { branchApplication = Just key })
                  (keyBranch $ stateKey $ transitionState transition) (ownerBranches next)
              }, result)
 where
  key = ApplicationKey (stateKey $ goalState goal) (goalId goal) identity
  recheck current = check session current (goalState goal) initial (DraftAction (goalId goal) draft) False

proposeClauseActions :: Session s -> GoalRef s -> Search.SearchLimits -> Policy.Models
                     -> Policy.RankingMode -> Maybe (NativeScorer n) -> [String] -> (Value -> IO ())
                     -> IO (Search.SearchStats, Either Failure (ClauseProposals s))
proposeClauseActions session goal limits models mode native excluded emit = do
  stats <- newIORef Search.emptyStats
  outcome <- request session (goalState goal) $ \owner state -> do
    ledger <- work session
    let point = goalId goal
        namespace = show (stateKey $ goalState goal) ++ ":clauses:" ++ show (requests ledger)
    (result, _) <- kernel session state $ do
      exists <- elem point <$> openInteractionPoints
      if not exists then pure $ Left UnknownGoal else withInteractionId point $ do
        target <- getMetaTypeInContext =<< lookupInteractionId point
        Right <$> Search.clauseProposals stats limits models mode native emit namespace excluded target
    pure (owner, fmap (map (\(intent, choices) -> (ClauseMove goal intent, choices))) $ result >>= id)
  observed <- readIORef stats
  recordSearchWork session observed
  pure (observed, (if Search.workExhausted observed then CensoredClauses else CompleteClauses) <$> outcome)

runGoalSearch :: Session s -> GoalRef s
              -> (IORef Search.SearchStats -> String -> InteractionId -> Maybe Recursion.Owner
                  -> (A.Expr -> TCM ()) -> I.Type -> TCM Search.Result)
              -> IO (Search.SearchStats, Either Failure
                   (Search.SearchStatus, Maybe (Transition s), [(T.Text,T.Text)]))
runGoalSearch session goal search = do
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
        Right <$> search stats namespace point origin validate target
    case searched >>= id of
      Left failure -> pure (owner, Left failure)
      Right (Search.Result status Nothing selected) -> pure (owner, Right (status, Nothing, selected))
      Right (Search.Result status (Just term) selected) -> do
        (next, checked) <- check session owner (goalState goal) state
          (DraftAction point $ nativeDraft term allocation) False
        pure (next, (\transition -> (status, Just transition, selected)) <$> checked)
  observed <- readIORef stats
  recordSearchWork session observed
  pure (observed, outcome)

-- Pure symbolic traversal is work, but not an Agda checking request. Keeping
-- both components avoids losing work at the agenda boundary or misreporting
-- in-memory focused/rewrite steps as checker calls.
recordSearchWork :: Session s -> Search.SearchStats -> IO ()
recordSearchWork session observed =
  charge (sessionWork session) $ \w -> w
    { checkingAttempts = checkingAttempts w + Search.checkerQueries observed
        + Search.inferenceQueries observed + Search.recursiveContextQueries observed
    , symbolicActions = symbolicActions w + Search.focusedActions observed + Search.algebraActions observed
        + Search.applicationGenerationSteps observed
    , rejectedChecks = rejectedChecks w + Search.rejectedQueries observed
    , helperQueries = helperQueries w + Search.helperInferenceQueries observed
    , clauseQueries = clauseQueries w + Search.helperClauseQueries observed }

check :: Session s -> Owner s -> StateRef s -> TCState -> DraftAction -> Bool
      -> IO (Owner s, Either Failure (Transition s))
check session owner parent initial (DraftAction point expression) isReplay = do
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
      pure $ if null bad then Right (scoped, display, term, target, telescope, obligations)
        else Left $ KernelRejected $ unlines (map tcWarningString bad)
  case result >>= id of
    Left failure -> do
      charge (sessionWork session) $ \w -> w { rejectedChecks = rejectedChecks w + 1 }
      pure (owner, Left failure)
    Right (scoped, abstract, term, target, telescope, obligations) -> do
      charge (sessionWork session) $ \w -> w { acceptedChecks = acceptedChecks w + 1 }
      let number = ownerNext owner
          ref = StateRef $ StateKey (sessionNonce session) (ownerEpoch owner) number
          origins = Map.fromList
            [(p, Map.findWithDefault origin p previous)
            | number' <- pendingGoals obligations, let p = fromIntegral number']
          draft = DraftAction point $ nativeDraft scoped child
          branch = Branch (Just child) (Just (keyBranch $ stateKey parent, draft)) origins Nothing
          next = owner { ownerNext = number + 1,
                         ownerBranches = Map.insert number branch (ownerBranches owner) }
          kind | not (null $ pendingGoals obligations) = AcceptedPartial
               | pendingMetas obligations > 0 || pendingConstraints obligations > 0 = AcceptedBlocked
               | otherwise = ApparentlyClosed
      draft `seq` pure (next, Right $ Transition ref kind obligations $
        CheckedEvidence ref abstract term target telescope)

expectedWarning :: TCWarning -> Bool
expectedWarning warning = case tcWarning warning of
  UnsolvedInteractionMetas{} -> True
  UnsolvedMetaVariables{} -> True
  UnsolvedConstraints{} -> True
  _ -> False

-- Reconstruct one original goal from native drafts along a checked descendant
-- branch, then check the assembled expression again from the original parent.
-- This neither serializes TCState nor mistakes the last solved leaf for the
-- complete source proof. Parent/descendant states and external costs survive.
reconstructGoal :: Session s -> GoalRef s -> StateRef s
                -> IO (Either Failure (Transition s))
reconstructGoal session goal descendant = fmap (fmap $ snd . NE.head) $
  reconstructGoals session (goalState goal) (goalId goal :| []) descendant

-- Requested original goals are reconstructed into one new coupled branch.
-- Rechecking them independently loses the substitutions that later definitions
-- depend on. A failure publishes none of the intermediate branches, but their
-- checking work remains charged. Unrequested source goals are never discarded.
reconstructGoals :: Session s -> StateRef s -> NonEmpty InteractionId -> StateRef s
                 -> IO (Either Failure (NonEmpty (InteractionId, Transition s)))
reconstructGoals session parent points descendant = fmap (fmap $ fmap (\(p, t, ()) -> (p, t))) $
  reconstructWith (\_ _ -> pure ()) session parent points descendant

exportGoals :: Session s -> StateRef s -> NonEmpty InteractionId -> StateRef s
            -> IO (Either Failure (NonEmpty (InteractionId, Transition s, Value)))
exportGoals session = reconstructWith (\point expression -> Source.view <$>
  Source.render (liftIO $ charge (sessionWork session) $ \w -> w
    { checkingAttempts = checkingAttempts w + 1, clauseQueries = clauseQueries w + 1 }) point expression) session

reconstructWith :: (InteractionId -> A.Expr -> TCM a) -> Session s -> StateRef s
                -> NonEmpty InteractionId -> StateRef s
                -> IO (Either Failure (NonEmpty (InteractionId, Transition s, a)))
reconstructWith present session parent points descendant = request session parent $ \owner initial ->
  case reconstructionDrafts session owner parent descendant of
    Left failure -> pure (owner, Left failure)
    Right (expressions, allocations) -> case mapM (\point ->
        (point,) <$> Assembly.assemble point expressions) points of
      Left reason -> pure (owner, Left $ KernelRejected reason)
      Right assembled -> do
        (valid, _) <- kernel session initial $ do
          open <- openInteractionPoints
          pure $ if Set.size (Set.fromList $ NE.toList points) /= length points
            then Left $ KernelRejected "native-reconstruction-duplicate-goals"
            else if all (`elem` open) points then Right () else Left UnknownGoal
        case valid >>= id of
          Left failure -> pure (owner, Left failure)
          Right () -> do
            let allocation = foldr maximumAllocation
                  (Allocation (initial ^. stFreshNameId) (initial ^. stFreshInteractionId)) allocations
            (next, result) <- go allocation owner parent initial $ NE.toList assembled
            case result of
              Left failure -> pure (owner, Left failure)
              Right [] -> pure (owner, Left $ KernelFailure "native-reconstruction-empty-batch")
              Right (first:rest) -> pure (next, Right $ first :| rest)
 where
  go _ owner _ _ [] = pure (owner, Right [])
  go allocation owner current state ((point, expression):rest) = do
    (rendered, _) <- kernel session state $ reserveAllocation allocation >> present point expression
    case rendered of
      Left failure -> pure (owner, Left failure)
      Right source -> do
        (next, result) <- check session owner current state
          (DraftAction point $ NativeDraft expression allocation) False
        case result of
          Left failure -> pure (owner, Left failure)
          Right transition -> case lookupState session (transitionState transition) next of
            Left failure -> pure (owner, Left failure)
            Right child -> do
              (done, results) <- go allocation next (transitionState transition) child rest
              pure (done, ((point, transition, source):) <$> results)

reconstructionDrafts :: Session s -> Owner s -> StateRef s -> StateRef s
                     -> Either Failure ([(InteractionId, A.Expr)], [Allocation])
reconstructionDrafts session owner parent descendant = drafts descendant >>= nativeActions
 where
  drafts ref
    | keySession key /= sessionNonce session = Left ForeignSession
    | keyEpoch key /= ownerEpoch owner = Left StaleEpoch
    | otherwise = walk (keyBranch key) []
   where
    key = stateKey ref
    root = keyBranch $ stateKey parent
    walk number actions
      | number == root = Right actions
      | otherwise = case Map.lookup number (ownerBranches owner) of
          Nothing -> Left UnknownState
          Just branch -> case branchTrail branch of
            Just (previous, action) | previous < number -> walk previous (action:actions)
            _ -> Left $ KernelRejected "native-reconstruction-not-a-descendant"
  nativeActions [] = Right ([], [])
  nativeActions (DraftAction point (NativeDraft expression allocation):rest) = do
    (expressions, allocations) <- nativeActions rest
    pure ((point, expression):expressions, allocation:allocations)
  nativeActions _ = Left $ KernelFailure "native-reconstruction-missing-scoped-draft"

maximumAllocation :: Allocation -> Allocation -> Allocation
maximumAllocation (Allocation a b) (Allocation c d) = Allocation (max a c) (max b d)

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
  let number = keyBranch (stateKey ref)
      key = Map.lookup number (ownerBranches owner) >>= branchApplication
  in
  if number == 0 then pure (owner, Left CannotEvictRoot) else
  pure (owner { ownerBranches = Map.adjust (\b -> b { branchState = Nothing, branchApplication = Nothing })
                 number (ownerBranches owner)
              , ownerApplications = maybe id Map.delete key (ownerApplications owner) }, Right ())

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
      Right (ancestor, state, actions) -> do
        (rebuilt, result) <- go current (StateRef key { keyBranch = ancestor }) state actions
        -- Replay publishes only its final handle. Intermediate checkpoints
        -- have no caller lease; keep their recipes for ancestry, not their
        -- resident TCStates. Never touch a pre-existing caller-owned handle.
        let published = either (const Nothing) (Just . keyBranch . stateKey) result
            unpublished = [number | number <- [ownerNext current .. ownerNext rebuilt - 1],
              Just number /= published]
            retired = foldr (\number branches -> Map.adjust
              (\branch -> branch { branchState = Nothing }) number branches)
              (ownerBranches rebuilt) unpublished
        pure (rebuilt { ownerBranches = retired }, result)
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
