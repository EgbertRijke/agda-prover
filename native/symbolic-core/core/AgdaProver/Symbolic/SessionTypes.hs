{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE OverloadedStrings #-}
-- SPDX-License-Identifier: GPL-3.0-or-later
module AgdaProver.Symbolic.SessionTypes
  ( StateKey (..), DraftExpression (..), Pending (..), TransitionKind (..)
  , Failure (..), Work (..), emptyWork, kindName, failureName ) where

import Control.Monad (unless)
import Data.Aeson
import Data.Aeson.KeyMap qualified as KeyMap
import Data.Set qualified as Set

-- Wire keys are requests, not capabilities to construct checked evidence.
-- The owner validates the nonce, epoch and live branch before using one.
data StateKey = StateKey
  { keySession :: String, keyEpoch :: Integer, keyBranch :: Integer }
  deriving (Eq, Ord, Show)

instance ToJSON StateKey where
  toJSON key = object ["session" .= keySession key, "epoch" .= keyEpoch key,
                        "branch" .= keyBranch key]

instance FromJSON StateKey where
  parseJSON = withObject "state key" $ \o -> do
    unless (Set.fromList (KeyMap.keys o) == Set.fromList ["session", "epoch", "branch"]) $
      fail "invalid state key fields"
    key <- StateKey <$> o .: "session" <*> o .: "epoch" <*> o .: "branch"
    unless (not (null $ keySession key) && keyEpoch key >= 0 && keyBranch key >= 0) $
      fail "invalid state key"
    pure key

-- Untrusted user/generator input. Agda parses and scopes it before checking;
-- it is never confused with a scoped or checked native term.
newtype DraftExpression = DraftExpression { draftSource :: String }
  deriving (Eq, Show)

data Pending = Pending
  { pendingGoals :: [Int], pendingMetas :: Int, pendingConstraints :: Int }
  deriving (Eq, Show)

instance ToJSON Pending where
  toJSON p = object ["goals" .= pendingGoals p, "metas" .= pendingMetas p,
                      "constraints" .= pendingConstraints p]

data TransitionKind = AcceptedPartial | AcceptedBlocked | ApparentlyClosed
  deriving (Eq, Show)

kindName :: TransitionKind -> String
kindName AcceptedPartial = "accepted-partial"
kindName AcceptedBlocked = "accepted-blocked"
kindName ApparentlyClosed = "apparently-closed"

data Failure = ForeignSession | StaleEpoch | UnknownState | EvictedState
  | ClosedSession | StaleInputs | UnknownGoal | KernelRejected String
  | KernelBlocked String | KernelFailure String | Cancelled | CannotEvictRoot
  | ReplayRejected String
  deriving (Eq, Show)

failureName :: Failure -> String
failureName ForeignSession = "foreign-session"
failureName StaleEpoch = "stale-epoch"
failureName UnknownState = "unknown-state"
failureName EvictedState = "evicted-state"
failureName ClosedSession = "closed-session"
failureName StaleInputs = "stale-inputs"
failureName UnknownGoal = "unknown-goal"
failureName KernelRejected{} = "kernel-rejected"
failureName KernelBlocked{} = "kernel-blocked"
failureName KernelFailure{} = "kernel-failure"
failureName Cancelled = "cancelled"
failureName CannotEvictRoot = "cannot-evict-root"
failureName ReplayRejected{} = "replay-rejected"

-- Physical time is integer nanoseconds/picoseconds, never rounded per action.
-- This ledger belongs to the owner, outside every restorable Agda snapshot.
data Work = Work
  { requests :: !Integer, checkingAttempts :: !Integer, replayedActions :: !Integer
  , acceptedChecks :: !Integer, rejectedChecks :: !Integer, cancelledRequests :: !Integer
  , inputBytesRead :: !Integer, elapsedNanoseconds :: !Integer, cpuPicoseconds :: !Integer
  } deriving (Eq, Show)

emptyWork :: Work
emptyWork = Work 0 0 0 0 0 0 0 0 0

instance ToJSON Work where
  toJSON w = object
    ["requests" .= requests w, "checking_attempts" .= checkingAttempts w,
     "replayed_actions" .= replayedActions w, "accepted_checks" .= acceptedChecks w,
     "rejected_checks" .= rejectedChecks w, "cancelled_requests" .= cancelledRequests w,
     "input_bytes_read" .= inputBytesRead w,
     "elapsed_nanoseconds" .= elapsedNanoseconds w, "cpu_picoseconds" .= cpuPicoseconds w]
