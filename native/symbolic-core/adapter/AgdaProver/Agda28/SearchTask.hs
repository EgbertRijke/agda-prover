{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
-- SPDX-License-Identifier: GPL-3.0-or-later
module AgdaProver.Agda28.SearchTask
  ( Task, Step (..), step, operation, suspended, attempt, atomicScope ) where

import Control.Monad (ap)
import Control.Monad.Except (catchError, throwError)
import Agda.TypeChecking.Monad

-- A scheduling continuation, not a checker continuation. Services are supplied
-- anew at each advance; no borrowed native scorer or mutable TCState reference
-- is captured by bind. The session owns the checking snapshot between advances.
newtype Task r a = Task { step :: r -> TCM (Step r a) }
data Step r a = Done a | Suspended (Task r a)

instance Functor (Task r) where
  fmap f action = action >>= pure . f
instance Applicative (Task r) where
  pure value = Task $ \_ -> pure $ Done value
  (<*>) = ap
instance Monad (Task r) where
  action >>= next = Task $ \services -> step action services >>= \case
    Done value -> step (next value) services
    Suspended rest -> pure $ Suspended (rest >>= next)

operation :: (r -> TCM a) -> Task r a
operation action = Task $ fmap Done . action

-- A denied operation is retried, not replaced by an unsuccessful proof branch.
suspended :: (r -> TCM Bool) -> Task r ()
suspended ready = waiting
 where
  waiting = Task $ \services -> ready services >>= \case
    True -> pure $ Done ()
    False -> pure $ Suspended waiting

-- Keep the failure continuation and its original state across every suspension.
-- Successful siblings keep their joint substitutions; a failed later operand
-- restores the state belonging to this choice, not the root or the last slice.
attempt :: (r -> TCErr -> TCM Bool) -> Task r (Maybe a) -> Task r (Maybe a)
attempt rejected action = operation (const getTC) >>= \initial -> go initial action
 where
  go initial current = Task $ \services -> do
    result <- step current services `catchError` \err -> do
      ordinary <- rejected services err
      if ordinary then pure $ Done Nothing else throwError err
    case result of
      Done Nothing -> putTC initial >> pure (Done Nothing)
      Done value -> pure $ Done value
      Suspended rest -> pure $ Suspended $ go initial rest

-- Agda's higher-order scope operations may have stateful epilogues (checkpoint
-- and shadowing bookkeeping). Do not claim their continuation can be captured
-- by saving TCEnv alone. Until they are resumable, replay this bounded scope
-- from its original state. All physical work stays charged by the caller.
atomicScope :: (r -> TCM ()) -> (forall b. TCM b -> TCM b) -> Task r a -> Task r a
atomicScope replayed scope action = scoped
 where
  scoped = Task $ \services -> do
    initial <- getTC
    result <- scope $ step action services
    case result of
      Done value -> pure $ Done value
      Suspended _ -> putTC initial >> pure (Suspended $ operation replayed >> scoped)
