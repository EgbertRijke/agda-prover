{-# LANGUAGE CPP #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE LambdaCase #-}

-- Query evidence only. Agda's typed traversal supplies the dependent context;
-- ordinary value/function arguments are not recursively normalized for ranking.
module QueryReduction (ReducedQuery (..), typeFamilies, checkedTypeChange) where

import Control.Monad (unless)
import Control.Monad.Except (catchError, throwError)
import Control.Monad.IO.Class (liftIO)
import Data.IORef (newIORef, modifyIORef', readIORef)

import Agda.Syntax.Common (unitRelevance)
import Agda.Syntax.Internal (Type, Type'' (..), Term (..))
import Agda.TypeChecking.CheckInternal qualified as C
import Agda.TypeChecking.Conversion (equalType)
#if defined(AGDAPROVER_AGDA_2643)
import Agda.TypeChecking.Constraints (noConstraints)
#else
import Agda.TypeChecking.Constraints (reallyNoConstraints)
#endif
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Reduce (reduce)

data ReducedQuery = ReducedQuery
  { queryType :: Maybe Type
  , termVisits :: Integer
  , typePositionReductions :: Integer
  }

typeFamilies :: Type -> TCM ReducedQuery
typeFamilies target = do
  visited <- liftIO $ newIORef 0
  reductions <- liftIO $ newIORef 0
  let action = C.defaultAction { C.preAction = \ty term -> do
        liftIO $ modifyIORef' visited (+ 1)
        family <- typeFamily ty
        if family then do
          liftIO $ modifyIORef' reductions (+ 1)
          reduce term
        else pure term }
  alternate <- checkedTypeChange target (C.inferInternal' action target)
  ReducedQuery alternate <$> liftIO (readIORef visited) <*> liftIO (readIORef reductions)

-- Shared by query and premise observers. Even success cannot commit state;
-- generated metas and obligations may not escape in an optional type view.
checkedTypeChange :: Type -> TCM Type -> TCM (Maybe Type)
checkedTypeChange target change = localTCState $ catchError
    (dontAssignMetas $ reallyNoConstraints $ do
      before <- useTC stFreshMetaId
      ty <- change
      localTC (\e -> e { envRelevance = unitRelevance }) $ equalType target ty
      after <- useTC stFreshMetaId
      unless (before == after) $ genericError "query-reduction-created-meta"
      pure (Just ty))
    (\case
      TypeError{} -> pure Nothing
      PatternErr{} -> pure Nothing
      -- Process/IO failures and asynchronous cancellation are not a safe
      -- optional-view miss. The enclosing request retains its normal failure.
      err -> throwError err)

typeFamily :: Type -> TCM Bool
typeFamily original = do
  El _ expected <- reduce original
  case expected of
    Sort{} -> pure True
    Pi domain body -> underAbstraction domain body typeFamily
    _ -> pure False

#if defined(AGDAPROVER_AGDA_2643)
-- In this kernel nonblocking constraints have no problem ID. A problem-local
-- test alone therefore misses them. Conservatively require an empty constraint
-- store before AND after the action; localTCState restores success/rejection.
reallyNoConstraints :: TCM a -> TCM a
reallyNoConstraints action = do
  before <- getAllConstraints
  unless (null before) $ genericError "query-reduction-existing-constraints"
  result <- noConstraints action
  after <- getAllConstraints
  unless (null after) $ genericError "query-reduction-created-constraint"
  pure result
#endif
