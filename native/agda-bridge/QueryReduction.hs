{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE LambdaCase #-}

-- Query evidence only. Agda's typed traversal supplies the dependent context;
-- ordinary value/function arguments are not recursively normalized for ranking.
module QueryReduction (ReducedQuery (..), typeFamilies) where

import Control.Monad (unless)
import Control.Monad.Except (catchError, throwError)
import Control.Monad.IO.Class (liftIO)
import Data.IORef (newIORef, modifyIORef', readIORef)

import Agda.Syntax.Common (unitRelevance)
import Agda.Syntax.Internal (Type, Type'' (..), Term (..))
import Agda.TypeChecking.CheckInternal qualified as C
import Agda.TypeChecking.Conversion (equalType)
import Agda.TypeChecking.Constraints (reallyNoConstraints)
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
  -- Even a successful observation cannot commit state. A generated meta must
  -- not escape in the returned type, and conversion must create no obligations.
  alternate <- localTCState $ catchError
    (dontAssignMetas $ reallyNoConstraints $ do
      before <- useTC stFreshMetaId
      ty <- C.inferInternal' action target
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
  ReducedQuery alternate <$> liftIO (readIORef visited) <*> liftIO (readIORef reductions)

typeFamily :: Type -> TCM Bool
typeFamily original = do
  El _ expected <- reduce original
  case expected of
    Sort{} -> pure True
    Pi domain body -> underAbstraction domain body typeFamily
    _ -> pure False
