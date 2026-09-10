{-# LANGUAGE ImportQualifiedPost #-}

-- Structural head/arity evidence. Do not normalize domains or neutral
-- arguments: their original vocabulary belongs to a separate similarity view.
module TypeSpine (ReducedSpine (..), resultSpine) where

import Control.Monad.IO.Class (liftIO)
import Data.IORef (newIORef, modifyIORef', readIORef)
import Agda.Syntax.Internal (Type, Type'' (..), Term (..), Abs (..))
import Agda.TypeChecking.Monad (TCM, underAbstraction)
import Agda.TypeChecking.Reduce (reduce)
import QueryReduction qualified as Q

data ReducedSpine = ReducedSpine
  { spineType :: Maybe Type
  , headReductions :: Integer
  }

resultSpine :: Type -> TCM ReducedSpine
resultSpine original = do
  calls <- liftIO $ newIORef 0
  let descend ty = do
        liftIO $ modifyIORef' calls (+ 1)
        normal@(El sort term) <- reduce ty
        case term of
          Pi domain body -> do
            bodyType <- underAbstraction domain body descend
            pure $ El sort $ Pi domain $ case body of
              Abs hint _ -> Abs hint bodyType
              NoAbs hint _ -> NoAbs hint bodyType
          _ -> pure normal
  alternate <- Q.checkedTypeChange original (descend original)
  ReducedSpine alternate <$> liftIO (readIORef calls)
