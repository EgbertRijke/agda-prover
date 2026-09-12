{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleContexts #-}
-- SPDX-License-Identifier: GPL-3.0-or-later
module AgdaProver.Agda28.Dependencies
  ( Snapshot, Step (..), observe, view, orderGoals ) where

import Control.Monad (forM, unless)
import Control.Monad.State.Strict
import Data.Aeson (Value, object, (.=))
import Data.List (sortOn)
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set
import Agda.Syntax.Abstract.Name (QName)
import Agda.Syntax.Common (InteractionId, MetaId, interactionId)
import Agda.Syntax.Info (MetaKind (..))
import Agda.Syntax.Internal.Names (NamesIn, namesAndMetasIn')
import Agda.TypeChecking.Monad
import AgdaProver.Agda28.Observation (openInteractionPoints)
import Structure qualified as S

data Node = Declaration QName | Meta MetaId deriving (Eq, Ord)
data Step = ReadDependency | WalkDependency
data Unknown = AbstractDeclaration | MissingMeta | BlockedMeta | PostponedChecking
  deriving (Eq, Ord)
data Reach = Reach InteractionId MetaId (Set.Set Node)
data Snapshot = Snapshot [Reach] Int [MetaId] Bool (Set.Set Unknown)
data Build = Build
  { summaries :: Map.Map Node (Set.Set Node)
  , instancesSeen :: Set.Set MetaId
  , censored :: Bool
  , unknown :: Set.Set Unknown }

-- Agda's NamesIn traversal includes Type sort annotations, level terms,
-- dependent telescopes, projections and clauses. allMetas/foldTerm omit some
-- of those annotations. Do not use pretty syntax as a dependency index.
references :: NamesIn a => a -> Set.Set Node
references = namesAndMetasIn' (Set.singleton . either Declaration Meta)

-- This is a conservative observation, not an independence certificate. Global
-- active constraints are retained as a coupling barrier, without pretending
-- their delayed closures or instance-search effects have been fully analyzed.
observe :: (Step -> TCM Bool) -> TCM Snapshot
observe chargeStep = localTCState $ dontAssignMetas $ do
  points <- openInteractionPoints
  constraints <- length <$> getAllConstraints
  (reaches, built) <- runStateT (forM points $ \point -> do
    allowed <- charge ReadDependency
    if not allowed then pure Nothing else do
      meta <- lift $ lookupInteractionId point
      lets <- lift $ withInteractionId point getLetBindings
      let locals = Set.unions [references (letType binding, letTerm binding) | (_, binding) <- lets]
      reached <- walk Set.empty $ Set.insert (Meta meta) locals
      pure $ Just $ Reach point meta reached) (Build Map.empty Set.empty False Set.empty)
  pure $ Snapshot [r | Just r <- reaches] constraints
    (Set.toAscList $ instancesSeen built) (censored built) (unknown built)
 where
  charge step = do
    spent <- gets censored
    if spent then pure False else do
      allowed <- lift $ chargeStep step
      unless allowed $ modify' $ \s -> s { censored = True }
      pure allowed
  uncertain reason = modify' $ \s -> s { unknown = Set.insert reason (unknown s) }
  walk visited frontier = case Set.minView frontier of
    Nothing -> pure visited
    Just (node, rest) | node `Set.member` visited -> walk visited rest
    Just (node, rest) -> charge WalkDependency >>= \case
      False -> pure visited
      True -> do
        next <- summary node
        walk (Set.insert node visited) $ Set.union rest (Set.difference next visited)
  summary node = gets (Map.lookup node . summaries) >>= \case
    Just refs -> pure refs
    Nothing -> charge ReadDependency >>= \case
      False -> pure Set.empty
      True -> do
        refs <- case node of
          Declaration name -> lift (isLocal name) >>= \case
            -- Imported interfaces are fixed in this pinned parent. We do not
            -- expand the whole library or expose these names as premises.
            False -> pure Set.empty
            True -> do
              definition <- lift $ getConstInfo name
              case theDef definition of
                AbstractDefn{} -> uncertain AbstractDeclaration >> pure (references $ defType definition)
                _ -> pure $ references definition
          Meta meta -> lift (lookupMeta meta) >>= \case
            Nothing -> uncertain MissingMeta >> pure Set.empty
            Just (Left remote) -> pure $
              references (jMetaType $ rmvJudgement remote, instBody $ rmvInstantiation remote)
            Just (Right local) -> do
              let target = references $ jMetaType $ mvJudgement local
              body <- case mvInstantiation local of
                InstV solution -> pure $ references $ instBody solution
                OpenMeta UnificationMeta -> pure Set.empty
                OpenMeta InstanceMeta -> do
                  modify' $ \s -> s { instancesSeen = Set.insert meta (instancesSeen s) }
                  pure Set.empty
                BlockedConst term -> uncertain BlockedMeta >> pure (references term)
                PostponedTypeCheckingProblem{} -> uncertain PostponedChecking >> pure Set.empty
              pure $ Set.union target body
        modify' $ \s -> s { summaries = Map.insert node refs (summaries s) }
        pure refs

-- This ordering is only a heuristic over known prerequisite goals. Even a
-- complete traversal is not a proof of independent future elaboration. Retain
-- the original order when the observation is censored or has opaque effects.
orderGoals :: Snapshot -> [Int] -> [Int]
orderGoals snapshot@(Snapshot _ constraints instances' cut reasons) selected
  | cut || constraints /= 0 || not (null instances') || not (Set.null reasons) = selected
  | any (`Map.notMember` dependencies) selected = selected
  | otherwise = sortOn (Set.size . (dependencies Map.!)) selected
 where
  dependencies = goalEdges snapshot

goalEdges :: Snapshot -> Map.Map Int (Set.Set Int)
goalEdges (Snapshot reaches _ _ _ _) = Map.fromList
  [(interactionId point, Set.fromList
      [interactionId other | Meta meta <- Set.toAscList reached,
       other <- Set.toAscList $ Map.findWithDefault Set.empty meta owners, other /= point])
  | Reach point _ reached <- reaches]
 where
  owners = Map.fromListWith Set.union [(meta, Set.singleton point) | Reach point meta _ <- reaches]

view :: Snapshot -> Value
view snapshot@(Snapshot reaches constraints instances' cut reasons) = object
  [ "schema_version" .= ("agdaprover.symbolic-dependencies.v1" :: String)
  , "status" .= (if cut then "censored" else "observed" :: String)
  , "independence" .= ("unknown" :: String)
  , "constraint_count" .= constraints
  , "reachable_instance_metas" .= map S.meta instances'
  , "unknown_reasons" .= map reasonName (Set.toAscList reasons)
  , "preferred_goal_order" .= orderGoals snapshot [interactionId p | Reach p _ _ <- reaches]
  , "goals" .= [object
      ["goal_id" .= interactionId point, "meta" .= S.meta meta,
       "prerequisite_goals" .= Set.toAscList (edges Map.! interactionId point),
       "reachable_metas" .= [S.meta m | Meta m <- Set.toAscList reached],
       "reachable_declaration_count" .= length [() | Declaration _ <- Set.toAscList reached]]
      | Reach point meta reached <- reaches]
  , "proof_authority" .= False ]
 where
  edges = goalEdges snapshot

reasonName :: Unknown -> String
reasonName AbstractDeclaration = "abstract-declaration"
reasonName MissingMeta = "unknown-meta"
reasonName BlockedMeta = "blocked-meta"
reasonName PostponedChecking = "postponed-typechecking"
