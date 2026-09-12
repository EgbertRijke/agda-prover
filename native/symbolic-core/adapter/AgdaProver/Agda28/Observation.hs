{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
-- SPDX-License-Identifier: GPL-3.0-or-later
module AgdaProver.Agda28.Observation
  ( GoalSnapshot, observeGoal, encodeGoal, openInteractionPoints, rewrite ) where

import Control.Monad (unless)
import Control.Monad.Except (runExceptT)
import Control.Monad.State.Strict (runStateT, evalStateT)
import Data.Aeson (Value, object, (.=))
import Data.Foldable (toList)
import Data.List (elemIndex)
import Data.Set qualified as Set

import Agda.Interaction.BasicOps (normalForm)
import Agda.Interaction.Base qualified as Interaction
import Agda.Syntax.Abstract.Name (Name)
import Agda.Syntax.Common (InteractionId, MetaId, interactionId)
import Agda.Syntax.Common.Pretty (prettyShow)
import Agda.Syntax.Internal (Type, Telescope, Tele (..), Abs (..))
import Agda.Syntax.Scope.Base
import Agda.Syntax.Scope.Monad (tryResolveName)
import Agda.TypeChecking.Monad
import AgdaProver.Symbolic.Protocol qualified as P
import Decode qualified as D
import Structure qualified as S

-- Native trees stay native inside the version-specific boundary. JSON is an
-- observation, not the object on which the future in-process search will reason.
-- No constructor is public; this snapshot can only be obtained from Agda.
data GoalSnapshot = GoalSnapshot
  { snapshotPoint :: InteractionId
  , snapshotMode :: P.ObservationMode
  , snapshotTarget :: Type
  , snapshotView :: Type
  , snapshotTelescope :: Telescope
  , snapshotContext :: Context
  , snapshotLets :: [(Name, LetBinding)]
  , snapshotScope :: ScopeInfo
  , snapshotNames :: [(String, Either String ResolvedName)]
  , snapshotMetas :: [MetaId]
  , snapshotConstraints :: Int
  }

rewrite :: P.ObservationMode -> Interaction.Rewrite
rewrite P.Raw = Interaction.AsIs
rewrite P.Instantiated = Interaction.Instantiated
rewrite P.HeadNormal = Interaction.HeadNormal
rewrite P.Simplified = Interaction.Simplified
rewrite P.Normalized = Interaction.Normalised

-- Agda keeps solved interaction points for source bookkeeping. The unfiltered
-- map's keys are not the outstanding goal set.
openInteractionPoints :: TCM [InteractionId]
openInteractionPoints = map fst <$> getInteractionIdsAndMetas

observeGoal :: InteractionId -> P.ObservationMode -> TCM GoalSnapshot
observeGoal point mode = localTCState $ withInteractionId point $ dontAssignMetas $ do
  before <- useTC stFreshMetaId
  meta <- lookupInteractionId point
  target <- getMetaTypeInContext meta
  view <- normalForm (rewrite mode) target
  scope <- getScope
  -- Resolve local aliases with Agda; a conflicting spelling is an observation,
  -- not a license to choose one overloaded declaration or scrape its source.
  names <- mapM (\alias -> do
    resolution <- runExceptT $ tryResolveName allKindsOfNames Nothing alias
    pure (prettyShow alias, either (const $ Left "ambiguous") Right resolution))
    (Set.toAscList $ concreteNamesInScope scope)
  result <- GoalSnapshot point mode target view
    <$> getContextTelescope <*> getContext <*> getLetBindings
    <*> pure scope <*> pure names <*> getOpenMetas
    <*> (length <$> getAllConstraints)
  after <- useTC stFreshMetaId
  unless (before == after) $ genericError "symbolic-observation-created-meta"
  pure result

-- Lossless structured view with local binding identities, native global IDs,
-- full spines, annotations, and an explicit raw telescope. It is not a portable
-- TCState snapshot: names/metas must never be reused across sessions from this JSON.
encodeGoal :: GoalSnapshot -> Either String Value
encodeGoal snapshot = do
  ((target, view, telescope, locals, lets, aliases), encoded) <- flip runStateT S.withAtoms $ do
    target <- S.typ 0 (snapshotTarget snapshot)
    view <- S.typ 0 (snapshotView snapshot)
    telescope <- S.telescope 0 (snapshotTelescope snapshot)
    let names = contextNames' (snapshotContext snapshot)
        locals = [object ["id" .= S.nameKey name, "index" .= index,
                          "display" .= prettyShow name]
                 | (index, name) <- zip [0 :: Int ..] names]
    lets <- mapM (\(name, binding) -> do
      ty <- S.domain 0 (letType binding)
      value <- S.term 0 (letTerm binding)
      pure $ object ["id" .= S.nameKey name, "type" .= ty, "term" .= value,
                     "origin" .= show (letOrigin binding)]) (snapshotLets snapshot)
    aliases <- mapM (aliasView names) (snapshotNames snapshot)
    pure (target, view, telescope, locals, lets, aliases)
  atoms <- maybe (Left "missing-native-atoms") Right (S.nativeAtoms encoded)
  (tel, ty, changed) <- D.run atoms $ do
    tel <- D.telescope 0 0 telescope
    ty <- D.typ (telSize tel) 0 target
    changed <- D.typ (telSize tel) 0 view
    pure (tel, ty, changed)
  values <- flip evalStateT S.initial $
    (,,) <$> S.telescope 0 tel <*> S.typ 0 ty <*> S.typ 0 changed
  unless (values == (telescope, target, view)) $ Left "reconstruction-structure-mismatch"
  pure $ object
    [ "schema_version" .= ("agdaprover.symbolic-goal.v1" :: String)
    , "status" .= ("observed" :: String)
    , "goal_id" .= interactionId (snapshotPoint snapshot)
    , "mode" .= P.modeName (snapshotMode snapshot)
    , "raw_target" .= target, "target" .= view
    , "context_mode" .= ("raw" :: String), "context" .= telescope
    , "locals_newest_first" .= locals, "let_bindings" .= lets
    , "module" .= S.moduleView (_scopeCurrent $ snapshotScope snapshot)
    , "aliases" .= aliases, "names" .= S.names encoded
    , "open_metas" .= map S.meta (snapshotMetas snapshot)
    , "constraint_count" .= snapshotConstraints snapshot
    , "structural_nodes" .= S.nodes encoded
    , "reconstruction" .= object ["status" .= ("structural-roundtrip" :: String)]
    , "proof_authority" .= False
    ]

aliasView :: [Name] -> (String, Either String ResolvedName) -> S.Encode Value
aliasView locals (alias, resolution) = do
  meaning <- case resolution of
    Left reason -> pure $ object ["kind" .= reason]
    Right (VarName name _) -> pure $ object
      ["kind" .= ("local" :: String), "id" .= S.nameKey name,
       "context_index" .= elemIndex name locals]
    Right (DefinedName _ name _) -> global "defined" [name]
    Right (FieldName names) -> global "field" (toList names)
    Right (ConstructorName _ names) -> global "constructor" (toList names)
    Right (PatternSynResName names) -> global "pattern-synonym" (toList names)
    Right UnknownName -> pure $ object ["kind" .= ("unknown" :: String)]
  pure $ object ["alias" .= alias, "resolution" .= meaning]
 where
  global :: String -> [AbstractName] -> S.Encode Value
  global kind names = do
    identities <- mapM (S.qname . anameName) names
    pure $ object ["kind" .= kind, "identities" .= identities]

telSize :: Telescope -> Int
telSize EmptyTel = 0
telSize (ExtendTel _ (Abs _ rest)) = 1 + telSize rest
telSize (ExtendTel _ (NoAbs _ rest)) = telSize rest
