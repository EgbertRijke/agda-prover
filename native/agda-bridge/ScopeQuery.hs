{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

-- A ranking-only projection from the live interaction closure. No source
-- scanner, private inventory, held-out proof, or unfiltered corpus participates.
module ScopeQuery (emit, request) where

import Control.Monad (foldM, unless, when)
import Control.Monad.IO.Class (liftIO)
import Control.Monad.Except (runExceptT)
import Data.Aeson (Value, eitherDecodeStrict', encode, object, (.=))
import Data.ByteString.Lazy.Char8 qualified as BL
import Data.Foldable (toList)
import Data.Map.Strict qualified as Map
import Data.List (stripPrefix)
import Data.Maybe (catMaybes)
import Data.Set qualified as Set
import Data.Text qualified as Text
import Data.Text.Encoding qualified as Text

import Agda.Syntax.Abstract.Name
import Agda.Syntax.Common
import Agda.Syntax.Common.Pretty (prettyShow)
import Agda.Syntax.Concrete.Name qualified as C
import Agda.Syntax.Internal hiding (arity)
import Agda.Syntax.Internal.Generic (foldTerm)
import Agda.Syntax.Internal.MetaVars (noMetas)
import Agda.Syntax.Literal (Literal (LitQName))
import Agda.Syntax.Scope.Base
import Agda.Syntax.Scope.Monad (tryResolveName)
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Pretty (prettyTCM)
import Agda.TypeChecking.Reduce (instantiateFull, normalise)

request :: String -> Maybe (Bool, String)
request payload = case stripPrefix "agdaprover:scoped-retrieval:v5:" payload of
  Just exclusions -> Just (True, exclusions)
  Nothing -> (\exclusions -> (False, exclusions)) <$>
    stripPrefix "agdaprover:scoped-retrieval:v4:" payload

key :: QName -> String
key q = case nameId (qnameName q) of
  NameId n (ModuleNameHash m) -> show m ++ ":" ++ show n

-- Count the syntactic Pi spine, without pretending similarity is unification.
-- NoAbs does not bind a variable. Context heads use the live de Bruijn index.
headArity :: Type -> (Maybe String, Int)
headArity = go 0 0 . unEl
 where
  go arity bound = \case
    Pi _ (Abs _ t) -> go (arity + 1) (bound + 1) (unEl t)
    Pi _ (NoAbs _ t) -> go (arity + 1) bound (unEl t)
    Def q _ -> (Just ("global:" ++ key q), arity)
    Con h _ _ -> (Just ("global:" ++ key (conName h)), arity)
    Var i _ | i >= bound -> (Just ("local:" ++ show (i - bound)), arity)
    _ -> (Nothing, arity)

-- This deliberately small feature view traverses term bodies, not type sorts.
-- Projections on a neutral/constructor spine are symbols too. Unknown metas
-- remain unknown; nothing here reduces, solves, or assigns an obligation.
features :: Type -> Either String (Value, Int)
features ty = do
  let terms = take 250001 (foldTerm (: []) ty)
      count = length terms
  when (count > 250000) $ Left "scope-feature-node-limit"
  let (head', arity) = headArity ty
      symbols = Set.toAscList $ Set.fromList $ concatMap termSymbols terms
  pure (object ["result_head" .= head', "symbols" .= symbols, "arity" .= arity], count)

termSymbols :: Term -> [String]
termSymbols = \case
  Def q es -> key q : projections es
  Con h _ es -> key (conName h) : projections es
  Var _ es -> projections es
  MetaV _ es -> projections es
  Lit (LitQName q) -> [key q]
  _ -> []
 where
  projections es = [key q | Proj _ q <- es]

-- Ordinary lookup preserves abstraction AND opacity. Only original concrete
-- RHSs participate; never compiled clauses, display forms or referenced bodies.
-- Raw metavariables (even assigned ones not instantiated in the RHS) make the
-- evidence unavailable. Filtering endpoints happens before anything is emitted.
dependencies :: Set.Set String -> Int -> QName -> TCM (Maybe [String], Int)
dependencies allowed remaining q = do
  def <- getConstInfo q
  case theDef def of
    FunctionDefn f | defAbstract def /= AbstractDef -> do
      let bodies = catMaybes (map clauseBody (_funClauses f))
          terms = take (remaining + 1) (concatMap (foldTerm (: [])) bodies)
          count = length terms
      when (count > remaining) $ genericError "scope-total-node-limit"
      pure (if noMetas bodies then
              Just $ Set.toAscList $ Set.delete (key q) $
                Set.intersection allowed (Set.fromList (concatMap termSymbols terms))
            else Nothing, count)
    _ -> pure (Nothing, 0)

emit :: Bool -> InteractionId -> String -> TCM ()
emit withDependencies point payload = do
  when (length payload > 65536) $ genericError "scope-exclusion-limit"
  excluded <- either (const $ genericError "invalid-scope-exclusions") pure $
    eitherDecodeStrict' (Text.encodeUtf8 (Text.pack payload)) :: TCM [String]
  when (length excluded > 5000 || any null excluded) $ genericError "scope-exclusion-limit"
  withInteractionId point $ dontAssignMetas $ do
    scope <- getScope
    let concrete = Set.toAscList (concreteNamesInScope scope)
        nameable = all (not . C.isNoName) . C.qnameParts
        aliases = filter nameable concrete
        unnameable = Set.toAscList $ Set.fromList
          [prettyShow a | a <- concrete, not (nameable a)]
    when (length (take 5001 concrete) > 5000) $ genericError "scope-alias-limit"
    -- Unused ambiguous spellings do not invalidate an otherwise legal module.
    -- Resolve each qualified view independently and retain supported overloads.
    attempted <- mapM (\a -> (,) (prettyShow a) <$>
      runExceptT (tryResolveName allKindsOfNames Nothing a)) aliases
    let resolved = [(a, r) | (a, Right r) <- attempted]
        ambiguous = Set.toAscList $ Set.fromList [a | (a, Left _) <- attempted]
    let globals = [(a, anameName n) | (a, r) <- resolved, n <- names r]
        excludedSet = Set.fromList excluded
        veto a = Set.member a excludedSet || Set.member (reverse (takeWhile (/= '.') (reverse a))) excludedSet
        -- Excluding any alias excludes the identity, not merely that spelling.
        vetoed = Set.fromList [q | (a, q) <- globals, veto a]
        allowed = Map.fromListWith Set.union
          [(q, Set.singleton a) | (a, q) <- globals, Set.notMember q vetoed]
        allowedIds = Set.fromList (map key (Map.keys allowed))
    when (Map.size allowed > 5000) $ genericError "scope-declaration-limit"
    -- Membership and exclusions are settled BEFORE querying types/features.
    meta <- lookupInteractionId point
    target <- instantiateFull =<< getMetaTypeInContext meta
    (query, goalNodes) <- either genericError pure (features target)
    (rows, nodes, dependencyNodes, _) <- foldM (\(previous, total, depTotal, bytesSoFar) (q, as) -> do
      ty <- instantiateFull =<< typeOfConst q
      (f, count) <- either genericError pure (features ty)
      when (total + count > 250000) $ genericError "scope-total-node-limit"
      -- The existing structural consumers expect the same Normalised view
      -- as Agda's module-contents command. Keep the ranking features on the
      -- original type: this view is not a new feature policy or typed IR.
      -- Count the reduced body before rendering it, still under the request
      -- deadline and local-state/dontAssignMetas isolation boundary.
      normalized <- normalise ty
      (_, viewCount) <- either genericError pure (features normalized)
      when (total + count + viewCount > 250000) $ genericError "scope-total-node-limit"
      view <- prettyShow <$> prettyTCM normalized
      when (length view > 65536) $ genericError "scope-type-view-limit"
      (refs, depCount) <- if withDependencies
        then dependencies allowedIds (250000 - total - count - viewCount) q
        else pure (Nothing, 0)
      let row = object $ ["id" .= key q, "aliases" .= Set.toAscList as,
                          "type" .= view, "features" .= f] ++
                          ["rhs_dependencies" .= refs | withDependencies]
          size = BL.length (encode row)
      when (bytesSoFar + size > 16 * 1024 * 1024) $ genericError "scope-output-limit"
      pure (row : previous, total + count + viewCount + depCount,
            depTotal + depCount, bytesSoFar + size))
      ([], goalNodes, 0, 0) (Map.toAscList allowed)
    let bytes = encode $ object $
          ["kind" .= ("AgdaProverScope" :: String),
           "schema_version" .= (if withDependencies then "agdaprover.live-scope.v5"
                                 else "agdaprover.live-scope.v4" :: String),
           "feature_policy" .= ("agda-term-body-head-symbol-arity-v1" :: String),
           "type_view_policy" .= ("agda-normalise-contextual-type-v1" :: String),
           "interaction_id" .= interactionId point,
           "excluded_names" .= excluded,
           "omitted_aliases" .= object ["ambiguous" .= ambiguous, "unnameable" .= unnameable],
           "target" .= query, "declarations" .= reverse rows,
           "structure_nodes" .= nodes] ++
          (if withDependencies then
            ["dependency_policy" .= ("permitted-clause-rhs-references-v1" :: String),
             "dependency_nodes" .= dependencyNodes] else [])
    unless (BL.length bytes <= 16 * 1024 * 1024) $ genericError "scope-output-limit"
    liftIO $ BL.putStrLn bytes
 where
  names = \case
    DefinedName _ a _ -> [a]
    FieldName as -> toList as
    ConstructorName _ as -> toList as
    -- Locals remain in the ordinary telescope. Pattern synonyms are not
    -- definition heads and are explicitly outside this first capability.
    _ -> []
