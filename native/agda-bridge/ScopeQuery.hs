{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

-- A ranking-only projection from the live interaction closure. No source
-- scanner, private inventory, held-out proof, or unfiltered corpus participates.
module ScopeQuery (emit, request) where

import Control.Monad (foldM, unless, when)
import Control.Monad.IO.Class (liftIO)
import Control.Monad.Except (runExceptT, throwError)
import Control.Monad.Trans (lift)
import Data.Aeson (FromJSON (parseJSON), Value, eitherDecodeStrict', encode, object, withObject, (.:), (.=))
import Data.Aeson.KeyMap qualified as KeyMap
import Data.ByteString.Lazy.Char8 qualified as BL
import Data.Foldable (toList)
import Data.Map.Strict qualified as Map
import Data.List (foldl', stripPrefix)
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
import Agda.TypeChecking.Conversion (equalType, tryConversion)
import Agda.TypeChecking.Pretty (prettyTCM)
import Agda.TypeChecking.Reduce (instantiateFull, normalise)

request :: String -> Maybe (Bool, Bool, String)
request payload = first
  [("v9", True, True), ("v8", False, True),
   ("v7", True, False), ("v6", False, False)]
 where
  first [] = Nothing
  first ((version, deps, views) : rest) =
    case stripPrefix ("agdaprover:scoped-retrieval:" ++ version ++ ":") payload of
      Just exclusions -> Just (deps, views, exclusions)
      Nothing -> first rest

-- The caller owns the operational output reservation. Geometry is evidence,
-- not a second implicit allowance. The transport separately enforces CPU,
-- memory, wall time, input/output bytes and cancellation for the owned process.
data ScopeRequest = ScopeRequest [String] Integer

instance FromJSON ScopeRequest where
  parseJSON = withObject "scope request" $ \o -> do
    unless (Set.fromList (KeyMap.keys o) == Set.fromList ["excluded_names", "output_bytes"]) $
      fail "invalid scope request fields"
    excluded <- o .: "excluded_names"
    limit <- o .: "output_bytes"
    unless (limit > 0 && all (\n -> not (null n) && '\0' `notElem` n) excluded
            && excluded == Set.toAscList (Set.fromList excluded)) $
      fail "invalid scope request"
    pure (ScopeRequest excluded limit)

schema :: Bool -> Bool -> String
schema withDependencies withQueryViews
  | withQueryViews = if withDependencies then "agdaprover.live-scope.v9"
                    else "agdaprover.live-scope.v8"
  | otherwise = if withDependencies then "agdaprover.live-scope.v7"
                else "agdaprover.live-scope.v6"

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
data Summary = Summary !Integer !(Set.Set String)

summarize :: [Term] -> Summary
summarize = foldl' (\(Summary count symbols) t ->
  Summary (count + 1) (foldl' (flip Set.insert) symbols (termSymbols t)))
  (Summary 0 Set.empty)

features :: Type -> (Value, Integer)
features ty =
  let Summary count symbols = summarize (foldTerm (: []) ty)
      (head', arity) = headArity ty
  in (object ["result_head" .= head', "symbols" .= Set.toAscList symbols, "arity" .= arity], count)

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
dependencies :: Set.Set String -> QName -> TCM (Maybe [String], Integer)
dependencies allowed q = do
  def <- getConstInfo q
  case theDef def of
    FunctionDefn f | defAbstract def /= AbstractDef -> do
      let bodies = catMaybes (map clauseBody (_funClauses f))
          Summary count symbols = summarize (concatMap (foldTerm (: [])) bodies)
      pure (if noMetas bodies then
              Just $ Set.toAscList $ Set.delete (key q) $
                Set.intersection allowed symbols
            else Nothing, count)
    _ -> pure (Nothing, 0)

emit :: Bool -> Bool -> InteractionId -> String -> TCM ()
emit withDependencies withQueryViews point payload = do
  ScopeRequest excluded limit <- either (const $ genericError "invalid-scope-request") pure $
    eitherDecodeStrict' (Text.encodeUtf8 (Text.pack payload))
  withInteractionId point $ dontAssignMetas $ do
    scope <- getScope
    let concrete = Set.toAscList (concreteNamesInScope scope)
        nameable = all (not . C.isNoName) . C.qnameParts
        aliases = filter nameable concrete
        unnameable = Set.toAscList $ Set.fromList
          [prettyShow a | a <- concrete, not (nameable a)]
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
    -- Membership and exclusions are settled BEFORE querying types/features.
    meta <- lookupInteractionId point
    target <- instantiateFull =<< getMetaTypeInContext meta
    let (query, goalNodes) = features target
    -- Normalize inside the ORIGINAL interaction telescope. Closing the goal
    -- would change local head coordinates and arity. Ordinary reduction keeps
    -- abstraction/opacity in force; conversion cannot assign unresolved metas.
    (queryFields, queryNodes) <- if withQueryViews then do
      normalized <- normalise target
      ok <- localTC (\e -> e { envRelevance = unitRelevance }) $
        tryConversion $ equalType target normalized
      unless ok $ genericError "query-normalization-conversion-failed"
      let (f, count) = features normalized
      pure (["normalized_query" .= object
        ["policy" .= ("agda-normalise-query-type-v1" :: String),
         "features" .= f, "structure_nodes" .= count,
         "conversion_checked" .= True]], count)
     else pure ([], 0)
    outcome <- runExceptT $ do
     (rows, nodes, dependencyNodes, _) <- foldM (\(previous, total, depTotal, bytesSoFar) (q, as) -> do
      ty <- lift $ instantiateFull =<< typeOfConst q
      let (f, count) = features ty
      -- The existing structural consumers expect the same Normalised view
      -- as Agda's module-contents command. Keep the ranking features on the
      -- original type: this view is not a new feature policy or typed IR.
      -- Count the reduced body before rendering it, still under the request
      -- deadline and local-state/dontAssignMetas isolation boundary.
      normalized <- lift $ normalise ty
      let !viewCount = foldl' (\n _ -> n + 1) 0 (foldTerm (: []) normalized)
      view <- lift $ prettyShow <$> prettyTCM normalized
      (refs, depCount) <- if withDependencies
        then lift $ dependencies allowedIds q
        else pure (Nothing, 0)
      let row = object $ ["id" .= key q, "aliases" .= Set.toAscList as,
                          "type" .= view, "features" .= f] ++
                          ["rhs_dependencies" .= refs | withDependencies]
          size = toInteger (BL.length (encode row))
      -- A lower bound on final encoded bytes permits early refusal, but never
      -- publishes the rows accumulated so far as a complete observation.
      when (bytesSoFar + size > limit) $ throwError (bytesSoFar + size)
      let !nextTotal = total + count + viewCount + depCount
          !nextDeps = depTotal + depCount
      pure (row : previous, nextTotal, nextDeps, bytesSoFar + size))
      ([], goalNodes + queryNodes, 0, 0) (Map.toAscList allowed)
     let bytes = encode $ object $
          ["kind" .= ("AgdaProverScope" :: String),
           "schema_version" .= schema withDependencies withQueryViews,
           "output_bytes" .= limit,
           "feature_policy" .= ("agda-term-body-head-symbol-arity-v1" :: String),
           "type_view_policy" .= ("agda-normalise-contextual-type-v1" :: String),
           "interaction_id" .= interactionId point,
           "excluded_names" .= excluded,
           "omitted_aliases" .= object ["ambiguous" .= ambiguous, "unnameable" .= unnameable],
           "target" .= query, "declarations" .= reverse rows,
           "structure_nodes" .= nodes] ++ queryFields ++
          (if withDependencies then
            ["dependency_policy" .= ("permitted-clause-rhs-references-v1" :: String),
             "dependency_nodes" .= dependencyNodes] else [])
     let size = toInteger (BL.length bytes)
     when (size > limit) $ throwError size
     pure bytes
    liftIO $ BL.putStrLn $ case outcome of
      Right bytes -> bytes
      Left observed -> encode $ object
        ["kind" .= ("AgdaProverScopeResource" :: String),
         "schema_version" .= ("agdaprover.live-scope-resource.v1" :: String),
         "request_schema" .= schema withDependencies withQueryViews,
         "interaction_id" .= interactionId point,
         "resource" .= ("output-bytes" :: String),
         "limit" .= limit,
         "observed_lower_bound" .= observed]
 where
  names = \case
    DefinedName _ a _ -> [a]
    FieldName as -> toList as
    ConstructorName _ as -> toList as
    -- Locals remain in the ordinary telescope. Pattern synonyms are not
    -- definition heads and are explicitly outside this first capability.
    _ -> []
