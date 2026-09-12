{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE LambdaCase #-}
-- SPDX-License-Identifier: GPL-3.0-or-later
-- Goal-directed use of supplied evidence and its native endpoint contexts.
-- This is a proposal generator, not an equality solver or a rewriting axiom.
module AgdaProver.Agda28.ContextualEvidence (propose, Event (..)) where

import Control.Monad (forM, guard)
import Control.Monad.Except (catchError, throwError)
import Data.Foldable (toList)
import Data.IntSet qualified as IntSet
import Data.List (nubBy)
import Data.Maybe (catMaybes, maybeToList)
import Data.Monoid (Any (..))
import Data.Set qualified as Set
import Agda.Syntax.Abstract qualified as A
import Agda.Syntax.Abstract.Views (foldExpr)
import Agda.Syntax.Common
import Agda.Syntax.Info qualified as Info
import Agda.Syntax.Internal qualified as I
import Agda.Syntax.Internal.MetaVars (noMetas)
import Agda.Syntax.Position (noRange)
import Agda.Syntax.Scope.Base (isNameInScope)
import Agda.Syntax.Translation.InternalToAbstract (reify)
import Agda.TypeChecking.Constraints (noConstraints)
import Agda.TypeChecking.CheckInternal qualified as Internal
import Agda.TypeChecking.Conversion (compareTerm)
import Agda.TypeChecking.Free (allFreeVars)
import Agda.TypeChecking.Monad
import Agda.TypeChecking.ProjectionLike (elimView, ProjEliminator (EvenLone))
import Agda.TypeChecking.Reduce (instantiateFull, reduce)
import Agda.TypeChecking.Rules.Term (checkExpr, inferExpr')
import Agda.TypeChecking.Substitute (absApp, apply, raise)
import AgdaProver.Agda28.Algebra qualified as Algebra
import AgdaProver.Agda28.Construction qualified as Construction

data Head = DefinitionHead A.QName | ConstructorHead A.QName | LocalHead Int deriving Eq
data Template = Template (Maybe Head)
data Side = Source | Destination
data Event = Inventory Int Int Int | Matched | Grounded | Lifted | Drafted | Completed

-- Compute redexes, retaining a named neutral call when weak-head reduction
-- merely exposes another definition. This retains source aliases for generated
-- case functions without hiding constructor computations. Terms stay native;
-- Agda conversion remains the authority when an evidence operand is inferred.
contextView :: TCM Bool -> I.Term -> TCM I.Term
contextView inspect original = inspect >>= \available ->
  if not available then pure original else do
    exposed <- reduce original
    let chosen = case (original, exposed) of
          (I.Def a _, I.Def b _) | a /= b -> original
          (I.Def{}, I.Lam{}) -> original
          _ -> exposed
    case spine chosen of
      Nothing -> pure chosen
      Just (rebuild, args) -> rebuild <$> mapM (traverse $ contextView inspect) args

contextType :: TCM Bool -> I.Type -> TCM I.Type
contextType inspect ty = reduce ty >>= \(I.El sort term) -> I.El sort <$> contextView inspect term

-- CheckInternal.infer accepts neutral terms only and rejects prefix-form
-- record projections with an internal panic. Ask Agda for the elimination
-- view first; a non-neutral result is outside this proposal fragment.
relationType :: I.Term -> TCM (Maybe I.Type)
relationType term = elimView EvenLone term >>= \case
  value@I.Var{} -> Just <$> Internal.infer value
  value@(I.Def name _) -> isRelevantProjection name >>= \case
    Nothing -> Just <$> Internal.infer value
    Just _ -> pure Nothing
  _ -> pure Nothing

headAt :: Int -> I.Term -> Maybe Head
headAt _ (I.Def name _) = Just $ DefinitionHead name
headAt _ (I.Con name _ _) = Just $ ConstructorHead $ I.conName name
headAt depth (I.Var index _) | index >= depth = Just $ LocalHead $ index - depth
headAt _ _ = Nothing

-- Only result-determined applications belong in this accelerator. Every
-- explicit operand must occur in the selected endpoint; proofs requiring other
-- premises retain the ordinary application/AND search. No arity restriction.
template :: TCM Bool -> Side -> I.Type -> TCM (Maybe Template)
template inspect side = go []
 where
  go visibleBinders ty = inspect >>= \allowed ->
    if not allowed then pure Nothing else reduce ty >>= \case
      I.El _ (I.Pi domain body) -> underAbstractionAbs domain body $
        go (visible domain : visibleBinders)
      I.El _ raw -> do
        term <- contextView inspect raw
        pure $ do
          (_, left, right) <- Algebra.binary term
          guard $ noMetas term
          let endpoint = case side of Source -> left; Destination -> right
              explicit = IntSet.fromList [i | (i, True) <- zip [0..] visibleBinders]
          guard $ explicit `IntSet.isSubsetOf` allFreeVars endpoint
          pure $ Template $ headAt (length visibleBinders) endpoint

-- Paths traverse real, relevant ordinary operands of definitions, local
-- functions and constructors (including record constructors). Binders and
-- non-application eliminations remain opaque. Rebuilding preserves all other
-- eliminations, argument modalities, parameters and native name identities.
sites :: I.Term -> [([Int], I.Term)]
sites term = ([], term) : case spine term of
  Nothing -> []
  Just (_, args) -> [(i:path, value)
    | (i, I.Apply argument) <- zip [0..] args
    , visible argument, usableModality argument
    , (path, value) <- sites $ unArg argument]

spine :: I.Term -> Maybe ([I.Elim] -> I.Term, [I.Elim])
spine (I.Def name args) = Just (I.Def name, args)
spine (I.Var index args) = Just (I.Var index, args)
spine (I.Con name info args) = Just (I.Con name info, args)
spine _ = Nothing

replaceAt :: [Int] -> I.Term -> I.Term -> Maybe I.Term
replaceAt [] value _ = Just value
replaceAt (i:path) value term = do
  (rebuild, args) <- spine term
  case drop i args of
    I.Apply argument : rest -> do
      changed <- replaceAt path value $ unArg argument
      pure $ rebuild $ take i args ++ I.Apply (argument { unArg = changed }) : rest
    _ -> Nothing

attempt :: TCM (Maybe a) -> TCM (Maybe a)
attempt action = action `catchError` \case
  TypeError{} -> pure Nothing
  PatternErr{} -> pure Nothing
  err -> throwError err

app :: A.Expr -> [A.Expr] -> A.Expr
app function = A.app function . map (defaultArg . unnamed)

-- Internal QNames are not permission to print private implementations or to
-- reuse definitions created only while checking a draft. Ordinary search can
-- instead apply the already-scoped public alias. Keep this accelerator's
-- replay terms nameable and free of declaration-generating case expressions.
replayable :: Set.Set A.QName -> A.Expr -> TCM Bool
replayable excluded expression = do
  scope <- getScope
  let names = foldExpr (\case
        A.Def name -> Set.singleton name
        A.Con (I.AmbQ candidates) -> Set.fromList $ toList candidates
        A.Proj _ (I.AmbQ candidates) -> Set.fromList $ toList candidates
        _ -> Set.empty) expression
      helpers = getAny $ foldExpr (\case A.ExtendedLam{} -> Any True; _ -> Any False) expression
  pure $ not helpers && all (\name -> isNameInScope name scope && not (Set.member name excluded)) names

-- Inference and conversion are charged before use. Instantiation is Agda's:
-- fresh native metas for the complete telescope, then conversion with the
-- observed subterm. No printed matching or parallel home-grown unifier.
instantiate :: TCM Bool -> TCM Bool -> Side -> A.Expr -> I.Term -> TCM (Maybe (A.Expr, I.Type))
instantiate inspect check side expression source = Construction.preservingAllocations $ attempt $ do
  available <- inspect
  if not available then pure Nothing else do
    (value, ty) <- inferExpr' DontExpandLast expression
    fill value ty
 where
  fill value ty = inspect >>= \available ->
    if not available then pure Nothing else reduce ty >>= \case
      I.El _ (I.Pi domain body) -> do
        hole <- Construction.omittedField $ getHiding domain
        allowed <- check
        if not allowed then pure Nothing else do
          operand <- checkExpr hole $ I.unDom domain
          fill (apply value [Arg (getArgInfo domain) operand]) $ absApp body operand
      result@(I.El _ term) -> case Algebra.binary term of
        Nothing -> pure Nothing
        Just (relation, left, right) -> do
          allowed <- inspect
          if not allowed then pure Nothing else do
            -- Recover the endpoint domain from the native relation's Pi,
            -- rather than comparing terms at an unrelated inferred carrier.
            inferred <- relationType relation
            maybe (pure Nothing) (\ty' -> endpointDomain side ty' left) inferred >>= \case
              Nothing -> pure Nothing
              Just domain -> do
                equal <- check
                if not equal then pure Nothing else do
                  -- The subterm is already native in this checkpoint. Going
                  -- through abstract syntax here can re-elaborate generated
                  -- case functions into fresh declarations, whose names would
                  -- become invalid when this speculative scope rolls back.
                  Internal.checkInternal source CmpEq domain
                  let endpoint = case side of Source -> left; Destination -> right
                  converted <- check
                  if not converted then pure Nothing else do
                    noConstraints $ compareTerm CmpEq domain endpoint source
                    closed <- instantiateFull value
                    closedType <- contextType inspect =<< instantiateFull result
                    if noMetas closed && noMetas closedType
                      then (\e -> Just (e, closedType)) <$> reify closed else pure Nothing
  endpointDomain :: Side -> I.Type -> I.Term -> TCM (Maybe I.Type)
  endpointDomain selected ty left = reduce ty >>= \case
    I.El _ (I.Pi domain body) -> case selected of
      Source -> pure $ Just $ I.unDom domain
      Destination -> reduce (absApp body left) >>= \case
        I.El _ (I.Pi other _) -> pure $ Just $ I.unDom other
        _ -> pure Nothing
    _ -> pure Nothing

-- One decreasing rewrite yields an ordinary partial composition. All other
-- proposals stay in the shared agenda. This finite hint neither normalizes
-- proofs away nor merges paths with equal endpoints. In particular, it does
-- not invent injectivity, congruence, transitivity, or proof irrelevance.
propose :: Set.Set A.QName -> (Event -> TCM ()) -> TCM Bool -> TCM Bool -> I.Type
        -> [(A.Expr, I.Type, p)] -> TCM [(A.Expr, [p])]
propose excluded observe inspect check supplied seeds = do
  available <- inspect
  resolved <- if available then instantiateFull supplied else pure supplied
  if not available || not (noMetas resolved) then pure [] else do
    target <- contextType inspect resolved
    Algebra.relationView target >>= \case
      Nothing -> pure []
      Just view -> case Algebra.binary $ I.unEl target of
        Nothing -> pure []
        Just (relation, left, right) -> do
          roles <- forM seeds $ \(expression, ty, provenance) -> do
            allowed <- inspect
            found <- if allowed then Construction.preservingAllocations $
              attempt $ Algebra.inspectEvidence view ty else pure Nothing
            pure (expression, provenance, found)
          let maps = [(e,p) | (e,p,Just Algebra.Congruence) <- roles]
              joins = [(e,p) | (e,p,Just Algebra.Transitivity) <- roles]
              inverses = [(e,p) | (e,p,Just Algebra.Symmetry) <- roles]
          observe $ Inventory (length seeds) (length maps) (length joins)
          templates <- if null maps && null joins then pure [] else fmap catMaybes $
            forM [(seed, side) | seed <- seeds, side <- [Source, Destination]] $ \(seed@(_, ty, _), side) -> do
              shape <- Construction.preservingAllocations $ attempt $ template inspect side ty
              pure $ fmap (\form -> (seed, side, form)) shape
          -- Compare checked proof terms, not endpoints: two different proofs
          -- of the same relation must remain alternatives. This removes only
          -- duplicate discoveries (for example from opposite endpoints).
          let uniqueSteps = map (\(_,e,t,p) -> (e,t,p)) .
                nubBy (\(v,_,_,_) (w,_,_,_) -> v == w)
              steps destination current = fmap (uniqueSteps . concat) $
               forM templates $ \((expression, _, provenance), side, Template sourceHead) ->
               fmap concat $ forM (sites current) $ \(_, source) -> do
                if maybe False (\h -> headAt 0 source /= Just h) sourceHead
                  then pure [] else do
                    observe Matched
                    fact <- instantiate inspect check side expression source
                    case fact of
                      Nothing -> pure []
                      Just (proof, factType) -> case Algebra.binary $ I.unEl factType of
                        Just (_, original, replacement) | original /= replacement -> fmap concat $
                         forM [path | (path, value) <- sites current, value == original] $ \path -> do
                          observe Grounded
                          let changed = replaceAt path replacement current
                          next <- traverse (contextView inspect) changed
                          if not (maybe False (\t -> t == destination || I.termSize t < I.termSize current) next)
                            then pure [] else do
                              lifted <- if null path then pure [(proof, [])] else
                                case replaceAt path (I.Var 0 []) $ raise 1 current of
                                  Nothing -> pure []
                                  Just body -> do
                                    context <- reify $ I.Lam defaultArgInfo $ I.Abs "value" body
                                    pure [(app lift [context, proof], [p]) | (lift,p) <- maps]
                              fmap concat $ forM lifted $ \(edge, picked) ->
                                Construction.preservingAllocations $ attemptList $ do
                                  allowed <- check
                                  scoped <- if allowed then replayable excluded edge else pure False
                                  if not scoped then pure [] else do
                                    let edgeType = I.El (I.getSort target) $
                                          apply relation [defaultArg current, defaultArg $ maybe current id next]
                                    checkedEdge <- checkExpr edge edgeType
                                    closedEdge <- instantiateFull checkedEdge
                                    edgeNormal <- contextType inspect =<< instantiateFull edgeType
                                    case Algebra.binary $ I.unEl edgeNormal of
                                      Just (r,a,_) | noMetas closedEdge, noMetas edgeNormal, r == relation, a == current -> do
                                        observe Lifted
                                        -- Keep the checkpoint-owned endpoint,
                                        -- not a type reconstructed while
                                        -- checking an expanded case lambda.
                                        -- The complete proposal still passes
                                        -- through the source-owner checker.
                                        pure [(closedEdge, edge, maybe current id next, provenance:picked)]
                                      _ -> pure []
                        _ -> pure []
              -- One deterministic normalization lane is an additional closure
              -- proposal, not a replacement search. Strictly smaller native
              -- terms terminate it; every intermediate check consumes the same
              -- caller allowance. If it stalls, all one-step alternatives below
              -- still enter the ordinary AND/OR agenda.
              complete _ [] = pure Nothing
              complete destination ((edge, next, picked):_)
                | next == destination = pure $ Just (edge, picked)
                | otherwise = case joins of
                    [] -> pure Nothing
                    (join, provenance):_ -> do
                      suffix <- steps destination next >>= complete destination
                      pure $ fmap (\(proof, used) ->
                        (app join [edge, proof], picked ++ provenance:used)) suffix
              -- Evidence endpoints can hide the useful redex even when the
              -- target is already atomic. Adapt a supplied proof through
              -- checked endpoint paths, rather than changing its type for
              -- free or asking application search to rediscover those paths.
              -- Direct alternatives keep distinct proofs; the decreasing lane
              -- remains an extra hint, not an exhaustive replacement search.
              toward destination current
                | current == destination = pure [(Nothing, [])]
                | otherwise = do
                    options <- steps destination current
                    let direct = [(Just edge, picked) | (edge, next, picked) <- options,
                          next == destination]
                    if not (null direct) then pure direct else do
                      path <- complete destination options
                      pure [(Just edge, picked) | (edge, picked) <- maybeToList path]
              adapt (proof, ty, provenance) = do
                factType <- contextType inspect ty
                case Algebra.binary $ I.unEl factType of
                  Just (r, a, b) | r == relation, noMetas factType,
                    (a /= left || b /= right), a == left || not (null inverses) -> do
                    prefixes <- toward left a
                    suffixes <- if null prefixes then pure [] else toward right b
                    pure $ concat
                      [ let starts = case before of
                              Nothing -> [(proof, [provenance])]
                              Just edge -> [(app join [app inverse [edge], proof],
                                usedBefore ++ [reverseLabel, joinLabel, provenance])
                                | (inverse, reverseLabel) <- inverses, (join, joinLabel) <- joins]
                        in case after of
                          Nothing -> starts
                          Just edge -> [(app join [start, edge], used ++ joinLabel:usedAfter)
                            | (start, used) <- starts, (join, joinLabel) <- joins]
                      | (before, usedBefore) <- prefixes, (after, usedAfter) <- suffixes]
                  _ -> pure []
          initial <- steps right left
          completed <- case initial of
            (_, next, _):_ | next == right -> pure Nothing -- already a one-step alternative
            _ -> complete right initial
          case completed of
            Nothing -> pure ()
            Just _ -> observe Completed
          alternatives <- fmap concat $ forM initial $ \(edge, next, picked) ->
            if next == right then pure [(edge, picked)] else forM joins $ \(join, p) -> do
              scope <- getScope
              point <- registerInteractionPoint False noRange Nothing
              let hole = A.QuestionMark (Info.emptyMetaInfo { Info.metaScope = scope }) point
              observe Drafted
              pure (app join [edge, hole], p:picked)
          adapted <- if null joins then pure [] else concat <$> mapM adapt seeds
          mapM_ (const $ observe Completed) adapted
          pure $ maybe [] pure completed ++ alternatives ++ adapted
 where
  attemptList action = maybe [] id <$> attempt (Just <$> action)
