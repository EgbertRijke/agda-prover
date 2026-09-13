{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE LambdaCase #-}
-- SPDX-License-Identifier: GPL-3.0-or-later
module AgdaProver.Agda28.Recursion
  ( Owner, owner, ownerName, ownerGroup, checkOwner, CallContext, inspect, callHead, callType
  , eligibleCall, callSubjects, callOperands, copatternCall, descentFacts, usesOwner ) where

import Control.Monad (unless, forM)
import Data.List (find, nub)
import Data.Maybe (mapMaybe, catMaybes)
import Data.IntSet qualified as IntSet
import Data.Map.Strict qualified as Map
import Data.Monoid (Any (..))
import Data.Set qualified as Set

import Agda.Interaction.MakeCase (recheckAbstractClause)
import Agda.Syntax.Abstract qualified as A
import Agda.Syntax.Abstract.Name (Name, QName)
import Agda.Syntax.Abstract.Views (foldExpr)
import Agda.Syntax.Common
import Agda.Syntax.Internal qualified as I
import Agda.Syntax.Internal.MetaVars (noMetas)
import Agda.Syntax.Internal.Pattern (patternsToElims)
import Agda.Syntax.Translation.InternalToAbstract (reify)
import Agda.Termination.TermCheck (termMutual)
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Free (allFreeVars)
import Agda.TypeChecking.Records (getRecordOfField, getRecordDef)
import Agda.TypeChecking.Reduce (reduceB)
import Agda.TypeChecking.Substitute (applySubst, parallelS)

-- An owner comes only from a checked source clause, never a supplied string.
-- Child goals inherit it across generated helpers. It does not make the owner
-- an ordinary visible premise or certify termination of any application.
newtype Owner = Owner { ownerName :: QName }
data CallAccess
  = ConstructorDescendants (Set.Set Name)
  | WithAncestryUnknown (Set.Set Name)
  | CoinductiveCopattern
data CallContext = CallContext Owner CallAccess [Name] [I.Term]

ownerGroup :: Owner -> TCM (Set.Set QName)
ownerGroup (Owner function) = do
  definition <- getConstInfo function
  mutualNames <$> lookupMutualBlock (defMutual definition)

checkOwner :: Owner -> A.Expr -> TCM ()
checkOwner (Owner function) expression = do
  block <- defMutual <$> getConstInfo function
  -- give restores a saved meta environment, which can create new lambda
  -- helpers in a separate block. Restore source-equivalent group membership
  -- for those newly declared native helpers before asking Agda about cycles.
  let helpers = foldExpr (\case
        A.ExtendedLam _ _ _ name _ -> Set.singleton name
        _ -> Set.empty) expression
  mapM_ (setMutualBlock block) helpers
  errors <- localTC (\env -> env { envMutualBlock = Just block }) $ termMutual []
  unless (null errors) $ genericError "native-recursive-call-termination-rejected"

owner :: InteractionId -> TCM (Maybe Owner)
owner point = lookupInteractionPoint point >>= \interaction -> case ipClause interaction of
  IPNoClause -> pure Nothing
  IPClause function _ _ _ _ _ -> sourceOwner function
 where
  sourceOwner function = getConstInfo function >>= \definition -> case theDef definition of
    Function { funWith = Just parent } -> sourceOwner parent
    Function { funExtLam = Nothing } -> pure $ Just $ Owner function
    _ -> pure Nothing

-- Reuse Agda's clause recheck, including forcing and dependent substitutions.
-- Constructor-descendant identity is only a proposal seed. Coinductive
-- observations are not an inductive descent witness; final give/validation
-- still owns actual termination, including wrappers and higher-order children.
inspect :: InteractionId -> Owner -> TCM (Maybe CallContext)
inspect point root = do
  interaction <- lookupInteractionPoint point
  case ipClause interaction of
    IPNoClause -> pure Nothing
    IPClause function _ ty sub clause closure -> do
      (checked, context, _) <- enterClosure closure $ \_ -> locallyTC eMakeCase (const True) $
        recheckAbstractClause ty sub clause
      current <- getContext
      let names = mapMaybe (nameAt context) $ concatMap (descendants False . namedArg) $
            I.namedClausePats checked
          available = Set.fromList $ map ctxEntryName current
          retained = Set.intersection available $ Set.fromList names
      definition <- getConstInfo function
      projections <- forM [field | I.ProjP _ field <- map namedArg $ I.namedClausePats checked] $ \field ->
        getRecordOfField field >>= \case
          Nothing -> pure False
          Just record -> (== Just CoInductive) . _recInduction <$> getRecordDef record
      -- A with-function can abstract away a parent constructor pattern. Its
      -- missing local witness is unknown descent, not evidence of no descent.
      -- Retain a typed fallback; Agda's full owner-group check decides validity.
      let seeds
            | or projections = Just CoinductiveCopattern
            | not (Set.null retained) = Just $ ConstructorDescendants retained
            | Function { funWith = Just _ } <- theDef definition
            , not (Set.null available) = Just $ WithAncestryUnknown available
            | otherwise = Nothing
      -- Keep the checked argument structure separately from descent evidence.
      -- A reconstructed parent argument can fill an unchanged coordinate of a
      -- recursive call; it is not itself a certificate of strict decrease.
      let arguments = [unArg argument | I.Apply argument <- patternsToElims $ I.namedClausePats checked,
            usableModality argument, noMetas $ unArg argument]
      pure $ (\access -> CallContext root access (map ctxEntryName context) arguments) <$> seeds
 where
  nameAt context index = ctxEntryName . snd <$> find ((== index) . fst) (zip [0..] context)
  descendants proper = \case
    I.VarP _ variable | proper -> [I.dbPatVarIndex variable]
    I.ConP constructor _ patterns
      | I.conInductive constructor == Inductive -> concatMap (descendants True . namedArg) patterns
    _ -> []

callHead :: CallContext -> A.Expr
callHead (CallContext (Owner function) _ _ _) = A.Def function

callType :: CallContext -> TCM I.Type
callType (CallContext (Owner function) _ _ _) = typeOfConst function

-- Rebase checked clause arguments by binder identity, not de Bruijn position
-- or display spelling. Generated helpers can remove/reorder the clause context.
-- Unavailable free variables decline the operand instead of being guessed.
-- Callers still filter visibility, infer its type and check complete calls.
callOperands :: TCM Bool -> CallContext -> TCM [A.Expr]
callOperands charge (CallContext _ _ names arguments) = do
  current <- getContext
  let indices = Map.fromList $ zip (map ctxEntryName current) [0..]
      retained = IntSet.fromList [index | (index, name) <- zip [0..] names, Map.member name indices]
      -- Missing slots are unreachable after the free-variable check below.
      substitution = parallelS [I.Var (Map.findWithDefault 0 name indices) [] | name <- names]
  fmap (nub . catMaybes) $ forM arguments $ \argument -> do
    allowed <- charge
    if not allowed || not (allFreeVars argument `IntSet.isSubsetOf` retained)
      then pure Nothing else Just <$> reify (applySubst substitution argument)

-- Keep proposal subjects as scoped native variables. The agenda may apply a
-- function-valued child to holes, but neither spelling nor result-type shape
-- can manufacture a descent witness. Unknown with-ancestry retains the same
-- conservative fallback as the coarse evidence search.
callSubjects :: CallContext -> TCM [A.Expr]
callSubjects context = do
  current <- getContext
  pure [expression | entry <- current, let expression = A.Var $ ctxEntryName entry,
    not (copatternCall context), eligibleCall context expression]

-- A real coinductive projection admits a fully applied owner proposal without
-- asserting descent. It does not prove guarding: give and the complete mutual
-- group's termination/productivity check must still accept the candidate.
copatternCall :: CallContext -> Bool
copatternCall (CallContext _ CoinductiveCopattern _ _) = True
copatternCall _ = False

descentFacts :: CallContext -> TCM (Maybe Bool, Maybe Bool)
descentFacts (CallContext _ (ConstructorDescendants names) _ _) = do
  context <- getContext
  shapes <- forM [index | (index, entry) <- zip [0..] context, Set.member (ctxEntryName entry) names] $ \index ->
    (reduceB =<< typeOfBV index) >>= \case
      I.Blocked{} -> pure Nothing
      I.NotBlocked _ (I.El _ I.Pi{}) -> pure $ Just True
      I.NotBlocked _ (I.El _ I.MetaV{}) -> pure Nothing
      I.NotBlocked _ (I.El _ I.Var{}) -> pure Nothing
      _ -> pure $ Just False
  let higher | Just True `elem` shapes = Just True
             | all (== Just False) shapes = Just False
             | otherwise = Nothing
  pure (Just True, higher)
descentFacts _ = pure (Nothing, Nothing)

eligibleCall :: CallContext -> A.Expr -> Bool
eligibleCall (CallContext _ CoinductiveCopattern _ _) _ = True
eligibleCall (CallContext _ seeds _ _) expression = getAny $ foldExpr (\case
  A.Var name -> Any $ Set.member name names
  _ -> Any False) expression
 where
  names = case seeds of
    ConstructorDescendants known -> known
    WithAncestryUnknown possible -> possible

usesOwner :: Owner -> A.Expr -> Bool
usesOwner (Owner function) = getAny . foldExpr (\case
  A.Def name -> Any $ name == function
  _ -> Any False)
