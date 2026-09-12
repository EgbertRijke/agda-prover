{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE LambdaCase #-}
-- SPDX-License-Identifier: GPL-3.0-or-later
module AgdaProver.Agda28.Recursion
  ( Owner, owner, ownerName, ownerGroup, checkOwner, CallContext, inspect, callHead, usesSeed, usesOwner ) where

import Control.Monad (unless)
import Data.List (find)
import Data.Maybe (mapMaybe)
import Data.Monoid (Any (..))
import Data.Set qualified as Set

import Agda.Interaction.MakeCase (recheckAbstractClause)
import Agda.Syntax.Abstract qualified as A
import Agda.Syntax.Abstract.Name (Name, QName)
import Agda.Syntax.Abstract.Views (foldExpr)
import Agda.Syntax.Common
import Agda.Syntax.Internal qualified as I
import Agda.Termination.TermCheck (termMutual)
import Agda.TypeChecking.Monad

-- An owner comes only from a checked source clause, never a supplied string.
-- Child goals inherit it across generated helpers. It does not make the owner
-- an ordinary visible premise or certify termination of any application.
newtype Owner = Owner { ownerName :: QName }
data DescentSeeds = ConstructorDescendants (Set.Set Name) | WithAncestryUnknown (Set.Set Name)
data CallContext = CallContext Owner DescentSeeds

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
      -- A with-function can abstract away a parent constructor pattern. Its
      -- missing local witness is unknown descent, not evidence of no descent.
      -- Retain a typed fallback; Agda's full owner-group check decides validity.
      let seeds
            | not (Set.null retained) = Just $ ConstructorDescendants retained
            | Function { funWith = Just _ } <- theDef definition
            , not (Set.null available) = Just $ WithAncestryUnknown available
            | otherwise = Nothing
      pure $ CallContext root <$> seeds
 where
  nameAt context index = ctxEntryName . snd <$> find ((== index) . fst) (zip [0..] context)
  descendants proper = \case
    I.VarP _ variable | proper -> [I.dbPatVarIndex variable]
    I.ConP constructor _ patterns
      | I.conInductive constructor == Inductive -> concatMap (descendants True . namedArg) patterns
    _ -> []

callHead :: CallContext -> A.Expr
callHead (CallContext (Owner function) _) = A.Def function

usesSeed :: CallContext -> A.Expr -> Bool
usesSeed (CallContext _ seeds) = getAny . foldExpr (\case
  A.Var name -> Any $ Set.member name names
  _ -> Any False)
 where
  names = case seeds of
    ConstructorDescendants known -> known
    WithAncestryUnknown possible -> possible

usesOwner :: Owner -> A.Expr -> Bool
usesOwner (Owner function) = getAny . foldExpr (\case
  A.Def name -> Any $ name == function
  _ -> Any False)
