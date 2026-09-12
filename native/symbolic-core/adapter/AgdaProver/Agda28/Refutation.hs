{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
-- SPDX-License-Identifier: GPL-3.0-or-later
-- The existing closed abstract-implication fragment, bound to a source owner.
-- Neither this compiler nor a Boolean model is a proof authority.
module AgdaProver.Agda28.Refutation (Snapshot, Kind (..), kind, propose, viewFields) where

import Control.Monad (guard, mzero)
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.Maybe
import Data.Aeson (Value, object, (.=))
import Data.Aeson.Types (Pair)
import Data.Map.Strict qualified as Map
import Agda.Syntax.Abstract qualified as A
import Agda.Syntax.Abstract.Views (deepUnscope)
import Agda.Syntax.Common
import Agda.Syntax.Common.Pretty (prettyShow)
import Agda.Syntax.Internal qualified as I
import Agda.Syntax.Internal.MetaVars (noMetas)
import Agda.TypeChecking.Conversion (equalType)
import Agda.TypeChecking.Constraints (noConstraints)
import Agda.TypeChecking.Free (isBinderUsed)
import Agda.TypeChecking.Monad hiding (Candidate)
import Agda.TypeChecking.Pretty (prettyTCM)
import Agda.TypeChecking.Reduce (instantiateFull, reduceB)
import Agda.TypeChecking.Substitute (absApp, raise)
import AgdaProver.Symbolic.Focused (Formula (..))
import AgdaProver.Symbolic.Refutation qualified as R

data Claim = Claim String String Int Formula
data Kind = Unavailable | NoCounterexample | Censored | Candidate deriving Eq
data Snapshot = Snapshot Kind Integer (Maybe (Claim, R.Witness))

kind :: Snapshot -> Kind
kind (Snapshot value _ _) = value

-- Charge native classification separately from pure assignment enumeration.
-- The caller supplies both allowance/cancellation hooks; no fixed atom cap.
propose :: TCM Bool -> TCM Bool -> InteractionId -> TCM Snapshot
propose chargeQuery chargeAssignment point = do
  allowed <- chargeQuery
  if not allowed then pure $ Snapshot Censored 0 Nothing else do
    claim <- localTCState $ dontAssignMetas $ runMaybeT $ sourceClaim point
    case claim of
      Nothing -> pure $ Snapshot Unavailable 0 Nothing
      Just original@(Claim _ _ _ formula) -> R.findCounterexample chargeAssignment formula >>= \case
        R.Censored n -> pure $ Snapshot Censored n Nothing
        R.NoCounterexample n -> pure $ Snapshot NoCounterexample n Nothing
        R.Counterexample witness n -> pure $ Snapshot Candidate n $ Just (original, witness)

viewFields :: InteractionId -> Snapshot -> [Pair]
viewFields point (Snapshot status checked found) = outcome status checked $ case found of
  Nothing -> []
  Just (Claim owner original count formula, witness) ->
          [ "owner" .= owner, "original_type_display" .= original
          , "canonical_type" .= fullType count formula
          , "parameter_count" .= count, "formula" .= formulaView formula
          , "recipe" .= recipeView (R.refutation witness)
          , "valuation" .= [object ["atom" .= atom, "value" .= value]
                            | (atom, value) <- Map.toAscList $ R.valuation witness]
          , "module_source" .= compile count formula witness
          , "module_filename" .= ("AgdaProverRefutation.agda" :: String)
          ]
 where
  outcome :: Kind -> Integer -> [Pair] -> [Pair]
  outcome state measured extra =
    [ "schema_version" .= ("agdaprover.symbolic-refutation-proposal.v1" :: String)
    , "goal_id" .= interactionId point
    , "status" .= name state, "assignments_checked" .= measured
    , "proof_authority" .= False
    , "fragment" .= ("pure-implication-over-abstract-types-v1" :: String)
    ] ++ extra
  name :: Kind -> String
  name Unavailable = "not-applicable"
  name NoCounterexample = "no-counterexample"
  name Censored = "censored"
  name Candidate = "refutation-candidate"

sourceClaim :: InteractionId -> MaybeT TCM Claim
sourceClaim point = do
  interaction <- lift $ lookupInteractionPoint point
  function <- case ipClause interaction of
    IPClause function _ _ _ original _ -> do
      guard $ A.clauseWhereDecls original == A.noWhereDecls
      guard $ null $ A.spLhsPats $ A.clauseLHS original
      case A.clauseRHS original of
        A.RHS rhs _ | A.QuestionMark _ p <- deepUnscope rhs, p == point -> pure ()
        _ -> mzero
      pure function
    IPNoClause -> mzero
  definition <- lift $ getConstInfo function
  case theDef definition of
    Function { funWith = Nothing, funExtLam = Nothing } -> pure ()
    _ -> mzero
  -- A module parameter is a fixed local assumption, not a universally
  -- quantified argument of this goal. Do not strengthen that contextual claim.
  section <- lift $ lookupSection $ I.qnameModule function
  guard $ section == I.EmptyTel
  MaybeT $ inTopContext $ runMaybeT $ do
    full <- lift $ instantiateFull $ defType definition
    guard $ noMetas full
    (count, body) <- parameters 0 full
    guard $ count > 0
    formula <- arrows count body
    -- Classification is a proposal too. Ask Agda to equate its reconstructed
    -- native type with the ACTUAL closed source declaration, before exporting
    -- a standalone certificate for its canonical presentation.
    lift $ localTC (\env -> env { envRelevance = unitRelevance }) $
      noConstraints $ equalType full $ canonicalType count formula
    display <- lift $ prettyShow <$> prettyTCM full
    pure $ Claim (prettyShow function) display count formula
 where
  parameters count supplied = do
    ty <- viewType supplied
    case ty of
      I.El _ (I.Pi domain result) | getHiding domain == Hidden && ordinary domain -> do
        domainType <- viewType $ I.unDom domain
        case domainType of
          I.El _ (I.Sort sort) | sort == I.mkType 0 ->
            -- Abs bodies already have a new variable; NoAbs bodies must be
            -- raised into that same extended context, even for unused types.
            parameters (count+1) $ absBody result
          _ -> pure (count, ty)
      _ -> pure (count, ty)
  -- Keep each implicit type parameter as a variable in the body. No context
  -- lookup is needed for the restricted syntax; indices are checked explicitly.
  absBody (I.Abs _ body) = body
  absBody (I.NoAbs _ body) = raise 1 body
  arrows count supplied = viewType supplied >>= \case
    I.El _ (I.Var index []) | index >= 0 && index < count -> pure $ Atom (count-index-1)
    I.El _ (I.Pi domain result) -> do
      guard $ visible domain && ordinary domain && not (isBinderUsed result)
      Arrow <$> arrows count (I.unDom domain)
            <*> arrows count (absApp result $ I.Var 0 [])
    _ -> mzero
  ordinary domain = getModality domain == getModality defaultArgInfo
  viewType supplied = lift (reduceB supplied) >>= \case
    I.Blocked{} -> mzero
    I.NotBlocked _ value -> pure value

canonicalType :: Int -> Formula -> I.Type
canonicalType count formula = quantify 0
 where
  quantify n
    | n == count = body formula
    | otherwise = I.El (I.mkType 1) $ I.Pi
        (setHiding Hidden $ I.defaultDom $ I.El (I.mkType 1) $ I.Sort $ I.mkType 0)
        (I.Abs ("a" ++ show n) $ quantify $ n+1)
  body (Atom atom) = I.El (I.mkType 0) $ I.Var (count-atom-1) []
  body (Arrow a b) = I.El (I.mkType 0) $ I.Pi (I.defaultDom $ body a) $ I.NoAbs "_" $ body b

formulaView :: Formula -> Value
formulaView (Atom atom) = object ["tag" .= ("atom" :: String), "id" .= atom]
formulaView (Arrow a b) = object ["tag" .= ("arrow" :: String), "domain" .= formulaView a, "codomain" .= formulaView b]

closedView :: R.ClosedType -> Value
closedView R.Empty = object ["tag" .= ("empty" :: String)]
closedView R.Unit = object ["tag" .= ("unit" :: String)]
closedView (R.Function a b) = object ["tag" .= ("arrow" :: String), "domain" .= closedView a, "codomain" .= closedView b]

recipeView :: R.Expression -> Value
recipeView (R.Variable index) = object ["tag" .= ("variable" :: String), "index" .= index]
recipeView R.UnitValue = object ["tag" .= ("unit" :: String)]
recipeView (R.Lambda domain body) = object ["tag" .= ("lambda" :: String), "domain" .= closedView domain, "body" .= recipeView body]
recipeView (R.Apply f x) = object ["tag" .= ("apply" :: String), "function" .= recipeView f, "argument" .= recipeView x]
recipeView (R.Absurd result x) = object ["tag" .= ("absurd" :: String), "result" .= closedView result, "subject" .= recipeView x]

fullType :: Int -> Formula -> String
fullType count formula = concat ["{a" ++ show n ++ " : Set} → " | n <- [0..count-1]] ++ go formula
 where
  go (Atom atom) = "a" ++ show atom
  go (Arrow a b) = "(" ++ go a ++ " → " ++ go b ++ ")"

-- Only this tiny closed syntax is rendered, never arbitrary user pretty text.
-- The full type is alpha-renamed from the native declaration classification.
compile :: Int -> Formula -> R.Witness -> String
compile count formula witness = unlines
  [ "{-# OPTIONS --safe --without-K #-}"
  , "module AgdaProverRefutation where"
  , "data APEmpty : Set where"
  , "data APUnit : Set where apUnit : APUnit"
  , "apAbsurd : {X : Set} → APEmpty → X"
  , "apAbsurd ()"
  , "refute : (" ++ fullType count formula ++ ") → APEmpty"
  , "refute = λ h → " ++ expression [applied] (R.refutation witness)
  ]
 where
  applied = "h" ++ concat [" {" ++ (if Map.findWithDefault False n (R.valuation witness)
    then "APUnit" else "APEmpty") ++ "}" | n <- [0..count-1]]
  closedType R.Empty = "APEmpty"
  closedType R.Unit = "APUnit"
  closedType (R.Function a b) = "(" ++ closedType a ++ " → " ++ closedType b ++ ")"
  expression env (R.Variable index) = "(" ++ env !! index ++ ")"
  expression _ R.UnitValue = "apUnit"
  expression env (R.Lambda domain body) =
    let name = "x" ++ show (length env) in
    "(λ (" ++ name ++ " : " ++ closedType domain ++ ") → " ++ expression (name:env) body ++ ")"
  expression env (R.Apply f x) = "(" ++ expression env f ++ " " ++ expression env x ++ ")"
  expression env (R.Absurd result x) = "(apAbsurd {" ++ closedType result ++ "} " ++ expression env x ++ ")"
