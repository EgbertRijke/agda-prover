{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE LambdaCase #-}
-- SPDX-License-Identifier: GPL-3.0-or-later
module AgdaProver.Agda28.HelperConstruction (Step (..), generate) where

import Control.Monad (guard, forM, void)
import Control.Monad.Except (catchError, throwError)
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.Maybe (MaybeT (..))
import Data.List.NonEmpty (NonEmpty (..))

import Agda.Interaction.BasicOps (give_, parseExprIn)
import Agda.Interaction.Base (UseForce (WithoutForce))
import Agda.Interaction.MakeCase (makeCase)
import Agda.Syntax.Abstract qualified as A
import Agda.Syntax.Abstract.Name (Name, nameConcrete, qualify)
import Agda.Syntax.Abstract.Pattern (lhsToSpine)
import Agda.Syntax.Abstract.Views (deepUnscope, appView, AppView' (Application))
import Agda.Syntax.Common
import Agda.Syntax.Common.Pretty (prettyShow)
import Agda.Syntax.Info qualified as Info
import Agda.Syntax.Internal qualified as I
import Agda.Syntax.Position (noRange)
import Agda.Syntax.Scope.Base
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Reduce (reduce)
import Agda.TypeChecking.Rules.Term (isType_)
import Agda.TypeChecking.Substitute (absApp, raise)
import Agda.Utils.Lens ((^.))
import Agda.Utils.Null (empty)

import AgdaProver.Agda28.ClauseExecution (patternLocals)
import AgdaProver.Agda28.Helpers qualified as Helpers
import AgdaProver.Symbolic.Protocol (ObservationMode)
import AgdaProver.Symbolic.SessionTypes (DraftExpression (..))

data Step = InferSignature | InspectSignature | CheckScaffold | GenerateClauses

-- Finite existing fragment: split one one-constructor operand and return one
-- of the resulting available explicit arguments/fields. Agda performs actual
-- dependent splitting, coverage and checking; this is not a hand-built matcher.
generate :: (Step -> TCM Bool) -> TCM () -> InteractionId -> ObservationMode -> DraftExpression
         -> TCM (Maybe [A.Expr])
generate allow rejected point mode draft@(DraftExpression source) = withInteractionId point $ do
  initial <- getTC
  result <- runMaybeT $ do
    snapshot <- charged InferSignature $ Helpers.infer point mode draft
    let signature = Helpers.signature snapshot
    -- Parse only the caller's input, not the inferred signature. The local
    -- binder and its application retain Agda's native binding identities.
    helperName <- case words source of
      first:_ -> pure first
      [] -> MaybeT $ pure Nothing
    parsed <- charged InspectSignature $ parseExprIn point noRange $
      "let " ++ helperName ++ " = _ in " ++ source
    (binding, body) <- case deepUnscope parsed of
      A.Let _ (A.LetBind _ _ name _ _ :| []) expression -> pure (name, expression)
      _ -> MaybeT $ pure Nothing
    ty <- charged InspectSignature $ isType_ signature
    let Application _ arguments = appView body
        arity = length $ filter visible arguments
    (patterns, slots) <- lift $ telescope allow 0 arity ty
    originalScope <- lift getScope
    fmap concat $ forM slots $ \subject -> MaybeT $ do
      saved <- getTC
      candidate <- runMaybeT (construct signature binding body patterns originalScope subject)
        `catchError` \err -> case err of
          TypeError{} -> rejected >> pure (Just [])
          PatternErr{} -> rejected >> pure (Just [])
          _ -> throwError err
      allocation <- getTC
      restore saved allocation
      pure candidate
  allocation <- getTC
  restore initial allocation
  pure result
 where
  charged step action = do
    allowed <- lift $ allow step
    guard allowed
    lift action
  construct signature binding body patterns originalScope subject = do
    helper <- lift $ qualify <$> currentModule <*> freshName_ "helperClauses"
    let info = Info.mkDefInfo (nameConcrete $ A.unBind binding) empty PublicAccess ConcreteDef noRange
        build clause = A.Let Info.exprNoRange
          (A.LetBind (Info.LetRange noRange) defaultArgInfo binding signature
            (A.ExtendedLam Info.exprNoRange info defaultErased helper (clause :| [])) :| []) body
        scope = setScopeLocals (concatMap patternLocals patterns ++ _scopeLocals originalScope) originalScope
    temporary <- lift $ registerInteractionPoint False noRange Nothing
    let hole = A.QuestionMark (Info.emptyMetaInfo { Info.metaScope = scope }) temporary
        clause = A.Clause (A.LHS empty $ A.LHSHead helper patterns) []
          (A.RHS hole Nothing) A.noWhereDecls empty
    charged CheckScaffold $ void $ give_ False WithoutForce point Nothing $ build clause
    (_, _, generated) <- charged GenerateClauses $ makeCase temporary noRange $ prettyShow $ nameConcrete subject
    pure $ case generated of
      [single] -> case A.clauseRHS single of
        A.AbsurdRHS -> [build single]
        A.RHS{} ->
          [build single { A.clauseRHS = A.RHS (A.Var name) Nothing }
          | (_, LocalVar name (PatternBound NotHidden) _) <-
              concatMap patternLocals $ A.spLhsPats $ A.clauseLHS $ lhsToSpine single]
        _ -> []
      _ -> []

-- Walk the actual telescope under its binders. Names exist to connect Agda's
-- clause operation to those binders; the eligibility test inspects native
-- datatype/record metadata, never those names or a printed domain.
telescope :: (Step -> TCM Bool) -> Int -> Int -> I.Type -> TCM ([NamedArg A.Pattern], [Name])
telescope _ _ 0 _ = pure ([], [])
telescope allow index remaining ty = do
  allowed <- allow InspectSignature
  if not allowed then pure ([], []) else reduce ty >>= \case
    I.El _ (I.Pi domain codomain) -> do
      name <- freshName_ $ "helperArgument" ++ show index
      eligible <- if not (visible domain) then pure False else singleConstructor $ I.unDom domain
      (rest, slots) <- addContext (name, domain) $
        -- Do not turn a function-valued RESULT into additional helper input.
        -- The caller's native application spine determines the explicit inputs.
        telescope allow (index + 1) (remaining - if visible domain then 1 else 0) $
          absApp (raise 1 codomain) (I.Var 0 [])
      pure (Arg (getArgInfo domain) (unnamed $ A.VarP $ A.mkBindName name) : rest,
        [name | eligible] ++ slots)
    _ -> pure ([], [])

singleConstructor :: I.Type -> TCM Bool
singleConstructor ty = reduce ty >>= \case
  I.El _ (I.Def name _) -> do
    definition <- getConstInfo name
    pure $ case theDef definition of
      Datatype { dataCons = [_] } -> True
      RecordDefn record -> _recInduction record /= Just CoInductive
      _ -> False
  _ -> pure False

restore :: TCState -> TCState -> TCM ()
restore saved allocation = do
  putTC saved
  stFreshNameId `setTCLens` (allocation ^. stFreshNameId)
  stFreshInteractionId `setTCLens` (allocation ^. stFreshInteractionId)
