{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE LambdaCase #-}

-- Shared ranking evidence for live and isolated worker observers. Callers
-- establish the allowed set BEFORE inspecting bodies; this grants no scope.
module ScopeEvidence (Summary (..), key, summarize, dependencies) where

import Data.List (foldl')
import Data.Maybe (catMaybes)
import Data.Set qualified as Set

import Agda.Syntax.Abstract.Name
import Agda.Syntax.Common (IsAbstract (AbstractDef), NameId (..), ModuleNameHash (..))
import Agda.Syntax.Internal
import Agda.Syntax.Internal.Generic (foldTerm)
import Agda.Syntax.Internal.MetaVars (noMetas)
import Agda.Syntax.Literal (Literal (LitQName))
import Agda.TypeChecking.Monad

key :: QName -> String
key q = case nameId (qnameName q) of
  NameId n (ModuleNameHash m) -> show m ++ ":" ++ show n

data Summary = Summary !Integer !(Set.Set String)

summarize :: [Term] -> Summary
summarize = foldl' (\(Summary count symbols) t ->
  Summary (count + 1) (foldl' (flip Set.insert) symbols (termSymbols t)))
  (Summary 0 Set.empty)

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
-- Raw metas (including assigned but uninstantiated ones) mean unavailable.
-- No traversal through a forbidden intermediate is exported to the retriever.
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
