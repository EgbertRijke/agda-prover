{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE FlexibleContexts #-}
-- SPDX-License-Identifier: GPL-3.0-or-later
-- In-memory implication proposals. Atoms are identities supplied by a typed
-- adapter, never names or parsed pretty-printing. No kernel operations here.
module AgdaProver.Symbolic.Focused
  ( Formula (..), Proof (..), Solution (..), Action (..), Event (..), Hooks (..)
  , enumerate, domainsResult ) where

import Control.Monad.State.Strict
import Data.List (sortOn)
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set

data Formula = Atom Int | Arrow Formula Formula deriving (Eq, Ord, Show)
data Proof = Variable Int | Lambda Formula Proof | Apply Proof [Proof]
  | Absurd Formula Proof deriving (Eq, Ord, Show)
data Solution label = Solution { proof :: Proof, decisions :: [label] }
  deriving (Eq, Show)
data Action = Action { assumption :: Int, domains :: [Formula], absurdResult :: Bool }
  deriving (Eq, Show)
data Event = Node | Rule | CacheHit | CyclePruned | Deferred deriving (Eq, Show)
data Hooks m label = Hooks
  { charge :: m Bool
  , observe :: Event -> m ()
  , order :: Formula -> [Formula] -> [Action] -> m [(Action, [label])] }

domainsResult :: Formula -> ([Formula], Formula)
domainsResult = go []
 where
  go acc (Arrow domain result) = go (domain:acc) result
  go acc result = (reverse acc, result)

size :: Formula -> Int
size (Atom _) = 1
size (Arrow a b) = 1 + size a + size b

-- Positive witnesses only. Failure beneath an active cycle, a resource bound,
-- or a rejected downstream continuation is never cached as logical failure.
-- Replaying a positive witness does not cut off any other local inhabitant.
enumerate :: Monad m => Hooks m label -> Set.Set Int -> Int -> [Formula] -> Formula
          -> (Solution label -> m (Maybe a)) -> m (Maybe a)
enumerate hooks emptyAtoms depth context target use =
  evalStateT (solve Set.empty depth context target $ lift . use) Map.empty
 where
  event = lift . observe hooks
  allowed = lift $ charge hooks
  choices [] = pure Nothing
  choices (next:rest) = next >>= maybe (choices rest) (pure . Just)
  solve active remaining assumptions goal accept
    | remaining < 0 = event Deferred >> pure Nothing
    | otherwise = do
      ok <- allowed
      if not ok then pure Nothing else do
        event Node
        let key = (assumptions, goal)
        known <- gets $ Map.findWithDefault [] key
        let cached solution = do
              ok' <- allowed
              if ok' then event CacheHit >> accept solution else pure Nothing
            remember solution = do
              modify' $ Map.insertWith (flip (++)) key [solution]
              accept solution
            fresh solution
              | any ((== proof solution) . proof) known = pure Nothing
              | otherwise = remember solution
            expand
              | Set.member key active = event CyclePruned >> pure Nothing
              | otherwise = search (Set.insert key active) remaining assumptions goal fresh
        choices $ map cached known ++ [expand]
  search active remaining assumptions goal accept = choices
    ([rule $ accept $ Solution (Variable index) []
      | (index, ty) <- zip [0..] assumptions, ty == goal]
     ++ [introduce active remaining assumptions goal accept | isArrow goal]
     ++ [focus active remaining assumptions goal accept])
  rule action = do
    ok <- allowed
    if ok then event Rule >> action else pure Nothing
  isArrow Arrow{} = True
  isArrow _ = False
  -- A whole nondependent right telescope is invertible: charge one phase and
  -- keep its individual binders in the proof, without a depth cap per binder.
  introduce active remaining assumptions goal accept = rule $
    let (introduced, result) = domainsResult goal
    in solve active (remaining-1) (assumptions ++ introduced) result $ \answer ->
      accept answer { proof = foldr Lambda (proof answer) introduced }
  focus active remaining assumptions goal accept = do
    let candidates =
          [Action index args absurd
          | (index, ty) <- zip [0..] assumptions
          , let (args, result) = domainsResult ty
                absurd = case result of Atom atom -> Set.member atom emptyAtoms && result /= goal; _ -> False
          , (not (null args) && result == goal) || absurd]
        ready domain = domain `elem` assumptions || snd (domainsResult domain) `elem` assumptions
        key action = (length $ filter (not . ready) $ domains action,
          absurdResult action, length $ domains action, size $ assumptions !! assumption action, assumption action)
    ranked <- lift $ order hooks goal assumptions $ sortOn key candidates
    choices [rule $ operands active (remaining-1) assumptions (domains action) [] labels $ \arguments tags ->
        let applied = if null arguments then Variable (assumption action)
                      else Apply (Variable $ assumption action) arguments
        in accept $ Solution (if absurdResult action then Absurd goal applied else applied) tags
      | (action, labels) <- ranked]
  operands _ _ _ [] arguments tags accept = accept (reverse arguments) tags
  operands active remaining assumptions (domain:rest) arguments tags accept =
    solve active remaining assumptions domain $ \answer ->
      operands active remaining assumptions rest (proof answer:arguments)
        (tags ++ decisions answer) accept
