{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE LambdaCase #-}
-- SPDX-License-Identifier: GPL-3.0-or-later
-- A narrow structural view of the existing binary AC fragment. All native
-- terms/eliminations remain intact; this module never parses display strings.
module AgdaProver.Agda28.Algebra
  ( View, Role (..), inspectGoal, relationView, binary, inspectEvidence, operations, endpoints, contexts, render ) where

import Control.Monad (guard)
import Agda.Syntax.Abstract qualified as A
import Agda.Syntax.Common
import Agda.Syntax.Info (exprNoRange)
import Agda.Syntax.Internal qualified as I
import Agda.Syntax.Internal.MetaVars (noMetas)
import Agda.Syntax.Position (noRange)
import Agda.Syntax.Translation.InternalToAbstract (reify)
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Reduce (instantiateFull, reduce)
import Agda.TypeChecking.Substitute (raise, apply)
import AgdaProver.Symbolic.Algebra qualified as R

data View = View I.Term I.Term (R.Term I.Term) (R.Term I.Term) [I.Term]
data Role = Commutativity | Associativity | Symmetry | Transitivity | Congruence
  | Concrete (R.Term I.Term) (R.Term I.Term)
data Head = Definition A.QName | Variable Int deriving Eq

-- The final two operands must be ordinary applications. Prefix parameters and
-- any preceding projections remain part of the exact callable head. Unsupported
-- eliminations are opaque atoms, not guessed applications.
binary :: I.Term -> Maybe (I.Term, I.Term, I.Term)
binary (I.Def name spine) = split (I.Def name) spine
binary (I.Var index spine) = split (I.Var index) spine
binary _ = Nothing

split :: ([I.Elim] -> I.Term) -> [I.Elim] -> Maybe (I.Term, I.Term, I.Term)
split headTerm spine = case reverse spine of
  I.Apply right : I.Apply left : rest | visible left && visible right ->
    Just (headTerm $ reverse rest, unArg left, unArg right)
  _ -> Nothing

tree :: I.Term -> I.Term -> R.Term I.Term
tree operation term = case binary term of
  Just (headTerm, left, right) | headTerm == operation ->
    R.Binary (tree operation left) (tree operation right)
  _ -> R.Atom term

inspectGoal :: I.Type -> TCM [View]
inspectGoal supplied = do
  I.El _ term <- instantiateFull supplied >>= reduce
  pure $ case binary term of
    Just (relation,left,right) | noMetas term -> views relation [] left right
    _ -> []
 where
  views relation wrappers left right =
    [View relation op (tree op left) (tree op right) wrappers
    | Just op <- [case (binary left,binary right) of
        (Just (f,_,_),_) -> Just f
        (_,Just (f,_,_)) -> Just f
        _ -> Nothing]]
    ++ case commonContext left right of
      Just (f,a,b) -> views relation (f:wrappers) a b
      Nothing -> []

-- A relation need not contain a binary algebraic operation. This view also
-- lets contextual evidence use the supplied mapping/composition schemas.
relationView :: I.Type -> TCM (Maybe View)
relationView supplied = do
  I.El _ term <- instantiateFull supplied >>= reduce
  pure $ do
    guard $ noMetas term
    (relation, left, right) <- binary term
    pure $ View relation relation (R.Atom left) (R.Atom right) []

-- Preserve a shared application context as an actual native lambda. Agda's
-- raising operation protects free variables; no substitution by printed name.
-- Exactly one ordinary operand may differ. Other eliminations remain exact.
commonContext :: I.Term -> I.Term -> Maybe (I.Term,I.Term,I.Term)
commonContext left right = do
  (headLeft,args) <- spine left
  (headRight,args') <- spine right
  guard $ headLeft == headRight && length args == length args'
  case [(index,a,b) | (index,(a,b)) <- zip [0..] $ zip args args', a /= b] of
    [(index,I.Apply a,I.Apply b)] | visible a, getArgInfo a == getArgInfo b -> do
      (raisedHead,raisedArgs) <- spine $ raise 1 left
      let body = applyElims raisedHead $ take index raisedArgs
            ++ [I.Apply $ a { unArg = I.Var 0 [] }] ++ drop (index+1) raisedArgs
      pure (I.Lam defaultArgInfo $ I.Abs "x" body,unArg a,unArg b)
    _ -> Nothing
 where
  spine (I.Def name args) = Just (Definition name,args)
  spine (I.Var index args) = Just (Variable index,args)
  spine _ = Nothing
  applyElims (Definition name) args = I.Def name args
  applyElims (Variable index) args = I.Var index args

endpoints :: View -> (R.Term I.Term, R.Term I.Term)
endpoints (View _ _ left right _) = (left,right)

contexts :: View -> TCM [A.Expr]
contexts (View _ _ _ _ wrappers) = mapM reify wrappers

-- This is only a proposal compatibility test. A polymorphic bound head is
-- unknown until application; Agda, not this test, infers its parameters. Free
-- local heads are rebased by telescope depth, and global heads use QName
-- identity. Different carriers/implicit parameters still require checking.
compatible :: Int -> I.Term -> I.Term -> Bool
compatible _ (I.Def a _) (I.Def b _) = a == b
compatible count (I.Var a _) (I.Var b _) = b < count || b-count == a
compatible count _ (I.Var b _) = b < count
compatible _ _ _ = False

inspectEvidence :: View -> I.Type -> TCM (Maybe Role)
inspectEvidence (View relation operation _ _ _) = go []
 where
  go domains supplied = reduce supplied >>= \case
    -- Schema operands include nondependent proof arguments. Ask Agda to
    -- expose NoAbs binders too; merely counting them shifts native identities.
    I.El _ (I.Pi domain body) -> underAbstractionAbs domain body $
      go (domain:domains)
    I.El _ term -> do
      -- Raise each domain once into the final context, not every retained
      -- domain again at each binder. The reversed list gives its exact offset.
      converted <- sequence [reduce $ raise (index+1) $ I.unDom domain
        | (index,domain) <- zip [0..] domains]
      let count = length domains
          explicit = reverse [(I.Var index [], value)
            | (index,(domain,I.El _ value)) <- zip [0..] $ zip domains converted
            , visible domain]
      pure $ do
        guard $ noMetas term
        (rel,left,right) <- binary term
        guard $ compatible count relation rel
        case explicit of
          [] -> do
            guard $ null domains
            pure $ Concrete (tree operation left) (tree operation right)
          [(x,_),(y,_)] | Just (op,a,b) <- binary left
            , Just (op',b',a') <- binary right
            , op == op', compatible count operation op
            , (a,b,b',a') == (x,y,y,x) -> Just Commutativity
          [(x,_),(y,_),(z,_)] | Just (op,ab,c) <- binary left
            , Just (op',a,bc) <- binary right
            , Just (op'',a',b) <- binary ab
            , Just (op''',b',c') <- binary bc
            , all (== op) [op',op'',op'''], compatible count operation op
            , (a,a',b,b',c,c') == (x,x,y,y,z,z) -> Just Associativity
          [(_,domain)] | Just (rel',a,b) <- binary domain
            , rel == rel', (left,right) == (b,a) -> Just Symmetry
          [(_,first),(_,second)] | Just (r1,a,b) <- binary first
            , Just (r2,b',c) <- binary second
            , rel == r1, rel == r2, b == b', (left,right) == (a,c) -> Just Transitivity
          [(f,_),(_,domain)] | Just (_,a,b) <- binary domain
            , left == apply f [defaultArg a]
            , right == apply f [defaultArg b] -> Just Congruence
          _ -> Nothing

operations :: [(Role,e)] -> (R.Operations e,[R.Edge I.Term e])
operations entries = (R.Operations
  [e | (Commutativity,e) <- entries] [e | (Associativity,e) <- entries]
  [e | (Symmetry,e) <- entries] [e | (Transitivity,e) <- entries]
  [e | (Congruence,e) <- entries], [R.Edge a b e | (Concrete a b,e) <- entries])

render :: View -> R.Proof I.Term A.Expr -> TCM A.Expr
render (View _ operation _ _ _) = proof
 where
  app f = A.app f . map (defaultArg . unnamed)
  term :: R.Term I.Term -> TCM A.Expr
  term (R.Atom value) = reify value
  term (R.Binary a b) = do
    f <- reify operation
    args <- mapM term [a,b]
    pure $ app f args
  proof :: R.Proof I.Term A.Expr -> TCM A.Expr
  proof (R.Given expression) = pure expression
  proof (R.Commute law a b) = app law <$> mapM term [a,b]
  proof (R.Associate law a b c) = app law <$> mapM term [a,b,c]
  proof (R.Invert inverse p) = app inverse . (:[]) <$> proof p
  proof (R.Compose compose p q) = app compose <$> mapM proof [p,q]
  proof (R.UnderLeft lift fixed p) = lifted lift fixed p True
  proof (R.UnderRight lift fixed p) = lifted lift fixed p False
  lifted :: A.Expr -> R.Term I.Term -> R.Proof I.Term A.Expr -> Bool -> TCM A.Expr
  lifted lift fixed p onLeft = do
    f <- reify operation
    value <- term fixed
    edge <- proof p
    withFreshName noRange "x" $ \name -> do
      let args = if onLeft then [A.Var name,value] else [value,A.Var name]
          lambda = A.Lam exprNoRange (A.mkDomainFree $ defaultArg $ unnamed $ A.mkBinder_ name) $ app f args
      pure $ app lift [lambda,edge]
