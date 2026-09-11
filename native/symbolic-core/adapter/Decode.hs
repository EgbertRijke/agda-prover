{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

-- SPDX-License-Identifier: GPL-3.0-or-later
-- Independent structural reconstruction. Only atomic names/annotations may be
-- resolved from the checked environment; no original terms enter this module.
module Decode (Decode, run, typ, telescope, arg, term) where

import Control.Monad (when)
import Control.Monad.Reader (ReaderT, asks, runReaderT)
import Control.Monad.State.Strict (StateT, evalStateT, modify')
import Control.Monad.Trans.Class (lift)
import Data.Aeson (Value (..), Result (..), fromJSON)
import Data.Map.Strict qualified as Map
import Data.Text qualified as T
import Data.Vector qualified as V
import Data.Word (Word64)
import GHC.Float (castWord64ToDouble)
import Text.Read (readMaybe)

import Agda.Syntax.Common hiding (named)
import Agda.Syntax.Internal hiding (qname)
import Agda.Syntax.Literal
import Atoms qualified

type Decode = ReaderT Atoms.Atoms (StateT Int (Either String))

run :: Atoms.Atoms -> Decode a -> Either String a
run atoms action = evalStateT (runReaderT action atoms) 0

reject :: String -> Decode a
reject = lift . lift . Left

malformed :: Decode a
malformed = reject "reconstruction-malformed-structure"

bounded :: Int -> Decode a -> Decode a
bounded _depth action = do
  modify' (+ 1)
  action

array :: Value -> Decode [Value]
array (Array xs) = pure $ V.toList xs
array _ = malformed

text :: Value -> Decode String
text (String s) = pure $ T.unpack s
text _ = malformed

integer :: Value -> Decode Int
integer v = case fromJSON v of
  Success i | i >= 0 -> pure i
  _ -> malformed

decimal :: Value -> Decode Integer
decimal (String s)
  | Just n <- readMaybe (T.unpack s), n >= 0,
    show n == T.unpack s = pure n
decimal _ = malformed

word :: Value -> Decode Word64
word v = do
  n <- decimal v
  if n <= toInteger (maxBound :: Word64) then pure (fromInteger n) else malformed

boolean :: Value -> Decode Bool
boolean (Bool b) = pure b
boolean _ = malformed

optional :: (Value -> Decode a) -> Value -> Decode (Maybe a)
optional _ Null = pure Nothing
optional f v = Just <$> f v

named :: Show a => [a] -> Value -> Decode a
named values v = do
  name <- text v
  case filter ((== name) . show) values of
    [value] -> pure value
    _ -> malformed

qname :: Value -> Decode QName
qname v = do
  key <- text v
  names <- asks Atoms.names
  maybe (reject "reconstruction-unknown-name") pure (Map.lookup key names)

info :: Value -> Decode ArgInfo
info v = do
  annotations <- asks Atoms.annotations
  maybe (reject "reconstruction-unknown-annotation") pure (Map.lookup v annotations)

meta :: Value -> Decode MetaId
meta v = do
  metas <- asks Atoms.metas
  maybe (reject "reconstruction-unknown-meta") pure (Map.lookup v metas)

domainName :: Value -> Decode NamedName
domainName v = do
  names <- asks Atoms.domainNames
  maybe (reject "reconstruction-unknown-domain-name") pure (Map.lookup v names)

arg :: (Value -> Decode a) -> Value -> Decode (Arg a)
arg f v = array v >>= \case
  [String "argument", i, x] -> Arg <$> info i <*> f x
  _ -> malformed

absValue :: (Int -> Int -> Value -> Decode a) -> Int -> Int -> Value -> Decode (Abs a)
absValue f n d v = array v >>= \case
  [String "abs", hint, x] -> Abs <$> text hint <*> f (n + 1) (d + 1) x
  [String "no-abs", hint, x] -> NoAbs <$> text hint <*> f n (d + 1) x
  _ -> malformed

domain :: (Int -> Int -> Value -> Decode a) -> Int -> Int -> [Value] -> Decode (Dom a)
domain f n d [i, name, finite, tactic, value] =
  Dom <$> info i
      <*> optional domainName name
      <*> boolean finite <*> optional (term n (d + 1)) tactic
      <*> f n (d + 1) value
domain _ _ _ _ = malformed

typ :: Int -> Int -> Value -> Decode Type
typ n d v = bounded d $ array v >>= \case
  [String "type", s, t] -> El <$> sort n (d + 1) s <*> term n (d + 1) t
  _ -> malformed

term :: Int -> Int -> Value -> Decode Term
term n d v = bounded d $ array v >>= \case
  [String "var", index, es] -> do
    i <- integer index
    when (i >= n) $ reject "reconstruction-unbound-variable"
    Var i <$> elims es
  [String "lam", i, body] -> Lam <$> info i <*> absValue term n d body
  [String "def", name, es] -> Def <$> qname name <*> elims es
  [String "con", name, kind, induction, origin, fields, es] -> do
    head' <- ConHead <$> qname name
      <*> named [IsData, IsRecord PatternMatching, IsRecord CopatternMatching] kind
      <*> named [Inductive, CoInductive] induction
      <*> (mapM (arg qname) =<< array fields)
    Con head' <$> named [ConOSystem, ConOCon, ConORec, ConOSplit] origin <*> elims es
  [String "pi", dom, body] -> do
    domain' <- bounded (d + 1) $ array dom >>= \case
      String "domain" : fields -> domain typ n (d + 1) fields
      _ -> malformed
    Pi domain' <$> absValue typ n d body
  [String "sort", s] -> Sort <$> sort n (d + 1) s
  [String "level-term", l] -> Level <$> level n (d + 1) l
  [String "dont-care", t] -> DontCare <$> term n (d + 1) t
  [String "lit-nat", x] -> Lit . LitNat <$> decimal x
  [String "lit-word64", x] -> Lit . LitWord64 <$> word x
  [String "lit-float-bits", x] -> Lit . LitFloat . castWord64ToDouble <$> word x
  [String "lit-string", x] -> Lit . LitString . T.pack <$> text x
  [String "lit-char", x] -> text x >>= \case
    [c] -> pure $ Lit $ LitChar c
    _ -> malformed
  [String "lit-qname", x] -> Lit . LitQName <$> qname x
  [String "meta", m, es] -> MetaV <$> meta m <*> elims es
  _ -> malformed
 where elims es = mapM (elim n (d + 1)) =<< array es

elim :: Int -> Int -> Value -> Decode Elim
elim n d v = bounded d $ array v >>= \case
  [String "apply", a] -> Apply <$> arg (term n (d + 1)) a
  [String "proj", origin, name] ->
    Proj <$> named [ProjPrefix, ProjPostfix, ProjSystem] origin <*> qname name
  [String "iapply", x, y, r] -> IApply <$> child x <*> child y <*> child r
  _ -> malformed
 where child = term n (d + 1)

sort :: Int -> Int -> Value -> Decode Sort
sort n d v = bounded d $ array v >>= \case
  [String "univ", u, l] -> Univ <$> universe u <*> level n (d + 1) l
  [String "inf", u, l] -> Inf <$> universe u <*> decimal l
  [String "size-univ"] -> pure SizeUniv
  [String "lock-univ"] -> pure LockUniv
  [String "level-univ"] -> pure LevelUniv
  [String "interval-univ"] -> pure IntervalUniv
  [String "pi-sort", i, name, finite, tactic, t, s, body] ->
    PiSort <$> domain term n d [i, name, finite, tactic, t]
           <*> child s <*> absValue sort n d body
  [String "fun-sort", a, b] -> FunSort <$> child a <*> child b
  [String "univ-sort", s] -> UnivSort <$> child s
  [String "def-sort", name, es] ->
    DefS <$> qname name <*> (mapM (elim n (d + 1)) =<< array es)
  [String "meta-sort", m, es] -> MetaS <$> meta m <*> (mapM (elim n (d + 1)) =<< array es)
  _ -> malformed
 where
  child = sort n (d + 1)
  universe = named [UProp, UType, USSet]

level :: Int -> Int -> Value -> Decode Level
level n d v = bounded d $ array v >>= \case
  [String "level", constant, parts] -> Max <$> decimal constant <*> (mapM plus =<< array parts)
  _ -> malformed
 where
  plus x = array x >>= \case
    [String "plus-level", offset, t] -> Plus <$> decimal offset <*> term n (d + 1) t
    _ -> malformed

telescope :: Int -> Int -> Value -> Decode Telescope
telescope n d v = bounded d $ array v >>= \case
  [String "empty-telescope"] -> pure EmptyTel
  [String "extend-telescope", dom, body] -> do
    domain' <- bounded (d + 1) $ array dom >>= \case
      String "domain" : fields -> domain typ n (d + 1) fields
      _ -> malformed
    b <- absValue telescope n d body
    case b of
      Abs{} -> pure $ ExtendTel domain' b
      NoAbs{} -> malformed
  _ -> malformed
