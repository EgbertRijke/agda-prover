{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE LambdaCase #-}

-- Syntactic proposal only. A fresh strict Agda check must establish completion.
module Prefix (boundary, omissions) where

import Agda.Syntax.Common (IsAbstract (ConcreteDef), IsInstance (NotInstanceDef), IsMacro (NotMacroDef))
import Agda.Syntax.Common.Pretty (prettyShow)
import Agda.Syntax.Concrete qualified as C
import Agda.Syntax.Concrete.Definitions qualified as N
import Agda.Syntax.Concrete.Generic qualified as G
import Agda.Syntax.Position
import Grouping qualified

extent :: HasRange a => a -> Either String (Int, Int)
extent value = case rangeToInterval (getRange value) of
  Nothing -> Left "prefix-binding-range-unavailable"
  Just r -> Right (fromIntegral (posPos (iStart r)) - 1,
                   fromIntegral (posPos (iEnd r)) - 1)

boundary :: String -> C.Module -> Int -> Either String Int
boundary source modul position = do
  end <- nested 0 (C.modDecls modul)
  -- Fixity/syntax declarations can scope backwards. Without reproducing the
  -- complete scope, dropping one may change the meaning of retained terms.
  let later = G.foldDecl (\case
        d@C.Infix{} -> [d]
        d@C.Syntax{} -> [d]
        _ -> []) (C.modDecls modul)
  ranges <- mapM extent later
  if any ((> end) . snd) ranges then Left "prefix-later-notation" else Right end
 where
  nested :: Int -> [C.Declaration] -> Either String Int
  nested depth ds
    | depth > 128 = Left "prefix-nesting-limit"
    | otherwise = do
        declarations <- Grouping.declarations ds
        choose depth declarations
  choose _ [] = Left "prefix-declaration-unavailable"
  choose depth (d : ds) = do
    location <- treeRange depth d
    (start, rawEnd) <- extent location
    -- Absurd patterns can have a range ending before the closing parenthesis.
    -- Keep the rest of that physical line, never discard reconstructed tokens.
    let end = rawEnd + length (takeWhile (/= '\n') (drop rawEnd source))
    if start <= position && position < end
      then case d of
        N.NiceModule _ _ _ _ _ _ children -> nested (depth + 1) children
        -- Keep mutual/record/opaque groups and all clauses/where declarations.
        -- Do not turn one of their incomplete fragments into a complete theorem.
        _ -> Right end
      else choose depth ds
  rawRange r children = foldr fuseRange r $
    G.foldDecl (\d -> [getRange d]) children
  treeRange depth d
    | depth > 128 = Left "prefix-nesting-limit"
    | otherwise = case d of
        N.NiceModule r _ _ _ _ _ children -> pure (rawRange r children)
        N.NiceMutual r _ _ _ children ->
          foldr fuseRange (getRange r) <$> mapM (treeRange (depth + 1)) children
        N.NiceOpaque r _ children ->
          foldr fuseRange (getRange r) <$> mapM (treeRange (depth + 1)) children
        N.NiceRecDef r _ _ _ _ _ _ _ children -> pure (rawRange r children)
        N.FunDef r originals _ _ _ _ _ _ -> pure (rawRange r originals)
        _ -> pure (getRange d)

-- Only adjacent, ordinary signature/function pairs with no where declarations.
-- The caller may omit one only if it contains an earlier unselected hole AND
-- no part of its name occurs elsewhere in the retained source. Instances and
-- checking groups are not candidates for this conservative weakening.
omissions :: C.Module -> Either String [(String, Int, Int)]
omissions modul
  -- Reflection can inspect the signature without mentioning a declaration in
  -- source. The lexical non-use guard is deliberately unavailable in that case.
  | or (G.foldDecl reflective (C.modDecls modul)) = pure []
  | otherwise = nested 0 (C.modDecls modul)
 where
  reflective = \case
    C.Macro{} -> [True]
    C.UnquoteDecl{} -> [True]
    C.UnquoteDef{} -> [True]
    C.UnquoteData{} -> [True]
    _ -> []
  nested :: Int -> [C.Declaration] -> Either String [(String, Int, Int)]
  nested depth ds
    | depth > 128 = Left "prefix-nesting-limit"
    | otherwise = Grouping.declarations ds >>= walk depth
  walk _ [] = pure []
  walk depth _ | depth > 128 = Left "prefix-nesting-limit"
  walk depth (N.NiceModule _ _ _ _ _ _ ds : rest) =
    (++) <$> nested (depth + 1) ds <*> walk depth rest
  walk depth (N.NiceMutual r _ _ _ [sig@N.FunSig{}, def@N.FunDef{}] : rest)
    | null (rangeIntervals (getRange r)) =
        (++) <$> walk (depth + 1) [sig, def] <*> walk depth rest
  walk depth (sig@(N.FunSig _ _ ConcreteDef NotInstanceDef NotMacroDef _ _ _ name _) :
              def@(N.FunDef _ originals ConcreteDef NotInstanceDef _ _ other _) : rest)
    | name == other, all noWhere originals = do
        (start, _) <- extent sig
        (_, end) <- extent def
        ((prettyShow name, start, end) :) <$> walk depth rest
  walk depth (_ : rest) = walk depth rest
  noWhere (C.FunClause _ _ C.NoWhere _) = True
  noWhere _ = False
