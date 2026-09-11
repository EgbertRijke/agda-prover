{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE OverloadedStrings #-}

-- Declaration-owned edit proposals for the user's independent entry tests.
-- Never expose an implementation expression or grant proof acceptance here.
module Entries (inventory) where

import Data.Aeson (Value, object, (.=))
import Data.Char (isSpace)
import Agda.Syntax.Common (IsMacro (MacroDef))
import Agda.Syntax.Common.Pretty (prettyShow)
import Agda.Syntax.Concrete qualified as C
import Agda.Syntax.Concrete.Definitions qualified as N
import Agda.Syntax.Position
import Grouping qualified

extent :: HasRange a => a -> Either String (Int, Int)
extent value = case rangeToInterval (getRange value) of
  Nothing -> Left "entry-range-unavailable"
  Just r -> Right (fromIntegral (posPos (iStart r)) - 1,
                   fromIntegral (posPos (iEnd r)) - 1)

inventory :: String -> C.Module -> Either String [Value]
inventory source modul = scan 0 (C.modDecls modul)
 where
  scan depth ds
    | depth > (128 :: Int) = Left "entry-nesting-limit"
    | otherwise = Grouping.declarations ds >>= walk depth . concatMap unwrap
  unwrap (N.NiceMutual _ _ _ _ ds) = concatMap unwrap ds
  unwrap (N.NiceOpaque _ _ ds) = concatMap unwrap ds
  unwrap d = [d]
  walk depth ds = concat <$> mapM visit ds
   where
    signatures name = [(sig, macro) |
      sig@(N.FunSig _ _ _ _ macro _ _ _ other _) <- ds, name == other]
    visit d = case d of
      N.NiceModule _ _ _ _ _ _ children -> scan (depth + 1) children
      N.NiceRecDef _ _ _ _ _ _ _ _ children -> scan (depth + 1) children
      N.FunDef _ originals _ _ _ _ name _ -> do
        let clauses = [c | c@C.FunClause{} <- originals]
        parts <- mapM extent clauses
        signature <- case signatures name of
          [(sig, macro)] -> do
            (start, end) <- extent sig
            pure (start, end, macro == MacroDef)
          _ -> pure (0, 0, False)
        let (start, end, macro) = signature
            reason
              | null parts = "missing-clause-ranges"
              | end <= start || end > fst (head parts) = "missing-fixed-signature"
              | macro = "macro-definition"
              | any namedWhere clauses = "exported-where-module"
              | any inlineTail parts = "inline-declaration-boundary"
              | otherwise = ""
        pure [object
          [ "name" .= prettyShow name
          , "parts" .= [[a, if null reason then clauseEnd b else b] | (a, b) <- parts]
          , "reason" .= (reason :: String)
          ]]
      N.NiceFunClause{} -> unsupported d "unsigned-clause"
      N.NiceUnquoteDecl{} -> unsupported d "generated-declaration"
      N.NiceUnquoteDef{} -> unsupported d "generated-definition"
      _ -> pure []
    unsupported d reason = do
      (a, b) <- extent d
      pure [object ["name" .= ("<unsupported>" :: String),
                    "parts" .= [[a, b]], "reason" .= (reason :: String)]]
  -- An absurd clause's range can end before its closing parenthesis. Include
  -- closing pattern tokens, but never swallow the start of a trailing comment
  -- (which might continue over several lines) or another declaration.
  clauseEnd end = end + length (takeWhile (\c -> c /= '\n' && (isSpace c || c == ')'))
    (drop end source))
  inlineTail (_, end) = case drop (clauseEnd end) source of
    ';' : _ -> True
    '}' : _ -> True
    _ -> False
  namedWhere (C.FunClause _ _ C.SomeWhere{} _) = True
  namedWhere _ = False
