{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE OverloadedStrings #-}
-- SPDX-License-Identifier: GPL-3.0-or-later
module AgdaProver.Symbolic.NNUE.Features
  ( GoalView (..), ModuleView (..), Classification (..), unknownClassification
  , TermView (..), CandidateView (..), FocusedView (..), FocusedAssumption (..)
  , stateTokens, classificationTokens, policyStateTokens, termTokens, refinementTokens
  , candidateTokens, focusedStateTokens, focusedActionTokens, surfaceSummary ) where

import Data.ByteString qualified as BS
import Data.Char (GeneralCategory (..), generalCategory, isSpace)
import Data.IntMap.Strict qualified as IM
import Data.List (foldl', nub)
import Data.Text (Text)
import Data.Text qualified as T
import Data.Text.Encoding (encodeUtf8)
import Data.Vector qualified as V
import AgdaProver.Symbolic.Classification

-- These are compatibility *feature views*. No type equality, candidate
-- generation, cache identity or proof validity may depend on their text.
data GoalView = GoalView { targetView :: Text, contextViews :: [Text], moduleView :: Maybe ModuleView }
data ModuleView = ModuleView { frameCount :: Int, parameterCount :: Int, directiveCount :: Int }
data TermView = TermView
  { termRoot :: Text, termSize :: Int, termDepth :: Int, termLambdas :: Int, termApplications :: Int }
data CandidateView = CandidateView
  { candidateFamily :: Text, candidateTag :: Text, candidateType :: Text
  , candidateExpression :: Text, symbolicKeyWidth :: Int, candidateMetadata :: [(Text, Text)] }

bucket :: [Int] -> Int -> Text
bucket bounds value = maybe "large" (T.pack . show) $ first [n | n <- bounds, value <= n]
 where first [] = Nothing
       first (x:_) = Just x
decimal :: Int -> Text
decimal = T.pack . show
pythonBool :: Bool -> Text
pythonBool True = "True"
pythonBool False = "False"
normalized :: Text -> Text
normalized = T.unwords . T.words

-- Mirror the legacy delimiter-aware *presentation* summary, including its
-- unreduced arrow count and first-word result head. Do not reinterpret aliases.
surfaceSummary :: Text -> Either String (Int, Text)
surfaceSummary text
  | T.null (T.strip text) = Right (0, "unknown")
  | otherwise = do
      stripped <- stripOuter (T.unpack $ T.strip text)
      (positions, _) <- scan stripped
      let pieces = splitPositions positions stripped
      if any null pieces then Left "malformed-function-type" else do
        tailView <- stripOuter (last pieces)
        pure (length pieces - 1, case words tailView of [] -> "unknown"; x:_ -> T.pack x)
 where
  splitPositions positions input = go 0 positions input
   where go _ [] remaining = [trim remaining]
         go start (p:ps) remaining = let (part, rest) = splitAt (p-start) remaining
           in trim part : go (p+1) ps (drop 1 rest)

trim :: String -> String
trim = reverse . dropWhile isSpace . reverse . dropWhile isSpace

closer :: Char -> Maybe Char
closer c = lookup c [('(', ')'), ('{', '}'), ('[', ']'), ('⦃', '⦄')]

scan :: String -> Either String ([Int], IM.IntMap Int)
scan input = do
  (stack, arrows, matches) <- foldl' step (Right ([], [], IM.empty)) (zip [0..] input)
  if null stack then Right (reverse arrows, matches) else Left "unbalanced-type-delimiters"
 where
  step prior (index, c) = do
    (stack, arrows, matches) <- prior
    case closer c of
      Just end -> Right ((end, index):stack, arrows, matches)
      Nothing | c `elem` ("})]⦄" :: String) -> case stack of
        (end, start):rest | end == c -> Right (rest, arrows, IM.insert start index matches)
        _ -> Left "unbalanced-type-delimiters"
      Nothing -> Right (stack, if c == '→' && null stack then index:arrows else arrows, matches)

stripOuter :: String -> Either String String
stripOuter input = do
  (_, matches) <- scan input
  let chars = V.fromList input
      skipLeft start end | start < end && isSpace (chars V.! start) = skipLeft (start+1) end
                         | otherwise = start
      skipRight start end | start < end && isSpace (chars V.! (end-1)) = skipRight start (end-1)
                          | otherwise = end
      go start end
        | start < end, Just _ <- closer (chars V.! start), IM.lookup start matches == Just (end-1) =
            let start' = skipLeft (start+1) (end-1)
            in go start' (skipRight start' (end-1))
        | otherwise = V.toList $ V.slice start (end-start) chars
  pure $ go 0 (V.length chars)

stateTokens :: GoalView -> Either String [Text]
stateTokens goal = do
  (arrows, headView) <- surfaceSummary $ targetView goal
  let symbols = take 8 $ nub [c | c <- T.unpack (targetView goal), c /= '→',
        generalCategory c `elem` [MathSymbol, CurrencySymbol, ModifierSymbol, OtherSymbol]]
      scopes = case moduleView goal of
        Nothing -> []
        Just view -> ["module-depth:" <> bucket [1,2,3,4] (frameCount view)
          , "module-parameters:" <> bucket [0,1,2,4,8] (parameterCount view)
          , "module-directives:" <> bucket [0,1,2,4,8] (directiveCount view)]
  pure $ ["goal-head:" <> headView, "goal-arrows:" <> bucket [0,1,2,3] arrows
    , "context-size:" <> bucket [0,1,2,4,8] (length $ contextViews goal)]
    ++ map (("goal-surface-symbol:" <>) . T.singleton) symbols ++ scopes
    ++ ["context-head:" <> case T.words view of [] -> "unknown"; h:_ -> h | view <- contextViews goal]

classificationTokens :: Classification -> [Text]
classificationTokens view = ["structural:" <> name <> "=" <> encode value | (name, value) <-
  [("recursive-result-head-matches-goal", recursiveResultMatch view)
  ,("construction-result-head-matches-goal", constructionResultMatch view)
  ,("construction-available", constructionAvailable view)
  ,("productive-elimination-available", productiveElimination view)
  ,("structural-descent-available", structuralDescent view)
  ,("higher-order-structural-descent-available", higherOrderDescent view)
  ,("dependencies-ready", dependenciesReady view)
  ,("homogeneous-coordinate-permutation", coordinatePermutation view)
  ,("reflexive-relation-target", reflexiveRelation view)
  ,("relational-elimination-available", relationalElimination view)
  ,("construction-elimination-compete", constructionEliminationCompete view)]]
 where encode = maybe "unknown" (T.toLower . pythonBool)

policyStateTokens :: GoalView -> Classification -> Either String [Text]
policyStateTokens goal classification = (++ classificationTokens classification) <$> stateTokens goal

termTokens :: GoalView -> TermView -> Either String [Text]
termTokens goal term = do
  (arrows, headView) <- surfaceSummary $ targetView goal
  pure ["action-root:" <> termRoot term
    , "action-size:" <> bucket [1,2,3,5,8,13] (termSize term)
    , "action-depth:" <> bucket [1,2,3,4,6] (termDepth term)
    , "action-lambdas:" <> bucket [0,1,2,3] (termLambdas term)
    , "action-applications:" <> bucket [0,1,2,4] (termApplications term)
    , "joint:arrows=" <> decimal arrows <> ":lambdas=" <> decimal (termLambdas term)
    , "joint:goal=" <> headView <> ":root=" <> termRoot term]

refinementTokens :: GoalView -> Text -> Maybe Text -> Either String [Text]
refinementTokens goal tag local = do
  let target = normalized $ targetView goal
      localType = normalized $ maybe "" id local
  (arrows, headView) <- surfaceSummary localType
  (_, goalHead) <- surfaceSummary target
  let localHead = if T.null localType then "none" else headView
  pure ["action-family:one-step-refinement", "action-root:" <> tag
    , "step-local-arrows:" <> bucket [0,1,2,3] arrows, "step-local-result:" <> localHead
    , "joint:goal=" <> goalHead <> ":step=" <> tag
    , "joint:goal=" <> goalHead <> ":local-result=" <> localHead
    , "joint:exact-local-type=" <> pythonBool (not (T.null localType) && localType == target)]

candidateTokens :: GoalView -> CandidateView -> [Text]
candidateTokens goal candidate =
  ["policy-family:" <> candidateFamily candidate, "policy-action-tag:" <> candidateTag candidate
  , "policy-type-arrows:" <> bucket [0,1,2,3,5,8] arrows
  , "policy-result-head:" <> headView, "policy-result-head-match:" <> pythonBool (headView == goalHead)
  , "policy-exact-type:" <> pythonBool (normalized (candidateType candidate) == normalized (targetView goal))
  , "policy-expression-bytes:" <> bucket [4,8,16,32,64,128] (BS.length $ encodeUtf8 $ candidateExpression candidate)
  , "policy-symbolic-key-width:" <> bucket [0,1,2,4,8] (symbolicKeyWidth candidate)]
  ++ ["policy-metadata:" <> name <> "=" <> value | (name, value) <- candidateMetadata candidate]
 where
  (arrows, headView) = either (const (1000000, "unknown")) id $ surfaceSummary $ candidateType candidate
  goalHead = either (const "unknown") snd $ surfaceSummary $ targetView goal

-- The already-supported focused implicational feature view. This is not the
-- kernel's Type or an equality decision procedure for dependent Agda types.
data FocusedView = AtomView Text | ArrowView FocusedView FocusedView deriving (Eq, Ord, Show)
data FocusedAssumption = FocusedAssumption { assumptionView :: FocusedView, assumptionOrder :: Int }
viewSize :: FocusedView -> Int
viewSize root = go [root] 0
 where go [] count = count
       go (AtomView _:rest) count = go rest $! count + 1
       go (ArrowView a b:rest) count = go (a:b:rest) $! count + 1
viewShape :: FocusedView -> Text
viewShape = T.concat . go . (:[]) . Left
 where go [] = []
       go (Right text:rest) = text : go rest
       go (Left (AtomView _):rest) = "•" : go rest
       go (Left (ArrowView a b):rest) = "(" : go (Left a:Right "→":Left b:Right ")":rest)
domainsResult :: FocusedView -> ([FocusedView], FocusedView)
domainsResult = go []
 where go domains (ArrowView a b) = go (a:domains) b
       go domains atom = (reverse domains, atom)
countBucket, sizeBucket :: Int -> Text
countBucket = bucket [0,1,2,3,4,8,16]
sizeBucket = bucket [1,3,5,8,13,21,34]

focusedStateTokens :: FocusedView -> [FocusedAssumption] -> [Text]
focusedStateTokens goal assumptions =
  ["policy:focused-v2", "goal-shape:" <> viewShape goal
  , "goal-symbol:" <> case goal of AtomView text -> text; _ -> "function"
  , "goal-size:" <> sizeBucket (viewSize goal), "assumptions:" <> countBucket (length assumptions)
  , "exact-assumptions:" <> countBucket (length $ filter ((== goal) . assumptionView) assumptions)
  , "producer-count:" <> countBucket (length [() | a <- assumptions,
       let (domains, result) = domainsResult $ assumptionView a, not (null domains), result == goal])]

focusedActionTokens :: FocusedView -> [FocusedAssumption] -> FocusedAssumption -> [FocusedView] -> [Text]
focusedActionTokens goal assumptions action domains =
  ["action:focus-assumption", "action-arity:" <> countBucket (length domains)
  , "action-type-size:" <> sizeBucket (viewSize $ assumptionView action)
  , "action-domain-shapes:" <> shapes, "action-direct-domains:" <> countBucket direct
  , "action-producible-domains:" <> countBucket producible
  , "action-duplicate-domains:" <> countBucket (length domains - length (nub domains))
  , "action-recursive-domains:" <> countBucket (length $ filter (== goal) domains)
  , "action-order:" <> countBucket (assumptionOrder action)
  , "joint:goal=" <> viewShape goal <> ":domains=" <> shapes
  , "joint:arity=" <> decimal (length domains) <> ":direct=" <> decimal direct <> ":producible=" <> decimal producible]
 where
  direct = length $ filter (`elem` map assumptionView assumptions) domains
  producible = length $ filter (`elem` map (snd . domainsResult . assumptionView) assumptions) domains
  shapes = T.intercalate "," $ map viewShape domains
