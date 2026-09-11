{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

-- Exact-version structural observations, not a normalizer or canonicalizer.
module Structure where

import Control.Monad.State.Strict
import Data.Aeson (Value, object, toJSON, (.=))
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set
import GHC.Float (castDoubleToWord64)

import Agda.Syntax.Abstract.Name hiding (qname)
import Agda.Syntax.Common hiding (argInfo, hiding)
import Agda.Syntax.Common.Pretty (prettyShow)
import Agda.Syntax.Internal hiding (qname)
import Agda.Syntax.Literal
import Agda.Syntax.Position
import StructureAnnotations qualified as Compat
import Atoms qualified

data Encoding = Encoding
  { nodes :: !Int
  , names :: !(Map.Map String [Value])
  , references :: !(Set.Set String)
  , nativeAtoms :: !(Maybe Atoms.Atoms)
  }

type Encode = StateT Encoding (Either String)

initial :: Encoding
initial = Encoding 0 Map.empty Set.empty Nothing

withAtoms :: Encoding
withAtoms = initial { nativeAtoms = Just Atoms.empty }

rememberInfo :: ArgInfo -> Encode ()
rememberInfo info = modify' $ \s -> s
  { nativeAtoms = fmap (\a -> a
      { Atoms.annotations = Map.insert (argInfo info) info (Atoms.annotations a) })
      (nativeAtoms s) }

rememberMeta :: MetaId -> Encode ()
rememberMeta value = modify' $ \s -> s
  { nativeAtoms = fmap (\a -> a
      { Atoms.metas = Map.insert (meta value) value (Atoms.metas a) }) (nativeAtoms s) }

rememberDomainName :: Maybe NamedName -> Encode ()
rememberDomainName Nothing = pure ()
rememberDomainName (Just value) = modify' $ \s -> s
  { nativeAtoms = fmap (\a -> a
      { Atoms.domainNames = Map.insert (Compat.domainNameView value) value (Atoms.domainNames a) })
      (nativeAtoms s) }

bounded :: Int -> Encode a -> Encode a
bounded _depth action = do
  -- Traversal counts describe work, not the supported mathematics. The
  -- owning process is supervised under the controller's CPU/RSS envelope.
  modify' $ \s -> s { nodes = nodes s + 1 }
  action

node :: String -> [Value] -> Value
node tag fields = toJSON (toJSON tag : fields)

decimal :: Show a => a -> Value
decimal = toJSON . show

nameKey :: Name -> String
nameKey name = case nameId name of
  NameId number (ModuleNameHash modHash) -> show modHash ++ ":" ++ show number

moduleView :: ModuleName -> Value
moduleView (MName parts) = toJSON
  [object ["id" .= nameKey p, "display" .= prettyShow p] | p <- parts]

spanOf :: Range -> Maybe [Int]
spanOf location = do
  interval <- rangeToInterval location
  pure [fromIntegral (posPos (iStart interval)) - 1,
        fromIntegral (posPos (iEnd interval)) - 1]

qname :: QName -> Encode Value
qname q = bounded 0 $ do
  let identifier = nameKey (qnameName q)
      view = object
        [ "display" .= prettyShow q
        , "module" .= moduleView (qnameModule q)
        , "binding_range" .= spanOf (nameBindingSite (qnameName q))
        ]
  old <- gets (Map.lookup identifier . names)
  -- Scope aliases and range-erased internal terms can have different views of
  -- the same native ID. Keep all views; none is a second declaration identity.
  let variants = maybe [view] (\vs -> if view `elem` vs then vs else vs ++ [view]) old
  modify' $ \s -> s
    { names = Map.insert identifier variants (names s)
    , references = Set.insert identifier (references s)
    , nativeAtoms = fmap (\a -> a
        { Atoms.names = Map.insert identifier q (Atoms.names a) }) (nativeAtoms s)
    }
  pure $ toJSON identifier

meta :: MetaId -> Value
meta (MetaId number (ModuleNameHash modHash)) =
  toJSON [show modHash, show number]

argInfo :: ArgInfo -> Value
argInfo info = object
  [ "hiding" .= hiding (argInfoHiding info)
  , "relevance" .= Compat.relevanceView (modRelevance modality)
  , "quantity" .= quantity (modQuantity modality)
  , "cohesion" .= show (modCohesion modality)
  , "polarity" .= Compat.polarityView info
  , "origin" .= show (argInfoOrigin info)
  , "locked" .= case annLock (argInfoAnnotation info) of
      IsNotLock -> False
      IsLock _ -> True
  -- Source/provenance annotations remain explicitly non-semantic views.
  , "provenance_view" .= show info
  ]
 where
  modality = argInfoModality info
  hiding = \case
    Hidden -> ["hidden"]
    NotHidden -> ["explicit"]
    Instance overlap -> ["instance", show overlap]
  quantity = \case
    Quantity0 _ -> "0" :: String
    Quantity1 _ -> "1"
    Quantityω _ -> "omega"

argument :: (a -> Encode Value) -> Arg a -> Encode Value
argument f (Arg info value) = do
  rememberInfo info
  node "argument" . (argInfo info :) . (: []) <$> f value

abstraction :: (a -> Encode Value) -> Abs a -> Encode Value
abstraction f = \case
  Abs hint value -> node "abs" . (toJSON hint :) . (: []) <$> f value
  NoAbs hint value -> node "no-abs" . (toJSON hint :) . (: []) <$> f value

domain :: Int -> Dom Type -> Encode Value
domain depth d = bounded depth $ do
  rememberInfo (domInfo d)
  rememberDomainName (domName d)
  value <- typ (depth + 1) (unDom d)
  tactic <- traverse (term (depth + 1)) (domTactic d)
  pure $ node "domain"
    [argInfo (domInfo d), toJSON (fmap Compat.domainNameView (domName d)),
     toJSON (domIsFinite d), toJSON tactic, value]

typ :: Int -> Type -> Encode Value
typ depth (El s t) = bounded depth $ do
  s' <- sort (depth + 1) s
  t' <- term (depth + 1) t
  pure $ node "type" [s', t']

term :: Int -> Term -> Encode Value
term depth value = bounded depth $ case value of
  Var index es -> node "var" . (toJSON index :) . (: []) <$> eliminations es
  Lam info body -> do
    rememberInfo info
    node "lam" . (argInfo info :) . (: []) <$> abstraction child body
  Lit l -> literal next l
  Def q es -> do
    q' <- qname q
    es' <- eliminations es
    pure $ node "def" [q', es']
  Con head' origin es -> do
    q <- qname (conName head')
    fields <- mapM (argument qname) (conFields head')
    es' <- eliminations es
    pure $ node "con" [q, toJSON (show (conDataRecord head')),
      toJSON (show (conInductive head')), toJSON (show origin), toJSON fields, es']
  Pi dom cod -> do
    d <- domain next dom
    c <- abstraction (typ next) cod
    pure $ node "pi" [d, c]
  Sort s -> node "sort" . (: []) <$> sort next s
  Level l -> node "level-term" . (: []) <$> level next l
  MetaV m es -> do
    rememberMeta m
    node "meta" . (meta m :) . (: []) <$> eliminations es
  DontCare t -> node "dont-care" . (: []) <$> child t
  Dummy{} -> lift $ Left "unsupported-dummy-term"
 where
  next = depth + 1
  child = term next
  eliminations = fmap toJSON . mapM (elim next)

elim :: Int -> Elim -> Encode Value
elim depth value = bounded depth $ case value of
  Apply a -> node "apply" . (: []) <$> argument (term (depth + 1)) a
  Proj origin q -> node "proj" . (toJSON (show origin) :) . (: []) <$> qname q
  IApply x y r -> node "iapply" <$> mapM (term (depth + 1)) [x, y, r]

sort :: Int -> Sort -> Encode Value
sort depth value = bounded depth $ case value of
  Univ u l -> node "univ" . (toJSON (show u) :) . (: []) <$> level next l
  Inf u n -> pure $ node "inf" [toJSON (show u), decimal n]
  SizeUniv -> pure $ node "size-univ" []
  LockUniv -> pure $ node "lock-univ" []
  LevelUniv -> pure $ node "level-univ" []
  IntervalUniv -> pure $ node "interval-univ" []
  PiSort d s body -> do
    rememberInfo (domInfo d)
    rememberDomainName (domName d)
    t <- term next (unDom d)
    tactic <- traverse (term next) (domTactic d)
    s' <- sort next s
    b <- abstraction (sort next) body
    pure $ node "pi-sort"
      [argInfo (domInfo d), toJSON (fmap Compat.domainNameView (domName d)),
       toJSON (domIsFinite d), toJSON tactic, t, s', b]
  FunSort a b -> node "fun-sort" <$> mapM (sort next) [a, b]
  UnivSort s -> node "univ-sort" . (: []) <$> sort next s
  MetaS m es -> do
    rememberMeta m
    node "meta-sort" . (meta m :) . (: []) <$> (toJSON <$> mapM (elim next) es)
  DefS q es -> do
    q' <- qname q
    es' <- mapM (elim next) es
    pure $ node "def-sort" [q', toJSON es']
  DummyS{} -> lift $ Left "unsupported-dummy-sort"
 where next = depth + 1

level :: Int -> Level -> Encode Value
level depth (Max constant parts) = bounded depth $ do
  terms <- mapM (\(Plus offset value) -> do
    t <- term (depth + 1) value
    pure $ node "plus-level" [decimal offset, t]) parts
  pure $ node "level" [decimal constant, toJSON terms]

literal :: Int -> Literal -> Encode Value
literal depth value = bounded depth $ case value of
  LitNat n -> pure $ node "lit-nat" [decimal n]
  LitWord64 n -> pure $ node "lit-word64" [decimal n]
  LitFloat n -> pure $ node "lit-float-bits" [decimal (castDoubleToWord64 n)]
  LitString s -> pure $ node "lit-string" [toJSON s]
  LitChar c -> pure $ node "lit-char" [toJSON [c]]
  LitQName q -> node "lit-qname" . (: []) <$> qname q
  -- Reflection's file-bound meta literals need their source identity as well.
  -- Do not silently replace the TopLevelModuleName by a pretty string.
  LitMeta{} -> lift $ Left "unsupported-reflection-meta-literal"

telescope :: Int -> Telescope -> Encode Value
telescope depth value = bounded depth $ case value of
  EmptyTel -> pure $ node "empty-telescope" []
  ExtendTel d rest -> do
    d' <- domain (depth + 1) d
    rest' <- abstraction (telescope (depth + 1)) rest
    pure $ node "extend-telescope" [d', rest']
