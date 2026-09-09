{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ImportQualifiedPost #-}

-- The same Agda nicifier owns clause groups in inventories and prefix checks.
module Grouping (declarations) where

import Agda.Syntax.Concrete qualified as C
import Agda.Syntax.Concrete.Definitions qualified as N
import Agda.Syntax.Concrete.Fixity qualified as F

newtype Fix a = Fix { runFix :: Either String a }
  deriving (Functor, Applicative, Monad)

instance F.MonadFixityError Fix where
  throwMultipleFixityDecls _ = Fix $ Left "multiple-fixity-declarations"
  throwMultiplePolarityPragmas _ = Fix $ Left "multiple-polarity-declarations"
  warnUnknownNamesInFixityDecl _ = pure ()
  warnUnknownNamesInPolarityPragmas _ = pure ()
  warnUnknownFixityInMixfixDecl _ = pure ()
  warnPolarityPragmasButNotPostulates _ = pure ()
  warnEmptyPolarityPragma _ = pure ()

declarations :: [C.Declaration] -> Either String [N.NiceDeclaration]
declarations ds = do
  (fixities, _) <- runFix $ F.fixitiesAndPolarities F.NoWarn ds
  let (nice, _) = N.runNice (N.NiceEnv False C.NoWhere_) $
        N.niceDeclarations fixities ds
  either (const $ Left "declaration-grouping-rejected") Right nice
