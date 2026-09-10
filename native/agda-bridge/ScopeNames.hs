{-# LANGUAGE ImportQualifiedPost #-}

-- Shared concrete-name admission, before resolution or type observation.
module ScopeNames (nameable) where

import Agda.Syntax.Concrete.Name qualified as C

-- Agda can resolve parser-generated import aliases as concrete objects even
-- though their rendered spelling cannot be used by the source parser. Respect
-- the native visibility annotation on EVERY qualifier, not spelling prefixes.
-- Independently exposed user aliases retain their own InScope components.
nameable :: C.QName -> Bool
nameable = all usable . C.qnameParts
 where
  usable n = not (C.isNoName n) && C.isInScope n == C.InScope
