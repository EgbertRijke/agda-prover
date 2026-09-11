{-# LANGUAGE ImportQualifiedPost #-}

-- SPDX-License-Identifier: GPL-3.0-or-later
-- Same-environment atomic identities, never term trees or proof bodies.
module Atoms where

import Data.Aeson (Value)
import Data.Map.Strict qualified as Map
import Agda.Syntax.Abstract.Name (QName)
import Agda.Syntax.Common (ArgInfo, MetaId, NamedName)

data Atoms = Atoms
  { names :: !(Map.Map String QName)
  , annotations :: !(Map.Map Value ArgInfo)
  , metas :: !(Map.Map Value MetaId)
  , domainNames :: !(Map.Map Value NamedName)
  }

empty :: Atoms
empty = Atoms Map.empty Map.empty Map.empty Map.empty
