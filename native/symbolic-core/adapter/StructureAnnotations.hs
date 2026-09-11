{-# LANGUAGE OverloadedStrings #-}
-- SPDX-License-Identifier: GPL-3.0-or-later
module StructureAnnotations (polarityView, relevanceView, domainNameView) where

import Agda.Syntax.Common
import Agda.Syntax.Common.Pretty (prettyShow)
import Data.Aeson (Value, object, (.=))

-- Display-equal names can have distinct origins/ranges. Keep the complete
-- provenance in the atom key; never overwrite one with its spelling twin.
domainNameView :: NamedName -> Value
domainNameView name = object ["display" .= prettyShow name, "provenance_view" .= show name]

polarityView :: ArgInfo -> Maybe [String]
polarityView info = Just $ map show
  [modPolarityAnn p, modPolarityOrigin p, modPolarityLock p]
  where p = modPolarity (argInfoModality info)

relevanceView :: Relevance -> String
relevanceView (Relevant _) = "relevant"
relevanceView (ShapeIrrelevant _) = "shape-irrelevant"
relevanceView (Irrelevant _) = "irrelevant"
