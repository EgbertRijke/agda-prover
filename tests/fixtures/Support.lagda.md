# Literate support module

The next three lines are documentation, not Agda, despite looking executable:

module Bogus where
open import MissingFromProse
postulate proseOnly : Set

They must remain semantically inert.

```agda
{-# OPTIONS --without-K --exact-split #-}

module Support where

identity : {A : Set} → A → A
identity x = x
```
