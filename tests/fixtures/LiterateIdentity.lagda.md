# A checked proof inside Markdown

AgdaProver must preserve this prose and the fence boundaries byte for byte.
The text `{!!}` here is an example, not an interaction hole.

```python
module NotAgda where
open import Missing
```

```agda
{-# OPTIONS --without-K --exact-split #-}

module LiterateIdentity where

open import Support

identity-again : {A : Set} → A → A
```

The definition can live in a separate, unlabelled Agda fence.

```
identity-again = {! !}
```
