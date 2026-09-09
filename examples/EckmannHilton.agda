{-# OPTIONS --without-K --exact-split #-}

module EckmannHilton where

infix 6 _＝_
infixl 15 _∙_

data _＝_ {A : Set} (x : A) : A → Set where
  refl : x ＝ x

_∙_ :
  {A : Set} {x y z : A} →
  x ＝ y → y ＝ z → x ＝ z
_∙_ = {!!}

inv :
  {A : Set} {x y : A} →
  x ＝ y → y ＝ x
inv = {!!}

right-unit :
  {A : Set} {x y : A} →
  (p : x ＝ y) → p ∙ refl ＝ p
right-unit = {!!}

ap-binary :
  {A B C : Set} (f : A → B → C) →
  {x x′ : A} {y y′ : B} →
  x ＝ x′ → y ＝ y′ → f x y ＝ f x′ y′
ap-binary = {!!}

left-whisker-concat :
  {A : Set} {x y z : A} →
  (p : x ＝ y) → {q q′ : y ＝ z} →
  q ＝ q′ → p ∙ q ＝ p ∙ q′
left-whisker-concat = {!!}

right-whisker-concat :
  {A : Set} {x y z : A} {p p′ : x ＝ y} →
  p ＝ p′ → (q : y ＝ z) → p ∙ q ＝ p′ ∙ q
right-whisker-concat = {!!}

horizontal-concat-Id² :
  {A : Set} {x y z : A}
  {p p′ : x ＝ y} {q q′ : y ＝ z} →
  p ＝ p′ → q ＝ q′ → p ∙ q ＝ p′ ∙ q′
horizontal-concat-Id² = {!!}

left-unit-law-left-whisker-Ω² :
  {A : Set} {a : A} →
  (α : refl {x = a} ＝ refl) →
  left-whisker-concat refl α ＝ α
left-unit-law-left-whisker-Ω² = {!!}

right-unit-naturality :
  {A : Set} {x y : A} {p p′ : x ＝ y} →
  (α : p ＝ p′) →
  right-whisker-concat α refl ∙ right-unit p′ ＝
  right-unit p ∙ α
right-unit-naturality = {!!}

right-unit-law-right-whisker-Ω² :
  {A : Set} {a : A} →
  (α : refl {x = a} ＝ refl) →
  right-whisker-concat α refl ＝ α
right-unit-law-right-whisker-Ω² = {!!}

commutative-left-whisker-right-whisker-concat :
  {A : Set} {x y z : A}
  {p p′ : x ＝ y} {q q′ : y ＝ z} →
  (β : q ＝ q′) (α : p ＝ p′) →
  left-whisker-concat p β ∙ right-whisker-concat α q′ ＝
  right-whisker-concat α q ∙ left-whisker-concat p′ β
commutative-left-whisker-right-whisker-concat = {!!}

eckmann-hilton-Ω² :
  {A : Set} {a : A} →
  (α β : refl {x = a} ＝ refl) →
  α ∙ β ＝ β ∙ α
eckmann-hilton-Ω² = {!!}
