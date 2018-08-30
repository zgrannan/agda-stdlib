------------------------------------------------------------------------
-- The Agda standard library
--
-- Convenient syntax for "equational reasoning" using two relations
-- (usually strict and non-strict versions of an inequality relation)
-- over some notion of equality.
--
-- This module is not supposed to be used directly but instead should
-- be instantiated with the appropriate operators.
------------------------------------------------------------------------

open import Relation.Binary hiding (Decidable)

module Relation.Binary.Reasoning.Core.Double
  {a ℓ₁ ℓ₂ ℓ₃} {A : Set a}
  {_≈_ : Rel A ℓ₁} {_≤_ : Rel A ℓ₂} {_<_ : Rel A ℓ₃}
  (≈-sym : Symmetric _≈_) (≤-refl  : Reflexive _≤_) (<⇒≤ : _<_ ⇒ _≤_)
  (≤-trans : Transitive _≤_) (<-trans : Transitive _<_)
  (≤-respˡ-≈ : _≤_ Respectsˡ _≈_) (<-respˡ-≈ : _<_ Respectsˡ _≈_)
  (<-≤-trans : Trans _<_ _≤_ _<_) (≤-<-trans : Trans _≤_ _<_ _<_)
  where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Nullary.Decidable using (True; False; toWitness)
open import Function using (case_of_)
open import Level using (_⊔_)

------------------------------------------------------------------------
-- This additonal relation "hides" whether the current relation is
-- strict or non strict.

data _≲_ (x y : A) : Set (ℓ₂ ⊔ ℓ₃) where
  strict    : x < y → x ≲ y
  nonstrict : x ≤ y → x ≲ y

------------------------------------------------------------------------
-- This type is used to test if a strict relation has been proved and
-- if so then extract that relation.

data IsStrict {x y} : x ≲ y → Set (ℓ₂ ⊔ ℓ₃) where
  isStrict : ∀ x<y → IsStrict (strict x<y)

IsStrict? : ∀ {x y} (x≲y : x ≲ y) → Dec (IsStrict x≲y)
IsStrict? (strict x<y)  = yes (isStrict x<y)
IsStrict? (nonstrict _) = no λ()

extractStrict : ∀ {x y} {x≲y : x ≲ y} → IsStrict x≲y → x < y
extractStrict (isStrict x<y) = x<y

------------------------------------------------------------------------
-- Reasoning combinators

infix  3 _∎
infixr 2 _<⟨_⟩_ _≤⟨_⟩_ _≈⟨_⟩_ _≡⟨_⟩_ _≡⟨⟩_
infix  1 begin-<_ begin_

begin_ : ∀ {x y : A} (x≲y : x ≲ y) → x ≤ y
begin strict    x<y = <⇒≤ x<y
begin nonstrict x≤y = x≤y

begin-<_ : ∀ {x y : A} (x≲y : x ≲ y) {eq : True (IsStrict? x≲y)}  → x < y
(begin-< p) {eq} = extractStrict (toWitness eq)

_<⟨_⟩_ : ∀ (x : A) {y z} → x < y → y ≲ z → x ≲ z
x <⟨ x<y ⟩ strict    y<z = strict (<-trans x<y y<z)
x <⟨ x<y ⟩ nonstrict y≤z = strict (<-≤-trans x<y y≤z)

_≤⟨_⟩_ : ∀ (x : A) {y z} → x ≤ y → y ≲ z → x ≲ z
x ≤⟨ x≤y ⟩ strict    y<z = strict    (≤-<-trans x≤y y<z)
x ≤⟨ x≤y ⟩ nonstrict y≤z = nonstrict (≤-trans x≤y y≤z)

_≈⟨_⟩_ : ∀ (x : A) {y z} → x ≈ y → y ≲ z → x ≲ z
x ≈⟨ x≈y ⟩ strict    y<z = strict    (<-respˡ-≈ (≈-sym x≈y) y<z)
x ≈⟨ x≈y ⟩ nonstrict y≤z = nonstrict (≤-respˡ-≈ (≈-sym x≈y) y≤z)

-- Note: the proof of propostional equality is not matched on in the
-- combinator below as we need to decide strict vs nonstrict for
-- neutral proofs

_≡⟨_⟩_ : ∀ (x : A) {y z} → x ≡ y → y ≲ z → x ≲ z
x ≡⟨ x≡y ⟩ strict    y<z = strict    (case x≡y of λ where refl → y<z)
x ≡⟨ x≡y ⟩ nonstrict y≤z = nonstrict (case x≡y of λ where refl → y≤z)

_≡⟨⟩_ : ∀ (x : A) {y} → x ≲ y → x ≲ y
x ≡⟨⟩ x≲y = x≲y

_∎ : ∀ (x : A) → x ≲ x
x ∎ = nonstrict ≤-refl

{-
-- Tests

postulate
  u v w x y z b c : A
  u≈v : u ≈ v
  v≡w : v ≡ w
  w<x : w < x
  x≤y : x ≤ y
  y<z : y < z
  z≡b : z ≡ b
  b≈c : b ≈ c

u≤c : u ≤ c
u≤c = begin
  u ≈⟨ u≈v ⟩
  v ≡⟨ v≡w ⟩
  w <⟨ w<x ⟩
  x ≤⟨ x≤y ⟩
  y <⟨ y<z ⟩
  z ≡⟨ z≡b ⟩
  b ≈⟨ b≈c ⟩
  c ∎

u<c : u < c
u<c = begin-<
  u ≈⟨ u≈v ⟩
  v ≡⟨ v≡w ⟩
  w <⟨ w<x ⟩
  x ≤⟨ x≤y ⟩
  y <⟨ y<z ⟩
  z ≡⟨ z≡b ⟩
  b ≈⟨ b≈c ⟩
  c ∎
-}

{-


#### Overhaul of reasoning

* Moved reasoning modules into `Relation.Binary.Reasoning`

* Deprecated `_≈⟨⟩_` in favour of `_≡⟨⟩_` in `Relation.Binary.Reasoning.Preorder`.

-}

