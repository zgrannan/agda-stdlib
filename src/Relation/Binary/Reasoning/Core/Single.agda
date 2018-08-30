------------------------------------------------------------------------
-- The Agda standard library
--
-- Convenient syntax for "equational reasoning" using a single
-- relation over some notion of equality.
--
-- This module is not supposed to be used directly but instead should
-- be instantiated with the appropriate operators.
------------------------------------------------------------------------

open import Relation.Binary

module Relation.Binary.Reasoning.Core.Single
  {a ℓ₁ ℓ₂} {A : Set a}
  {_≈_ : Rel A ℓ₁} (≈-refl : Reflexive _≈_) (≈-sym   : Symmetric _≈_)
  {_∼_ : Rel A ℓ₂} (∼-reflexive  : _≈_ ⇒ _∼_) (∼-trans : Transitive _∼_)
  where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

------------------------------------------------------------------------
-- Auxillary types
--
-- This seemingly unnecessary type is used to make it possible to
-- infer arguments even if the underlying equality evaluates.

infix 4 _IsRelatedTo_

data _IsRelatedTo_ (x y : A) : Set ℓ₂ where
  relTo : (x∼y : x ∼ y) → x IsRelatedTo y

------------------------------------------------------------------------
-- Reasoning combinators

infix  3 _∎
infixr 2 _∼⟨_⟩_ _≈⟨_⟩_ _≈⟨⟩_
infix  1 begin_

begin_ : ∀ {x y} → x IsRelatedTo y → x ∼ y
begin relTo x∼y = x∼y

_∼⟨_⟩_ : ∀ x {y z} → x ∼ y → y IsRelatedTo z → x IsRelatedTo z
_ ∼⟨ x∼y ⟩ relTo y∼z = relTo (∼-trans x∼y y∼z)

_≈⟨_⟩_ : ∀ x {y z} → x ≈ y → y IsRelatedTo z → x IsRelatedTo z
_ ≈⟨ x≈y ⟩ relTo y∼z = relTo (∼-trans (∼-reflexive x≈y) y∼z)

_≡⟨_⟩_ : ∀ x {y z} → x ≡ y → y IsRelatedTo z → x IsRelatedTo z
_ ≡⟨ refl ⟩ relTo y∼z = relTo y∼z

_≡⟨⟩_ : ∀ x {y} → x IsRelatedTo y → x IsRelatedTo y
_ ≡⟨⟩ x∼y = x∼y

_∎ : ∀ x → x IsRelatedTo x
_∎ _ = relTo (∼-reflexive ≈-refl)

------------------------------------------------------------------------
-- Deprecated

_≈⟨⟩_ = _≡⟨⟩_



-- If you need to use several instances of this module in a given
-- file, then you can use the following approach:
--
--   import Relation.Binary.PreorderReasoning as Pre
--
--   f x y z = begin
--     ...
--       ∎
--     where open Pre preorder₁
--
--   g i j = begin
--     ...
--       ∎
--     where open Pre preorder₂
