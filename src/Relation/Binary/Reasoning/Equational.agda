------------------------------------------------------------------------
-- The Agda standard library
--
-- Convenient syntax for equational reasoning
--
-- Module ≡-Reasoning in Relation.Binary.PropositionalEquality
-- is recommended for equational reasoning when the underlying equality is
-- Relation.Binary.PropositionalEquality._≡._
------------------------------------------------------------------------
--
-- Example use:
--
-- eq : ∀ x y z → y • x ≈ z • x → x • y ≈ x • z
-- eq x y z y•x≈z•x = begin
--   x • y  ≈⟨ comm x y ⟩
--   y • x  ≈⟨ y•x≈z•x ⟩
--   z • x  ≈⟨ comm z x ⟩
--   x • z  ∎
--   where open import Relation.Binary.Reasoning.Equational setoid

open import Relation.Binary

module Relation.Binary.Reasoning.Equational {s₁ s₂} (S : Setoid s₁ s₂) where

open Setoid S

open import Relation.Binary.Reasoning.Preorder preorder public
  renaming ( _∼⟨_⟩_  to _≈⟨_⟩_)
  hiding   (_≈⟨_⟩_; _≈⟨⟩_)
