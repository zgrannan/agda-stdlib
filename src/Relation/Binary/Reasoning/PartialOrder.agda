------------------------------------------------------------------------
-- The Agda standard library
--
-- Convenient syntax for "inequality reasoning" using an underlying
-- partial order. The corresponding strict relation is generated using
-- `Relation.Binary.NonStrictToStrict`.
------------------------------------------------------------------------
--
-- Example: proving a non strict inequality
--
-- u≤c : u ≤ c
-- u≤c = begin
--   u  ≈⟨ u≈v ⟩
--   v  ≡⟨ v≡w ⟩
--   w  <⟨ w<x ⟩
--   x  ≤⟨ x≤y ⟩
--   y  <⟨ y<z ⟩
--   z  ≡⟨ z≡b ⟩
--   b  ≈⟨ b≈c ⟩
--   c  ∎
--
-- Example: proving a strict inequality
--
-- u<c : u < c
-- u<c = begin-strict
--   u  ≈⟨ u≈v ⟩
--   v  ≡⟨ v≡w ⟩
--   w  <⟨ w<x ⟩
--   x  ≤⟨ x≤y ⟩
--   y  <⟨ y<z ⟩
--   z  ≡⟨ z≡b ⟩
--   b  ≈⟨ b≈c ⟩
--   c  ∎

open import Relation.Binary

module Relation.Binary.Reasoning.PartialOrder
  {p₁ p₂ p₃} (P : Poset p₁ p₂ p₃) where

open Poset P

import Relation.Binary.Reasoning.Core.Double as Base
import Relation.Binary.NonStrictToStrict _≈_ _≤_ as NSPO

------------------------------------------------------------------------
-- Re-export the contents of the base reasoning module publicly

open Base _≈_ _≤_ NSPO._<_
  Eq.sym
  refl
  (NSPO.<⇒≤)
  trans
  (NSPO.<-trans isPartialOrder)
  ≤-respˡ-≈
  (NSPO.<-respˡ-≈ Eq.trans ≤-respˡ-≈)
  (NSPO.<-≤-trans Eq.sym trans antisym ≤-respʳ-≈)
  (NSPO.≤-<-trans trans antisym ≤-respˡ-≈)
  public
