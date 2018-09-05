------------------------------------------------------------------------
-- The Agda standard library
--
-- Convenient syntax for "inequality reasoning" using a strict partial
-- order. The corresponding non-strict relation is generated using
-- `Relation.Binary.StrictToNonStrict`.
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

module Relation.Binary.Reasoning.StrictPartialOrder
         {p₁ p₂ p₃} (S : StrictPartialOrder p₁ p₂ p₃) where

open StrictPartialOrder S

import Relation.Binary.Reasoning.Core.Double as Base
import Relation.Binary.StrictToNonStrict _≈_ _<_ as SPO
open import Data.Sum using (inj₁)
open import Data.Product using (proj₂)

------------------------------------------------------------------------
-- Re-export the contents of the base reasoning module publicly

open Base _≈_ SPO._≤_ _<_
  Eq.sym
  (SPO.reflexive Eq.refl)
  (SPO.<⇒≤)
  (SPO.trans isEquivalence <-resp-≈ trans)
  trans
  (λ {x} → SPO.≤-respˡ-≈ Eq.sym Eq.trans <-respˡ-≈ {x})
  <-respˡ-≈
  (SPO.<-≤-trans trans <-respʳ-≈)
  (SPO.≤-<-trans Eq.sym trans <-respˡ-≈)
  public
