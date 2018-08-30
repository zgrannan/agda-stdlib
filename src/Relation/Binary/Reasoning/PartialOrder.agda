------------------------------------------------------------------------
-- The Agda standard library
--
-- Convenient syntax for "equational reasoning" using a partial order
------------------------------------------------------------------------

open import Relation.Binary

module Relation.Binary.Reasoning.PartialOrder
  {p₁ p₂ p₃} (P : Poset p₁ p₂ p₃) where

open Poset P

import Relation.Binary.Reasoning.Core.Double as Base
import Relation.Binary.NonStrictToStrict _≈_ _≤_ as NSPO

------------------------------------------------------------------------
-- Re-export the contents of the base reasoning module publicly

open Base {A = Carrier} {_≈_} {_≤_} {NSPO._<_}
  Eq.sym
  refl
  {!!}
  trans
  (NSPO.<-trans isPartialOrder)
  ≤-respˡ-≈
  (NSPO.<-respˡ-≈ Eq.trans ≤-respˡ-≈)
  (NSPO.<-≤-trans Eq.sym trans antisym ≤-respʳ-≈)
  (NSPO.≤-<-trans trans antisym ≤-respˡ-≈)
  public

{-
import Relation.Binary.Reasoning.Preorder as PreR
open PreR preorder public renaming (_∼⟨_⟩_ to _≤⟨_⟩_)
-}
