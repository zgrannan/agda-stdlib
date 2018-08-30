------------------------------------------------------------------------
-- The Agda standard library
--
-- Convenient syntax for "equational reasoning" using a strict partial
-- order.
------------------------------------------------------------------------

open import Relation.Binary

module Relation.Binary.Reasoning.StrictPartialOrder
         {p₁ p₂ p₃} (S : StrictPartialOrder p₁ p₂ p₃) where

import Relation.Binary.Reasoning.Core.Double as Base
import Relation.Binary.StrictToNonStrict as SPO
-- open import Data.Sum
open import Data.Product using (proj₂)

open StrictPartialOrder S

------------------------------------------------------------------------
-- Re-export the contents of the base reasoning module publically

open Base {A = Carrier}
  Eq.sym
  (SPO.trans _ _ isEquivalence <-resp-≈ trans)
  (proj₂ (SPO.≤-resp-≈ _ _ isEquivalence <-resp-≈))
  {!!}
  trans
  (proj₂ <-resp-≈)
  {!!}
  {!!}
  {!!}
  public
