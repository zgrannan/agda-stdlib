------------------------------------------------------------------------
-- The Agda standard library
--
-- Convenient syntax for "equational reasoning" using a preorder
------------------------------------------------------------------------

-- I think that the idea behind this library is originally Ulf
-- Norell's. I have adapted it to my tastes and mixfix operators,
-- though.

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

open import Relation.Binary

module Relation.Binary.Reasoning.Preorder
  {p₁ p₂ p₃} (P : Preorder p₁ p₂ p₃) where

import Relation.Binary.Reasoning.Core.Single as Base
open Preorder P

------------------------------------------------------------------------
-- Re-export the contents of the base reasoning module publicly

open Base (λ {x} → Eq.refl {x}) Eq.sym reflexive trans public
