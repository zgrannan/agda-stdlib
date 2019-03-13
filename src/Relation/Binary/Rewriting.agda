module Relation.Binary.Rewriting where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (_×_; ∃ ; _,_)
open import Level
open import Relation.Binary.Core
open import Relation.Binary.Construct.Closure.ReflexiveTransitive

Deterministic : ∀ {A B : Set} → {ℓ : Level} → REL A B ℓ → Set _
Deterministic _—→_ = ∀ {A B C} → A —→ B → A —→ C → B ≡ C

Confluent : ∀ {A : Set} → {ℓ : Level} → (r :  Rel A ℓ) → Set _
Confluent _—→_ = ∀ {A B C} → (A —↠ B × A —↠ C) → ∃ λ D → (B —↠ D) × (C —↠ D)
  where
     _—↠_ = Star _—→_

Diamond : ∀ {A : Set} → {ℓ : Level} → (r :  Rel A ℓ) → Set _
Diamond _—→_ = ∀ {A B C} → (A —→ B × A —→ C) → ∃ λ D → (B —↠ D) × (C —↠ D)
  where
    _—↠_ = Star _—→_

det-is-conf : ∀ {A : Set} → {ℓ : Level} → {r : Rel A ℓ} → Deterministic r → Confluent r
det-is-conf f (ε , snd) = _ , snd , ε
det-is-conf f (fst , ε) = _ , ε , fst
det-is-conf f (a ◅ fst , b ◅ snd) rewrite f a b = det-is-conf f ( fst , snd )

conf-is-diamond : ∀ {A : Set} → {ℓ : Level} → {r : Rel A ℓ} → Confluent r → Diamond r
conf-is-diamond c (fst , snd) = c (fst ◅ ε , snd ◅ ε)
