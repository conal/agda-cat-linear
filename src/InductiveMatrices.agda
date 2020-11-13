{-# OPTIONS --without-K --safe #-}

-- Inductive matrices

open import Level

open import Algebra.Bundles using (Semiring)

module InductiveMatrices {r ℓr : Level} (semiring : Semiring r ℓr) where

open import Data.Product using (_,_) renaming (_×_ to _×→_)

open import Algebra.Module.Bundles using (LeftSemimodule)

open Semiring semiring hiding (_+_) renaming (Carrier to R; setoid to R-setoid)

open import Categories.Category.Core

open import AlgebraicCats r ℓr hiding (setoid)

LSM = LeftSemimodule semiring r ℓr

LSMs = LeftSemimodules semiring

open Category LSMs

open import Categories.Category.Cartesian   using (Cartesian)
open import Categories.Category.Cocartesian using (Cocartesian)

-- open import Categories.Category.Cartesian   LSMs
-- open import Categories.Category.Cocartesian LSMs
open import Biproduct LSMs

module PC = PreadditiveCartesian (LeftSemimodules-PreadditiveCartesian semiring)

open PC

-- open Cartesian cartesian
-- open Cocartesian cocartesian

-- LeftSemimodules-PreadditiveCartesian

-- open import Categories.Category LSMs

open import Algebra.Module.Construct.TensorUnit using () renaming (leftSemimodule to R′)

open import Relation.Binary.Reasoning.MultiSetoid

private
  variable
    A B C D : Obj

infixr 1 _⊸_
data _⊸_ : Obj → Obj → Set (suc (r ⊔ ℓr)) where
  scale : R → R′ ⊸ R′
  join  : ∀ {A B C} → (A ⊸ C) → (B ⊸ C) → (A + B ⊸ C)
  fork  : ∀ {A C D} → (A ⊸ C) → (A ⊸ D) → (A ⊸ C × D)

μ : ∀ {A B} → (A ⊸ B) → (A ⇒ B)
μ (scale r)  = record { _⟨$⟩_ = r *_ ; cong = *-congˡ }
             , distribˡ _
             , zeroʳ _
             , (λ s x → begin⟨ R-setoid ⟩
                  r * (s * x) ≈⟨ {!!} ⟩  -- oops!
                  s * (r * x) ∎ )
-- μ (join f g)  = [ μ f , μ g ]   -- many errors
-- μ (fork f g)  = ⟨ μ f , μ g ⟩   -- many errors

μ (join {A}{B}{C} f g) = [_,_] {A}{B}{C} (μ f) (μ g)
μ (fork {A}{C}{D} f g) = ⟨_,_⟩ {A}{C}{D} (μ f) (μ g)

-- The "oops" reveals that we need a *commutative* semiring.

-- Experiment

-- foo : (A ⇒ C × D) → (A ⇒ C)
foo : ∀ {A}{C}{D} → (A ⇒ C × D) → (A ⇒ C)
-- foo f = π₁ ∘ f -- nope
-- foo {A}{C}{D} f = π₁ {C}{D} ∘ f -- nope
foo {A}{C}{D} f = _∘_ {A} {C × D} {C} (π₁ {C}{D}) f -- yep

-- -- t : ∀ {A B} → A × B ⇒ A
-- t : A × B ⇒ A
-- t {A} {B} = π₁ {A} {B}  -- yep

-- id' : A ⇒ A
-- -- id' = id   -- nope
-- id' {A} = id {A}   -- yep

-- unjoin₂ : ∀ {A B C} → (A + B ⇒ C) → (A ⇒ C) ×→ (B ⇒ C)
-- unjoin₂ f = f ∘ i₁ , f ∘ i₂
