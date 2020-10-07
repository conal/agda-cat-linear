{-# OPTIONS --without-K --safe #-}

-- Some algebraic categories via SubCategory

open import Level

module AlgebraicCats (o ℓ : Level) where

open import Function.Equality hiding (setoid) -- renaming (id to ⟶-id)
open import Relation.Binary.Bundles  -- TEMP
open import Algebra.Bundles
open import Algebra.Morphism.Structures

open import Categories.Category
open import Categories.Category.Instance.Setoids
open import Categories.Category.SubCategory (Setoids o ℓ)
open import Categories.Category.Instance.Setoids

open import Homomorphisms

------------------------------------------------------------------------
-- Magma-like structures
------------------------------------------------------------------------

Magmas : Category _ _ _
Magmas = SubCategory record
  { U    = Magma.setoid
  ; R    = λ {a b} → IsMagmaHomomorphism′ a b
  ; Rid  = λ {a} → idIsMagmaHomomorphism a
  ; _∘R_ = λ {a b c} {f} {g} → _∘IsMagmaHomomorphism_ {M₁ = a} {b} {c} {f} {g}
  }

-- Is there a way to avoid all of this eta expansion?

Semigroups : Category _ _ _
Semigroups = SubCategory record
  { U    = Semigroup.setoid
  ; R    = λ {a b} → IsMagmaHomomorphism′ (magma a) (magma b)
  ; Rid  = λ {a} → idIsMagmaHomomorphism (magma a)
  ; _∘R_ = λ {a b c} {f} {g} →
             _∘IsMagmaHomomorphism_ {M₁ = magma a} {magma b} {magma c} {f} {g}
  } where open Semigroup

-- Likewise for Bands, CommutativeSemigroups, Semilattices, SelectiveMagmas.


------------------------------------------------------------------------
-- Monoid-like structures
------------------------------------------------------------------------

Monoids : Category _ _ _
Monoids = SubCategory record
  { U    = Monoid.setoid
  ; R    = λ {a b} → IsMonoidHomomorphism′ a b
  ; Rid  = λ {a} → idIsMonoidHomomorphism a
  ; _∘R_ = λ {a b c} {f} {g} → _∘IsMonoidHomomorphism_ {M₁ = a} {b} {c} {f} {g}
  }

-- Likewise for CommutativeMonoids, IdempotentCommutativeMonoids. 
