-- {-# OPTIONS --without-K --safe #-}

-- Based on Categories.Category.Construction.MonoidAsCategory

open import Algebra.Bundles using (Semiring)

module SemiringAsCategory o {c ℓ} (S : Semiring c ℓ) where

open import Data.Unit.Polymorphic
open import Level

open import Categories.Category.Core

open Semiring S

-- A semiring is a category with one object
SemiringAsCategory : Category o c ℓ
SemiringAsCategory = record
  { Obj = ⊤
  ; assoc = *-assoc _ _ _
  ; sym-assoc = sym (*-assoc _ _ _)
  ; identityˡ = *-identityˡ _
  ; identityʳ = *-identityʳ _
  ; identity² = *-identityˡ _
  ; equiv = isEquivalence
  ; ∘-resp-≈ = *-cong
  }

-- Can I instead use MonoidAsCategory directly? Probably, by building a Monoid out of S.

open import Algebra.Bundles using (Monoid)

open import Categories.Category.Construction.MonoidAsCategory o (record { isMonoid = *-isMonoid })

SemiringAsCategory′ : Category o c ℓ
SemiringAsCategory′ = MonoidAsCategory
