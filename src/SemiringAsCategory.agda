-- {-# OPTIONS --without-K --safe #-}

-- Based on Categories.Category.Construction.MonoidAsCategory

open import Algebra.Bundles using (Monoid;Semiring)

module SemiringAsCategory o {c ℓ} (S : Semiring c ℓ) where

open import Categories.Category.Core

open Semiring S

open import Categories.Category.Construction.MonoidAsCategory o
              (record { isMonoid = *-isMonoid })

SemiringAsCategory : Category o c ℓ
SemiringAsCategory = MonoidAsCategory

