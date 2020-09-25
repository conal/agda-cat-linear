-- {-# OPTIONS --without-K --safe #-}  -- not in MonoidAsCategory

-- Based on Categories.Category.Construction.MonoidAsCategory

open import Algebra.Bundles

module SemiringAsCategory o {c ℓ} (S : Semiring c ℓ) where

open import Categories.Category.Core

open Semiring S

open import Categories.Category.Construction.MonoidAsCategory o
              (record { isMonoid = *-isMonoid })

SemiringAsCategory : Category o c ℓ
SemiringAsCategory = MonoidAsCategory

open Category SemiringAsCategory

open import Biproduct SemiringAsCategory

SemiringAsPreadditive : Preadditive
SemiringAsPreadditive = record
  { _⊹_ = _+_
  ; 𝟎 = 0#
  ; isPreadditive = record
     { ⊹-zero-isMonoid = +-isMonoid
     ; bilinearˡ = distribˡ _ _ _
     ; bilinearʳ = distribʳ _ _ _
     }
  }
