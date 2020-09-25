-- {-# OPTIONS --without-K --safe #-}  -- not in MonoidAsCategory

-- Based on Categories.Category.Construction.MonoidAsCategory

open import Algebra.Bundles
open import Algebra.Module.Bundles

module LeftSemimoduleAsCategory o {c ℓ} (S : LeftSemimodule c ℓ) where

open import Data.Product using (proj₁; proj₂)

open import Categories.Category.Core

open LeftSemimodule S

open import Categories.Category.Construction.MonoidAsCategory o
              (record { isMonoid = *-isMonoid })

LeftSemimoduleAsCategory : Category o c ℓ
LeftSemimoduleAsCategory = MonoidAsCategory

-- open Category LeftSemimoduleAsCategory

-- open import Categories.Category.Cocartesian LeftSemimoduleAsCategory
-- open import Biproduct LeftSemimoduleAsCategory

-- LeftSemimoduleAsPreadditive : Preadditive
-- LeftSemimoduleAsPreadditive = record
--   { _⊹_ = _+_
--   ; 𝟎 = 0#
--   ; isPreadditive = record
--      { ⊹-zero-isMonoid = +-isMonoid
--      ; bilinearˡ = distribˡ _ _ _
--      ; bilinearʳ = distribʳ _ _ _
--      }
--   }
