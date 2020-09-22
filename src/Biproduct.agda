{-# OPTIONS --without-K --safe #-}

open import Categories.Category.Core using (Category)

module Biproduct {o ℓ e} (𝒞 : Category o ℓ e) where

open import Level

open import Relation.Binary.PropositionalEquality using (_≡_)
open import Algebra.Core using (Op₂)

open import Categories.Category.Cartesian 𝒞
open import Categories.Category.Cocartesian 𝒞
open import Categories.Object.Zero 𝒞

open Category 𝒞

-- A bicartesian category is cartesian and cocartesian
record Bicartesian : Set (levelOfTerm 𝒞) where
  field
    cartesian : Cartesian
    cocartesian : Cocartesian

  module cartesian = Cartesian cartesian
  module cocartesian = Cocartesian cocartesian
  open cartesian public
  open cocartesian public

open Bicartesian

-- A biproduct category is bicartesian, has a zero object, and has coinciding
-- products and coproducts.
record Biproduct : Set (levelOfTerm 𝒞) where
  field
    bicartesian : Bicartesian
    zeroObj : Zero
    isBiproduct : _×_ ≡ _+_
  module bicartesian = Bicartesian bicartesian
  open bicartesian public

open Biproduct



record Preadditive (_+_ : {A B : Obj} → Op₂ (A ⇒ B)) : Set (levelOfTerm 𝒞) where
  field
    biproduct : Biproduct

    -- add

-- open import Algebra.Structures
--   {A : Set a}  -- The underlying set
--   (_≈_ : Rel A ℓ)    -- The underlying equality relation
--   where
