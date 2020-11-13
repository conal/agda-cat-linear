{-# OPTIONS --without-K --safe #-}

-- Miscellaneous definitions belonging elsewhere

module Misc where

-- open import Level

open import Categories.Category 

module _ {o ℓ e} {C : Category o ℓ e} where

  open import Categories.Morphism C using (_≅_)
  open Category C
  open HomReasoning
  open import Categories.Morphism.Reasoning C

  -- Is this function in agda-categories?
  id≅ : {A : Obj} → A ≅ A
  id≅ = record { iso = record { isoˡ = Category.identity² C
                              ; isoʳ = Category.identity² C } }
  
  infixr 9 _∘≅_
  _∘≅_ : {A B C : Obj} → B ≅ C → A ≅ B → A ≅ C

  g ∘≅ f = record
   { iso = record { isoˡ = cancelInner isoˡG ○  isoˡF
                  ; isoʳ = cancelInner isoʳF ○  isoʳG }
   } where open _≅_ g renaming (isoˡ to isoˡG ; isoʳ to isoʳG)
           open _≅_ f renaming (isoˡ to isoˡF ; isoʳ to isoʳF)

  -- TODO: category of isomorphisms

  open import Relation.Binary.PropositionalEquality using (_≡_; refl)

  -- Is this function in agda-categories?
  ≡≅ : {A B : Obj} → A ≡ B → A ≅ B
  ≡≅ refl = id≅

  id≡ : {A : Obj} → A ≡ A
  id≡ = refl

  open import Data.Product renaming (_×_ to _×′_)

  open import Categories.Category.Cartesian
  module _ {cartesian : Cartesian C} where
    open Cartesian cartesian
    ⟨⟩⁻¹ : ∀ {A B C} → (A ⇒ B × C) → (A ⇒ B) ×′ (A ⇒ C)
    ⟨⟩⁻¹ f = π₁ ∘ f , π₂ ∘ f

  open import Categories.Category.Cocartesian
  module _ {cocartesian : Cocartesian C} where
    open Cocartesian cocartesian
    []⁻¹ : ∀ {A B C} → (A + B ⇒ C) → (A ⇒ C) ×′ (B ⇒ C)
    []⁻¹ f = f ∘ i₁ , f ∘ i₂
