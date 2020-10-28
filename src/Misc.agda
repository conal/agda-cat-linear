{-# OPTIONS --without-K --safe #-}

-- Miscellaneous definitions belonging elsewhere

module Misc where

infixr 4 _,₁_ _,₂_

open import Data.Product

_,₁_ : ∀ {z a b} {Z : Set z} {A : Set a} {B : Set b}
     → (Z → A) → (Z → B) → (Z → A × B)
f ,₁ g = λ z → f z , g z

_,₂_ : ∀ {y z a b} {Y : Set y} {Z : Set z} {A : Set a} {B : Set b}
     → (Y → Z → A) → (Y → Z → B) → (Y → Z → A × B)
f ,₂ g = λ y z → f y z , g y z

-- TODO: maybe generalize _,₁_ _,₂_ to dependent function types

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


       
