{-# OPTIONS --without-K --safe #-}

open import Categories.Category.Core using (Category)

module Biproduct {o ℓ e} (𝒞 : Category o ℓ e) where

open import Level

open import Relation.Binary.PropositionalEquality using (_≡_)
open import Algebra.Core using (Op₂)

open import Categories.Category.Cartesian 𝒞
open import Categories.Category.Cocartesian 𝒞
open import Categories.Object.Terminal 𝒞
open import Categories.Object.Initial 𝒞
open import Categories.Morphism 𝒞

open import Categories.Object.Zero 𝒞
-- open Zero.initial
-- open Zero.terminal

open Category 𝒞

private
  variable
    A B C : Obj
    f g : A ⇒ B

-- A bicartesian category is cartesian and cocartesian
record Bicartesian : Set (levelOfTerm 𝒞) where
  field
    cartesian : Cartesian
    cocartesian : Cocartesian

  module cartesian = Cartesian cartesian
  module cocartesian = Cocartesian cocartesian
  open cartesian public
  open cocartesian public

  -- Co-diagonal. Belongs in Cocartesian? Already in agda-categories somewhere?
  ∇ : A + A ⇒ A
  ∇ = [ id , id ]

-- open Bicartesian using ()

record IsBiproduct (bi : Bicartesian) (z : Zero) : Set (levelOfTerm 𝒞) where
  module bi = Bicartesian bi ; open bi hiding (!;¡)
  module zm = Zero z ; open zm

  zero⇒ : A ⇒ B
  zero⇒ = ! ∘ ¡

  +⇒× : A + B ⇒ A × B
  +⇒× = ⟨ [ id , zero⇒ ] , [ zero⇒ , id ] ⟩

-- Do we really need Zero, or could we define zero⇒ from ! and ¡ of Bicartesian?

-- A biproduct category is bicartesian, has a zero object, and has coinciding
-- products and coproducts.
record Biproduct : Set (levelOfTerm 𝒞) where
  field
    zeroObj : Zero
    bicartesian : Bicartesian
    isBiproduct : IsBiproduct bicartesian zeroObj
    
  module bicartesian = Bicartesian bicartesian
  open bicartesian public

  -- fork : (A ⇒ B) → (A ⇒ C) → (A ⇒ B × C)
  -- fork = ⟨_,_⟩

  -- _⊹_ : Op₂ (A ⇒ B)
  -- f ⊹ g = ∇ ∘ ⟨ f , g ⟩

open Biproduct



-- record Preadditive (_+_ : {A B : Obj} → Op₂ (A ⇒ B)) : Set (levelOfTerm 𝒞) where
--   field
--     biproduct : Biproduct

--     -- add

-- open import Algebra.Structures
--   {A : Set a}  -- The underlying set
--   (_≈_ : Rel A ℓ)    -- The underlying equality relation
--   where

