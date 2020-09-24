{-# OPTIONS --without-K --safe #-}

open import Categories.Category.Core using (Category)

module Biproduct {o ℓ e} (𝒞 : Category o ℓ e) where

open import Level

open import Relation.Binary.PropositionalEquality using (_≡_)
open import Algebra.Core using (Op₂)
open import Algebra.Structures using (IsMonoid)

open import Categories.Category.Cartesian 𝒞
open import Categories.Category.Cocartesian 𝒞
open import Categories.Object.Zero 𝒞

open Category 𝒞

private
  variable
    A B C : Obj

-- A bicartesian category is cartesian and cocartesian
record Bicartesian : Set (levelOfTerm 𝒞) where
  field
    cartesian : Cartesian
    cocartesian : Cocartesian

  module cartesian = Cartesian cartesian ; open cartesian public
  module cocartesian = Cocartesian cocartesian ; open cocartesian public

record IsBiproduct (bi : Bicartesian) (z : Zero) : Set (levelOfTerm 𝒞) where
  module bi = Bicartesian bi ; open bi hiding (!;¡)
  module zm = Zero z ; open zm

  zero⇒ : A ⇒ B
  zero⇒ = ! ∘ ¡

  +⇒× : A + B ⇒ A × B
  +⇒× = ⟨ [ id , zero⇒ ] , [ zero⇒ , id ] ⟩

  -- Maybe a field along with an isomorphism proof.
  -- ×⇒+ : A × B ⇒ A + B
  -- ×⇒+ = ?

-- Do we really need Zero, or could we fashion zero⇒ from ! and ¡ of Bicartesian?
-- We'd need ⊥ → ⊤ and maybe ⊥ ≅ ⊤.

-- A biproduct category is bicartesian, has a zero object, and has coinciding
-- products and coproducts.
record Biproduct : Set (levelOfTerm 𝒞) where
  field
    bicartesian : Bicartesian
    zeroObj : Zero
    isBiproduct : IsBiproduct bicartesian zeroObj
    
  module bicartesian = Bicartesian bicartesian ; open bicartesian public
  module isBiproduct = IsBiproduct isBiproduct ; open isBiproduct public

open Biproduct

Op⇒₂ : Set (o ⊔ ℓ)
Op⇒₂ = ∀ {A B} → Op₂ (A ⇒ B)

record IsPreadditive (bi : Biproduct) (_⊹_ : Op⇒₂) : Set (levelOfTerm 𝒞) where
  private
    module biproduct = Biproduct bi ; open bi
  field
    ⊹-zero-isMonoid : ∀ {A B} → IsMonoid (_≈_ {A} {B}) _⊹_ (zero⇒ bi)
    -- Why do I need the explicit "bi" argument here?

record Preadditive : Set (levelOfTerm 𝒞) where
  field
    biproduct : Biproduct
    _⊹_ : Op⇒₂
    isPreadditive : IsPreadditive biproduct _⊹_

  module biproduct = Biproduct biproduct ; open biproduct public
  module isPreadditive = IsPreadditive isPreadditive ; open isPreadditive public
