{-# OPTIONS --without-K --safe #-}

open import Categories.Category.Core using (Category)

module Biproduct {o ℓ e} (𝒞 : Category o ℓ e) where

open import Level

open import Relation.Binary.PropositionalEquality using (_≡_)
open import Algebra.Core using (Op₂)
open import Algebra.Structures using (IsMonoid)

open import Categories.Category.Cartesian 𝒞
open import Categories.Category.Cocartesian 𝒞

open Category 𝒞

private
  variable
    A B C : Obj

Op⇒₀ : Set (o ⊔ ℓ)
Op⇒₀ = ∀ {A B} → A ⇒ B

Op⇒₂ : Set (o ⊔ ℓ)
Op⇒₂ = ∀ {A B} → Op₂ (A ⇒ B)

record IsPreadditive (_⊹_ : Op⇒₂) (𝟎 : Op⇒₀) : Set (levelOfTerm 𝒞) where
  field
    ⊹-zero-isMonoid : ∀ {A B} → IsMonoid (_≈_ {A} {B}) _⊹_ 𝟎
    -- Why do I need the explicit "bi" argument here?
    bilinearˡ : ∀ {f g : A ⇒ B} {h : B ⇒ C} → h ∘ (f ⊹ g) ≈ (h ∘ f) ⊹ (h ∘ g)
    bilinearʳ : ∀ {f g : B ⇒ C} {h : A ⇒ B} → (f ⊹ g) ∘ h ≈ (f ∘ h) ⊹ (g ∘ h)

record Preadditive : Set (levelOfTerm 𝒞) where
  field
    _⊹_ : Op⇒₂
    𝟎 : Op⇒₀
    isPreadditive : IsPreadditive _⊹_ 𝟎
  open IsPreadditive isPreadditive public

-- TODO: Try replacing _⊹_, 𝟎, and ⊹-zero-isMonoid with a single polymorphic
-- Monoid field in Preadditive.

-- A bicartesian category is cartesian and cocartesian
record Bicartesian : Set (levelOfTerm 𝒞) where
  field
    cartesian   : Cartesian
    cocartesian : Cocartesian
  open   Cartesian   cartesian public
  open Cocartesian cocartesian public

record IsBiproduct (bi : Bicartesian) (pre : Preadditive) : Set (levelOfTerm 𝒞) where
  open Bicartesian bi
  open Preadditive pre
  +⇒× : A + B ⇒ A × B
  +⇒× = ⟨ [ id , 𝟎 ] , [ 𝟎 , id ] ⟩

  -- Maybe a field along with an isomorphism proof.
  -- ×⇒+ : A × B ⇒ A + B
  -- ×⇒+ = ?

-- A biproduct category is bicartesian, has a zero object, and has coinciding
-- products and coproducts.
record Biproduct : Set (levelOfTerm 𝒞) where
  field
    bicartesian : Bicartesian
    preadditive : Preadditive
    isBiproduct : IsBiproduct bicartesian preadditive
  open Bicartesian bicartesian public
  open Preadditive preadditive public
  open IsBiproduct isBiproduct public

open Biproduct
