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

open Equiv using (sym)

private
  variable
    A B C : Obj

Op⇒₀ : Set (o ⊔ ℓ)
Op⇒₀ = ∀ {A B} → A ⇒ B

Op⇒₂ : Set (o ⊔ ℓ)
Op⇒₂ = ∀ {A B} → Op₂ (A ⇒ B)

record IsPreadditive (_⊹_ : Op⇒₂) (𝟎 : Op⇒₀) : Set (o ⊔ ℓ ⊔ e) where
  field
    ⊹-zero-isMonoid : IsMonoid (_≈_ {A} {B}) _⊹_ 𝟎
    distrib-⊹ˡ : ∀ {f g : A ⇒ B} {h : B ⇒ C} → h ∘ (f ⊹ g) ≈ (h ∘ f) ⊹ (h ∘ g)
    distrib-⊹ʳ : ∀ {f g : B ⇒ C} {h : A ⇒ B} → (f ⊹ g) ∘ h ≈ (f ∘ h) ⊹ (g ∘ h)
    distrib-𝟎ˡ : ∀ {g : B ⇒ C} → g ∘ 𝟎 ≈ 𝟎 {A} {C}
    distrib-𝟎ʳ : ∀ {f : A ⇒ B} → 𝟎 ∘ f ≈ 𝟎 {A} {C}
    ⊹-resp-≈  : ∀ {f h g i : A ⇒ B} → f ≈ h → g ≈ i → f ⊹ g ≈ h ⊹ i

  module monoid {A} {B} = IsMonoid (⊹-zero-isMonoid {A} {B})

  ⊹-identityˡ : ∀ {A B} {f : A ⇒ B} → 𝟎 ⊹ f ≈ f
  ⊹-identityˡ {f = f} = monoid.identityˡ f

  ⊹-identityʳ : ∀ {A B} {f : A ⇒ B} → f ⊹ 𝟎 ≈ f
  ⊹-identityʳ {f = f} = monoid.identityʳ f

  ⊹-assoc : ∀ {A B} {f g h : A ⇒ B} → (f ⊹ g) ⊹ h ≈ f ⊹ (g ⊹ h)
  ⊹-assoc {f = f} {g} {h} = monoid.assoc f g h
  
record Preadditive : Set (o ⊔ ℓ ⊔ e) where
  infixl 6 _⊹_
  field
    _⊹_ : Op⇒₂
    𝟎 : Op⇒₀
    isPreadditive : IsPreadditive _⊹_ 𝟎
  open IsPreadditive isPreadditive public

open import Categories.Object.Initial 𝒞

record PreadditiveCartesian : Set (suc (o ⊔ ℓ ⊔ e)) where
  field
    cartesian : Cartesian
    preadditive : Preadditive
  open Cartesian cartesian public
  open Preadditive preadditive public
  field
    unique-𝟎 : ∀ {f : ⊤ ⇒ A} → f ≈ 𝟎
    ⟨⟩⊹⟨⟩ : ∀ {f h : A ⇒ B} {g i : A ⇒ C} → ⟨ f , g ⟩ ⊹ ⟨ h , i ⟩ ≈ ⟨ f ⊹ h , g ⊹ i ⟩

-- Cocartesian via Cartesian + Preadditive
Preadditive⇒Cocartesian : Cartesian → Preadditive → Cocartesian
Preadditive⇒Cocartesian cartesian preadditive = record
  { initial = record
      { ⊥ = ⊤
      ; ⊥-is-initial = record
         { ! = 𝟎
         ; !-unique = {!!}  -- ???
         }
      }
  ; coproducts = record
     { coproduct = λ {A B} → record
         { A+B = A × B
         ; i₁ = ⟨ id , 𝟎 ⟩
         ; i₂ = ⟨ 𝟎 , id ⟩
         ; [_,_] = λ {C} f g → f ∘ π₁ ⊹ g ∘ π₂
         ; inject₁ = λ {C} {f : A ⇒ C} {g : B ⇒ C} →
             begin
               (f ∘ π₁ ⊹ g ∘ π₂) ∘ ⟨ id , 𝟎 ⟩
                 ≈⟨ distrib-⊹ʳ ⟩
               (f ∘ π₁) ∘ ⟨ id , 𝟎 ⟩ ⊹ (g ∘ π₂) ∘ ⟨ id , 𝟎 ⟩
                 ≈⟨ ⊹-resp-≈ assoc assoc ⟩
               f ∘ π₁ ∘ ⟨ id , 𝟎 ⟩ ⊹ g ∘ (π₂ ∘ ⟨ id , 𝟎 ⟩)
                 ≈⟨ ⊹-resp-≈ (∘-resp-≈ʳ project₁) (∘-resp-≈ʳ project₂) ⟩
               f ∘ id ⊹ g ∘ 𝟎
                 ≈⟨ ⊹-resp-≈ identityʳ distrib-𝟎ˡ ⟩
               f ⊹ 𝟎
                 ≈⟨ ⊹-identityʳ ⟩
               f
                 ∎
         ; inject₂ = λ {C} {f : A ⇒ C} {g : B ⇒ C} →
             begin
               (f ∘ π₁ ⊹ g ∘ π₂) ∘ ⟨ 𝟎 , id ⟩
                 ≈⟨ distrib-⊹ʳ ⟩
               (f ∘ π₁) ∘ ⟨ 𝟎 , id ⟩ ⊹ (g ∘ π₂) ∘ ⟨ 𝟎 , id ⟩
                 ≈⟨ ⊹-resp-≈ assoc assoc ⟩
               f ∘ π₁ ∘ ⟨ 𝟎 , id ⟩ ⊹ g ∘ (π₂ ∘ ⟨ 𝟎 , id ⟩)
                 ≈⟨ ⊹-resp-≈ (∘-resp-≈ʳ project₁) (∘-resp-≈ʳ project₂) ⟩
               f ∘ 𝟎 ⊹ g ∘ id
                 ≈⟨ ⊹-resp-≈ distrib-𝟎ˡ identityʳ ⟩
               𝟎 ⊹ g
                 ≈⟨ ⊹-identityˡ ⟩
               g
                 ∎
         ; unique = λ {C} {h : A × B ⇒ C} {f : A ⇒ C} {g : B ⇒ C}
                      (eq₁ : h ∘ ⟨ id , 𝟎 ⟩ ≈ f) (eq₂ : h ∘ ⟨ 𝟎 , id ⟩ ≈ g) → 
             begin
               f ∘ π₁ ⊹ g ∘ π₂
                 ≈⟨ ⊹-resp-≈ (∘-resp-≈ˡ (sym eq₁)) (∘-resp-≈ˡ (sym eq₂)) ⟩
               (h ∘ ⟨ id , 𝟎 ⟩) ∘ π₁ ⊹ (h ∘ ⟨ 𝟎 , id ⟩) ∘ π₂
                 ≈⟨ ⊹-resp-≈ assoc assoc ⟩
               h ∘ (⟨ id , 𝟎 ⟩ ∘ π₁) ⊹ h ∘ (⟨ 𝟎 , id ⟩ ∘ π₂)
                 ≈˘⟨ distrib-⊹ˡ ⟩
               h ∘ ( ⟨ id , 𝟎 ⟩ ∘ π₁ ⊹ ⟨ 𝟎 , id ⟩ ∘ π₂)
                 ≈⟨ ∘-resp-≈ʳ (⊹-resp-≈ ⟨⟩∘ ⟨⟩∘) ⟩
               h ∘ (⟨ id ∘ π₁ , 𝟎 ∘ π₁ ⟩ ⊹ ⟨ 𝟎 ∘ π₂ , id ∘ π₂ ⟩)
                 ≈⟨ ∘-resp-≈ʳ (⊹-resp-≈ (⟨⟩-cong₂ identityˡ distrib-𝟎ʳ)
                                        (⟨⟩-cong₂ distrib-𝟎ʳ identityˡ)) ⟩
               h ∘ (⟨ π₁ , 𝟎 ⟩ ⊹ ⟨ 𝟎 , π₂ ⟩)
                 ≈⟨ ∘-resp-≈ʳ {!!} ⟩
               h ∘ ⟨ π₁ ⊹ 𝟎 , 𝟎 ⊹ π₂ ⟩
                 ≈⟨ ∘-resp-≈ʳ (⟨⟩-cong₂ ⊹-identityʳ ⊹-identityˡ) ⟩
               h ∘ ⟨ π₁ , π₂ ⟩
                 ≈⟨ ∘-resp-≈ʳ η ⟩
               h ∘ id
                 ≈⟨ identityʳ ⟩
               h
                 ∎

         } }
  } where open Cartesian cartesian
          open Preadditive preadditive
          open HomReasoning


    -- inject₁ : [ f , g ] ∘ i₁ ≈ f
    -- inject₂ : [ f , g ] ∘ i₂ ≈ g
    -- unique   : h ∘ i₁ ≈ f → h ∘ i₂ ≈ g → [ f , g ] ≈ h


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
  field
    ×⇒+ : A × B ⇒ A + B
    -- Isomorphism

  +⇒× : A + B ⇒ A × B
  +⇒× = ⟨ [ id , 𝟎 ] , [ 𝟎 , id ] ⟩

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
