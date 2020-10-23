{-# OPTIONS --without-K --safe #-}

-- Per-operation homomorphisms in nullary, unary, and binary flavors

open import Level
open import Relation.Binary using (Setoid)

module Category.Homomorphisms {o ℓ : Level} {i : Level} {I : Set i} (U : I → Setoid o ℓ) where

open import Data.Product using (_,_)
open import Function.Equality using (Π; _⟨$⟩_; _⟶_)
open import Relation.Binary.Reasoning.MultiSetoid
open import Algebra using (Op₁; Op₂; Opₗ; Opᵣ)

open import Categories.Category.Instance.Setoids using (Setoids)

open import Category.Sub (Setoids o ℓ)

open Setoid using (Carrier; refl)

-- Nullary homomorphism, given a nullary operation on its carrier.
H₀ : ((A : I) → Carrier (U A)) → SubCat U
H₀ p₀ = record
  { R = λ {A B} f′ → let ∙ = p₀ A ; ∘ = p₀ B
                         _≈_ = Setoid._≈_ (U B)
                         open Π f′ renaming (_⟨$⟩_ to f)
                     in
                       f ∙ ≈ ∘
  ; Rid  = λ {A} → refl (U A)
  ; _∘R_ = λ {A B C} {g′} {f′} gᴴ fᴴ →
             let ∙ = p₀ A ; ∘ = p₀ B ; ⋆ = p₀ C
                 open Π g′ renaming (_⟨$⟩_ to g; cong to cong-g)
                 open Π f′ renaming (_⟨$⟩_ to f)
             in begin⟨ U C ⟩
                  g (f ∙) ≈⟨ cong-g fᴴ ⟩
                  g ∘     ≈⟨ gᴴ ⟩
                  ⋆       ∎
  }

-- Unary homomorphism, given a unary operation on its carrier.
H₁ : ((A : I) → Op₁ (Carrier (U A))) → SubCat U
H₁ p₁ = record
  { R = λ {A B} f′ → let ∙_ = p₁ A ; ∘_ = p₁ B
                         _≈_ = Setoid._≈_ (U B) ; infix 4 _≈_
                         open Π f′ renaming (_⟨$⟩_ to f)
                     in
                       ∀ x → f (∙ x) ≈ ∘ f x
  ; Rid  = λ {A} → λ _ → refl (U A)
  ; _∘R_ = λ {A B C} {g′} {f′} gᴴ fᴴ →
             let ∙_ = p₁ A ; ∘_ = p₁ B ; ⋆_ = p₁ C
                 open Π g′ renaming (_⟨$⟩_ to g; cong to cong-g)
                 open Π f′ renaming (_⟨$⟩_ to f)
             in λ x → begin⟨ U C ⟩
                        g (f (∙ x)) ≈⟨ cong-g (fᴴ x) ⟩
                        g (∘ f x)   ≈⟨ gᴴ (f x) ⟩
                        ⋆ g (f x)   ∎
  }

-- Binary homomorphism, given a binary operation on its carrier.
H₂ : ((A : I) → Op₂ (Carrier (U A))) → SubCat U
H₂ p₂ = record
  { R = λ {A B} f′ → let _∙_ = p₂ A ; _∘_ = p₂ B
                         _≈_ = Setoid._≈_ (U B) ; infix 4 _≈_
                         open Π f′ renaming (_⟨$⟩_ to f)
                     in
                       ∀ x y → f (x ∙ y) ≈ f x ∘ f y
  ; Rid  = λ {A} → λ _ _ → refl (U A)
  ; _∘R_ = λ {A B C} {g′} {f′} gᴴ fᴴ →
             let _∙_ = p₂ A ; _∘_ = p₂ B ; _⋆_ = p₂ C
                 open Π g′ renaming (_⟨$⟩_ to g; cong to cong-g)
                 open Π f′ renaming (_⟨$⟩_ to f)
             in λ x y → begin⟨ U C ⟩
                          g (f (x ∙ y))     ≈⟨ cong-g (fᴴ x y) ⟩
                          g (f x ∘ f y)     ≈⟨ gᴴ (f x) (f y) ⟩
                          g (f x) ⋆ g (f y) ∎
  }

-- Left- and right-action homomorphisms. Maybe semi-homomorphisms, since one
-- argument is held constant.
module Action {s : Level} (S : Set s) where
  Hₗ : ((A : I) → Opₗ S (Carrier (U A))) → SubCat U
  Hₗ pₗ = ⋂ (λ s → H₁ (λ A x → pₗ A s x))

  Hᵣ : ((A : I) → Opᵣ S (Carrier (U A))) → SubCat U
  Hᵣ pᵣ = ⋂ (λ s → H₁ (λ A x → pᵣ A x s))
