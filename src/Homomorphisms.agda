{-# OPTIONS --without-K --safe #-}

-- Per-operation homomorphisms in nullary, unary, and binary flavors

open import Level
open import Relation.Binary using (Setoid)

module Homomorphisms {o ℓ q : Level} {Q : Set q} (setoid : Q → Setoid o ℓ) where

open import Function.Equality using (Π; _⟨$⟩_; _⟶_)
open import Relation.Binary.Reasoning.MultiSetoid
open import Algebra using (Op₁; Op₂)

open import Categories.Category.Instance.Setoids using (Setoids)

open import SubCat (Setoids o ℓ)

open Setoid using (Carrier; refl)

-- Nullary homomorphism, given a nullary operation on its carrier.
H₀ : ((A : Q) → Carrier (setoid A)) → SubCat setoid
H₀ op = record
  { R = λ {A B} f′ →
          let ∙ = op A ; ∘ = op B
              _≈_ = Setoid._≈_ (setoid B)
              open Π f′ renaming (_⟨$⟩_ to f)
          in
            f ∙ ≈ ∘
  ; Rid  = λ {A} → refl (setoid A)
  ; _∘R_ = λ {A B C} {g′} {f′} gᴴ fᴴ →
             let ∙ = op A ; ∘ = op B ; ⋆ = op C
                 open Π g′ renaming (_⟨$⟩_ to g; cong to cong-g)
                 open Π f′ renaming (_⟨$⟩_ to f)
             in begin⟨ setoid C ⟩
                    g (f ∙) ≈⟨ cong-g fᴴ ⟩
                    g ∘     ≈⟨ gᴴ ⟩
                    ⋆       ∎
  }

-- Unary homomorphism, given A unary operation on its carrier.
H₁ : ((A : Q) → Op₁ (Carrier (setoid A))) → SubCat setoid
H₁ op = record
  { R = λ {A B} f′ →
          let ∙_ = op A ; ∘_ = op B
              _≈_ = Setoid._≈_ (setoid B) ; infix 4 _≈_
              open Π f′ renaming (_⟨$⟩_ to f)
          in
            ∀ x → f (∙ x) ≈ ∘ f x
  ; Rid  = λ {A} → λ _ → refl (setoid A)
  ; _∘R_ = λ {A B C} {g′} {f′} gᴴ fᴴ →
             let ∙_ = op A ; ∘_ = op B ; ⋆_ = op C
                 open Π g′ renaming (_⟨$⟩_ to g; cong to cong-g)
                 open Π f′ renaming (_⟨$⟩_ to f)
             in λ x → begin⟨ setoid C ⟩
                          g (f (∙ x)) ≈⟨ cong-g (fᴴ x) ⟩
                          g (∘ f x)   ≈⟨ gᴴ (f x) ⟩
                          ⋆ g (f x)   ∎
  }

-- Binary homomorphism, given A binary operation on its carrier.
H₂ : ((A : Q) → Op₂ (Carrier (setoid A))) → SubCat setoid
H₂ op = record
  { R = λ {A B} f′ →
          let _∙_ = op A ; _∘_ = op B
              _≈_ = Setoid._≈_ (setoid B) ; infix 4 _≈_
              open Π f′ renaming (_⟨$⟩_ to f)
          in
            ∀ x y → f (x ∙ y) ≈ f x ∘ f y
  ; Rid  = λ {A} → λ _ _ → refl (setoid A)
  ; _∘R_ = λ {A B C} {g′} {f′} gᴴ fᴴ →
             let _∙_ = op A ; _∘_ = op B ; _⋆_ = op C
                 open Π g′ renaming (_⟨$⟩_ to g; cong to cong-g)
                 open Π f′ renaming (_⟨$⟩_ to f)
             in λ x y → begin⟨ setoid C ⟩
                          g (f (x ∙ y))     ≈⟨ cong-g (fᴴ x y) ⟩
                          g (f x ∘ f y)     ≈⟨ gᴴ (f x) (f y) ⟩
                          g (f x) ⋆ g (f y) ∎
  }

