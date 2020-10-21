{-# OPTIONS --without-K --safe #-}

-- Per-operation homomorphisms in nullary, unary, and binary flavors

open import Level
open import Relation.Binary using (Setoid)

module Cartesian.Homomorphisms {o ℓ : Level} {i : Level} {I : Set i}
          {U : I → Setoid o ℓ} where

open import Data.Product using (_,_)
open import Function.Equality using (Π; _⟨$⟩_; _⟶_; const)
open import Relation.Binary.Reasoning.MultiSetoid
open import Algebra using (Op₁; Op₂; Opₗ; Opᵣ)

open import Categories.Category.Cartesian.Structure using (CartesianCategory)

open import Categories.Category.Monoidal.Instance.Setoids
     using (Setoids-CartesianCategory)

Setoids-CC : CartesianCategory _ _ _
Setoids-CC = Setoids-CartesianCategory o ℓ

open CartesianCategory Setoids-CC using (terminal) renaming (U to category)

open import Categories.Object.Terminal category

open import Cartesian.Sub Setoids-CC

import Category.Homomorphisms U as CH

open Setoid using (Carrier)

import Data.Unit.Polymorphic.Base as PU

module _ (ops : CartOps {i = i} {I = I} U) where
  open CartOps ops

  -- Nullary homomorphism, given a nullary operation on its carrier.
  H₀ : ((A : I) → Carrier (U A)) → SubCart ops
  H₀ op = record
    { subCat = subCat
    ; R! = λ {A : I} → 
       let ∙ = op A ; ∘ = op ⊤ᴵ
           open Setoid (U A) using (refl)
           module t′ = Terminal (transport-by-iso terminal ⊤≅)
       in
         t′.!-unique {U A} (const ∘) (refl {∙})
    ; Rπ₁ = {!!}
    ; Rπ₂ = {!!}
    ; R⟨_,_⟩ = {!!}
    } where subCat = CH.H₀ op

  -- -- Unary homomorphism, given a unary operation on its carrier.
  -- H₁ : ((A : I) → Op₁ (Carrier (U A))) → SubCart ops
  -- H₁ op = record
  --   { subCat = subCat
  --   ; R! = λ {A : I} → 
  --      let ∙_ = op A ; ⋆_ = op ⊤ᴵ
  --          open Setoid (U A) using (refl)
  --          module t′ = Terminal (transport-by-iso terminal ⊤≅)
  --      in
  --        t′.!-unique {U A} (const ⋆) (refl {∙})
  --   ; Rπ₁ = {!!}
  --   ; Rπ₂ = {!!}
  --   ; R⟨_,_⟩ = {!!}
  --   } where subCat = CH.H₀ op

  {-

  -- Unary homomorphism, given a unary operation on its carrier.
  H₁ : ((A : I) → Op₁ (Carrier (U A))) → SubCart U
  H₁ op = record
    { R = λ {A B} f′ → let ∙_ = op A ; ∘_ = op B
                           _≈_ = Setoid._≈_ (U B) ; infix 4 _≈_
                           open Π f′ renaming (_⟨$⟩_ to f)
                       in
                         ∀ x → f (∙ x) ≈ ∘ f x
    ; Rid  = λ {A} → λ _ → refl (U A)
    ; _∘R_ = λ {A B C} {g′} {f′} gᴴ fᴴ →
               let ∙_ = op A ; ∘_ = op B ; ⋆_ = op C
                   open Π g′ renaming (_⟨$⟩_ to g; cong to cong-g)
                   open Π f′ renaming (_⟨$⟩_ to f)
               in λ x → begin⟨ U C ⟩
                          g (f (∙ x)) ≈⟨ cong-g (fᴴ x) ⟩
                          g (∘ f x)   ≈⟨ gᴴ (f x) ⟩
                          ⋆ g (f x)   ∎
    }

  -- Binary homomorphism, given a binary operation on its carrier.
  H₂ : ((A : I) → Op₂ (Carrier (U A))) → SubCart U
  H₂ op = record
    { R = λ {A B} f′ → let _∙_ = op A ; _∘_ = op B
                           _≈_ = Setoid._≈_ (U B) ; infix 4 _≈_
                           open Π f′ renaming (_⟨$⟩_ to f)
                       in
                         ∀ x y → f (x ∙ y) ≈ f x ∘ f y
    ; Rid  = λ {A} → λ _ _ → refl (U A)
    ; _∘R_ = λ {A B C} {g′} {f′} gᴴ fᴴ →
               let _∙_ = op A ; _∘_ = op B ; _⋆_ = op C
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
    Hₗ : ((A : I) → Opₗ S (Carrier (U A))) → SubCart U
    Hₗ op = ⋂ (λ s → H₁ (λ A x → op A s x))

    Hᵣ : ((A : I) → Opᵣ S (Carrier (U A))) → SubCart U
    Hᵣ op = ⋂ (λ s → H₁ (λ A x → op A x s))

  -}
