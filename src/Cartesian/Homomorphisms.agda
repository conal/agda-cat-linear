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

open import Categories.Category using (Category)
open import Categories.Category.Cartesian using (Cartesian)
open import Categories.Object.Product.Core using (Product)
open import Categories.Category.Cartesian.Structure using (CartesianCategory)
open import Categories.Morphism

open import Categories.Category.Monoidal.Instance.Setoids
     using (Setoids-CartesianCategory)

Setoids-CC : CartesianCategory _ _ _
Setoids-CC = Setoids-CartesianCategory o ℓ

open CartesianCategory Setoids-CC using (cartesian) renaming (U to category)

open import Categories.Object.Terminal category

open import Cartesian.Sub Setoids-CC

import Category.Homomorphisms U as CH

open Setoid using (Carrier)

import Data.Unit.Polymorphic.Base as PU

-- TODO: Try flattening to a single module with an ops argument. Unsure, as I'd
-- probably need to replicate constructing Setoids-CartesianCategory.

open import Relation.Binary.PropositionalEquality using (_≡_) renaming (refl to refl≡)
open import Data.Product using (_,_)
open import Function.Base using (case_of_)

{-

module _ (ops : CartOps {i = i} {I = I} U) where
  open CartOps ops
  open Cartesian cartesian
  record Oper₀ : Set _ where
    field
      p : (A : I) → Carrier (U A)

      p⊤ : let -- open ⊤ using (tt)
               open Setoid ⊤ using (_≈_) in
           {!!} -- p ⊤ᴵ ≈ tt

      -- p× : ∀ {A B : I} → p (A ×ᴵ B) ≡ (p A , p B)

      -- p (A ×ᴵ B) : Carrier (U (A ×ᴵ B))
      --            : Carrier (U A × U B))
      --            : Carrier (U A) × Carrier (U B)


      -- ?1 : Carrier (U (A ×ᴵ B))
      -- ×≡ : {a b : I} → U a × U b ≡ U (a ×ᴵ b)
      -- (p A , p B)

  -- Nullary homomorphism, given a nullary operation on its carrier.
  H₀ : ((A : I) → Carrier (U A)) → SubCart ops
  H₀ p₀ = record
    { subCat = subCat
    ; R! = λ {A : I} → let ∙ = p₀ A ; ⋆ = p₀ ⊤ᴵ
                           open Setoid (U A) using (refl) in
           ? -- !-unique {U A} (const ⋆) (refl {∙})
    ; Rπ₁ = λ {A B : I} → let ∙ = p₀ (A ×ᴵ B) ; ⋆ = p₀ A in
                            begin⟨ U A ⟩
                              π₁ ⟨$⟩ ∙ ≈⟨ {!!} ⟩
                              ⋆               ∎
    ; Rπ₂ = {!!}
    ; R⟨_,_⟩ = {!!}
    } where subCat = CH.H₀ p₀
            open SubCat subCat
            -- open Category category
            open Cartesian cartesian

    -- -- Note: the !, π₁, π₂, ⟨_,_⟩ here are from terminal and product
    -- R!     : {a : I} → R (! {U a})
    -- Rπ₁    : {a b : I} → R (π₁ {a} {b})
    -- Rπ₂    : {a b : I} → R (π₂ {a} {b})
    -- R⟨_,_⟩ : {a c d : I} {f : U a ⇒ U c} {g : U a ⇒ U d}
    --        → R f → R g → R (⟨ f , g ⟩)


  -- Unary homomorphism, given a unary operation on its carrier.
  H₁ : ((A : I) → Op₁ (Carrier (U A))) → SubCart U
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
  H₂ : ((A : I) → Op₂ (Carrier (U A))) → SubCart U
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
    Hₗ : ((A : I) → Opₗ S (Carrier (U A))) → SubCart U
    Hₗ pₗ = ⋂ (λ s → H₁ (λ A x → pₗ A s x))

    Hᵣ : ((A : I) → Opᵣ S (Carrier (U A))) → SubCart U
    Hᵣ pᵣ = ⋂ (λ s → H₁ (λ A x → pᵣ A x s))

  -}
