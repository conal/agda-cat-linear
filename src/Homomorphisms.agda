-- N-ary homomorphism properties as categories (one per n).
-- Generalizes pointed setoids, which corresponds to n ≡ 0.

open import Level

module Homomorphisms (c ℓ : Level) where

open import Data.Product
open import Function using (_∘′_; _$_; _on_) renaming (id to id′)
open import Relation.Binary
open import Function.Equality hiding (id; _∘_)
open import Relation.Binary.Reasoning.MultiSetoid
open import Algebra using (Op₁; Op₂)
open import Algebra.Morphism.Definitions
open import Relation.Binary.Construct.On

open import Categories.Category
open import Categories.Category.Instance.Setoids
open import Categories.Category.SubCategory

open Setoid using (Carrier; refl)
open Category (Setoids c ℓ)

-- Nullary homomorphisms, i.e., "pointed setoids"
H₀ : Category (suc (c ⊔ ℓ)) (c ⊔ ℓ) (c ⊔ ℓ)
H₀ = SubCategory (Setoids c ℓ) {I = Σ (Setoid c ℓ) Carrier} record
  { U = proj₁
  ; R = λ {(A , ε₁) (B , ε₂)} f′ → let open Π f′ renaming (_⟨$⟩_ to f)
                                       open Setoid B renaming (_≈_ to _≈₂_) in
                                    f ε₁ ≈₂ ε₂
  ; Rid = λ {(A , _)} → refl A
  ; _∘R_ = λ {(A , ε₁)} {(B , ε₂)} {(C , ε₃)} {g′ f′} gᴴ fᴴ →
             let open Π g′ renaming (_⟨$⟩_ to g; cong to cong-g)
                 open Π f′ renaming (_⟨$⟩_ to f) in
               begin⟨ C ⟩
                 g (f ε₁) ≈⟨ cong-g fᴴ ⟩
                 g ε₂     ≈⟨ gᴴ ⟩
                 ε₃       ∎
  }

-- Unary homomorphisms
H₁ : Category (suc (c ⊔ ℓ)) (c ⊔ ℓ) (c ⊔ ℓ)
H₁ = SubCategory (Setoids c ℓ) record
  { U = proj₁ {B = Op₁ ∘′ Carrier}   -- {B = λ A → Op₁ (Carrier A)}
  ; R = λ {( A , μ₁ ) ( B , μ₂ )} f′ →
            let open Π f′ renaming (_⟨$⟩_ to f)
                open Setoid A renaming (_≈_ to _≈₁_)
                open Setoid B renaming (_≈_ to _≈₂_) in ∀ x →
              f (μ₁ x) ≈₂ μ₂ (f x)
  ; Rid = λ {(A , _)} _ → refl A
  ; _∘R_ = λ {(A , μ₁)} {(B , μ₂)} {(C , μ₃)} {g′ f′} gᴴ fᴴ →
             let open Π g′ renaming (_⟨$⟩_ to g; cong to cong-g)
                 open Π f′ renaming (_⟨$⟩_ to f) in λ x →
               begin⟨ C ⟩
                 g (f (μ₁ x)) ≈⟨ cong-g (fᴴ x) ⟩
                 g (μ₂ (f x)) ≈⟨ gᴴ (f x) ⟩
                 μ₃ (g (f x)) ∎
  }

-- Binary homomorphisms
H₂ : Category (suc (c ⊔ ℓ)) (c ⊔ ℓ) (c ⊔ ℓ)
H₂ = SubCategory (Setoids c ℓ) record
  { U = proj₁ {B = Op₂ ∘′ Carrier}
  ; R = λ {( A , _∙₁_ ) ( B , _∙₂_ )} f′ →
            let open Π f′ renaming (_⟨$⟩_ to f)
                open Setoid A renaming (_≈_ to _≈₁_)
                open Setoid B renaming (_≈_ to _≈₂_) in ∀ x y →
              f (x ∙₁ y) ≈₂ f x ∙₂ f y
  ; Rid = λ {(A , _)} _ _ → refl A
  ; _∘R_ = λ {(A , _∙₁_)} {(B , _∙₂_)} {(C , _∙₃_)} {g′ f′} gᴴ fᴴ →
             let open Π g′ renaming (_⟨$⟩_ to g; cong to cong-g)
                 open Π f′ renaming (_⟨$⟩_ to f) in λ x y →
               begin⟨ C ⟩
                 g (f (x ∙₁ y))     ≈⟨ cong-g (fᴴ x y) ⟩
                 g (f x ∙₂ f y)     ≈⟨ gᴴ (f x) (f y) ⟩
                 g (f x) ∙₃ g (f y) ∎
  }
