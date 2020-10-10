-- N-ary homomorphism properties as categories (one per n).
-- Generalizes pointed setoids, which corresponds to n ≡ 0.

open import Level

module Homomorphisms (c ℓ : Level) where

open import Data.Product using (Σ; proj₁; _,_)
open import Function using (_∘_)
open import Relation.Binary using (Setoid)
open import Function.Equality using (Π;_⟨$⟩_)
open import Relation.Binary.Reasoning.MultiSetoid
open import Algebra using (Op₁; Op₂)

open import Categories.Category using (Category)
open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Category.SubCategory

open Setoid using (Carrier; refl)

-- Nullary homomorphisms, i.e., "pointed setoids"
H₀ : Category (suc (c ⊔ ℓ)) (c ⊔ ℓ) (c ⊔ ℓ)
H₀ = SubCategory (Setoids c ℓ) {I = Σ (Setoid c ℓ) Carrier} record
  { U = proj₁
  ; R = λ {(A , ∙₁) (B , ∙₂)} f′ → let open Π f′ renaming (_⟨$⟩_ to f)
                                       open Setoid B renaming (_≈_ to _≈₂_) in
                                    f ∙₁ ≈₂ ∙₂
  ; Rid = λ {(A , _)} → refl A
  ; _∘R_ = λ {(A , ∙₁)} {(B , ∙₂)} {(C , ∙₃)} {g′ f′} gᴴ fᴴ →
             let open Π g′ renaming (_⟨$⟩_ to g; cong to cong-g)
                 open Π f′ renaming (_⟨$⟩_ to f) in
               begin⟨ C ⟩
                 g (f ∙₁) ≈⟨ cong-g fᴴ ⟩
                 g ∙₂     ≈⟨ gᴴ ⟩
                 ∙₃       ∎
  }

-- Unary homomorphisms
H₁ : Category (suc (c ⊔ ℓ)) (c ⊔ ℓ) (c ⊔ ℓ)
H₁ = SubCategory (Setoids c ℓ) record
  { U = proj₁ {B = Op₁ ∘ Carrier}   -- {B = λ A → Op₁ (Carrier A)}
  ; R = λ {( A , ∙₁_ ) ( B , ∙₂_ )} f′ →
            let open Π f′ renaming (_⟨$⟩_ to f)
                open Setoid A renaming (_≈_ to _≈₁_)
                open Setoid B renaming (_≈_ to _≈₂_) in ∀ x →
              f (∙₁ x) ≈₂ ∙₂ (f x)
  ; Rid = λ {(A , _)} _ → refl A
  ; _∘R_ = λ {(A , ∙₁_)} {(B , ∙₂_)} {(C , ∙₃_)} {g′ f′} gᴴ fᴴ →
             let open Π g′ renaming (_⟨$⟩_ to g; cong to cong-g)
                 open Π f′ renaming (_⟨$⟩_ to f) in λ x →
               begin⟨ C ⟩
                 g (f (∙₁ x)) ≈⟨ cong-g (fᴴ x) ⟩
                 g (∙₂ (f x)) ≈⟨ gᴴ (f x) ⟩
                 ∙₃ (g (f x)) ∎
  }

-- Binary homomorphisms
H₂ : Category (suc (c ⊔ ℓ)) (c ⊔ ℓ) (c ⊔ ℓ)
H₂ = SubCategory (Setoids c ℓ) record
  { U = proj₁ {B = Op₂ ∘ Carrier}
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
