-- N-ary homomorphism properties as categories (one per n).
-- Generalizes pointed setoids, which corresponds to n ≡ 0.

open import Level

module Homomorphisms (c ℓ : Level) where

open import Data.Product using (Σ; proj₁; _×_; _,_)
open import Function using (_∘_)
open import Relation.Binary using (Setoid)
open import Function.Equality using (Π;_⟨$⟩_)
open import Relation.Binary.Reasoning.MultiSetoid
open import Algebra using (Op₁; Op₂)

open import Categories.Category using (Category)
open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Category.SubCategory

open Setoid using (Carrier; refl)

-------------------------------------------------------------------------------
-- | Nullary homomorphisms, i.e., "pointed setoids"
-------------------------------------------------------------------------------

Sub₀ : SubCat (Setoids c ℓ) (Σ (Setoid c ℓ) Carrier)
Sub₀ = record
  { U = proj₁
  ; R = λ {(A , ∙) (B , ∘)} f′ → let open Π f′ renaming (_⟨$⟩_ to f)
                                     open Setoid B renaming (_≈_ to _≈₂_) in
                                   f ∙ ≈₂ ∘
  ; Rid = λ {(A , _)} → refl A
  ; _∘R_ = λ {(A , ∙)} {(B , ∘)} {(C , ⋆)} {g′ f′} gᴴ fᴴ →
             let open Π g′ renaming (_⟨$⟩_ to g; cong to cong-g)
                 open Π f′ renaming (_⟨$⟩_ to f) in
               begin⟨ C ⟩
                 g (f ∙) ≈⟨ cong-g fᴴ ⟩
                 g ∘     ≈⟨ gᴴ ⟩
                 ⋆       ∎
  }

H₀ : Category (suc (c ⊔ ℓ)) (c ⊔ ℓ) (c ⊔ ℓ)
H₀ = SubCategory (Setoids c ℓ) Sub₀

-------------------------------------------------------------------------------
-- | Unary homomorphisms
-------------------------------------------------------------------------------

Sub₁ : SubCat (Setoids c ℓ) (Σ (Setoid c ℓ) (Op₁ ∘ Carrier))
Sub₁ = record
  { U = proj₁
  ; R = λ {( A , ∙_ ) ( B , ∘_ )} f′ →
            let open Π f′ renaming (_⟨$⟩_ to f)
                open Setoid B using (_≈_) in ∀ x →
              f (∙ x) ≈ ∘ f x
  ; Rid = λ {(A , _)} _ → refl A
  ; _∘R_ = λ {(A , ∙_)} {(B , ∘_)} {(C , ⋆_)} {g′ f′} gᴴ fᴴ →
             let open Π g′ renaming (_⟨$⟩_ to g; cong to cong-g)
                 open Π f′ renaming (_⟨$⟩_ to f) in λ x →
               begin⟨ C ⟩
                 g (f (∙ x)) ≈⟨ cong-g (fᴴ x) ⟩
                 g (∘ f x)   ≈⟨ gᴴ (f x) ⟩
                 ⋆ g (f x)   ∎
  }

H₁ : Category (suc (c ⊔ ℓ)) (c ⊔ ℓ) (c ⊔ ℓ)
H₁ = SubCategory (Setoids c ℓ) Sub₁

-------------------------------------------------------------------------------
-- | Binary homomorphisms
-------------------------------------------------------------------------------

Sub₂ : SubCat (Setoids c ℓ) (Σ (Setoid c ℓ) (Op₂ ∘ Carrier))
Sub₂ = record
  { U = proj₁
  ; R = λ {( A , _∙_ ) ( B , _∘_ )} f′ →
            let open Π f′ renaming (_⟨$⟩_ to f)
                open Setoid B using (_≈_) in ∀ x y →
              f (x ∙ y) ≈ f x ∘ f y
  ; Rid = λ {(A , _)} _ _ → refl A
  ; _∘R_ = λ {(A , _∙_)} {(B , _∘_)} {(C , _⋆_)} {g′ f′} gᴴ fᴴ →
             let open Π g′ renaming (_⟨$⟩_ to g; cong to cong-g)
                 open Π f′ renaming (_⟨$⟩_ to f) in λ x y →
               begin⟨ C ⟩
                 g (f (x ∙ y))     ≈⟨ cong-g (fᴴ x y) ⟩
                 g (f x ∘ f y)     ≈⟨ gᴴ (f x) (f y) ⟩
                 g (f x) ⋆ g (f y) ∎
  }

H₂ : Category (suc (c ⊔ ℓ)) (c ⊔ ℓ) (c ⊔ ℓ)
H₂ = SubCategory (Setoids c ℓ) Sub₂

-------------------------------------------------------------------------------
-- | Experiments in usage
-------------------------------------------------------------------------------

open import Algebra.Bundles

Magmas : Category _ _ _
Magmas = FullSubCategory H₂ (λ M → let open Magma M in setoid , _∙_)

Semigroups            = FullSubCategory Magmas Semigroup.magma
Bands                 = FullSubCategory Magmas Band.magma
CommutativeSemigroups = FullSubCategory Magmas CommutativeSemigroup.magma
Semilattices          = FullSubCategory Magmas Semilattice.magma
SelectiveMagmas       = FullSubCategory Magmas SelectiveMagma.magma


-- foo = merge (Setoids c ℓ) Sub₂ Sub₁ ?
