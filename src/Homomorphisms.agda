-- N-ary homomorphism properties as categories (one per n).
-- Generalizes pointed setoids, which corresponds to n ≡ 0.

open import Level

module Homomorphisms (c ℓ : Level) where

open import Data.Product
open import Function using (_∘′_; _$_; _on_) -- renaming (id to idf)
open import Relation.Binary
open import Function.Equality hiding (id; _∘_)
open import Relation.Binary.Reasoning.MultiSetoid
open import Algebra using (Op₁; Op₂)
open import Algebra.Morphism.Definitions
open import Relation.Binary.Construct.On

open import Categories.Category
open import Categories.Category.Instance.Setoids

open Setoid using (Carrier; refl)
open Category (Setoids c ℓ)

-- Nullary homomorphisms, i.e., "pointed setoids"
H₀ : Category (suc (c ⊔ ℓ)) (c ⊔ ℓ) (c ⊔ ℓ)
H₀ = record
  { Obj = Σ (Setoid c ℓ) Carrier
  ; _⇒_ = λ ( A , ε₁ ) ( B , ε₂ ) → let open Setoid B renaming (_≈_ to _≈₂_) in
                                      Σ (A ⟶ B) (λ f → f ⟨$⟩ ε₁ ≈₂ ε₂)
  ; _≈_ = _≈_ on proj₁
  ; id = λ {(A , _)} → id , refl A
  ; _∘_ = λ {(A , ε₁)} {(B , ε₂)} {(C , ε₃)} (g′ , gᴴ) (f′ , fᴴ) →
              g′ ∘ f′ , let open Π g′ renaming (_⟨$⟩_ to g; cong to cong-g)
                            open Π f′ renaming (_⟨$⟩_ to f) in
                          begin⟨ C ⟩
                            g (f ε₁) ≈⟨ cong-g fᴴ ⟩
                            g ε₂     ≈⟨ gᴴ ⟩
                            ε₃       ∎
  ; assoc = λ {_ _ _ _} {(f , _) (g , _) (h , _)} →
              assoc {f = f} {g} {h}
  ; sym-assoc = λ {_ _ _ _} {(f , _) (g , _) (h , _)} →
              sym-assoc {f = f} {g} {h}
  ; identityˡ = λ {_ _} {(f , _)} → identityˡ {f = f}
  ; identityʳ = λ {_ _} {(f , _)} → identityʳ {f = f}
  ; identity² = λ {(A , _)} → identity² {A}
  ; equiv = isEquivalence proj₁ equiv 
  ; ∘-resp-≈ = λ {(A , _)} {(B , _)} {(C , _)}
                 {(f , _) (h , _)} {(g , _) (i , _)} →
                 ∘-resp-≈ {A} {B} {C} {f} {h} {g} {i}
  }

-- Unary homomorphisms
H₁ : Category _ _ _
H₁ = record
  { Obj = Σ (Setoid c ℓ) (λ s → Op₁ (Carrier s))  -- (Op₁ ∘′ Carrier)
  ; _⇒_ = λ ( A , μ₁ ) ( B , μ₂ ) →
            let open Setoid A renaming (_≈_ to _≈₁_)
                open Setoid B renaming (_≈_ to _≈₂_) in
              Σ (A ⟶ B) (λ f′ → let open Π f′ renaming (_⟨$⟩_ to f) in ∀ x →
                                  f (μ₁ x) ≈₂ μ₂ (f x))
  ; _≈_ = _≈_ on proj₁
  ; id = λ {(A , _)} → id , (λ _ → refl A)
  ; _∘_ = λ {(A , μ₁)} {(B , μ₂)} {(C , μ₃)} (g′ , gᴴ) (f′ , fᴴ) →
              g′ ∘ f′ , let open Π g′ renaming (_⟨$⟩_ to g; cong to cong-g)
                            open Π f′ renaming (_⟨$⟩_ to f) in λ x →
                          begin⟨ C ⟩
                            g (f (μ₁ x)) ≈⟨ cong-g (fᴴ x) ⟩
                            g (μ₂ (f x)) ≈⟨ gᴴ (f x) ⟩
                            μ₃ (g (f x)) ∎
  ; assoc = λ {_ _ _ _} {(f , _) (g , _) (h , _)} →
              assoc {f = f} {g} {h}
  ; sym-assoc = λ {_ _ _ _} {(f , _) (g , _) (h , _)} →
              sym-assoc {f = f} {g} {h}
  ; identityˡ = λ {_ _} {(f , _)} → identityˡ {f = f}
  ; identityʳ = λ {_ _} {(f , _)} → identityʳ {f = f}
  ; identity² = λ {(A , _)} → identity² {A}
  ; equiv = isEquivalence proj₁ equiv 
  ; ∘-resp-≈ = λ {(A , _)} {(B , _)} {(C , _)}
                 {(f , _) (h , _)} {(g , _) (i , _)} →
                 ∘-resp-≈ {A} {B} {C} {f} {h} {g} {i}
  }

-- Binary homomorphisms
H₂ : Category _ _ _
H₂ = record
  { Obj = Σ (Setoid c ℓ) (λ s → Op₂ (Carrier s))  -- (Op₁ ∘′ Carrier)
  ; _⇒_ = λ ( A , _∙₁_ ) ( B , _∙₂_ ) →
            let open Setoid A renaming (_≈_ to _≈₁_)
                open Setoid B renaming (_≈_ to _≈₂_) in
              Σ (A ⟶ B) (λ f′ → let open Π f′ renaming (_⟨$⟩_ to f) in ∀ x y →
                                  f (x ∙₁ y) ≈₂ f x ∙₂ f y)
  ; _≈_ = _≈_ on proj₁
  ; id = λ {(A , _)} → id , (λ _ _ → refl A)

  ; _∘_ = λ {(A , _∙₁_)} {(B , _∙₂_)} {(C , _∙₃_)} (g′ , gᴴ) (f′ , fᴴ) →
              g′ ∘ f′ , let open Π g′ renaming (_⟨$⟩_ to g; cong to cong-g)
                            open Π f′ renaming (_⟨$⟩_ to f) in λ x y →
                          begin⟨ C ⟩
                            g (f (x ∙₁ y))     ≈⟨ cong-g (fᴴ x y) ⟩
                            g (f x ∙₂ f y)     ≈⟨ gᴴ (f x) (f y) ⟩
                            g (f x) ∙₃ g (f y) ∎
  ; assoc = λ {_ _ _ _} {(f , _) (g , _) (h , _)} →
              assoc {f = f} {g} {h}
  ; sym-assoc = λ {_ _ _ _} {(f , _) (g , _) (h , _)} →
              sym-assoc {f = f} {g} {h}
  ; identityˡ = λ {_ _} {(f , _)} → identityˡ {f = f}
  ; identityʳ = λ {_ _} {(f , _)} → identityʳ {f = f}
  ; identity² = λ {(A , _)} → identity² {A}
  ; equiv = isEquivalence proj₁ equiv 
  ; ∘-resp-≈ = λ {(A , _)} {(B , _)} {(C , _)}
                 {(f , _) (h , _)} {(g , _) (i , _)} →
                 ∘-resp-≈ {A} {B} {C} {f} {h} {g} {i}
  }


-- TODO: redefine as subcategories of Setoid, eliminating repetition of assoc, etc.
