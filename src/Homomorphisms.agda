-- N-ary homomorphism properties as categories (one per n).
-- Generalizes pointed setoids, which corresponds to n ≡ 0.

open import Level

module Homomorphisms (c ℓ : Level) where

open import Data.Product
open import Function using (_∘′_; _$_; _on_) renaming (id to idf)
open import Relation.Binary
open import Function.Equality hiding (id; _∘_)
open import Relation.Binary.Reasoning.MultiSetoid

open import Categories.Category
open import Categories.Category.Instance.Setoids

open Setoid using (Carrier; refl)
open Category (Setoids c ℓ)

open import Relation.Binary.Construct.On

H₀ : Category (suc (c ⊔ ℓ)) (c ⊔ ℓ) (c ⊔ ℓ)
H₀ = record
  { Obj = Σ (Setoid c ℓ) Carrier
  ; _⇒_ = λ ( A , x ) ( B , y ) → let open Setoid B renaming (_≈_ to _≈₂_) in
                                    Σ (A ⟶ B) (λ f → f ⟨$⟩ x ≈₂ y)
  ; _≈_ = _≈_ on proj₁
  ; id = λ {(A , _)} → id , refl A
  ; _∘_ = λ {(A , a)} {(B , b)} {(C , c)} (g′ , gᴴ) (f′ , fᴴ) →
              g′ ∘ f′ , let open Π g′ renaming (_⟨$⟩_ to g; cong to cong-g)
                            open Π f′ renaming (_⟨$⟩_ to f) in
                          begin⟨ C ⟩
                            g (f a) ≈⟨ cong-g fᴴ ⟩
                            g b     ≈⟨ gᴴ ⟩
                            c       ∎
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
