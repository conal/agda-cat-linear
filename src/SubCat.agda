{-# OPTIONS --without-K --safe #-}

-- Variation on Categories.Category.SubCategory. The U field of SubCat is moved
-- out to a parameter, so it can be kept in common for SubCat intersection.

open import Categories.Category

module SubCat {o ℓ e} (C : Category o ℓ e) where

open Category C
open Equiv

open import Level
open import Data.Product hiding (map)

private
  variable
    ℓ′ i j : Level
    I : Set i
    J : Set j
    U : I → Obj

record SubCat {I : Set i} (U : I → Obj) : Set (o ⊔ ℓ ⊔ i ⊔ suc ℓ′) where
  infixr 9 _∘R_
  field
    R : {a b : I} → U a ⇒ U b → Set ℓ′
    Rid : {a : I} → R (id {U a})
    _∘R_ : {a b c : I} {f : U b ⇒ U c} {g : U a ⇒ U b} → R f → R g → R (f ∘ g)

SubCategory : SubCat {ℓ′ = ℓ′} {I} U → Category _ _ _
SubCategory {I = I} {U} sc = let open SubCat sc in record
  { Obj       = I
  ; _⇒_       = λ a b → Σ (U a ⇒ U b) R
  ; _≈_       = λ f g → proj₁ f ≈ proj₁ g
  ; id        = id , Rid
  ; _∘_       = zip _∘_ _∘R_
  ; assoc     = assoc
  ; sym-assoc = sym-assoc
  ; identityˡ = identityˡ
  ; identityʳ = identityʳ
  ; identity² = identity²
  ; equiv     = record -- need to expand this out, else the levels don't work out
    { refl  = refl
    ; sym   = sym
    ; trans = trans
    }
  ; ∘-resp-≈  = ∘-resp-≈
  }

FullSubCategory : (U : I → Obj) → Category _ _ _
FullSubCategory {I = I} U = record
  { Obj       = I
  ; _⇒_       = λ x y → U x ⇒ U y
  ; _≈_       = _≈_
  ; id        = id
  ; _∘_       = _∘_
  ; assoc     = assoc
  ; sym-assoc = sym-assoc
  ; identityˡ = identityˡ
  ; identityʳ = identityʳ
  ; identity² = identity²
  ; equiv     = equiv
  ; ∘-resp-≈  = ∘-resp-≈
  }

map : (J→I : J → I) → SubCat {ℓ′ = ℓ′} U → SubCat {ℓ′ = ℓ′} (λ j → U (J→I j))
map J→I subcat = record {R = R; Rid = Rid; _∘R_ = _∘R_}
  where open SubCat subcat

infixr 7 _∩_
_∩_ : ∀ {ℓ₁ ℓ₂} {U : I → Obj}
        (sub₁ : SubCat {ℓ′ = ℓ₁} U) → (sub₂ : SubCat {ℓ′ = ℓ₂} U)
      → SubCat {ℓ′ = ℓ₁ ⊔ ℓ₂} U
record {R = R₁; Rid = Rid₁; _∘R_ = _∘R₁_}
 ∩ record {R = R₂; Rid = Rid₂; _∘R_ = _∘R₂_} = record
  { R = λ f → R₁ f × R₂ f  -- R₁ ∩ R₂
  ; Rid = Rid₁ , Rid₂
  ; _∘R_ = λ (g₁ , g₂) (f₁ , f₂) → g₁ ∘R₁ f₁ , g₂ ∘R₂ f₂
  }
