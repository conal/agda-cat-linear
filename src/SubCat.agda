{-# OPTIONS --without-K --safe #-}

-- Variation on Categories.Category.SubCategory. The U field of SubCat is moved
-- out to a parameter, so it can be kept in common for SubCat intersection.

open import Categories.Category

module SubCat {o ℓ e} (C : Category o ℓ e) where

open Category C
open Equiv

open import Level
open import Data.Product hiding (map)

import Categories.Category.SubCategory C as Sub

open import Categories.Category.SubCategory C using (FullSubCategory) public

private
  variable
    r i j : Level
    I : Set i
    J : Set j
    U : I → Obj

record SubCat {I : Set i} (U : I → Obj) : Set (o ⊔ ℓ ⊔ i ⊔ suc r) where
  infixr 9 _∘R_
  field
    R : {a b : I} → U a ⇒ U b → Set r
    Rid : {a : I} → R (id {U a})
    _∘R_ : {a b c : I} {f : U b ⇒ U c} {g : U a ⇒ U b} → R f → R g → R (f ∘ g)

SubCategory : SubCat {r = r} {I} U → Category _ _ _
SubCategory {I = I} {U} sc = let open SubCat sc in
  Sub.SubCategory record { U = U; R = R ; Rid = Rid ; _∘R_ = _∘R_ }

infixr 9 _⊢_
_⊢_ : (J→I : J → I) → SubCat {r = r} U → SubCat {r = r} (λ j → U (J→I j))
_⊢_ J→I subcat = record {R = R; Rid = Rid; _∘R_ = _∘R_} where open SubCat subcat

infixr 7 _∩_
_∩_ : ∀ {r₁ r₂} {U : I → Obj}
      → SubCat {r = r₁     } U
      → SubCat {r =      r₂} U
      → SubCat {r = r₁ ⊔ r₂} U
record {R = R₁; Rid = Rid₁; _∘R_ = _∘R₁_}
 ∩ record {R = R₂; Rid = Rid₂; _∘R_ = _∘R₂_} = record
  { R = λ f → R₁ f × R₂ f  -- R₁ ∩ R₂
  ; Rid = Rid₁ , Rid₂
  ; _∘R_ = λ (g₁ , g₂) (f₁ , f₂) → g₁ ∘R₁ f₁ , g₂ ∘R₂ f₂
  }

infix 10 ⋂
⋂ : ∀ {J : Set j} → (J → SubCat {r = r} U) → SubCat {r = j ⊔ r} U
⋂ {J = J} H = record
  { R = λ f → ∀ j → R (H j) f  -- ⋂ H R
  ; Rid = λ j → Rid (H j)
  ; _∘R_ = λ G F → λ j → _∘R_ (H j) (G j) (F j)
  } where open SubCat

syntax ⋂ (λ j → P) = ⋂[ j ] P

-- TODO: generalize H to a *dependent* function.

-- TODO: disjunctions/unions
