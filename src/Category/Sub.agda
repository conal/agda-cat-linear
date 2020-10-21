{-# OPTIONS --without-K --safe -Wall #-}

-- Variation on Categories.Category.SubCategory. The U field of SubCat is moved
-- out to a parameter, so it can be kept in common for SubCat intersection.

open import Categories.Category

module Category.Sub {o ℓ e} (C : Category o ℓ e) where

open Category C
open Equiv

open import Level
open import Function using (_∘′_)
open import Data.Product

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
    _∘R_ : {a b c : I} {g : U b ⇒ U c} {f : U a ⇒ U b} → R g → R f → R (g ∘ f)

  SubCategory : Category _ _ _
  SubCategory =
    Sub.SubCategory record { U = U; R = R ; Rid = Rid ; _∘R_ = _∘R_ }

  -- open Category SubCategory public

infixr 9 _⊢_
_⊢_ : (J→I : J → I) → SubCat {r = r} U → SubCat {r = r} (U ∘′ J→I)
_ ⊢ subcat = record {R = R; Rid = Rid; _∘R_ = _∘R_} where open SubCat subcat

infixr 7 _∩_
_∩_ : ∀ {r₁ r₂} {U : I → Obj}
      → SubCat {r = r₁     } U
      → SubCat {r =      r₂} U
      → SubCat {r = r₁ ⊔ r₂} U
S₁ ∩ S₂ = record
  { R = λ f → S₁.R f × S₂.R f  -- S₁.R ∩ S₂.R
  ; Rid = S₁.Rid , S₂.Rid
  ; _∘R_ = λ (g₁ , g₂) (f₁ , f₂) → g₁ S₁.∘R f₁ , g₂ S₂.∘R f₂
  } where module S₁ = SubCat S₁
          module S₂ = SubCat S₂

infix 10 ⋂
⋂ : ∀ {J : Set j} → (J → SubCat {r = r} U) → SubCat {r = j ⊔ r} U
⋂ {J = J} H = record
  { R = λ f → ∀ j → R (H j) f  -- ⋂ H R
  ; Rid = λ j → Rid (H j)
  ; _∘R_ = λ G F → λ j → _∘R_ (H j) (G j) (F j)
  } where open SubCat

syntax ⋂ (λ j → P) = ⋂[ j ] P

-- TODO: generalize H to a *dependent* function.

-- TODO: Try disjunctions/unions. Probably gets hung up on _∘R_ for mismatched
-- disjuncts.
