{-# OPTIONS --without-K --safe #-}

-- Cartesian counterpart to SubCat

open import Level
open import Categories.Category
open import Categories.Category.Cartesian
open import Categories.Category.Cartesian.Structure

module Cartesian.Sub {o ℓ e} (CC : CartesianCategory o ℓ e) where

open CartesianCategory CC renaming (U to C)

open import Function using (_∘′_; case_of_)
open import Data.Product using (_,_) renaming (_×_ to _×′_)

import Categories.Object.Product C as P
import Categories.Object.Terminal C as T
open import Categories.Morphism C using (_≅_)
open import Categories.Morphism.Reasoning C

import Category.Sub C as SC
open SC hiding (_⊢_; _∩_; ⋂) public

open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)
open _≡_

record CartOps {i} {I : Set i} (U : I → Obj) : Set (o ⊔ ℓ ⊔ e ⊔ i) where
  infixr 2 _×ᴵ_
  field
    ⊤ᴵ : I
    ⊤≅ : ⊤ ≅ U ⊤ᴵ
    _×ᴵ_ : I → I → I
    ×≅   : {a b : I} → U a × U b ≅ U (a ×ᴵ b)

private
  variable
    r i j : Level
    I : Set i
    J : Set j
    U : I → Obj
    ops : CartOps U

record SubCart {i r} {I : Set i} {U : I → Obj} (ops : CartOps {i = i} {I = I} U)
       : Set (ℓ ⊔ i ⊔ o ⊔ suc r) where
  open CartOps ops public
  field
    subCat : SubCat {r = r} U
  open SubCat subCat public
  open _≅_
  field
    R!     : {a : I} → R (from ⊤≅ ∘ ! {U a})
    Rπ₁    : {a b : I} → R (π₁ ∘ to (×≅ {a} {b}))
    Rπ₂    : {a b : I} → R (π₂ ∘ to (×≅ {a} {b}))
    R⟨_,_⟩ : {a c d : I} {f : U a ⇒ U c} {g : U a ⇒ U d}
           → R f → R g → R (from (×≅ {c} {d}) ∘ ⟨ f , g ⟩)

open HomReasoning

SubCartesian : ∀ {i I U ops}
             → (sc : SubCart {i = i} {r = r} {I = I} {U = U} ops)
             → let open SubCart sc in
               Cartesian (SubCategory subCat)
SubCartesian {i = i} {I} {U} sc = record
  { terminal = let module t′ = T.Terminal (T.transport-by-iso terminal ⊤≅)
      in record
      { ⊤ = ⊤ᴵ
      ; ⊤-is-terminal = record
          { ! = t′.! , R!
          ; !-unique = λ (f , _) → t′.!-unique f
          }
      }
  ; products = record
      { product = λ {a b} →
          let module p′ = P.Product (P.transport-by-iso product (×≅ {a} {b}))
          in record
          { A×B = a ×ᴵ b
          ; π₁ = p′.π₁ , Rπ₁
          ; π₂ = p′.π₂ , Rπ₂
          ; ⟨_,_⟩ = λ {c : I} (f , Rf) (g , Rg) → p′.⟨ f , g ⟩ , R⟨ Rf , Rg ⟩
          ; project₁ = p′.project₁
          ; project₂ = p′.project₂
          ; unique = λ {_ (h , _) (i , _) (j , _)} → p′.unique {_} {h} {i} {j}
          } }
  } where open SubCart sc

-- TODO: counterpart to FullSubCategory.

infixr 7 _∩_
_∩_ : ∀ {r₁ r₂} {U : I → Obj} {ops}
      → SubCart {r = r₁     } {U = U} ops
      → SubCart {r =      r₂} {U = U} ops
      → SubCart {r = r₁ ⊔ r₂} {U = U} ops
S₁ ∩ S₂ = record
 { subCat = S₁.subCat SC.∩ S₂.subCat
 ; R! =  S₁.R!  , S₂.R!
 ; Rπ₁ = S₁.Rπ₁ , S₂.Rπ₁
 ; Rπ₂ = S₁.Rπ₂ , S₂.Rπ₂
 ; R⟨_,_⟩ = λ (Rf₁ , Rf₂) (Rg₁ , Rg₂) → S₁.R⟨ Rf₁ , Rg₁ ⟩ , S₂.R⟨ Rf₂ , Rg₂ ⟩
 } where
     module S₁ = SubCart S₁
     module S₂ = SubCart S₂

infix 10 ⋂
⋂ : ∀ {J : Set j}
    → (J → SubCart {r = r} {U = U} ops)
    → SubCart {r = j ⊔ r} {U = U} ops
⋂ {J = J} H = record
  { subCat = SC.⋂ (λ j → subCat (H j))
  ; R! = λ j → R! (H j)
  ; Rπ₁ = λ j → Rπ₁ (H j)
  ; Rπ₂ = λ j → Rπ₂ (H j)
  ; R⟨_,_⟩ = λ Rfs Rgs → λ j → R⟨_,_⟩ (H j) (Rfs j) (Rgs j)
  } where open SubCart

syntax ⋂ (λ j → P) = ⋂[ j ] P


{-
-- _⊢_ : (J→I : J → I) → SubCat {r = r} {I = I} U → SubCat {r = r} {I = J} (U ∘′ J→I)

record IsCartMorphism (N : CartOps {j} {J} V) (ops : CartOps {i} {I} U) 
                      (F₀ : J → I) : Set (j ⊔ i) where
  private
    module M = CartOps M
    module N = CartOps N
  field
    F⊤ : M.⊤ᴵ ≡ F₀ (N.⊤ᴵ)
    F× : ∀ {a b : J} → (F₀ a M.×ᴵ F₀ b) ≡ F₀ (a N.×ᴵ b)

record CartMorphism (N : CartOps {j} {J} V) (M : CartOps {i} {I} U) : Set (j ⊔ i) where
  field
    F₀ : J → I
    isCartMorphism : IsCartMorphism N M F₀

  open IsCartMorphism isCartMorphism public

-- record CartOps {i} {I : Set i} (U : I → Obj) : Set (o ⊔ ℓ ⊔ e ⊔ i) where
--   infixr 2 _×ᴵ_
--   field
--     ⊤ᴵ : I
--     ⊤≅ : ⊤ ≅ U ⊤ᴵ
--     _×ᴵ_ : I → I → I
--     ×≅   : {a b : I} → U a × U b ≅ U (a ×ᴵ b)

-- mapOps : ∀ {i j} {I : Set i} {J : Set j} {U : I → Obj}
--        → (F : CartMorphism U → CartOps {j} {J} (U ∘′ J→I)
-- mapOps J→I ops = record { ⊤ᴵ = {!!} ; ⊤≅ = {!!} ; _×ᴵ_ = {!!} ; ×≅ = {!!} }

-- infixr 9 _⊢_
map : ∀ {i j} {I : Set i} {J : Set j} {U : I → Obj} {M : CartOps U}
        (F₀ : J → I) 
      → let V = U ∘′ F₀ in
        {N : CartOps V}
        (CM : IsCartMorphism N M F₀)
    → SubCart {r = r} {I = I} {U = U} M
    → SubCart {r = r} {I = J} {U = V} N
map {i = i} {j} {I} {J} {U} {M} F₀ {N} CM subCart = record
  { subCat = F₀ SC.⊢ subCat
  ; R! = λ {a : J} → -- {!!} 
                     -- let open _≡_ in
                     -- refl
                     case F⊤ of λ { refl → R! }
                     -- let refl = F⊤ in {!!} -- {!!} -- let open _≡_ F⊤ in ?
                     -- let ≡.refl = F⊤ in {!!}
                     -- let refl = F⊤ in R! -- {F₀ a}
  ; Rπ₁ = λ {a b : J} → {!!} -- Rπ₁ {{!!}} {{!!}} -- {!!}
  ; Rπ₂ = λ {a b : J} → {!!}
  ; R⟨_,_⟩ = λ {a c d} {f g} Rf Rg → {!!}
  } where open SubCart subCart
          open IsCartMorphism CM
          open _≅_
          -- open CartOps
          -- open _≡_
          -- open CartOps (F M)

-- Goal: R (from (⊤≅ (F M)) ∘ !)


    -- R!     : {a : I} → R (from ⊤≅ ∘ ! {U a})
    -- Rπ₁    : {a b : I} → R (π₁ ∘ to (×≅ {a} {b}))
    -- Rπ₂    : {a b : I} → R (π₂ ∘ to (×≅ {a} {b}))
    -- R⟨_,_⟩ : {a c d : I} {f : U a ⇒ U c} {g : U a ⇒ U d}
    --        → R f → R g → R (from (×≅ {c} {d}) ∘ ⟨ f , g ⟩)

-}


{-
Goal: SC.SubCat.R (subCat subCart) (from (CartOps.⊤≅ (F M)) ∘ !)

Goal: R (from (CartOps.⊤≅ (F M)) ∘ !)

! : 

-}

-- TODO: trim explicit implicits
