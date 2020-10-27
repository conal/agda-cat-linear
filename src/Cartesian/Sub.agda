{-# OPTIONS --without-K --safe #-}

-- Cartesian counterpart to SubCat

open import Level
open import Categories.Category
open import Categories.Category.Cartesian
open import Categories.Category.Cartesian.Structure

module Cartesian.Sub {o ℓ e} (CC : CartesianCategory o ℓ e) where

open CartesianCategory CC using () renaming (U to C)
open Category C

open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_)

import Categories.Object.Product C as P
import Categories.Object.Terminal C as T
open import Categories.Morphism C using (_≅_)

import Category.Sub C as SC
open SC hiding (_⊢_; _∩_; ⋂) public

open import Misc using (≡≅)

record CartOps {i} {I : Set i} (U : I → Obj) : Set (o ⊔ ℓ ⊔ e ⊔ i) where
  infixr 2 _×ᴵ_
  open CartesianCategory CC using (⊤ ; _×_) renaming (terminal to T₀ ; product to P₀)
  field
    ⊤ᴵ : I
    ⊤≡ : ⊤ ≡ U ⊤ᴵ
    _×ᴵ_ : I → I → I
    ×≡   : {a b : I} → U a × U b ≡ U (a ×ᴵ b)

  -- I'm unsure whether to use equality or isomorphism. Define equality but use
  -- the weaker isomorphism wherever possible.
  ⊤≅ : ⊤ ≅ U ⊤ᴵ
  ⊤≅ = ≡≅ ⊤≡
  ×≅ : {a b : I} → U a × U b ≅ U (a ×ᴵ b)
  ×≅ = ≡≅ ×≡

  open import Function using (case_of_)
  
  open _≡_
  -- foo₀ : ∀ {a b} → U (a ×ᴵ b) ≡ U (a ×ᴵ b)
  -- foo₀ = refl

  -- -- Fails with or without K
  -- foo₁ : ∀ {a b} → U a × U b ≡ U (a ×ᴵ b)
  -- foo₁ {a} {b} = case ×≡ {a} {b} of λ { refl → refl }

  -- foo₁ : {a b : I} → U a × U b ≡ U (a ×ᴵ b
  -- foo₁ {a} {b} = bar (×≡ {a} {b})
  --   where bar : U a × U b ≡ U (a ×ᴵ b) → U a × U b ≡ U (a ×ᴵ b)
  --         bar refl = refl  )  -- fail
  --         -- bar x = x

  -- foo : {a b : I} → a ≡ b → a ≡ b  -- okay
  -- foo refl = refl

  -- foo : {a b : I} → U a × U b ≡ U (a ×ᴵ b) → U a × U b ≡ U (a ×ᴵ b)
  -- foo {a} {b} refl = ? -- nope

  -- foo : {a b : I} → U a ≡ U b → U a ≡ U b
  -- foo refl = {!!} -- fails with or without K

  -- foo : {a : I} → U a ≡ U a → U a ≡ U a
  -- foo refl = {!!} -- needs K

  -- -- This one fails if compiling --without-K and succeeds otherwise.
  -- foo : {a : I} → U a ≡ U a → U a ≡ U a
  -- foo refl = {!!} -- nope


  -- foo₂ : ∀ {a b} → Carrier (U (a ×ᴵ b)) → Carrier (U a × U b)

  module terminal′      = T.Terminal (T.transport-by-iso T₀ ⊤≅         )
  module product′ {a b} = P.Product  (P.transport-by-iso P₀ (×≅ {a} {b}))

  -- open terminal′ public
  -- open product′  public

-- TODO: Replace ⊤ᴵ and _×ᴵ_ by a terminal and a product. I guess from a full
-- subcategory of C. Use terminal′ and product′ to make them.

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
  open terminal′ ; open product′
  open SubCat subCat public
  open _≅_
  field
    -- Note: the !, π₁, π₂, ⟨_,_⟩ here are from terminal and product, thus
    -- hiding the isomorphisms.
    R!     : {a : I} → R (! {U a})
    Rπ₁    : {a b : I} → R (π₁ {a} {b})
    Rπ₂    : {a b : I} → R (π₂ {a} {b})
    R⟨_,_⟩ : {a c d : I} {f : U a ⇒ U c} {g : U a ⇒ U d}
           → R f → R g → R (⟨ f , g ⟩)

  SubCartesian : Cartesian SubCategory
  SubCartesian = record
    { terminal = record
        { ⊤ = ⊤ᴵ
        ; ⊤-is-terminal = record
            { ! = ! , R!
            ; !-unique = λ (f , _) → !-unique f
            }
        }
    ; products = record
        { product = λ {a b} → record
            { A×B = a ×ᴵ b
            ; π₁ = π₁ , Rπ₁
            ; π₂ = π₂ , Rπ₂
            ; ⟨_,_⟩ = λ {c : I} (f , Rf) (g , Rg) → ⟨ f , g ⟩ , R⟨ Rf , Rg ⟩
            ; project₁ = project₁
            ; project₂ = project₂
            ; unique = λ {_ (h , _) (i , _) (j , _)} → unique {a} {b} {_} {h} {i} {j}
            } }
    }

  -- open Cartesian SubCartesian public

-- TODO: This SubCartesian definition looks like a special case of a more
-- general construction. Investigate.

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
