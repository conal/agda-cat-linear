{-# OPTIONS --without-K --safe #-}

-- Cartesian counterpart to SubCat

open import Level
open import Categories.Category
open import Categories.Category.Cartesian


module SubCart {o ℓ e} {C : Category o ℓ e} (CC : Cartesian C) where


open import Data.Product hiding (_×_)

open import Categories.Morphism C using (_≅_)
open import Categories.Morphism.Reasoning C

open import SubCat C

open Category C
open Cartesian CC
open Equiv

private
  variable
    r i : Level
    I : Set i
    U : I → Obj

open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)

record SubCart {I : Set i} (U : I → Obj) : Set (ℓ ⊔ i ⊔ o ⊔ e ⊔ suc r) where
  field
    subCat : SubCat {r = r} U
  open SubCat subCat public
  open _≅_
  field
    ⊤ᴵ : I
    ⊤≅ : ⊤ ≅ U ⊤ᴵ
    R! : {a : I} → R (from ⊤≅ ∘ ! {U a})
  infixr 2 _×ᴵ_
  field
    _×ᴵ_ : I → I → I
    ×≅   : {a b : I} → U a × U b ≅ U (a ×ᴵ b)
    Rπ₁  : {a b : I} → R (π₁ ∘ to (×≅ {a} {b}))
    Rπ₂  : {a b : I} → R (π₂ ∘ to (×≅ {a} {b}))
    R⟨,⟩ : ∀ {a c d : I} {f : U a ⇒ U c} {g : U a ⇒ U d}
         → R f → R g → R (from (×≅ {c} {d}) ∘ ⟨ f , g ⟩)

open HomReasoning

SubCartesian : ∀ {i I U}
             → (sc : SubCart {i = i} {r} {I} U)
             → let open SubCart sc in
               Cartesian (SubCategory subCat)
SubCartesian {i = i} {I} {U} sc = record
  { terminal = record
      { ⊤ = ⊤ᴵ
      ; ⊤-is-terminal = let open _≅_ ⊤≅ in record
          { ! = from ∘ ! , R!
          ; !-unique = λ {a : I} (f , _) →
              begin
                from ∘ !      ≈⟨ refl⟩∘⟨ !-unique (to ∘ f) ⟩
                from ∘ to ∘ f ≈⟨ cancelˡ isoʳ ⟩
                f             ∎
          }
      }
  ; products = record
      { product = λ {a b} → let open _≅_ (×≅ {a} {b}) in record
          { A×B = a ×ᴵ b
          ; π₁ = π₁ ∘ to , Rπ₁
          ; π₂ = π₂ ∘ to , Rπ₂
          ; ⟨_,_⟩ = λ {c : I} (f , Rf) (g , Rg) → from ∘ ⟨ f , g ⟩ , R⟨,⟩ Rf Rg
          ; project₁ = cancelInner isoˡ ○ project₁
          ; project₂ = cancelInner isoˡ ○ project₂
          ; unique = λ {_ (h , _) (i , _) (j , _)} eq₁ eq₂ →
            begin
                from ∘ ⟨ i , j ⟩                        
              ≈˘⟨ refl⟩∘⟨ ⟨⟩-cong₂ eq₁ eq₂ ⟩
                from ∘ ⟨ (π₁ ∘ to) ∘ h , (π₂ ∘ to) ∘ h ⟩
              ≈⟨ refl⟩∘⟨ unique sym-assoc sym-assoc ⟩
                from ∘ to ∘ h
              ≈⟨ cancelˡ isoʳ ⟩
                h
              ∎
          } }
  } where open SubCart sc

-- SubCartesian is *almost* trivially definable via the transport-by-iso
-- functions from Terminal and Product. Those functions, however, assume that
-- the constructed terminal or product is in the same category as the given
-- terminal or product (IIUC). TODO: generalize them.

-- TODO: counterpart to FullSubCategory.
