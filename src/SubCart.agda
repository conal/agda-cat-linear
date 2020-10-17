{-# OPTIONS --without-K --safe #-}

-- Cartesian counterpart to SubCat

open import Level
open import Categories.Category
open import Categories.Category.Cartesian


module SubCart {o ℓ e} {C : Category o ℓ e} (CC : Cartesian C) where


open import Data.Product hiding (_×_)

open import Categories.Morphism C using (_≅_)

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
    -- R : {a b : I} → U a ⇒ U b → Set r -- Factor out? Replace by SubCat?
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
              let open HomReasoning {U a} {U ⊤ᴵ} in
              begin
                from ∘ !        ≈⟨ refl⟩∘⟨ !-unique (to ∘ f) ⟩
                from ∘ (to ∘ f) ≈⟨ sym-assoc ⟩
                (from ∘ to) ∘ f ≈⟨ isoʳ ⟩∘⟨refl ⟩
                id ∘ f          ≈⟨ identityˡ ⟩
                f               ∎
          }
      }
  ; products = record
      { product = λ {a b} → let open _≅_ (×≅ {a} {b}) in record
          { A×B = a ×ᴵ b
          ; π₁ = π₁ ∘ to , Rπ₁
          ; π₂ = π₂ ∘ to , Rπ₂
          ; ⟨_,_⟩ = λ {c : I} (f , Rf) (g , Rg) →
              from ∘ ⟨ f , g ⟩ , R⟨,⟩ Rf Rg
          ; project₁ = λ {c : I} {(h , _ )} {(i , _)} →
              let open HomReasoning in
              begin
                (π₁ ∘ to) ∘ (from ∘ ⟨ h , i ⟩) ≈⟨ assoc ⟩
                π₁ ∘ (to ∘ (from ∘ ⟨ h , i ⟩)) ≈⟨ ∘-resp-≈ʳ sym-assoc ⟩
                π₁ ∘ ((to ∘ from) ∘ ⟨ h , i ⟩) ≈⟨ ∘-resp-≈ʳ (∘-resp-≈ˡ isoˡ) ⟩
                π₁ ∘ (id ∘ ⟨ h , i ⟩)          ≈⟨ ∘-resp-≈ʳ identityˡ ⟩
                π₁ ∘ ⟨ h , i ⟩                 ≈⟨ project₁ ⟩
                h                              ∎
          ; project₂ = λ {c : I} {(h , _ )} {(i , _)} →
              let open HomReasoning in
              begin
                (π₂ ∘ to) ∘ (from ∘ ⟨ h , i ⟩) ≈⟨ assoc ⟩
                π₂ ∘ (to ∘ (from ∘ ⟨ h , i ⟩)) ≈⟨ ∘-resp-≈ʳ sym-assoc ⟩
                π₂ ∘ ((to ∘ from) ∘ ⟨ h , i ⟩) ≈⟨ ∘-resp-≈ʳ (∘-resp-≈ˡ isoˡ) ⟩
                π₂ ∘ (id ∘ ⟨ h , i ⟩)          ≈⟨ ∘-resp-≈ʳ identityˡ ⟩
                π₂ ∘ ⟨ h , i ⟩                 ≈⟨ project₂ ⟩
                i                              ∎
          ; unique = λ {c : I} {(h , _)} {(i , _)} {(j , _)}
                       (eq₁ : (π₁ ∘ to) ∘ h ≈ i)
                       (eq₂ : (π₂ ∘ to) ∘ h ≈ j) →
              let open HomReasoning
                  eq₁′ : π₁ ∘ (to ∘ h) ≈ i ; eq₁′ = sym-assoc ○ eq₁
                  eq₂′ : π₂ ∘ (to ∘ h) ≈ j ; eq₂′ = sym-assoc ○ eq₂ in
              begin
                from ∘ ⟨ i , j ⟩ ≈⟨ ∘-resp-≈ʳ (unique eq₁′ eq₂′) ⟩
                from ∘ (to ∘ h)  ≈⟨ sym-assoc ⟩
                (from ∘ to) ∘ h  ≈⟨ ∘-resp-≈ˡ isoʳ ⟩
                id ∘ h           ≈⟨ identityˡ ⟩
                h                ∎
          } }
  } where open SubCart sc

-- SubCartesian is *almost* trivially definable via the transport-by-iso
-- functions from Terminal and Product. Those functions, however, assume that
-- the constructed terminal or product is in the same category as the given
-- terminal or product (IIUC). TODO: generalize them.

-- TODO: counterpart to FullSubCategory.
