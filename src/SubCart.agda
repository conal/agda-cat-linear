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
    r i j : Level
    I : Set i
    J : Set j
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
    ⊤≅ : U ⊤ᴵ ≅ ⊤
    R! : {a : I} → R (to ⊤≅ ∘ ! {U a})
  infixr 2 _×ᴵ_
  field
    _×ᴵ_ : I → I → I
    ×≅   : {a b : I} → U (a ×ᴵ b) ≅ U a × U b
    Rπ₁  : {a b : I} → R (π₁ ∘ from (×≅ {a} {b}))
    Rπ₂  : {a b : I} → R (π₂ ∘ from (×≅ {a} {b}))
    R⟨,⟩ : ∀ {a c d : I} {f : U a ⇒ U c} {g : U a ⇒ U d}
         → R f → R g → R (to (×≅ {c} {d}) ∘ ⟨ f , g ⟩)

SubCartesian : ∀ {i I U}
             → (sc : SubCart {i = i} {r} {I} U)
             → let open SubCart sc in
               Cartesian (SubCategory subCat)
SubCartesian {i = i} {I} {U} sc = record
  { terminal = record
      { ⊤ = ⊤ᴵ
      ; ⊤-is-terminal = let open _≅_ ⊤≅ in record
          { ! = to ∘ ! , R!
          ; !-unique = λ {a : I} (f , _) →
              let open HomReasoning {U a} {U ⊤ᴵ} in
              begin
                to ∘ !          ≈⟨ refl⟩∘⟨ !-unique (from ∘ f) ⟩
                to ∘ (from ∘ f) ≈⟨ sym-assoc ⟩
                (to ∘ from) ∘ f ≈⟨ isoˡ ⟩∘⟨refl ⟩
                id ∘ f          ≈⟨ identityˡ ⟩
                f               ∎
          }
      }
  ; products = record
      { product = λ {a b} → let open _≅_ (×≅ {a} {b}) in record
          { A×B = a ×ᴵ b
          ; π₁ = π₁ ∘ from , Rπ₁
          ; π₂ = π₂ ∘ from , Rπ₂
          ; ⟨_,_⟩ = λ {c : I} (f , Rf) (g , Rg) →
              to ∘ ⟨ f , g ⟩ , R⟨,⟩ Rf Rg
          ; project₁ = λ {c : I} {(h , _ )} {(i , _)} →
              let open HomReasoning in
              begin
                (π₁ ∘ from) ∘ (to ∘ ⟨ h , i ⟩) ≈⟨ assoc ⟩
                π₁ ∘ (from ∘ (to ∘ ⟨ h , i ⟩)) ≈⟨ ∘-resp-≈ʳ sym-assoc ⟩
                π₁ ∘ ((from ∘ to) ∘ ⟨ h , i ⟩) ≈⟨ ∘-resp-≈ʳ (∘-resp-≈ˡ isoʳ) ⟩
                π₁ ∘ (id ∘ ⟨ h , i ⟩)          ≈⟨ ∘-resp-≈ʳ identityˡ ⟩
                π₁ ∘ ⟨ h , i ⟩                 ≈⟨ project₁ ⟩
                h                              ∎
          ; project₂ = λ {c : I} {(h , _ )} {(i , _)} →
              let open HomReasoning in
              begin
                (π₂ ∘ from) ∘ (to ∘ ⟨ h , i ⟩) ≈⟨ assoc ⟩
                π₂ ∘ (from ∘ (to ∘ ⟨ h , i ⟩)) ≈⟨ ∘-resp-≈ʳ sym-assoc ⟩
                π₂ ∘ ((from ∘ to) ∘ ⟨ h , i ⟩) ≈⟨ ∘-resp-≈ʳ (∘-resp-≈ˡ isoʳ) ⟩
                π₂ ∘ (id ∘ ⟨ h , i ⟩)          ≈⟨ ∘-resp-≈ʳ identityˡ ⟩
                π₂ ∘ ⟨ h , i ⟩                 ≈⟨ project₂ ⟩
                i                              ∎
          ; unique = λ {c : I} {H@(h , _)} {I@(i , _)} {J@(j , _)}
                       (eq₁ : (π₁ ∘ from) ∘ h ≈ i)
                       (eq₂ : (π₂ ∘ from) ∘ h ≈ j) →
              let open HomReasoning
                  eq₁′ : π₁ ∘ (from ∘ h) ≈ i ; eq₁′ = sym-assoc ○ eq₁
                  eq₂′ : π₂ ∘ (from ∘ h) ≈ j ; eq₂′ = sym-assoc ○ eq₂ in
              begin
                to ∘ ⟨ i , j ⟩  ≈⟨ ∘-resp-≈ʳ (unique eq₁′ eq₂′) ⟩
                to ∘ (from ∘ h) ≈⟨ sym-assoc ⟩
                (to ∘ from) ∘ h ≈⟨ ∘-resp-≈ˡ isoˡ ⟩
                id ∘ h          ≈⟨ identityˡ ⟩
                h               ∎
          } }
  } where open SubCart sc

-- Maybe use this function (from Categories.Object.Terminal) instead:

-- transport-by-iso : (t : Terminal) → ∀ {X} → ⊤ t ≅ X → Terminal
