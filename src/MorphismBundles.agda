{-# OPTIONS --without-K --safe #-}

open import Level

module MorphismBundles {c ℓ : Level} where

open import Function
open import Relation.Binary.Definitions
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Bundles using (Setoid)
open import Algebra.Core
open import Algebra.Bundles
open import Algebra.Morphism

import Relation.Binary.Reasoning.Setoid as SetoidReasoning

record SemigroupMorphism (From : Semigroup c ℓ) (To : Semigroup c ℓ)
        : Set (suc (c ⊔ ℓ)) where
  field
    ⟦_⟧ : Semigroup.Carrier From → Semigroup.Carrier To
    isSemigroupMorphism : IsSemigroupMorphism From To ⟦_⟧

  open IsSemigroupMorphism isSemigroupMorphism public

-- TODO: maybe make ⟦_⟧ be a setoid morphism rather than a regular function.

open SemigroupMorphism

idᴴ : {A : Semigroup c ℓ} → SemigroupMorphism A A
idᴴ {A} = record
  { ⟦_⟧ = id
  ; isSemigroupMorphism = record
      { ⟦⟧-cong = id
      ; ∙-homo = λ _ _ → Semigroup.refl A
      }
  }

infixr 9 _∘ᴴ_
_∘ᴴ_ : ∀ {A B C : Semigroup c ℓ}
         → SemigroupMorphism B C → SemigroupMorphism A B → SemigroupMorphism A C
_∘ᴴ_ {A} {B} {C} G F = record
  { ⟦_⟧ = G.⟦_⟧ ∘ F.⟦_⟧
  ; isSemigroupMorphism = record
      { ⟦⟧-cong = G.⟦⟧-cong ∘ F.⟦⟧-cong
      ; ∙-homo = λ x y →
        -- G.⟦ F.⟦ x A.∙ y ⟧ ⟧ C.≈ G.⟦ F.⟦ x ⟧ ⟧ C.∙ G.⟦ F.⟦ y ⟧ ⟧
        begin
          G.⟦ F.⟦ x A.∙ y ⟧ ⟧              ≈⟨ G.⟦⟧-cong (F.∙-homo x y) ⟩
          G.⟦ F.⟦ x ⟧ B.∙ F.⟦ y ⟧ ⟧        ≈⟨ G.∙-homo (F.⟦ x ⟧) (F.⟦ y ⟧) ⟩
          G.⟦ F.⟦ x ⟧ ⟧ C.∙ G.⟦ F.⟦ y ⟧ ⟧  ∎
      }
  } where
      module F = SemigroupMorphism F
      module G = SemigroupMorphism G
      module A = Semigroup A
      module B = Semigroup B
      module C = Semigroup C
      open SetoidReasoning C.setoid

infix 4 _≈ᴴ_
_≈ᴴ_ : ∀ {A B : Semigroup c ℓ} → Rel (SemigroupMorphism A B) (c ⊔ ℓ)
_≈ᴴ_ {A} {B} f g = ∀ x y → x A.≈ y → ⟦ f ⟧ x B.≈ ⟦ g ⟧ y
 where module A = Semigroup A
       module B = Semigroup B

-- ≈ᴴ-refl : ∀ {A B : Semigroup c ℓ} → {f : SemigroupMorphism A B} → f ≈ᴴ f
≈ᴴ-refl : ∀ {A B : Semigroup c ℓ} → Reflexive {A = SemigroupMorphism A B} _≈ᴴ_
≈ᴴ-refl {_} {_} {f} = λ _ _ → F.⟦⟧-cong
 where module F = SemigroupMorphism f

≈ᴴ-sym : ∀ {A B : Semigroup c ℓ} → {f g : SemigroupMorphism A B}
       → f ≈ᴴ g → g ≈ᴴ f
≈ᴴ-sym {A} {B} {f} {g} f≈g x y x≈y =
  {!!}
  -- begin
  --   G.⟦ x ⟧   ≈⟨ {!!} ⟩  -- f≈g x≈y
  --   G.⟦ y ⟧   ≈⟨ {!!} ⟩
  --   F.⟦ y ⟧   ∎

  -- -- Goal: G.⟦ x ⟧ B.≈ F.⟦ y ⟧
  -- begin
  --   G.⟦ x ⟧   ≈⟨ {!!} ⟩  -- f≈g x≈y
  --   G.⟦ y ⟧   ≈⟨ {!!} ⟩
  --   F.⟦ y ⟧   ∎

 where
   module A = Semigroup A
   module B = Semigroup B
   module F = SemigroupMorphism f
   module G = SemigroupMorphism g
   -- open B.setoid
   open SetoidReasoning B.setoid

-- record IsEquivalence : Set (a ⊔ ℓ) where
--   field
--     refl  : Reflexive _≈_
--     sym   : Symmetric _≈_
--     trans : Transitive _≈_

-- Sym : REL A B ℓ₁ → REL B A ℓ₂ → Set _
-- Sym P Q = P ⇒ flip Q


setoidᴴ : ∀ {A B : Semigroup c ℓ} → Setoid _ _
setoidᴴ {A} {B} = record
  { Carrier = SemigroupMorphism A B
  ; _≈_ = _≈ᴴ_
  ; isEquivalence = record
     { refl = λ x y q → {!!}
     ; sym = {!!}
     ; trans = {!!}
     }
  } where module A = Semigroup A
          module B = Semigroup B



-- record Setoid c ℓ : Set (suc (c ⊔ ℓ)) where
--   infix 4 _≈_
--   field
--     Carrier       : Set c
--     _≈_           : Rel Carrier ℓ
--     isEquivalence : IsEquivalence _≈_



-- ∘-assoc : ∀ {A B C D : Semigroup c ℓ}
--         → {h : SemigroupMorphism C D} → {g : SemigroupMorphism B C} → {f : SemigroupMorphism A B}
--         → (h ∘ᴴ g) ∘ᴴ f ≈ᴴ h ∘ᴴ (g ∘ᴴ f)
-- ∘-assoc {A} {B} {C} {D} {h} {g} {f} =
--  begin
--     (h ∘ᴴ g) ∘ᴴ f   ≈⟨ ? ⟩
--     h ∘ᴴ (g ∘ᴴ f)      ∎
--   where
--     module F = SemigroupMorphism f
--     module G = SemigroupMorphism g
--     module A = Semigroup A
--     module B = Semigroup B
--     module C = Semigroup C
--     module D = Semigroup D
--     open SetoidReasoning D.setoid



----------

open import Categories.Category.Core

Semigroups : Category (suc c ⊔ suc ℓ) (suc c ⊔ suc ℓ) (c ⊔ ℓ)
Semigroups = record
  { Obj = Semigroup c ℓ
  ; _⇒_ = SemigroupMorphism
  ; _≈_ = _≈ᴴ_
  ; id = idᴴ
  ; _∘_ = _∘ᴴ_
  ; assoc = {!!}
  ; sym-assoc = {!!}
  ; identityˡ = {!!}
  ; identityʳ = {!!}
  ; identity² = {!!}
  ; equiv = {!!}
  ; ∘-resp-≈ = {!!}
  }
