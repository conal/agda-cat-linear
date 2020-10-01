{-# OPTIONS --without-K --safe #-}

open import Level

module MorphismBundles where

open import Function.Equality renaming (id to ⟶-id; _∘_ to _⟶-∘_ )
open import Relation.Binary.Definitions
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Bundles using (Setoid)
open import Algebra.Core
open import Algebra.Bundles
open import Algebra.Structures
open import Algebra.Morphism.Structures

import Function.Definitions as FunctionDefinitions

import Relation.Binary.Reasoning.Setoid as SetoidReasoning

private
  variable
    a ℓ : Level

module _ (M₁ M₂ : Magma a ℓ) where
  module M₁ = Magma M₁
  module M₂ = Magma M₂
  open FunctionDefinitions M₁._≈_ M₂._≈_ using (Injective; Surjective)

  record MagmaHomomorphism : Set (a ⊔ ℓ) where
    field
      ⟦_⟧ : M₁.Carrier → M₂.Carrier
      isMagmaHomomorphism : IsMagmaHomomorphism M₁.rawMagma M₂.rawMagma ⟦_⟧
    open IsMagmaHomomorphism isMagmaHomomorphism public

  record MagmaMonomorphism : Set (a ⊔ ℓ) where
    field magmaHomomorphism : MagmaHomomorphism
    open MagmaHomomorphism magmaHomomorphism public
    field injective : Injective ⟦_⟧
    homomorphism : MagmaHomomorphism
    homomorphism = record { isMagmaHomomorphism = isMagmaHomomorphism }

  record MagmaIsomorphism : Set (a ⊔ ℓ) where
    field magmaMonomorphism : MagmaMonomorphism
    open MagmaMonomorphism magmaMonomorphism public
    field surjective : Surjective ⟦_⟧
    monomorphism : MagmaMonomorphism
    monomorphism = record
     { magmaHomomorphism = magmaHomomorphism ; injective = injective }

module _ (G₁ G₂ : Semigroup a ℓ) where
  module G₁ = Semigroup G₁
  module G₂ = Semigroup G₂

  SemigroupHomomorphism : Set (a ⊔ ℓ)
  SemigroupHomomorphism = MagmaHomomorphism G₁.magma G₂.magma

  SemigroupMonomorphism : Set (a ⊔ ℓ)
  SemigroupMonomorphism = MagmaMonomorphism G₁.magma G₂.magma

  SemigroupIsomorphism  : Set (a ⊔ ℓ)
  SemigroupIsomorphism  = MagmaIsomorphism  G₁.magma G₂.magma

{-

idᴴ : {A : Semigroup c ℓ} → SemigroupMorphism A A
idᴴ {A} = record
  { setoidM = ⟶-id
  ; isSemigroupMorphism = record
     { ⟦⟧-cong = id
     ; ∙-homo = λ _ _ → Semigroup.refl A
     }
  }

infixr 9 _∘ᴴ_
_∘ᴴ_ : ∀ {A B C : Semigroup c ℓ}
         → SemigroupMorphism B C → SemigroupMorphism A B → SemigroupMorphism A C
_∘ᴴ_ {A} {B} {C} G F = record
  { setoidM = G.setoidM ⟶-∘ F.setoidM
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

-- -- Equivalently? Not quite.
-- _≈ᴴ_ {A} {B} f g = Setoid._≈_ (A.setoid ⇨ B.setoid) F.setoidM G.setoidM
--  where
--    module A = Semigroup A
--    module B = Semigroup B
--    module F = SemigroupMorphism f
--    module G = SemigroupMorphism g

-- ≈ᴴ-refl : ∀ {A B : Semigroup c ℓ} → {f : SemigroupMorphism A B} → f ≈ᴴ f
≈ᴴ-refl : ∀ {A B : Semigroup c ℓ} → Reflexive {A = SemigroupMorphism A B} _≈ᴴ_
≈ᴴ-refl {_} {_} {f} = λ _ _ → F.⟦⟧-cong
 where module F = SemigroupMorphism f

≈ᴴ-sym : ∀ {A B : Semigroup c ℓ} → {f g : SemigroupMorphism A B}
       → f ≈ᴴ g → g ≈ᴴ f
≈ᴴ-sym {A} {B} {f} {g} f≈g x y x≈y = B.sym (f≈g y x (A.sym x≈y))
 where
   module A = Semigroup A
   module B = Semigroup B
   module F = SemigroupMorphism f
   module G = SemigroupMorphism g


∘-assoc : ∀ {A B C D : Semigroup c ℓ}
        → {h : SemigroupMorphism C D} → {g : SemigroupMorphism B C} → {f : SemigroupMorphism A B}
        → (h ∘ᴴ g) ∘ᴴ f ≈ᴴ h ∘ᴴ (g ∘ᴴ f)
∘-assoc {A} {B} {C} {D} {h} {g} {f} =
  λ x y x~y →
  -- ⟦ ((h ∘ᴴ g) ∘ᴴ f) ⟧ x D.≈ ⟦ h ∘ᴴ (g ∘ᴴ f) ⟧ y
  begin
    ⟦ (h ∘ᴴ g) ∘ᴴ f ⟧ x  ≈⟨ {!!} ⟩
    ⟦ (h ∘ᴴ g) ∘ᴴ f ⟧ x  ≈⟨ {!!} ⟩
    ⟦ h ∘ᴴ (g ∘ᴴ f) ⟧ y    ∎

 -- begin
 --    (h ∘ᴴ g) ∘ᴴ f   ≈⟨ ? ⟩
 --    h ∘ᴴ (g ∘ᴴ f)      ∎

  where
    module F = SemigroupMorphism f
    module G = SemigroupMorphism g
    module A = Semigroup A
    module B = Semigroup B
    module C = Semigroup C
    module D = Semigroup D
    open SetoidReasoning D.setoid

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

-}
