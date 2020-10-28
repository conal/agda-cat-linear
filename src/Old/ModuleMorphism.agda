------------------------------------------------------------------------
-- For submission to The Agda standard library
--
-- Morphisms between modules, semimodules, etc
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module ModuleMorphism where

import Algebra.Morphism.Definitions as MorphismDefinitions
open import Relation.Binary
open import Algebra
import Algebra.Properties.Group as GroupP
open import Function hiding (Morphism)
-- open import Function.Equality
open import Level
import Relation.Binary.Reasoning.Setoid as EqR

-- TODO: trim imports

private
  variable
    a b ℓ₁ ℓ₂ : Level
    A : Set a
    B : Set b

------------------------------------------------------------------------
--

module Definitions {a b ℓ₁} (A : Set a) (B : Set b) (_≈_ : Rel B ℓ₁) where
  open MorphismDefinitions A B _≈_ public

open import Algebra.Morphism.Structures public
open import Algebra.Module.Structures
open import Algebra.Module.Bundles
open import Algebra.Morphism using (IsCommutativeMonoidMorphism)

------------------------------------------------------------------------
-- Bundle homomorphisms

module _ {r ℓᵣ c₁ ℓ₁ c₂ ℓ₂}
         {R    : Semiring r ℓᵣ}
         (From : LeftSemimodule R c₁ ℓ₁)
         (To   : LeftSemimodule R c₂ ℓ₂) where
  private
    module F = LeftSemimodule From
    module T = LeftSemimodule To
  open Definitions F.Carrierᴹ T.Carrierᴹ T._≈ᴹ_

  record IsLeftSemimoduleMorphism (⟦_⟧ : Morphism) :
         Set (r ⊔ c₁ ⊔ ℓ₁ ⊔ c₂ ⊔ ℓ₂) where
    field
      m-homo : IsCommutativeMonoidMorphism
                 F.+ᴹ-commutativeMonoid T.+ᴹ-commutativeMonoid ⟦_⟧
      *ₗ-homo : ∀ {s} → Homomorphic₁ ⟦_⟧ (s F.*ₗ_) (s T.*ₗ_)

    open IsCommutativeMonoidMorphism m-homo public

  IsLeftSemimoduleMorphism-syntax = IsLeftSemimoduleMorphism
  syntax IsLeftSemimoduleMorphism-syntax From To F =
    F Is From -LeftSemimodule⟶ To

  record LeftSemimoduleMorphism : Set (r ⊔ c₁ ⊔ ℓ₁ ⊔ c₂ ⊔ ℓ₂) where
    field
      ⟦_⟧ : Morphism
      isLeftSemimoduleMorphism : IsLeftSemimoduleMorphism ⟦_⟧
    open IsLeftSemimoduleMorphism isLeftSemimoduleMorphism

  LSMM = LeftSemimoduleMorphism

-- Move elsewhere, perhaps into stdlib

open import Algebra.Morphism

  -- record IsSemigroupMorphism (⟦_⟧ : Morphism) :
  --        Set (c₁ ⊔ ℓ₁ ⊔ c₂ ⊔ ℓ₂) where
  --   field
  --     ⟦⟧-cong : ⟦_⟧ Preserves F._≈_ ⟶ T._≈_
  --     ∙-homo  : Homomorphic₂ ⟦_⟧ F._∙_ T._∙_

-- _Preserves_⟶_ : (A → B) → Rel A ℓ₁ → Rel B ℓ₂ → Set _
-- f Preserves P ⟶ Q = P =[ f ]⇒ Q

-- _=[_]⇒_ : Rel A ℓ₁ → (A → B) → Rel B ℓ₂ → Set _
-- P =[ f ]⇒ Q = P ⇒ (Q on f)

-- _⇒_ : REL A B ℓ₁ → REL A B ℓ₂ → Set _
-- P ⇒ Q = ∀ {x y} → P x y → Q x y



-- record IsMagma (∙ : Op₂ A) : Set (a ⊔ ℓ) where
--   field
--     isEquivalence : IsEquivalence _≈_
--     ∙-cong        : Congruent₂ ∙

id-Semigroup : ∀ {c ℓ} {A : Semigroup c ℓ} → IsSemigroupMorphism A A id
id-Semigroup {A = A} = record { ⟦⟧-cong = id ; ∙-homo = λ _ _ → Semigroup.refl A}

_∘-Semigroup_ : ∀ {c ℓ} {A B C : Semigroup c ℓ} {f g}
              → IsSemigroupMorphism B C g
              → IsSemigroupMorphism A B f
              → IsSemigroupMorphism A C (g ∘ f)
record  { ⟦⟧-cong = ⟦⟧-cong-g ; ∙-homo = ∙-homo-g }
   ∘-Semigroup
 record { ⟦⟧-cong = ⟦⟧-cong-f ; ∙-homo = ∙-homo-f }
 = record { ⟦⟧-cong = ⟦⟧-cong-g ∘ ⟦⟧-cong-f
          ; ∙-homo = {!!}
          }

-- I think I want identity and composition on congruences and homomorphisms.

id-cong : ∀ {ℓ a} {A : Set a} {_≈_ : Rel A ℓ} → id Preserves _≈_ ⟶ _≈_
id-cong = id

-- ⟦⟧-cong : ⟦_⟧ Preserves F._≈_ ⟶ T._≈_

_∘-cong_ : ∀ {ℓ i j k}
             {I : Set i} {J : Set j} {K : Set k}
             {_≈ᴵ_ : Rel I ℓ} {_≈ᴶ_ : Rel J ℓ} {_≈ᴷ_ : Rel K ℓ}
             {g : J → K} {f : I → J}
           → g Preserves _≈ᴶ_ ⟶ _≈ᴷ_
           → f Preserves _≈ᴵ_ ⟶ _≈ᴶ_
           → (g ∘ f) Preserves _≈ᴵ_ ⟶ _≈ᴷ_
q ∘-cong r = q ∘ r

  --     ∙-homo  : Homomorphic₂ ⟦_⟧ F._∙_ T._∙_

-- Homomorphic₂ : (A → B) → Op₂ A → Op₂ B → Set _
-- Homomorphic₂ ⟦_⟧ _∙_ _∘_ = ∀ x y → ⟦ x ∙ y ⟧ ≈ (⟦ x ⟧ ∘ ⟦ y ⟧)

open import Algebra.Morphism.Definitions

open import Relation.Binary.Structures using (IsEquivalence)

id-homo : ∀ {ℓ a} {A : Set a} {_≈_ : Rel A ℓ} {_∙_ : Op₂ A} → IsEquivalence _≈_
        → Homomorphic₂ A A _≈_ id _∙_ _∙_
id-homo isEqᴬ = λ _ _ → IsEquivalence.refl isEqᴬ


open import Relation.Binary.Reasoning.Setoid

_∘-homo_ : ∀ {ℓ i j k}
             {I : Set i} {J : Set j} {K : Set k}
             {_≈ᴵ_ : Rel I ℓ} {_≈ᴶ_ : Rel J ℓ} {_≈ᴷ_ : Rel K ℓ}
             {g : J → K} {f : I → J}
           → (g Preserves _≈ᴶ_ ⟶ _≈ᴷ_) → (f Preserves _≈ᴵ_ ⟶ _≈ᴶ_)
           → {_∙ᴵ_ : Op₂ I} → {_∙ᴶ_ : Op₂ J} → {_∙ᴷ_ : Op₂ K}
           → IsEquivalence _≈ᴵ_ → IsEquivalence _≈ᴶ_ → IsEquivalence _≈ᴷ_
           → Homomorphic₂ _ _ _≈ᴷ_ g _∙ᴶ_ _∙ᴷ_
           → Homomorphic₂ _ _ _≈ᴶ_ f _∙ᴵ_ _∙ᴶ_
           → Homomorphic₂ _ _ _≈ᴷ_ (g ∘ f) _∙ᴵ_ _∙ᴷ_
_∘-homo_ {g = g} {f = f} cong-g cong-f {_∙ᴵ_ = _∙ᴵ_} {_∙ᴶ_ = _∙ᴶ_ } {_∙ᴷ_ = _∙ᴷ_ }
         eqᴵ eqᴶ eqᴷ hom-g hom-f x y =
  -- (g ∘ f) (x ∙ᴵ y) ≈ᴷ ((g ∘ f) x ∙ᴷ (g ∘ f) y)

  begin
    (g ∘ f) (x ∙ᴵ y)       ≡⟨⟩
    g (f (x ∙ᴵ y))         ≈⟨ cong-g hom-f ⟩
    g (f x ∙ᴶ f y)         ≈⟨ hom-g ⟩
    g (f x) ∙ᴷ g (f y)     ≡⟨⟩
    (g ∘ f) x ∙ᴷ (g ∘ f) y ∎

-- ∘-homo : ∀ {...} {A : Set a} {_≈_ : Rel A ℓ} {_∙_ : Op₂ A} → IsEquivalence _≈_
--        → Homomorphic₂ _ id _∙_ _∙_

-- Wouldn't all of this be simpler on setoids?

-- id⇒ : ∀ {A} → LSMM A A
-- id⇒ = record
--   { ⟦_⟧ = λ x → x
--   ; isLeftSemimoduleMorphism = record
--       { m-homo = {!!}
--       ; *ₗ-homo = {!!}
--       }
--   }

-- TODO: LeftModule, RightSemimodule, etc
