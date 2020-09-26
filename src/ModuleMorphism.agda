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


module _ {r ℓr c₁ ℓ₁ c₂ ℓ₂}
         {R    : Semiring r ℓr}
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

  record LeftSemimoduleMorphism :
         Set (r ⊔ c₁ ⊔ ℓ₁ ⊔ c₂ ⊔ ℓ₂) where
    field
      ⟦_⟧ : Morphism
      isLeftSemimoduleMorphism : IsLeftSemimoduleMorphism ⟦_⟧
    open IsLeftSemimoduleMorphism isLeftSemimoduleMorphism


-- TODO: LeftModule, RightSemimodule, etc
