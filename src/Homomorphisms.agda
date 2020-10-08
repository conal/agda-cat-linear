{-# OPTIONS --without-K --safe #-}

module Homomorphisms where

-- Algebra.Morphism.Structures has IsMagmaHomomorphism, IsMonoidHomomorphism,
-- etc. Show that the identity function is a homomorphism (for magmas, monoids,
-- etc) and that function composition preserves homomorphicity.

open import Level

open import Algebra.Structures
open import Algebra.Bundles
open import Algebra.Morphism.Structures
open import Function using () renaming (id to id→; _∘_ to _∘→_)
open import Function.Equality  -- setoid functions
open import Relation.Binary.Reasoning.MultiSetoid

private
  variable
    a b c ℓ₁ ℓ₂ ℓ₃ : Level

------------------------------------------------------------------------
-- Morphisms over magma-like structures
------------------------------------------------------------------------

-- IsMagmaHomomorphism uses RawMagma, which lacks reflexivity of _≈_ and thus
-- doesn't compose.

IsMagmaHomomorphism′ : ∀ (M₁ : Magma a ℓ₁) (M₂ : Magma b ℓ₂)
                     → (Magma.setoid M₁ ⟶ Magma.setoid M₂) → Set (a ⊔ ℓ₁ ⊔ ℓ₂)
IsMagmaHomomorphism′ M₁ M₂ f =
  IsMagmaHomomorphism (Magma.rawMagma M₁) (Magma.rawMagma M₂) (f ⟨$⟩_)

idIsMagmaHomomorphism : ∀ (M : Magma a ℓ₁) → IsMagmaHomomorphism′ M M id
idIsMagmaHomomorphism M = record
  { isRelHomomorphism = record { cong = id→ }
  ; homo = λ _ _ → refl
  } where
      open Magma M using (refl)

infixr 9 _∘IsMagmaHomomorphism_
_∘IsMagmaHomomorphism_
  : ∀ {M₁ : Magma a ℓ₁} {M₂ : Magma b ℓ₂} {M₃ : Magma c ℓ₃}
      {f : Magma.setoid M₂ ⟶ Magma.setoid M₃}
      {g : Magma.setoid M₁ ⟶ Magma.setoid M₂}
    → IsMagmaHomomorphism′ M₂ M₃ f
    → IsMagmaHomomorphism′ M₁ M₂ g
    → IsMagmaHomomorphism′ M₁ M₃ (f ∘ g)
_∘IsMagmaHomomorphism_ {M₁ = M₁} {M₂} {M₃} {f} {g} fᴴ gᴴ = record
  { isRelHomomorphism = record { cong = Π.cong (f ∘ g) }
  ; homo = λ (x y : Magma.Carrier M₁) →
      begin⟨ Magma.setoid M₃ ⟩
        f ⟨$⟩ (g ⟨$⟩ (x ∙₁ y))                 ≈⟨ Π.cong f (homo-g x y) ⟩
        f ⟨$⟩ ((g ⟨$⟩ x) ∙₂ (g ⟨$⟩ y))         ≈⟨ homo-f (g ⟨$⟩ x) (g ⟨$⟩ y) ⟩
        (f ⟨$⟩ (g ⟨$⟩ x)) ∙₃ (f ⟨$⟩ (g ⟨$⟩ y)) ∎
  }
 where
   open Magma M₁ renaming (_∙_ to _∙₁_)
   open Magma M₂ renaming (_∙_ to _∙₂_)
   open Magma M₃ renaming (_∙_ to _∙₃_)
   open IsMagmaHomomorphism fᴴ renaming (homo to homo-f)
   open IsMagmaHomomorphism gᴴ renaming (homo to homo-g)

IsSemigroupHomomorphism′ : ∀ (M₁ : Semigroup a ℓ₁) (M₂ : Semigroup b ℓ₂)
                         → (Semigroup.setoid M₁ ⟶ Semigroup.setoid  M₂)
                         → Set (a ⊔ ℓ₁ ⊔ ℓ₂)
IsSemigroupHomomorphism′ M₁ M₂ =
  IsMagmaHomomorphism′ (Semigroup.magma M₁) (Semigroup.magma M₂)

-- Try making do with magma homomorphisms instead of adding semigroup
-- homomorphisms.


------------------------------------------------------------------------
-- Morphisms over monoid-like structures
------------------------------------------------------------------------

IsMonoidHomomorphism′
  : ∀ (M₁ : Monoid a ℓ₁) (M₂ : Monoid b ℓ₂)
    → (Monoid.setoid M₁ ⟶ Monoid.setoid M₂) → Set (a ⊔ ℓ₁ ⊔ ℓ₂)
IsMonoidHomomorphism′ M₁ M₂ f =
  IsMonoidHomomorphism (Monoid.rawMonoid M₁) (Monoid.rawMonoid M₂) (f ⟨$⟩_)

idIsMonoidHomomorphism : ∀ (M : Monoid a ℓ₁) → IsMonoidHomomorphism′ M M id
idIsMonoidHomomorphism M = record
  { isMagmaHomomorphism = idIsMagmaHomomorphism magma
  ; ε-homo = refl
  } where open Monoid M

infixr 9 _∘IsMonoidHomomorphism_
_∘IsMonoidHomomorphism_
  : ∀ {M₁ : Monoid a ℓ₁} {M₂ : Monoid b ℓ₂} {M₃ : Monoid c ℓ₃}
      {f : Monoid.setoid M₂ ⟶ Monoid.setoid M₃}
      {g : Monoid.setoid M₁ ⟶ Monoid.setoid M₂}
    → IsMonoidHomomorphism′ M₂ M₃ f
    → IsMonoidHomomorphism′ M₁ M₂ g
    → IsMonoidHomomorphism′ M₁ M₃ (f ∘ g)
_∘IsMonoidHomomorphism_ {M₁ = M₁} {M₂} {M₃} {f} {g} fᴴ gᴴ = record
  { isMagmaHomomorphism =
      _∘IsMagmaHomomorphism_ {M₁ = magma₁} {magma₂} {magma₃} {f} {g}
                             isMagmaHomo-f isMagmaHomo-g
  ; ε-homo =
      -- f ⟨$⟩ (g ⟨$⟩ ε₁) ≈ ε₃
      begin⟨ Monoid.setoid M₃ ⟩
        f ⟨$⟩ (g ⟨$⟩ ε₁) ≈⟨ Π.cong f ε-homo-g ⟩
        f ⟨$⟩ ε₂         ≈⟨ ε-homo-f ⟩
        ε₃               ∎
 } where
     open Monoid M₁ renaming (ε to ε₁; magma to magma₁)
     open Monoid M₂ renaming (ε to ε₂; magma to magma₂)
     open Monoid M₃ renaming (ε to ε₃; magma to magma₃)
     open IsMonoidHomomorphism fᴴ renaming
       (ε-homo to ε-homo-f; isMagmaHomomorphism to isMagmaHomo-f)
     open IsMonoidHomomorphism gᴴ renaming
       (ε-homo to ε-homo-g; isMagmaHomomorphism to isMagmaHomo-g)

-- ------------------------------------------------------------------------
-- -- Morphisms over group-like structures
-- ------------------------------------------------------------------------

-- -- ...
