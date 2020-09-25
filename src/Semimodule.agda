{-# OPTIONS --without-K --safe #-}



-- Hah! After updating my clone of agda-stdlib, I see that it has semimodules!
-- Junk this module.


open import Algebra.Structures using (IsMonoid)
open import Algebra.Bundles using (Monoid;Semiring)

module Semimodule {c ℓ} (S : Semiring c ℓ) where

open import Level hiding (zero)
open import Data.Product
open import Relation.Binary using (Rel)

open import Algebra.Core using (Op₁;Op₂)

open Semiring S renaming (Carrier to Scalar)

-- For Algebra.Structures

record IsSemimodule {Carrier : Set c} (_≈_ : Rel Carrier ℓ)
         (_+m_ : Op₂ Carrier) (0m : Carrier)
         (_·_ : Scalar → Op₁ Carrier) : Set (c ⊔ ℓ) where
  field
    isMonoid : IsMonoid _≈_ _+m_ 0m
    ·-distribˡ : ∀ {r u v} → (r · (u +m v)) ≈ ((r · u) +m (r · v))
    ·-distribʳ : ∀ {r s u} → ((r + s) · u)  ≈ ((r · u) +m (s · u))
    ·-· : ∀ {r s u} → ((r * s) · u) ≈ (r · (s · u))
    1· : ∀ {u} → (1# · u) ≈ u
    0· : ∀ {u} → (0# · u) ≈ 0m
  open IsMonoid isMonoid public

-- For Algebra.Bundles

record RawSemimodule : Set (suc c ⊔ suc ℓ) where
  infixl 7 _·_
  infixl 6 _+m_
  infix  4 _≈_
  field
    Carrier  : Set c
    _≈_      : Rel Carrier ℓ
    _+m_     : Op₂ Carrier
    0m       : Carrier
    _·_      : Scalar → Op₁ Carrier

-- Left semimodule
record Semimodule : Set (suc c ⊔ suc ℓ) where
  infixl 7 _·_
  infixl 6 _+m_
  infix  4 _≈_
  field
    Carrier  : Set c
    _≈_      : Rel Carrier ℓ
    _+m_     : Op₂ Carrier
    0m       : Carrier
    _·_      : Scalar → Op₁ Carrier
    isSemimodule : IsSemimodule _≈_ _+m_ 0m _·_
  open IsSemimodule isSemimodule

SemiringAsSemimodule : Semimodule
SemiringAsSemimodule = record
  { Carrier = Scalar
  ; _≈_ = _≈_
  ; _+m_ = _+_
  ; 0m = 0#
  ; _·_ = _*_
  ; isSemimodule = record
      { isMonoid = +-isMonoid
      ; ·-distribˡ = distribˡ _ _ _
      ; ·-distribʳ = distribʳ _ _ _
      ; ·-· = *-assoc _ _ _
      ; 1· = *-identityˡ _
      ; 0· = proj₁ zero _
      }
  }

-- For Algebra.Construct.DirectProduct

open import Data.Product.Relation.Binary.Pointwise.NonDependent

private
  variable
    a b ℓ₁ ℓ₂ : Level

rawSemimodule : Op₂ RawSemimodule
rawSemimodule M N = record
  { Carrier = M.Carrier × N.Carrier
  ; _≈_     = Pointwise M._≈_ N._≈_
  ; _+m_    = zip M._+m_ N._+m_
  ; 0m      = M.0m , N.0m
  ; _·_     = λ s → map (s M.·_) (s N.·_)
  } where module M = RawSemimodule M; module N = RawSemimodule N
