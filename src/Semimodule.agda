{-# OPTIONS --without-K --safe #-}

open import Algebra.Structures using (IsMonoid)
open import Algebra.Bundles using (Monoid;Semiring)

module Semimodule {c ℓ} (S : Semiring c ℓ) where

open import Level using (suc;_⊔_)
open import Data.Product
open import Relation.Binary using (Rel)

open import Algebra.Core using (Op₁;Op₂)

open Semiring S renaming (Carrier to Scalar)

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

-- Semimodule constructions, starting with products and functions

_×m_ : ∀ {c} → Op₂ (Monoid c ℓ)
record { Carrier = Carrier₁ ; _≈_ = _≈₁_ ; _∙_ = _∙₁_ ; ε = ε₁ ; isMonoid = isMonoid₁ }
  ×m record { Carrier = Carrier₂ ; _≈_ = _≈₂_ ; _∙_ = _∙₂_ ; ε = ε₂ ; isMonoid = isMonoid₂ } =
 record
   { Carrier = Carrier₁ × Carrier₂
   ; _≈_ = λ { (a₁ , a₂) (b₁ , b₂) → (a₁ ≈₁ b₁) × (a₂ ≈₂ b₂) }
   ; _∙_ = λ { (a₁ , a₂) (b₁ , b₂) → (a₁ ∙₁ b₁) , (a₂ ∙₂ b₂) }
   ; ε = ε₁ , ε₂
   ; isMonoid = {!!}
   }

_×sm_ : Op₂ Semimodule
record { Carrier = Carrier₁ ; _≈_ = _≈₁_ ; _+m_ = _+m₁_ ; 0m = 0m₁ ; _·_ = _·₁_ ; isSemimodule = isSemimodule₁ }
  ×sm
 record { Carrier = Carrier₂ ; _≈_ = _≈₂_ ; _+m_ = _+m₂_ ; 0m = 0m₂ ; _·_ = _·₂_ ; isSemimodule = isSemimodule₂ } =
  record
    { Carrier = Carrier₁ × Carrier₂
    ; _≈_ = λ { (a₁ , b₁) (a₂ , b₂) → (a₁ ≈₁ a₁) × (b₂ ≈₂ b₂) }
    ; _+m_ = λ { (a₁ , b₁) (a₂ , b₂) → (a₁ +m₁ a₂) , (b₁ +m₂ b₂) }
    ; 0m = 0m₁ , 0m₂
    ; _·_ = λ { s (a₁ , a₂) → (s ·₁ a₁) , (s ·₂ a₂) }
    ; isSemimodule = record
        { isMonoid = {!!}
        ; ·-distribˡ = {!!}
        ; ·-distribʳ = {!!}
        ; ·-· = {!!}
        ; 1· = {!!}
        ; 0· = {!!}
        }
    }

-- Dang. There's a lot of work to be done here.
-- Are they in Agda's standard library and I'm just not seeing them?
-- TODO: post an issue.

{-

-}
