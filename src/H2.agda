-- Experiments in homomorphism construction

open import Level

module H2 (o ℓ : Level) where

open import Algebra using (Op₁; Op₂)

open import Function.Equality using (Π; _⟨$⟩_; _⟶_)
open import Relation.Binary
open import Relation.Binary.Reasoning.MultiSetoid

open import Categories.Category.Instance.Setoids

open Setoid using (Carrier; refl)

open import SubCat (Setoids o ℓ)

-------------------------------------------------------------------------------
-- | Per-operation homomorphisms in nullary, unary, and binary flavors
-------------------------------------------------------------------------------

private
  variable
    q : Level
    Q : Set q

-- Nullary homomorphism, given means of extracting a setoid and nullary
-- operation on its carrier. For instance, S = Monoid.setoid and op = ε.
H₀ : (S : Q → Setoid o ℓ) → ((A : Q) → Carrier (S A)) → SubCat S
H₀ setoid op = record
  { R = λ {a b} f′ →
          let ∙ = op a ; ∘ = op b
              _≈_ = Setoid._≈_ (setoid b)
              open Π f′ renaming (_⟨$⟩_ to f)
          in
            f ∙ ≈ ∘
  ; Rid  = λ {a} → refl (setoid a)
  ; _∘R_ = λ {a b c} {g′} {f′} gᴴ fᴴ →
             let ∙ = op a ; ∘ = op b ; ⋆ = op c
                 open Π g′ renaming (_⟨$⟩_ to g; cong to cong-g)
                 open Π f′ renaming (_⟨$⟩_ to f)
             in begin⟨ setoid c ⟩
                    g (f ∙) ≈⟨ cong-g fᴴ ⟩
                    g ∘     ≈⟨ gᴴ ⟩
                    ⋆       ∎
  }

-- Unary homomorphism, given means of extracting a setoid and unary
-- operation on its carrier. For instance, Q = Group and op = _⁻¹.
H₁ : (S : Q → Setoid o ℓ) → ((A : Q) → Op₁ (Carrier (S A))) → SubCat S
H₁ setoid op = record
  { R = λ {a b} f′ →
          let ∙_ = op a ; ∘_ = op b
              _≈_ = Setoid._≈_ (setoid b) ; infix 4 _≈_
              open Π f′ renaming (_⟨$⟩_ to f)
          in
            ∀ x → f (∙ x) ≈ ∘ f x
  ; Rid  = λ {a} → λ _ → refl (setoid a)
  ; _∘R_ = λ {a b c} {g′} {f′} gᴴ fᴴ →
             let ∙_ = op a ; ∘_ = op b ; ⋆_ = op c
                 open Π g′ renaming (_⟨$⟩_ to g; cong to cong-g)
                 open Π f′ renaming (_⟨$⟩_ to f)
             in λ x → begin⟨ setoid c ⟩
                          g (f (∙ x)) ≈⟨ cong-g (fᴴ x) ⟩
                          g (∘ f x)   ≈⟨ gᴴ (f x) ⟩
                          ⋆ g (f x)   ∎
  }

-- Binary homomorphism, given means of extracting a setoid and binary
-- operation on its carrier. For instance, Q = Semigroup and op = _∙_.
H₂ : (S : Q → Setoid o ℓ) → ((A : Q) → Op₂ (Carrier (S A))) → SubCat S
H₂ setoid op = record
  { R = λ {a b} f′ →
          let _∙_ = op a ; _∘_ = op b
              _≈_ = Setoid._≈_ (setoid b) ; infix 4 _≈_
              open Π f′ renaming (_⟨$⟩_ to f)
          in
            ∀ x y → f (x ∙ y) ≈ f x ∘ f y
  ; Rid  = λ {a} → λ _ _ → refl (setoid a)
  ; _∘R_ = λ {a b c} {g′} {f′} gᴴ fᴴ →
             let _∙_ = op a ; _∘_ = op b ; _⋆_ = op c
                 open Π g′ renaming (_⟨$⟩_ to g; cong to cong-g)
                 open Π f′ renaming (_⟨$⟩_ to f)
             in λ x y → begin⟨ setoid c ⟩
                          g (f (x ∙ y))     ≈⟨ cong-g (fᴴ x y) ⟩
                          g (f x ∘ f y)     ≈⟨ gᴴ (f x) (f y) ⟩
                          g (f x) ⋆ g (f y) ∎
  }

-------------------------------------------------------------------------------
-- | Homomorphisms on algebraic structures, embodied as SubCat structures
-------------------------------------------------------------------------------

open import Algebra.Bundles

-- Sample signatures. The rest all fit this pattern.
MagmaS : SubCat Magma.setoid
SemigroupS : SubCat Semigroup.setoid

MagmaS = H₂ setoid _∙_ where open Magma

SemigroupS            = map            Semigroup.magma MagmaS
BandS                 = map                 Band.magma MagmaS
CommutativeSemigroupS = map CommutativeSemigroup.magma MagmaS
SemilatticeS          = map          Semilattice.magma MagmaS
SelectiveMagmaS       = map       SelectiveMagma.magma MagmaS

MonoidS = map semigroup SemigroupS ∩ H₀ setoid ε where open Monoid

CommutativeMonoidS = map CommutativeMonoid.monoid MonoidS
BoundedLatticeS    = map    BoundedLattice.monoid MonoidS
IdempotentCommutativeMonoidS =
  map IdempotentCommutativeMonoid.monoid MonoidS

GroupS = map monoid MonoidS ∩ H₁ setoid _⁻¹ where open Group

AbelianGroupS = map AbelianGroup.group GroupS

LatticeS = H₂ setoid _∨_ ∩ H₂ setoid _∧_ where open Lattice

DistributiveLatticeS = map DistributiveLattice.lattice LatticeS

NearSemiringS = H₂ setoid _*_ ∩ H₂ setoid _+_ where open NearSemiring

SemiringWithoutOneS =
   map           SemiringWithoutOne.nearSemiring NearSemiringS
CommutativeSemiringWithoutOneS =
  map CommutativeSemiringWithoutOne.nearSemiring NearSemiringS

SemiringWithoutAnnihilatingZeroS =
    H₂ setoid _+_
  ∩ H₂ setoid _*_
  ∩ H₀ setoid  0#
  ∩ H₀ setoid  1#
 where open SemiringWithoutAnnihilatingZero

SemiringS = map Semiring.semiringWithoutAnnihilatingZero
               SemiringWithoutAnnihilatingZeroS

CommutativeSemiringS = map CommutativeSemiring.semiring SemiringS

RingS = map semiring SemiringS ∩ H₁ setoid (-_) where open Ring

CommutativeRingS = map CommutativeRing.ring RingS

BooleanAlgebraS = H₂ setoid _∨_ ∩ H₂ setoid _∧_ ∩ H₁ setoid ¬_
  where open BooleanAlgebra

Magmas                           = SubCategory                           MagmaS
Semigroups                       = SubCategory                       SemigroupS
Bands                            = SubCategory                            BandS
CommutativeSemigroups            = SubCategory            CommutativeSemigroupS
Semilattices                     = SubCategory                     SemilatticeS
SelectiveMagmas                  = SubCategory                  SelectiveMagmaS

Monoids                          = SubCategory                          MonoidS
CommutativeMonoids               = SubCategory               CommutativeMonoidS
BoundedLattices                  = SubCategory                  BoundedLatticeS
IdempotentCommutativeMonoids     = SubCategory     IdempotentCommutativeMonoidS

Groups                           = SubCategory                           GroupS
AbelianGroups                    = SubCategory                    AbelianGroupS

Lattices                         = SubCategory                         LatticeS
DistributiveLattices             = SubCategory             DistributiveLatticeS

NearSemirings                    = SubCategory                    NearSemiringS
SemiringWithoutOnes              = SubCategory              SemiringWithoutOneS
CommutativeSemiringWithoutOnes   = SubCategory   CommutativeSemiringWithoutOneS

Semirings                        = SubCategory                        SemiringS
CommutativeSemirings             = SubCategory             CommutativeSemiringS

CommutativeRings                 = SubCategory                 CommutativeRingS
BooleanAlgebras                  = SubCategory                  BooleanAlgebraS

SemiringWithoutAnnihilatingZeros = SubCategory SemiringWithoutAnnihilatingZeroS

