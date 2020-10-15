{-# OPTIONS --without-K --safe #-}

-- Homomorphisms on algebraic structures, embodied as SubCat structures

open import Level

module Old.Algebraic2 (o ℓ : Level) where

open import Relation.Binary using (Setoid)

open import Categories.Category.Instance.Setoids using (Setoids)

open import SubCat (Setoids o ℓ)
import Homomorphisms as H

private

  open import Algebra.Bundles

  -- Sample signatures. The rest all fit this pattern.
  MagmaS : SubCat Magma.setoid
  SemigroupS : SubCat Semigroup.setoid

  MagmaS = H₂ _∙_ where open Magma ; open H setoid

  SemigroupS            =            Semigroup.magma ⊢ MagmaS
  BandS                 =                 Band.magma ⊢ MagmaS
  CommutativeSemigroupS = CommutativeSemigroup.magma ⊢ MagmaS
  SemilatticeS          =          Semilattice.magma ⊢ MagmaS
  SelectiveMagmaS       =       SelectiveMagma.magma ⊢ MagmaS

  MonoidS = semigroup ⊢ SemigroupS ∩ H₀ ε where open Monoid ; open H setoid

  CommutativeMonoidS = CommutativeMonoid.monoid ⊢ MonoidS
  BoundedLatticeS    =    BoundedLattice.monoid ⊢ MonoidS
  IdempotentCommutativeMonoidS =
    IdempotentCommutativeMonoid.monoid ⊢ MonoidS

  GroupS = monoid ⊢ MonoidS ∩ H₁ _⁻¹ where open Group ; open H setoid

  AbelianGroupS = AbelianGroup.group ⊢ GroupS

  LatticeS = H₂ _∨_ ∩ H₂ _∧_ where open Lattice ; open H setoid

  DistributiveLatticeS = DistributiveLattice.lattice ⊢ LatticeS

  NearSemiringS = H₂ _*_ ∩ H₂ _+_ where open NearSemiring ; open H setoid

  SemiringWithoutOneS =
               SemiringWithoutOne.nearSemiring ⊢ NearSemiringS
  CommutativeSemiringWithoutOneS =
    CommutativeSemiringWithoutOne.nearSemiring ⊢ NearSemiringS

  SemiringWithoutAnnihilatingZeroS = H₂ _+_ ∩ H₂ _*_ ∩ H₀ 0# ∩ H₀ 1#
   where open SemiringWithoutAnnihilatingZero ; open H setoid

  SemiringS = Semiring.semiringWithoutAnnihilatingZero
                ⊢ SemiringWithoutAnnihilatingZeroS

  CommutativeSemiringS = CommutativeSemiring.semiring ⊢ SemiringS

  RingS = semiring ⊢ SemiringS ∩ H₁ (-_) where open Ring ; open H setoid

  CommutativeRingS = CommutativeRing.ring ⊢ RingS

  BooleanAlgebraS = H₂ _∨_ ∩ H₂ _∧_ ∩ H₁ ¬_
    where open BooleanAlgebra ; open H setoid

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
