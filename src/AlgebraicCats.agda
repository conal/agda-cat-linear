{-# OPTIONS --without-K --safe #-}

-- Homomorphisms on algebraic structures, embodied as SubCat structures

open import Level

module AlgebraicCats (o ℓ : Level) where

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

  SemigroupS            = map            Semigroup.magma MagmaS
  BandS                 = map                 Band.magma MagmaS
  CommutativeSemigroupS = map CommutativeSemigroup.magma MagmaS
  SemilatticeS          = map          Semilattice.magma MagmaS
  SelectiveMagmaS       = map       SelectiveMagma.magma MagmaS

  MonoidS = map semigroup SemigroupS ∩ H₀ ε where open Monoid ; open H setoid

  CommutativeMonoidS = map CommutativeMonoid.monoid MonoidS
  BoundedLatticeS    = map    BoundedLattice.monoid MonoidS
  IdempotentCommutativeMonoidS =
    map IdempotentCommutativeMonoid.monoid MonoidS

  GroupS = map monoid MonoidS ∩ H₁ _⁻¹ where open Group ; open H setoid

  AbelianGroupS = map AbelianGroup.group GroupS

  LatticeS = H₂ _∨_ ∩ H₂ _∧_ where open Lattice ; open H setoid

  DistributiveLatticeS = map DistributiveLattice.lattice LatticeS

  NearSemiringS = H₂ _*_ ∩ H₂ _+_ where open NearSemiring ; open H setoid

  SemiringWithoutOneS =
     map           SemiringWithoutOne.nearSemiring NearSemiringS
  CommutativeSemiringWithoutOneS =
    map CommutativeSemiringWithoutOne.nearSemiring NearSemiringS

  SemiringWithoutAnnihilatingZeroS = H₂ _+_ ∩ H₂ _*_ ∩ H₀ 0# ∩ H₀ 1#
   where open SemiringWithoutAnnihilatingZero ; open H setoid

  SemiringS = map Semiring.semiringWithoutAnnihilatingZero
                 SemiringWithoutAnnihilatingZeroS

  CommutativeSemiringS = map CommutativeSemiring.semiring SemiringS

  RingS = map semiring SemiringS ∩ H₁ (-_) where open Ring ; open H setoid

  CommutativeRingS = map CommutativeRing.ring RingS

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
