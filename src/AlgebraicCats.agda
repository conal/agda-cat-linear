{-# OPTIONS --without-K --safe #-}

-- Algebraic categories via homomorphisms and SubCat structures

open import Level

module AlgebraicCats (o ℓ : Level) where

open import Relation.Binary using (Setoid)

open import Categories.Category.Instance.Setoids using (Setoids)

open import SubCat (Setoids o ℓ) using (_∩_) renaming (SubCategory to Sub)

open import SubCat using () renaming (FullSubCategory to Full)

import Homomorphisms as H

open import Algebra.Bundles

Magmas          = Sub (H₂ _∙_)                    where open Magma          ; open H setoid
Monoids         = Sub (H₂ _∙_ ∩ H₀ ε)             where open Monoid         ; open H setoid
Groups          = Sub (H₂ _∙_ ∩ H₀ ε ∩ H₁ _⁻¹)    where open Group          ; open H setoid
Lattices        = Sub (H₂ _∨_ ∩ H₂ _∧_)           where open Lattice        ; open H setoid
NearSemirings   = Sub (H₂ _*_ ∩ H₂ _+_)           where open NearSemiring   ; open H setoid
Rings           = Sub (H₂ _*_ ∩ H₂ _+_ ∩ H₁ (-_)) where open Ring           ; open H setoid
BooleanAlgebras = Sub (H₂ _∨_ ∩ H₂ _∧_ ∩ H₁ ¬_)   where open BooleanAlgebra ; open H setoid
 
Semigroups                     = Full Magmas        Semigroup.magma
Bands                          = Full Magmas        Band.magma
CommutativeSemigroups          = Full Magmas        CommutativeSemigroup.magma
Semilattices                   = Full Magmas        Semilattice.magma
SelectiveMagmas                = Full Magmas        SelectiveMagma.magma
CommutativeMonoids             = Full Monoids       CommutativeMonoid.monoid
BoundedLattices                = Full Monoids       BoundedLattice.monoid
IdempotentCommutativeMonoids   = Full Monoids       IdempotentCommutativeMonoid.monoid
AbelianGroups                  = Full Groups        AbelianGroup.group
DistributiveLattices           = Full Lattices      DistributiveLattice.lattice
SemiringWithoutOnes            = Full NearSemirings SemiringWithoutOne.nearSemiring
CommutativeSemiringWithoutOnes = Full NearSemirings CommutativeSemiringWithoutOne.nearSemiring
CommutativeRings               = Full Rings         CommutativeRing.ring
