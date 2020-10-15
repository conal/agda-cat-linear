{-# OPTIONS --without-K --safe #-}

-- Algebraic categories via homomorphisms and SubCat structures

open import Level

module AlgebraicCats (o ℓ : Level) where

open import Algebra.Bundles

module _ where

  import Homomorphisms as H
  open import Categories.Category.Instance.Setoids using (Setoids)
  open import SubCat (Setoids o ℓ) using (_∩_) renaming (SubCategory to ⟨_⟩)

  Magmas          = ⟨ H₂ _∙_                    ⟩ where open Magma          ; open H setoid
  Monoids         = ⟨ H₂ _∙_ ∩ H₀ ε             ⟩ where open Monoid         ; open H setoid
  Groups          = ⟨ H₂ _∙_ ∩ H₀ ε ∩ H₁ _⁻¹    ⟩ where open Group          ; open H setoid
  Lattices        = ⟨ H₂ _∨_ ∩ H₂ _∧_           ⟩ where open Lattice        ; open H setoid
  NearSemirings   = ⟨ H₂ _*_ ∩ H₂ _+_           ⟩ where open NearSemiring   ; open H setoid
  Rings           = ⟨ H₂ _*_ ∩ H₂ _+_ ∩ H₁ (-_) ⟩ where open Ring           ; open H setoid
  BooleanAlgebras = ⟨ H₂ _∨_ ∩ H₂ _∧_ ∩ H₁ ¬_   ⟩ where open BooleanAlgebra ; open H setoid

module _ where

  open import SubCat using () renaming (FullSubCategory to _⇰_)
 
  Semigroups                     = Magmas        ⇰ Semigroup.magma
  Bands                          = Magmas        ⇰ Band.magma
  CommutativeSemigroups          = Magmas        ⇰ CommutativeSemigroup.magma
  Semilattices                   = Magmas        ⇰ Semilattice.magma
  SelectiveMagmas                = Magmas        ⇰ SelectiveMagma.magma
  CommutativeMonoids             = Monoids       ⇰ CommutativeMonoid.monoid
  BoundedLattices                = Monoids       ⇰ BoundedLattice.monoid
  IdempotentCommutativeMonoids   = Monoids       ⇰ IdempotentCommutativeMonoid.monoid
  AbelianGroups                  = Groups        ⇰ AbelianGroup.group
  DistributiveLattices           = Lattices      ⇰ DistributiveLattice.lattice
  SemiringWithoutOnes            = NearSemirings ⇰ SemiringWithoutOne.nearSemiring
  CommutativeSemiringWithoutOnes = NearSemirings ⇰ CommutativeSemiringWithoutOne.nearSemiring
  CommutativeRings               = Rings         ⇰ CommutativeRing.ring
