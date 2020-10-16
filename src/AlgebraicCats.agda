{-# OPTIONS --without-K --safe #-}

-- Algebraic categories via homomorphisms and SubCat structures

open import Level

module AlgebraicCats (c ℓ : Level) where

open import Algebra.Bundles
open import Algebra.Module.Bundles

module _ where
  open import Function.Base using (flip)
  open import Categories.Category.Instance.Setoids using (Setoids)
  open import SubCat (Setoids c ℓ) using (_∩_; ⋂) renaming (SubCategory to ⟨_⟩)
  import Homomorphisms as H

  Magmas          = ⟨ H₂ _∙_                    ⟩ where open Magma          ; open H setoid
  Monoids         = ⟨ H₂ _∙_ ∩ H₀ ε             ⟩ where open Monoid         ; open H setoid
  Groups          = ⟨ H₂ _∙_ ∩ H₀ ε ∩ H₁ _⁻¹    ⟩ where open Group          ; open H setoid
  Lattices        = ⟨ H₂ _∨_ ∩ H₂ _∧_           ⟩ where open Lattice        ; open H setoid
  NearSemirings   = ⟨ H₂ _*_ ∩ H₂ _+_ ∩ H₀ 0#   ⟩ where open NearSemiring   ; open H setoid
  Rings           = ⟨ H₂ _*_ ∩ H₂ _+_ ∩ H₁ (-_) ⟩ where open Ring           ; open H setoid
  BooleanAlgebras = ⟨ H₂ _∨_ ∩ H₂ _∧_ ∩ H₁ ¬_   ⟩ where open BooleanAlgebra ; open H setoid

  SemiringWithoutAnnihilatingZeros = ⟨ H₂ _*_ ∩ H₂ _+_ ∩ H₀ 0# ∩ H₀ 1# ⟩
    where open SemiringWithoutAnnihilatingZero ; open H setoid

  -- Algebraic modules and variants
  private variable r ℓr s ℓs : Level

  module _ (R : Semiring r ℓr) where
    open Semiring R
    LeftSemimodules = ⟨ H₂ _+ᴹ_ ∩ H₀ 0ᴹ ∩ Hₗ _*ₗ_ ⟩
      where open LeftSemimodule {semiring = R} ; open H ≈ᴹ-setoid ; open Action Carrier
    RightSemimodules = ⟨ H₂ _+ᴹ_ ∩ H₀ 0ᴹ ∩ Hᵣ _*ᵣ_ ⟩
      where open RightSemimodule {semiring = R} ; open H ≈ᴹ-setoid ; open Action Carrier

  module _ (R : Ring r ℓr) where
    open Ring R
    LeftModules  = ⟨ H₂ _+ᴹ_ ∩ H₀ 0ᴹ ∩ Hₗ _*ₗ_ ⟩
      where open LeftModule {ring = R} ; open H ≈ᴹ-setoid ; open Action Carrier
    RightModules = ⟨ H₂ _+ᴹ_ ∩ H₀ 0ᴹ ∩ Hᵣ _*ᵣ_ ⟩
      where open RightModule {ring = R} ; open H ≈ᴹ-setoid ; open Action Carrier

  module _ (R : Semiring r ℓr) (S : Semiring s ℓs) where
    open Semiring R renaming (Carrier to setoidₗ)
    open Semiring S renaming (Carrier to setoidᵣ)
    Bisemimodules = ⟨ H₂ _+ᴹ_ ∩ H₀ 0ᴹ ∩ Hₗ _*ₗ_ ∩ Hᵣ _*ᵣ_ ⟩
      where open Bisemimodule {R-semiring = R} {S-semiring = S} ; open H ≈ᴹ-setoid
            open Action setoidₗ using (Hₗ)
            open Action setoidᵣ using (Hᵣ)

  module _ (R : Ring r ℓr) (S : Ring s ℓs) where
    open Ring R renaming (Carrier to setoidₗ)
    open Ring S renaming (Carrier to setoidᵣ)
    Bimodules = ⟨ H₂ _+ᴹ_ ∩ H₀ 0ᴹ ∩ Hₗ _*ₗ_ ∩ Hᵣ _*ᵣ_ ⟩
      where open Bimodule {R-ring = R} {S-ring = S} ; open H ≈ᴹ-setoid
            open Action setoidₗ using (Hₗ)
            open Action setoidᵣ using (Hᵣ)

  module _ (R : CommutativeSemiring r ℓr) where
    open CommutativeSemiring R
    Semimodules = ⟨ H₂ _+ᴹ_ ∩ H₀ 0ᴹ ∩ Hₗ _*ₗ_ ∩ Hᵣ _*ᵣ_ ⟩
      where open Semimodule {commutativeSemiring = R} ; open H ≈ᴹ-setoid
            open Action Carrier

  module _ (R : CommutativeRing r ℓr) where
    open CommutativeRing R
    Modules = ⟨ H₂ _+ᴹ_ ∩ H₀ 0ᴹ ∩ Hₗ _*ₗ_ ∩ Hᵣ _*ᵣ_ ⟩
      where open Module {commutativeRing = R} ; open H ≈ᴹ-setoid
            open Action Carrier

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

  Semirings = SemiringWithoutAnnihilatingZeros ⇰ Semiring.semiringWithoutAnnihilatingZero
  CommutativeSemirings = SemiringWithoutAnnihilatingZeros
                           ⇰ CommutativeSemiring.semiringWithoutAnnihilatingZero

