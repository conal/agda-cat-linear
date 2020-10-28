{-# OPTIONS --without-K --safe #-}

-- Algebraic categories via homomorphisms and SubCat structures

open import Level

module AlgebraicCats (c ℓ : Level) where

open import Algebra.Bundles
open import Algebra.Module.Bundles

open import Categories.Category.Core

private variable r ℓr s ℓs : Level

module _ where
  open import Categories.Category.Instance.Setoids using (Setoids)
  open import Category.Sub (Setoids c ℓ) as Sub using (_∩_; ⋂) -- renaming (SubCat.SubCategory to ⟨_⟩)
  open Sub.SubCat renaming (SubCategory to ⟨_⟩)
  import Category.Homomorphisms as H

  -- Temporarily comment out most categories to speed up reloading
{-
  Magmas          = ⟨ H₂ _∙_                    ⟩ where open Magma          ; open H setoid
  Monoids         = ⟨ H₂ _∙_ ∩ H₀ ε             ⟩ where open Monoid         ; open H setoid
  Groups          = ⟨ H₂ _∙_ ∩ H₀ ε ∩ H₁ _⁻¹    ⟩ where open Group          ; open H setoid
  Lattices        = ⟨ H₂ _∨_ ∩ H₂ _∧_           ⟩ where open Lattice        ; open H setoid
  NearSemirings   = ⟨ H₂ _*_ ∩ H₂ _+_ ∩ H₀ 0#   ⟩ where open NearSemiring   ; open H setoid
  Rings           = ⟨ H₂ _*_ ∩ H₂ _+_ ∩ H₁ (-_) ⟩ where open Ring           ; open H setoid
  BooleanAlgebras = ⟨ H₂ _∨_ ∩ H₂ _∧_ ∩ H₁ ¬_   ⟩ where open BooleanAlgebra ; open H setoid
 -}

  SemiringWithoutAnnihilatingZeros = ⟨ H₂ _*_ ∩ H₂ _+_ ∩ H₀ 0# ∩ H₀ 1# ⟩
    where open SemiringWithoutAnnihilatingZero ; open H setoid

  module _ (R : Semiring r ℓr) where
    open Semiring R
    LeftSemimodules = ⟨ H₂ _+ᴹ_ ∩ H₀ 0ᴹ ∩ Hₗ _*ₗ_ ⟩
      where open LeftSemimodule {semiring = R} ; open H ≈ᴹ-setoid ; open Action Carrier
{-
    RightSemimodules = ⟨ H₂ _+ᴹ_ ∩ H₀ 0ᴹ ∩ Hᵣ _*ᵣ_ ⟩
      where open RightSemimodule {semiring = R} ; open H ≈ᴹ-setoid ; open Action Carrier

  module _ (R : Ring r ℓr) where
    open Ring R
    LeftModules  = ⟨ H₂ _+ᴹ_ ∩ H₀ 0ᴹ ∩ Hₗ _*ₗ_ ⟩
      where open LeftModule  {ring = R} ; open H ≈ᴹ-setoid ; open Action Carrier
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
      where open Module {commutativeRing = R} ; open H ≈ᴹ-setoid ; open Action Carrier
-}

module _ where
  open import Category.Sub using () renaming (FullSubCategory to _⇰_)
 
{-
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
-}

  Semirings = SemiringWithoutAnnihilatingZeros ⇰ Semiring.semiringWithoutAnnihilatingZero
  CommutativeSemirings = SemiringWithoutAnnihilatingZeros
                           ⇰ CommutativeSemiring.semiringWithoutAnnihilatingZero


-------------------------------------------------------------------------------
-- | Cartesian categories. Start with a few, and then generalize.
-------------------------------------------------------------------------------

module _ (R : Semiring r ℓr) where
  open Semiring R using (Carrier)
  -- open import Function using (const)
  open import Data.Unit.Polymorphic
  open import Data.Product using (_,_)
  open import Relation.Binary.Bundles using (Setoid)
  import Algebra.Module.Construct.Zero as Z
  import Algebra.Module.Construct.DirectProduct    as P

  open import Categories.Category.Cartesian
  open import Categories.Category.Monoidal.Instance.Setoids
  open import Categories.Category.Instance.Setoids using (Setoids)

  open import Category.Sub (Setoids c ℓ) using (_∩_; ⋂)
  open import Cartesian.Sub (Setoids-CartesianCategory c ℓ) as Sub hiding (_∩_)
  open Sub.SubCart using (SubCartesian)
  import Category.Homomorphisms as H
  open import Misc
  
  setoid = LeftSemimodule.≈ᴹ-setoid {semiring = R}
  lsm = LeftSemimodules R

  open import Relation.Binary.PropositionalEquality using (_≡_)
  LeftSemimodule-CartOps : Ops setoid
  LeftSemimodule-CartOps = record 
    { ⊤ᴵ = Z.leftSemimodule
    ; ⊤≡ = refl
    ; _×ᴵ_ = P.leftSemimodule
    ; ×≡ = refl
    } where open _≡_

  LeftSemimodules-Cartesian : Cartesian lsm
  LeftSemimodules-Cartesian = SubCartesian {ops = LeftSemimodule-CartOps} record
    { subCat = subCat
    ; R! = (λ _ _ → tt) , tt , (λ _ _ → tt)
    ; Rπ₁ = λ {a₁ a₂} → let open Setoid (≈ᴹ-setoid a₁) in
                          (λ _ _ → refl) , refl , (λ _ _ → refl)
    ; Rπ₂ = λ {a₁ a₂} → let open Setoid (≈ᴹ-setoid a₂) in
                          (λ _ _ → refl) , refl , (λ _ _ → refl)
    ; R⟨_,_⟩ = λ (_+₁_ , 0₁ , _*₁_) (_+₂_ , 0₂ , _*₂_) →
                 (λ x y → x +₁ y , x +₂ y) , (0₁ , 0₂) , (λ s x → s *₁ x , s *₂ x)
    } where
        open LeftSemimodule {semiring = R} ; open H ≈ᴹ-setoid ; open Action Carrier
        subCat = H₂ _+ᴹ_ ∩ H₀ 0ᴹ ∩ Hₗ _*ₗ_

  -- LeftSemimodule-CocartOps : Ops setoid
  -- LeftSemimodule-CocartOps = record
  --   { ⊤ᴵ = {!!}
  --   ; ⊤≡ = {!!}
  --   ; _×ᴵ_ = {!!}
  --   ; ×≡ = {!!}
  --   }
        
  -- TODO: eliminate the redundant SubCat construction and associated imports.
  -- Return to the style of Old.Algebraic2
