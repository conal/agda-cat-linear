-- Experiments in homomorphism construction

open import Level

module Homomorphisms (o ℓ : Level) where

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

module H {q : Level} {Q : Set q} (setoid : Q → Setoid o ℓ) where

  -- Nullary homomorphism, given a nullary operation on its carrier.
  H₀ : ((A : Q) → Carrier (setoid A)) → SubCat setoid
  H₀ op = record
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

  -- Unary homomorphism, given a unary operation on its carrier.
  H₁ : ((A : Q) → Op₁ (Carrier (setoid A))) → SubCat setoid
  H₁ op = record
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

  -- Binary homomorphism, given a binary operation on its carrier.
  H₂ : ((A : Q) → Op₂ (Carrier (setoid A))) → SubCat setoid
  H₂ op = record
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

