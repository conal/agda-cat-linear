-- Experiments in homomorphism construction

open import Level

module H2 (o ℓ : Level) where

open import Algebra using (Op₁; Op₂)

open import Function.Equality using (Π; _⟨$⟩_; _⟶_)
open import Relation.Binary
open import Relation.Binary.Reasoning.MultiSetoid

open import Categories.Category.Instance.Setoids

open Setoid using (Carrier; refl)

open import Categories.Category.SubCategory (Setoids o ℓ)

-------------------------------------------------------------------------------
-- | Per-operation homomorphisms in nullary, unary, and binary flavors
-------------------------------------------------------------------------------

private
  variable
    q : Level
    Q : Set q

H₀ : (setoid : Q → Setoid o ℓ) → ((A : Q) → Carrier (setoid A)) → SubCat Q
H₀ setoid op = record
  { U = setoid
  ; R = λ {a b} f′ →
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

H₁ : (setoid : Q → Setoid o ℓ) → ((A : Q) → Op₁ (Carrier (setoid A))) → SubCat Q
H₁ setoid op = record
  { U = setoid
  ; R = λ {a b} f′ →
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

H₂ : (setoid : Q → Setoid o ℓ) → ((A : Q) → Op₂ (Carrier (setoid A))) → SubCat Q
H₂ setoid op = record
  { U = setoid
  ; R = λ {a b} f′ →
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
-- | Homomorphisms on algebraic structures
-------------------------------------------------------------------------------

open import Algebra.Bundles
open import Relation.Binary.PropositionalEquality as ≡
  using (_≡_) renaming (refl to refl≡)

MagmaS : SubCat (Magma o ℓ)
MagmaS = H₂ setoid _∙_ where open Magma

SemigroupS            = map            Semigroup.magma MagmaS
BandS                 = map                 Band.magma MagmaS
CommutativeSemigroupS = map CommutativeSemigroup.magma MagmaS
SemilatticeS          = map          Semilattice.magma MagmaS
SelectiveMagmaS       = map       SelectiveMagma.magma MagmaS

MonoidS : SubCat (Monoid o ℓ)
MonoidS = merge (map magma MagmaS) (H₀ setoid ε) refl≡ where open Monoid

CommutativeMonoidS = map CommutativeMonoid.monoid MonoidS
BoundedLatticeS    = map    BoundedLattice.monoid MonoidS
IdempotentCommutativeMonoidS =
  map IdempotentCommutativeMonoid.monoid MonoidS

GroupS : SubCat (Group o ℓ)
GroupS = merge (map monoid MonoidS) (H₁ setoid _⁻¹) refl≡ where open Group

AbelianGroupS = map AbelianGroup.group GroupS

LatticeS : SubCat (Lattice o ℓ)
LatticeS = merge (H₂ setoid _∨_) (H₂ setoid _∧_) refl≡ where open Lattice

DistributiveLatticeS = map DistributiveLattice.lattice LatticeS

NearSemiringS : SubCat (NearSemiring o ℓ)
NearSemiringS = merge (H₂ setoid _*_) (H₂ setoid _+_) refl≡
  where open NearSemiring

SemiringWithoutOneS =
   map           SemiringWithoutOne.nearSemiring NearSemiringS
CommutativeSemiringWithoutOneS =
  map CommutativeSemiringWithoutOne.nearSemiring NearSemiringS

SemiringWithoutAnnihilatingZeroS
 : SubCat (SemiringWithoutAnnihilatingZero o ℓ)
SemiringWithoutAnnihilatingZeroS =
  merge
    (merge (H₂ setoid _+_) (H₂ setoid _*_) refl≡)
    (merge (H₀ setoid  0#) (H₀ setoid  1#) refl≡)
    refl≡
 where open SemiringWithoutAnnihilatingZero

SemiringS = map Semiring.semiringWithoutAnnihilatingZero
               SemiringWithoutAnnihilatingZeroS

CommutativeSemiringS = map CommutativeSemiring.semiring SemiringS

RingS : SubCat (Ring o ℓ)
RingS = merge (map semiring SemiringS) (H₁ setoid (-_)) refl≡
  where open Ring

CommutativeRingS = map CommutativeRing.ring RingS

BooleanAlgebraS : SubCat (BooleanAlgebra o ℓ)
BooleanAlgebraS = merge (merge (H₂ setoid _∨_) (H₂ setoid _∧_) refl≡)
                          (H₁ setoid ¬_)
                          refl≡
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
