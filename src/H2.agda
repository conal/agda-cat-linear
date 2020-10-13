-- Experiments in homomorphism construction

open import Level

module H2 (o ℓ : Level) where

-- open import Data.Product
open import Algebra using (Op₁; Op₂)

open import Function.Equality using (Π; _⟨$⟩_; _⟶_)
open import Relation.Binary
open import Function.Bundles
open import Relation.Binary.Reasoning.MultiSetoid

open import Categories.Category.Instance.Setoids

open Setoid using (Carrier; refl)

module _ where

  open import Categories.Category.SubCategory (Setoids o ℓ)

  H₀ : {q : Level} {Q : Set q} → (setoid : Q → Setoid o ℓ)
     → ((A : Q) → Carrier (setoid A)) → SubCat Q
  H₀ {Q = Q} setoid op = record
    { U = setoid
    ; R = λ {a b} f′ →
            let ∙ = op a ; ∘ = op b
                _≈_ = Setoid._≈_ (setoid b) ; infix 4 _≈_
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

  H₁ : {q : Level} {Q : Set q} → (setoid : Q → Setoid o ℓ)
     → ((A : Q) → Op₁ (Carrier (setoid A))) → SubCat Q
  H₁ {Q = Q} setoid op = record
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

  H₂ : {q : Level} {Q : Set q} → (setoid : Q → Setoid o ℓ)
     → ((A : Q) → Op₂ (Carrier (setoid A))) → SubCat Q
  H₂ {Q = Q} setoid op = record
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

-- Subcategories of Setoids

module _ where

  open import Categories.Category.SubCategory (Setoids o ℓ)
  open import Relation.Binary.PropositionalEquality as ≡
    using (_≡_) renaming (refl to refl≡)

  MagmaSub : SubCat (Magma o ℓ)
  MagmaSub = H₂ setoid _∙_ where open Magma

  Magmas = SubCategory MagmaSub

  MonoidSub : SubCat (Monoid o ℓ)
  MonoidSub = merge (map magma MagmaSub) (H₀ setoid ε) refl≡ where open Monoid

  Monoids = SubCategory MonoidSub

  GroupSub : SubCat (Group o ℓ)
  GroupSub = merge (map monoid MonoidSub) (H₁ setoid _⁻¹) refl≡ where open Group

  Groups = SubCategory GroupSub

  LatticeSub : SubCat (Lattice o ℓ)
  LatticeSub = merge (H₂ setoid _∨_) (H₂ setoid _∧_) refl≡ where open Lattice

  Lattices = SubCategory LatticeSub

  NearSemiringSub : SubCat (NearSemiring o ℓ)
  NearSemiringSub = merge (H₂ setoid _*_) (H₂ setoid _+_) refl≡ where open NearSemiring

  NearSemirings = SubCategory NearSemiringSub

  SemiringWithoutAnnihilatingZeroSub : SubCat (SemiringWithoutAnnihilatingZero o ℓ)
  SemiringWithoutAnnihilatingZeroSub =
    merge
      (merge (H₂ setoid _+_) (H₂ setoid _*_) refl≡)
      (merge (H₀ setoid  0#) (H₀ setoid  1#) refl≡)
      refl≡
   where open SemiringWithoutAnnihilatingZero

  SemiringSub =
    map semiringWithoutAnnihilatingZero SemiringWithoutAnnihilatingZeroSub
   where open Semiring

  SemiringWithoutAnnihilatingZeros = SubCategory SemiringWithoutAnnihilatingZeroSub

  RingSub : SubCat (Ring o ℓ)
  RingSub = merge (map semiring SemiringSub) (H₁ setoid (-_)) refl≡ where open Ring

module _ where

  open import Categories.Category.SubCategory

  Semigroups            = FullSubCategory Magmas Semigroup.magma
  Bands                 = FullSubCategory Magmas Band.magma
  CommutativeSemigroups = FullSubCategory Magmas CommutativeSemigroup.magma
  Semilattices          = FullSubCategory Magmas Semilattice.magma
  SelectiveMagmas       = FullSubCategory Magmas SelectiveMagma.magma

  CommutativeMonoids = FullSubCategory Monoids CommutativeMonoid.monoid
  BoundedLattices    = FullSubCategory Monoids BoundedLattice.monoid
  IdempotentCommutativeMonoids =
    FullSubCategory Monoids IdempotentCommutativeMonoid.monoid

  AbelianGroups = FullSubCategory Groups AbelianGroup.group

  DistributiveLattices = FullSubCategory Lattices DistributiveLattice.lattice

  SemiringWithoutOnes =
    FullSubCategory NearSemirings SemiringWithoutOne.nearSemiring
  CommutativeSemiringWithoutOnes =
    FullSubCategory NearSemirings CommutativeSemiringWithoutOne.nearSemiring

  Semirings = FullSubCategory SemiringWithoutAnnihilatingZeros
                Semiring.semiringWithoutAnnihilatingZero
  CommutativeSemirings = FullSubCategory SemiringWithoutAnnihilatingZeros
                           CommutativeSemiring.semiringWithoutAnnihilatingZero