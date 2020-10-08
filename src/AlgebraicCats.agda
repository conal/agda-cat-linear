{-# OPTIONS --without-K --safe #-}

-- Some algebraic categories via SubCategory

open import Level

module AlgebraicCats (o ℓ : Level) where

open import Data.Product using (_×_ ; _,_)
open import Algebra.Bundles
open import Function.Equality using (Π)
open import Relation.Binary.Reasoning.MultiSetoid

open import Categories.Category using (Category)
open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Category.SubCategory using (SubCategory; FullSubCategory)

------------------------------------------------------------------------
-- Magma-like structures
------------------------------------------------------------------------

Magmas : Category _ _ _
Magmas = SubCategory (Setoids o ℓ) record
  { U = setoid
  ; R = λ {a} {b} f′ →
          let open Magma a renaming (_∙_ to _∙₁_)
              open Magma b renaming (_∙_ to _∙₂_; _≈_ to _≈₂_)
              open Π f′ renaming (_⟨$⟩_ to f)
          in
            ∀ x y → f (x ∙₁ y) ≈₂ f x ∙₂ f y
  ; Rid  = λ {a} → λ _ _ → refl a
  ; _∘R_ = λ {a b c} {g′} {f′} homo-g homo-f →
             let open Magma a using () renaming (_∙_ to _∙₁_)
                 open Magma b using () renaming (_∙_ to _∙₂_)
                 open Magma c using () renaming (_∙_ to _∙₃_)
                 open Π g′ renaming (_⟨$⟩_ to g; cong to cong-g)
                 open Π f′ renaming (_⟨$⟩_ to f)
             in λ x y → begin⟨ setoid c ⟩
                          g (f (x ∙₁ y))     ≈⟨ cong-g (homo-f x y) ⟩
                          g (f x ∙₂ f y)     ≈⟨ homo-g (f x) (f y) ⟩
                          g (f x) ∙₃ g (f y) ∎
  } where open Magma

Semigroups            = FullSubCategory Magmas Semigroup.magma
Bands                 = FullSubCategory Magmas Band.magma
CommutativeSemigroups = FullSubCategory Magmas CommutativeSemigroup.magma
Semilattices          = FullSubCategory Magmas Semilattice.magma
SelectiveMagmas       = FullSubCategory Magmas SelectiveMagma.magma

------------------------------------------------------------------------
-- Monoid-like structures
------------------------------------------------------------------------

Monoids : Category _ _ _
Monoids = SubCategory Semigroups record
  { U = semigroup
  ; R = λ {a b : Monoid o ℓ} (f′ , _) →
          let open Monoid a using () renaming (ε to ε₁)
              open Monoid b using () renaming (ε to ε₂; _≈_ to _≈₂_)
              open Π f′ renaming (_⟨$⟩_ to f)
          in
            f ε₁ ≈₂ ε₂
  ; Rid  = λ {a} → refl a
  ; _∘R_ = λ {a b c} {(g′ , _)} {(f′ , _)} homo-g homo-f
             → let open Monoid a using () renaming (ε to ε₁)
                   open Monoid b using () renaming (ε to ε₂)
                   open Monoid c using () renaming (ε to ε₃)
                   open Π g′ renaming (_⟨$⟩_ to g; cong to cong-g)
                   open Π f′ renaming (_⟨$⟩_ to f)
               in 
                 begin⟨ setoid c ⟩
                   g (f ε₁)  ≈⟨ cong-g homo-f ⟩
                   g ε₂      ≈⟨ homo-g ⟩
                   ε₃        ∎
  } where open Monoid

CommutativeMonoids = FullSubCategory Monoids CommutativeMonoid.monoid
BoundedLattices    = FullSubCategory Monoids BoundedLattice.monoid
IdempotentCommutativeMonoids =
  FullSubCategory Monoids IdempotentCommutativeMonoid.monoid


------------------------------------------------------------------------
-- Group-like structures
------------------------------------------------------------------------

Groups : Category _ _ _
Groups = SubCategory Monoids record
  { U = monoid
  ; R = λ {a b : Group o ℓ} ((f′ , _) , _) →
          let open Group a renaming (_⁻¹ to _⁻¹₁)
              open Group b renaming (_⁻¹ to _⁻¹₂; _≈_ to _≈₂_)
              open Π f′ renaming (_⟨$⟩_ to f)
          in
            ∀ a → f (a ⁻¹₁) ≈₂ f a ⁻¹₂
  ; Rid  = λ {a} _ → refl a
  ; _∘R_ = λ {a b c} {((g′ , _) , _)} {((f′ , _) , _)} homo-g homo-f
             → let open Group a using () renaming (_⁻¹ to _⁻¹₁)
                   open Group b using () renaming (_⁻¹ to _⁻¹₂)
                   open Group c using () renaming (_⁻¹ to _⁻¹₃)
                   open Π g′ renaming (_⟨$⟩_ to g; cong to cong-g)
                   open Π f′ renaming (_⟨$⟩_ to f)
               in 
                 λ x → begin⟨ setoid c ⟩
                         g (f (x ⁻¹₁)) ≈⟨ cong-g (homo-f x) ⟩
                         g (f x ⁻¹₂)   ≈⟨ homo-g (f x) ⟩
                         g (f x) ⁻¹₃   ∎
  } where
      open Group

AbelianGroups = FullSubCategory Groups AbelianGroup.group

-------------------------------------------------------------------------------
-- | Lattice-like structures
-------------------------------------------------------------------------------

Lattices : Category _ _ _
Lattices = SubCategory (Setoids o ℓ) record
  { U = setoid
  ; R = λ {a} {b} f′ →
          let open Lattice a renaming (_∧_ to _∧₁_; _∨_ to _∨₁_)
              open Lattice b renaming (_∧_ to _∧₂_; _∨_ to _∨₂_; _≈_ to _≈₂_)
              open Π f′ renaming (_⟨$⟩_ to f)
          in
            -- Pair of relations. Also try as λ x y → f (x ∧₁ y) , f (x ∨₁ y).
            (∀ x y → f (x ∧₁ y) ≈₂ f x ∧₂ f y) ×
            (∀ x y → f (x ∨₁ y) ≈₂ f x ∨₂ f y)
  ; Rid  = λ {a} → (λ _ _ → refl a) , (λ _ _ → refl a)
  ; _∘R_ = λ {a b c} {g′} {f′} (homo-∧-g , homo-∨-g) (homo-∧-f , homo-∨-f) →
             let open Lattice a using () renaming (_∧_ to _∧₁_; _∨_ to _∨₁_)
                 open Lattice b using () renaming (_∧_ to _∧₂_; _∨_ to _∨₂_)
                 open Lattice c using () renaming (_∧_ to _∧₃_; _∨_ to _∨₃_)
                 open Π g′ renaming (_⟨$⟩_ to g; cong to cong-g)
                 open Π f′ renaming (_⟨$⟩_ to f)
             in (λ x y → begin⟨ setoid c ⟩
                           g (f (x ∧₁ y))     ≈⟨ cong-g (homo-∧-f x y) ⟩
                           g (f x ∧₂ f y)     ≈⟨ homo-∧-g (f x) (f y) ⟩
                           g (f x) ∧₃ g (f y) ∎) ,
                (λ x y → begin⟨ setoid c ⟩
                           g (f (x ∨₁ y))     ≈⟨ cong-g (homo-∨-f x y) ⟩
                           g (f x ∨₂ f y)     ≈⟨ homo-∨-g (f x) (f y) ⟩
                           g (f x) ∨₃ g (f y) ∎)

  } where open Lattice

DistributiveLattices = FullSubCategory Lattices DistributiveLattice.lattice


-- To come: like near semirings, semirings, rings, boolean algebra. Then flavors of (semi)modules.
