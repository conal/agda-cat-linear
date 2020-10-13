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
open import Categories.Category.SubCategory

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
  ; _∘R_ = λ {a b c} {g′} {f′} g∙ f∙ →
             let open Magma a using () renaming (_∙_ to _∙₁_)
                 open Magma b using () renaming (_∙_ to _∙₂_)
                 open Magma c using () renaming (_∙_ to _∙₃_)
                 open Π g′ renaming (_⟨$⟩_ to g; cong to cong-g)
                 open Π f′ renaming (_⟨$⟩_ to f)
             in λ x y → begin⟨ setoid c ⟩
                          g (f (x ∙₁ y))     ≈⟨ cong-g (f∙ x y) ⟩
                          g (f x ∙₂ f y)     ≈⟨ g∙ (f x) (f y) ⟩
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
  ; _∘R_ = λ {a b c} {(g′ , _)} {(f′ , _)} gε fε →
             let open Monoid a using () renaming (ε to ε₁)
                 open Monoid b using () renaming (ε to ε₂)
                 open Monoid c using () renaming (ε to ε₃)
                 open Π g′ renaming (_⟨$⟩_ to g; cong to cong-g)
                 open Π f′ renaming (_⟨$⟩_ to f)
             in 
               begin⟨ setoid c ⟩
                 g (f ε₁) ≈⟨ cong-g fε ⟩
                 g ε₂     ≈⟨ gε ⟩
                 ε₃       ∎
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
            ∀ x → f (x ⁻¹₁) ≈₂ f x ⁻¹₂
  ; Rid  = λ {a} _ → refl a
  ; _∘R_ = λ {a b c} {((g′ , _) , _)} {((f′ , _) , _)} g⁻¹ f⁻¹
             → let open Group a using () renaming (_⁻¹ to _⁻¹₁)
                   open Group b using () renaming (_⁻¹ to _⁻¹₂)
                   open Group c using () renaming (_⁻¹ to _⁻¹₃)
                   open Π g′ renaming (_⟨$⟩_ to g; cong to cong-g)
                   open Π f′ renaming (_⟨$⟩_ to f)
               in 
                 λ x → begin⟨ setoid c ⟩
                         g (f (x ⁻¹₁)) ≈⟨ cong-g (f⁻¹ x) ⟩
                         g (f x ⁻¹₂)   ≈⟨ g⁻¹ (f x) ⟩
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
            (∀ x y → f (x ∧₁ y) ≈₂ f x ∧₂ f y) ×
            (∀ x y → f (x ∨₁ y) ≈₂ f x ∨₂ f y)
  ; Rid  = λ {a} → (λ _ _ → refl a) , (λ _ _ → refl a)
  ; _∘R_ = λ {a b c} {g′} {f′} (g∧ , g∨) (f∧ , f∨) →
             let open Lattice a using () renaming (_∧_ to _∧₁_; _∨_ to _∨₁_)
                 open Lattice b using () renaming (_∧_ to _∧₂_; _∨_ to _∨₂_)
                 open Lattice c using () renaming (_∧_ to _∧₃_; _∨_ to _∨₃_)
                 open Π g′ renaming (_⟨$⟩_ to g; cong to cong-g)
                 open Π f′ renaming (_⟨$⟩_ to f)
             in (λ x y → begin⟨ setoid c ⟩
                           g (f (x ∧₁ y))     ≈⟨ cong-g (f∧ x y) ⟩
                           g (f x ∧₂ f y)     ≈⟨ g∧ (f x) (f y) ⟩
                           g (f x) ∧₃ g (f y) ∎) ,
                (λ x y → begin⟨ setoid c ⟩
                           g (f (x ∨₁ y))     ≈⟨ cong-g (f∨ x y) ⟩
                           g (f x ∨₂ f y)     ≈⟨ g∨ (f x) (f y) ⟩
                           g (f x) ∨₃ g (f y) ∎)
  } where open Lattice

DistributiveLattices = FullSubCategory Lattices DistributiveLattice.lattice

-------------------------------------------------------------------------------
-- | NearSemiring-like structures
-------------------------------------------------------------------------------

NearSemirings : Category _ _ _
NearSemirings = SubCategory (Setoids o ℓ) record
  { U = setoid
  ; R = λ {a} {b} f′ →
          let open NearSemiring a renaming
                 (_+_ to _+₁_; _*_ to _*₁_; 0# to 0₁)
              open NearSemiring b renaming
                 (_+_ to _+₂_; _*_ to _*₂_; 0# to 0₂; _≈_ to _≈₂_)
              open Π f′ renaming (_⟨$⟩_ to f)
          in
            (∀ x y → f (x +₁ y) ≈₂ f x +₂ f y) ×
            (∀ x y → f (x *₁ y) ≈₂ f x *₂ f y) ×
            f 0₁ ≈₂ 0₂
  ; Rid  = λ {a} → (λ _ _ → refl a) , (λ _ _ → refl a) , refl a
  ; _∘R_ = λ {a b c} {g′} {f′} (g+ , g* , g0) (f+ , f* , f0) →
             let open NearSemiring a using () renaming
                   (_+_ to _+₁_; _*_ to _*₁_; 0# to 0₁)
                 open NearSemiring b using () renaming
                   (_+_ to _+₂_; _*_ to _*₂_; 0# to 0₂)
                 open NearSemiring c using () renaming
                   (_+_ to _+₃_; _*_ to _*₃_; 0# to 0₃)
                 open Π g′ renaming (_⟨$⟩_ to g; cong to cong-g)
                 open Π f′ renaming (_⟨$⟩_ to f)
             in (λ x y → begin⟨ setoid c ⟩
                           g (f (x +₁ y))     ≈⟨ cong-g (f+ x y) ⟩
                           g (f x +₂ f y)     ≈⟨ g+ (f x) (f y) ⟩
                           g (f x) +₃ g (f y) ∎) ,
                (λ x y → begin⟨ setoid c ⟩
                           g (f (x *₁ y))     ≈⟨ cong-g (f* x y) ⟩
                           g (f x *₂ f y)     ≈⟨ g* (f x) (f y) ⟩
                           g (f x) *₃ g (f y) ∎) ,
                (begin⟨ setoid c ⟩
                   g (f 0₁) ≈⟨ cong-g f0 ⟩
                   g 0₂     ≈⟨ g0 ⟩
                   0₃       ∎)
  } where open NearSemiring

SemiringWithoutOnes =
  FullSubCategory NearSemirings SemiringWithoutOne.nearSemiring
CommutativeSemiringWithoutOnes =
  FullSubCategory NearSemirings CommutativeSemiringWithoutOne.nearSemiring

-------------------------------------------------------------------------------
-- | Semiring-like structures
-------------------------------------------------------------------------------

SemiringWithoutAnnihilatingZeros : Category _ _ _
SemiringWithoutAnnihilatingZeros = SubCategory (Setoids o ℓ) record
  { U = setoid
  ; R = λ {a} {b} f′ →
          let open SemiringWithoutAnnihilatingZero a renaming
                 (_+_ to _+₁_; _*_ to _*₁_; 0# to 0₁; 1# to 1₁)
              open SemiringWithoutAnnihilatingZero b renaming
                 (_+_ to _+₂_; _*_ to _*₂_; 0# to 0₂; 1# to 1₂; _≈_ to _≈₂_)
              open Π f′ renaming (_⟨$⟩_ to f)
          in
            (∀ x y → f (x +₁ y) ≈₂ f x +₂ f y) ×
            (∀ x y → f (x *₁ y) ≈₂ f x *₂ f y) ×
            f 0₁ ≈₂ 0₂ × f 1₁ ≈₂ 1₂
  ; Rid  = λ {a} → (λ _ _ → refl a) , (λ _ _ → refl a) , refl a , refl a
  ; _∘R_ = λ {a b c} {g′} {f′} (g+ , g* , g0 , g1) (f+ , f* , f0 , f1) →
             let open SemiringWithoutAnnihilatingZero a using () renaming
                   (_+_ to _+₁_; _*_ to _*₁_; 0# to 0₁; 1# to 1₁)
                 open SemiringWithoutAnnihilatingZero b using () renaming
                   (_+_ to _+₂_; _*_ to _*₂_; 0# to 0₂; 1# to 1₂)
                 open SemiringWithoutAnnihilatingZero c using () renaming
                   (_+_ to _+₃_; _*_ to _*₃_; 0# to 0₃; 1# to 1₃)
                 open Π g′ renaming (_⟨$⟩_ to g; cong to cong-g)
                 open Π f′ renaming (_⟨$⟩_ to f)
             in (λ x y → begin⟨ setoid c ⟩
                           g (f (x +₁ y))     ≈⟨ cong-g (f+ x y) ⟩
                           g (f x +₂ f y)     ≈⟨ g+ (f x) (f y) ⟩
                           g (f x) +₃ g (f y) ∎) ,
                (λ x y → begin⟨ setoid c ⟩
                           g (f (x *₁ y))     ≈⟨ cong-g (f* x y) ⟩
                           g (f x *₂ f y)     ≈⟨ g* (f x) (f y) ⟩
                           g (f x) *₃ g (f y) ∎) ,
                (begin⟨ setoid c ⟩
                   g (f 0₁) ≈⟨ cong-g f0 ⟩
                   g 0₂     ≈⟨ g0 ⟩
                   0₃       ∎) ,
                (begin⟨ setoid c ⟩
                   g (f 1₁) ≈⟨ cong-g f1 ⟩
                   g 1₂     ≈⟨ g1 ⟩
                   1₃       ∎)
  } where open SemiringWithoutAnnihilatingZero

Semirings = FullSubCategory SemiringWithoutAnnihilatingZeros
              Semiring.semiringWithoutAnnihilatingZero
CommutativeSemirings = FullSubCategory SemiringWithoutAnnihilatingZeros
                         CommutativeSemiring.semiringWithoutAnnihilatingZero

-------------------------------------------------------------------------------
-- | Ring-like structures
-------------------------------------------------------------------------------

Rings : Category _ _ _
Rings = SubCategory Semirings record
  { U = semiring
  ; R = λ {a b : Ring o ℓ} (f′ , _) →
          let open Ring a renaming (-_ to -₁_)
              open Ring b renaming (-_ to -₂_; _≈_ to _≈₂_)
              open Π f′ renaming (_⟨$⟩_ to f)
          in
            ∀ x → f (-₁ x) ≈₂ -₂ f x
  ; Rid  = λ {a} _ → refl a
  ; _∘R_ = λ {a b c} {(g′ , _)} {(f′ , _)} -g -f
             → let open Ring a using () renaming (-_ to -₁_)
                   open Ring b using () renaming (-_ to -₂_)
                   open Ring c using () renaming (-_ to -₃_)
                   open Π g′ renaming (_⟨$⟩_ to g; cong to cong-g)
                   open Π f′ renaming (_⟨$⟩_ to f)
               in 
                 λ x → begin⟨ setoid c ⟩
                         g (f (-₁ x)) ≈⟨ cong-g (-f x) ⟩
                         g (-₂ f x)   ≈⟨ -g (f x) ⟩
                         -₃ g (f x)   ∎
  } where
      open Ring

CommutativeRings = FullSubCategory Rings CommutativeRing.ring

BooleanAlgebras : Category _ _ _
BooleanAlgebras = SubCategory DistributiveLattices record
  { U = distributiveLattice
  ; R = λ {a b : BooleanAlgebra o ℓ} (f′ , _) →
          let open BooleanAlgebra a using () renaming
                (⊤ to ⊤₁; ⊥ to ⊥₁; ¬_ to ¬₁_)
              open BooleanAlgebra b using () renaming
                (⊤ to ⊤₂; ⊥ to ⊥₂; ¬_ to ¬₂_; _≈_ to _≈₂_)
              open Π f′ renaming (_⟨$⟩_ to f)
          in
            f ⊤₁ ≈₂ ⊤₂ × f ⊥₁ ≈₂ ⊥₂ × (∀ x → f (¬₁ x) ≈₂ ¬₂ (f x))
  ; Rid  = λ {a} → refl a , refl a , (λ _ → refl a)
  ; _∘R_ = λ {a b c} {(g′ , _)} {(f′ , _)} (g⊤ , g⊥ , ¬g) (f⊤ , f⊥ , ¬f) →
             let open BooleanAlgebra a using () renaming
                   (⊤ to ⊤₁; ⊥ to ⊥₁; ¬_ to ¬₁_)
                 open BooleanAlgebra b using () renaming
                   (⊤ to ⊤₂; ⊥ to ⊥₂; ¬_ to ¬₂_)
                 open BooleanAlgebra c using () renaming
                   (⊤ to ⊤₃; ⊥ to ⊥₃; ¬_ to ¬₃_)
                 open Π g′ renaming (_⟨$⟩_ to g; cong to cong-g)
                 open Π f′ renaming (_⟨$⟩_ to f)
             in 
               (begin⟨ setoid c ⟩
                  g (f ⊤₁) ≈⟨ cong-g f⊤ ⟩
                  g ⊤₂     ≈⟨ g⊤ ⟩
                  ⊤₃       ∎) ,
               (begin⟨ setoid c ⟩
                  g (f ⊥₁) ≈⟨ cong-g f⊥ ⟩
                  g ⊥₂     ≈⟨ g⊥ ⟩
                  ⊥₃       ∎) ,
               (λ x → begin⟨ setoid c ⟩
                        g (f (¬₁ x)) ≈⟨ cong-g (¬f x) ⟩
                        g (¬₂ f x)   ≈⟨ ¬g (f x) ⟩
                        ¬₃ g (f x)   ∎)
  } where open BooleanAlgebra

