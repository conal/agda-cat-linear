{-# OPTIONS --without-K --safe #-}

-- Some algebraic categories via SubCategory

open import Level

module AlgebraicCats (o ℓ : Level) where

open import Algebra.Structures
open import Algebra.Bundles
open import Function using () renaming (id to id→; _∘_ to _∘→_)
open import Function.Equality renaming (id to id⟶; _∘_ to _∘⟶_)
open import Relation.Binary.Reasoning.MultiSetoid

open import Categories.Category
open import Categories.Category.Instance.Setoids
open import Categories.Category.SubCategory
open import Categories.Category.Instance.Setoids

------------------------------------------------------------------------
-- SubCat structures for magma-like structures
------------------------------------------------------------------------

Magmas : Category _ _ _
Magmas = SubCategory (Setoids o ℓ) record
  { U    = Magma.setoid
  ; R    = λ {a} {b} f′ →
             let open Magma a renaming (_∙_ to _∙₁_)
                 open Magma b renaming (_∙_ to _∙₂_; _≈_ to _≈₂_)
                 f = f′ ⟨$⟩_
             in
               ∀ x y → f (x ∙₁ y) ≈₂ f x ∙₂ f y
  ; Rid  = λ {a} → λ _ _ → Magma.refl a
  ; _∘R_ = λ {a b c} {g′} {f′} homo-g homo-f →
             let open Magma a renaming (_∙_ to _∙₁_)
                 open Magma b renaming (_∙_ to _∙₂_)
                 open Magma c renaming (_∙_ to _∙₃_)
             in λ (x y : Magma.Carrier a) →
                    let g = g′ ⟨$⟩_ ; f = f′ ⟨$⟩_ in
                    begin⟨ Magma.setoid c ⟩
                      g (f (x ∙₁ y))     ≈⟨ Π.cong g′ (homo-f x y) ⟩
                      g (f x ∙₂ f y)     ≈⟨ homo-g (f x) (f y) ⟩
                      g (f x) ∙₃ g (f y) ∎
  }

Semigroups            = FullSubCategory Magmas Semigroup.magma
Bands                 = FullSubCategory Magmas Band.magma
CommutativeSemigroups = FullSubCategory Magmas CommutativeSemigroup.magma
Semilattices          = FullSubCategory Magmas Semilattice.magma
SelectiveMagmas       = FullSubCategory Magmas SelectiveMagma.magma

-- TODO: try redefining the `Setoids` category via `SubCategory Sets`.

open import Data.Product

Monoids : Category _ _ _
Monoids = SubCategory Semigroups record
  { U = Monoid.semigroup
  ; R = λ {a b : Monoid o ℓ} ((f , _) : semigroup a ⇒ semigroup b) →
          let open Monoid a renaming (_≈_ to _≈₁_; ε to ε₁)
              open Monoid b renaming (_≈_ to _≈₂_; ε to ε₂)
          in
            f ⟨$⟩ ε₁ ≈₂ ε₂
  ; Rid = λ {a} → Monoid.refl a
  ; _∘R_ = λ {a b c : Monoid o ℓ}
             {(g′ , _) : semigroup b ⇒ semigroup c}
             {(f′ , _) : semigroup a ⇒ semigroup b}
             gε≈ε fε≈ε
             → let open Monoid a renaming (ε to ε₁)
                   open Monoid b renaming (ε to ε₂)
                   open Monoid c renaming (ε to ε₃)
                   g = g′ ⟨$⟩_ ; f = f′ ⟨$⟩_
               in
               begin⟨ Monoid.setoid c ⟩
                 g (f ε₁)  ≈⟨ Π.cong g′ fε≈ε ⟩
                 g ε₂      ≈⟨ gε≈ε ⟩
                 ε₃        ∎
  } where
      open Monoid
      open Category Semigroups

CommutativeMonoids           = FullSubCategory Monoids CommutativeMonoid.monoid
IdempotentCommutativeMonoids = FullSubCategory Monoids IdempotentCommutativeMonoid.monoid
BoundedLattices              = FullSubCategory Monoids BoundedLattice.monoid
