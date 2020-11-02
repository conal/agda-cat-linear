{-# OPTIONS --without-K --safe #-}

-- Algebraic categories via homomorphisms and SubCat structures

open import Level

open import Algebra.Bundles using (Semiring)

module InductiveMatrices {r ℓr : Level} (semiring : Semiring r ℓr) where

open import Data.Product using (_,_)

open import Algebra.Module.Bundles using (LeftSemimodule)

open Semiring semiring hiding (_+_) renaming (Carrier to R; setoid to R-setoid)

open import Categories.Category.Core

open import AlgebraicCats r ℓr hiding (setoid)

LSM = LeftSemimodule semiring r ℓr

LSMs = LeftSemimodules semiring

open Category LSMs

open import Categories.Category.Cartesian   using (Cartesian)
open import Categories.Category.Cocartesian using (Cocartesian)

-- open import Categories.Category.Cartesian   LSMs
-- open import Categories.Category.Cocartesian LSMs
open import Biproduct LSMs

module PC = PreadditiveCartesian (LeftSemimodules-PreadditiveCartesian semiring)

open PC

-- open Cartesian cartesian
-- open Cocartesian cocartesian

-- LeftSemimodules-PreadditiveCartesian

-- open import Categories.Category LSMs

open import Algebra.Module.Construct.TensorUnit using () renaming (leftSemimodule to R′)

open import Relation.Binary.Reasoning.MultiSetoid

private
  variable
    A B C D : LSM

infix 10 [[_,_]]
infix 11 ⟨⟨_,_⟩⟩

infixr 1 _⊸_
data _⊸_ : LSM → LSM → Set (suc (r ⊔ ℓr)) where
  ⌞_⌟     : R → R′ ⊸ R′
  [[_,_]] : A ⊸ C → B ⊸ C → A + B ⊸ C
  ⟨⟨_,_⟩⟩ : A ⊸ C → A ⊸ D → A ⊸ C × D

infix 5 ⟦_⟧
⟦_⟧ : (A ⊸ B) → (A ⇒ B)
⟦ ⌞ r ⌟ ⟧ = record { _⟨$⟩_ = r *_ ; cong = *-congˡ }
          , distribˡ r
          , zeroʳ _
          , (λ s x → begin⟨ R-setoid ⟩
               r * (s * x) ≈⟨ {!!} ⟩  -- oops!
               s * (r * x) ∎ )
⟦ [[ f , g ]] ⟧ = [ ⟦ f ⟧ , ⟦ g ⟧ ]   -- many errors
⟦ ⟨⟨ f , g ⟩⟩ ⟧ = ⟨ ⟦ f ⟧ , ⟦ g ⟧ ⟩   -- many errors

-- The "oops" reveals that we need a commutative 
