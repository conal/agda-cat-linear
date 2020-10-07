{-# OPTIONS --without-K --safe #-}
module Concrete where

-- Relatively concrete categories, i.e., defined by a forgetful functor to a known category.
-- Inspired by <https://github.com/JacquesCarette/TheoriesAndDataStructures/>.

open import Level
open import Function using (_on_) renaming (id to id→; _∘_ to _∘→_)
open import Function.Equality using (_⟶_; _⇨_) renaming (id to id⟶; _∘_ to _∘⟶_)
open import Relation.Binary using (Rel;IsEquivalence)
open import Relation.Binary.Reasoning.MultiSetoid

open import Categories.Category.Core
open import Categories.Functor using (Functor)
open import Categories.Functor.Properties using (Faithful)

record RawCategory (o ℓ e : Level) : Set (suc (o ⊔ ℓ ⊔ e)) where
  infix  4 _≈ᴿ_ _⇒ᴿ_
  infixr 9 _∘ᴿ_

  field
    Objᴿ : Set o
    _⇒ᴿ_ : Rel Objᴿ ℓ
    _≈ᴿ_ : ∀ {A B} → Rel (A ⇒ᴿ B) e

    idᴿ  : ∀ {A} → (A ⇒ᴿ A)
    _∘ᴿ_ : ∀ {A B C} → (B ⇒ᴿ C) → (A ⇒ᴿ B) → (A ⇒ᴿ C)

private
  variable
    o ℓ e o′ ℓ′ e′ : Level

record RawFunctor (U : RawCategory o ℓ e) (V : Category o′ ℓ′ e′) : Set (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′) where
  eta-equality
  private module U = RawCategory U ; open U
  private module V =    Category V ; open V

  field
    F₀ : Objᴿ → Obj
    F₁ : ∀ {A B : Objᴿ} → (A ⇒ᴿ B) → (F₀ A ⇒ F₀ B)

    identity     : ∀ {A} → F₁ (idᴿ {A}) ≈ id 
    homomorphism : ∀ {X Y Z} {f : X ⇒ᴿ Y } {g : Y ⇒ᴿ Z} →
                     F₁ (g ∘ᴿ f) ≈ F₁ g ∘ F₁ f
    F-resp-≈     : ∀ {A B} {f g : A ⇒ᴿ B} → f ≈ᴿ g → F₁ f ≈ F₁ g

RawFunctorCategory : ∀ {U : RawCategory o ℓ e} {V : Category o′ ℓ′ e′} → RawFunctor U V → Category o ℓ e′
RawFunctorCategory {U = U} {V} F = record
  { Obj = Objᴿ
  ; _⇒_ = _⇒ᴿ_
  ; _≈_ = _≈_ on F₁
  ; id = idᴿ
  ; _∘_ = _∘ᴿ_
  ; assoc = assoc′
  ; sym-assoc = Equiv.sym assoc′
  ; identityˡ = identityˡ′
  ; identityʳ = identityʳ′
  ; identity² = λ {A} → identityˡ′ {A} {A} {idᴿ}
  ; equiv = isEquivalence F₁ equiv
  ; ∘-resp-≈ = λ {A} {B} {C} {f} {h} {g} {i} f≈h g≈i →
     begin⟨ hom-setoid ⟩
       F₁ (f ∘ᴿ g)   ≈⟨ homomorphism ⟩
       F₁ f ∘ F₁ g   ≈⟨ ∘-resp-≈ˡ f≈h ⟩
       F₁ h ∘ F₁ g   ≈⟨ ∘-resp-≈ʳ g≈i ⟩
       F₁ h ∘ F₁ i   ≈˘⟨ homomorphism ⟩
       F₁ (h ∘ᴿ i)   ∎
  } where
      open RawCategory U
      open    Category V
      open RawFunctor  F
      open import Relation.Binary.Construct.On
      assoc′ : ∀ {A B C D} {f : A ⇒ᴿ B} {g : B ⇒ᴿ C} {h : C ⇒ᴿ D} → F₁ ((h ∘ᴿ g) ∘ᴿ f) ≈ F₁ (h ∘ᴿ (g ∘ᴿ f))
      assoc′ {f = f} {g} {h} =
        begin⟨ hom-setoid ⟩
          F₁ ((h ∘ᴿ g) ∘ᴿ f)    ≈⟨ homomorphism ⟩
          F₁ (h ∘ᴿ g) ∘ F₁ f    ≈⟨ ∘-resp-≈ˡ homomorphism ⟩
          (F₁ h ∘ F₁ g) ∘ F₁ f  ≈⟨ assoc ⟩
          F₁ h ∘ (F₁ g ∘ F₁ f)  ≈˘⟨ ∘-resp-≈ʳ homomorphism ⟩
          F₁ h ∘ F₁ (g ∘ᴿ f)    ≈˘⟨ homomorphism ⟩
          F₁ (h ∘ᴿ (g ∘ᴿ f))   ∎
      identityˡ′ : ∀ {A B} {f : A ⇒ᴿ B} → F₁ (idᴿ ∘ᴿ f) ≈ F₁ f
      identityˡ′ {A} {B} {f} =
        begin⟨ hom-setoid ⟩
          F₁ (idᴿ ∘ᴿ f)         ≈⟨ homomorphism ⟩
          F₁ idᴿ ∘ F₁ f         ≈⟨ ∘-resp-≈ˡ identity ⟩
          id ∘ F₁ f             ≈⟨ identityˡ ⟩
          F₁ f          ∎
      identityʳ′ : ∀ {A B} {f : A ⇒ᴿ B} → F₁ (f ∘ᴿ idᴿ) ≈ F₁ f
      identityʳ′ {A} {B} {f} =
        begin⟨ hom-setoid ⟩
          F₁ (f ∘ᴿ idᴿ)         ≈⟨ homomorphism ⟩
          F₁ f ∘ F₁ idᴿ         ≈⟨ ∘-resp-≈ʳ identity ⟩
          F₁ f ∘ id             ≈⟨ identityʳ ⟩
          F₁ f          ∎

private
  variable
    U : RawCategory o ℓ e
    V : Category o′ ℓ′ e′
    F : RawFunctor U V

Forget : (F : RawFunctor U V) → Functor (RawFunctorCategory F) V
Forget F = record
  { F₀ = F₀
  ; F₁ = F₁
  ; identity = identity
  ; homomorphism = homomorphism
  ; F-resp-≈ = id→
  } where open RawFunctor F

faithful : (F : RawFunctor U V) → Faithful (Forget F)
faithful _ _ _ = id→  -- trivial from definition of _≈_ for RawFunctorCategory.

-- Generalization of Concrete from Categories.Category.Concrete.
-- Maybe move into agda-categories.
record RelativelyConcrete (C : Category o ℓ e) (D : Category o′ ℓ′ e′)
        : Set (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′) where
  field
    concretize : Functor C D
    conc-faithful : Faithful concretize

relativelyConcrete : ∀ {F : RawFunctor U V}
                   → RelativelyConcrete (RawFunctorCategory F) V
relativelyConcrete {F = F} = record
  { concretize = Forget F ; conc-faithful = faithful F }


record Functorial (C : Category o ℓ e) : Set (o ⊔ ℓ ⊔ suc e) where
  open Category C
  infixr 9 _∘-preserves_
  field
    prop : ∀ {A B : Obj} → (A ⇒ B) → Set e
    id-sat : ∀ {A : Obj} → prop (id {A})
    _∘-preserves_ : ∀ {A B C : Obj} {f : A ⇒ B} {g : B ⇒ C} →
      prop g → prop f → prop (g ∘ f)

-- TODO: maybe split out IsFunctorial {C} prop


open import Relation.Binary
open import Algebra.Bundles

MonoidsRaw : ∀ {o ℓ} → RawCategory (suc o ⊔ suc ℓ) (o ⊔ ℓ) (o ⊔ ℓ)
MonoidsRaw {o} {ℓ} = record
  { Objᴿ = Monoid o ℓ
  ; _⇒ᴿ_ = λ A B → setoid A ⟶ setoid B
  ; _≈ᴿ_ = λ {A B} → Setoid._≈_ (setoid A ⇨ setoid B)
  ; idᴿ  = id⟶
  ; _∘ᴿ_ = _∘⟶_
  } where open Monoid

-- TODO: Get this structure from the Setoids category. Maybe a sub-category?

-- Oops! I haven't restricted MonoidsRaw._⇒ᴿ_ to include only monoid *homomorphisms*.

open import Categories.Category.Instance.Setoids

open import Algebra.Structures

Monoids : ∀ {o ℓ} → Category _ _ _
Monoids {o} {ℓ} = RawFunctorCategory {U = MonoidsRaw} {V = Setoids o ℓ} record
  { F₀ = setoid
  ; F₁ = id→
  ; identity = id→
  ; homomorphism = λ {X Y Z} {f g} → Equiv.refl {setoid X} {setoid Z} {g ∘ f}
  ; F-resp-≈ = id→
  } where
       open Monoid using (setoid)
       open Category (Setoids o ℓ)

-- There's almost nothing specific to Monoid here. Generalize. Maybe take a sort
-- and a function from that sort to Setoid.
