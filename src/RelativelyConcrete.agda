{-# OPTIONS --without-K --safe #-}
module RelativelyConcrete where

-- Relatively concrete categories, i.e., defined by a forgetful functor to a known category.
-- Inspired by <https://github.com/JacquesCarette/TheoriesAndDataStructures/>.

open import Level
open import Function using (_on_) renaming (id to id′)
open import Relation.Binary using (Rel;IsEquivalence)
import Relation.Binary.Reasoning.Setoid as SetoidReasoning

open import Categories.Category.Core
open import Categories.Functor using (Functor)

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
  ; assoc = assoc'
  ; sym-assoc = Equiv.sym assoc'
  ; identityˡ = identityˡ'
  ; identityʳ = identityʳ'
  ; identity² = λ {A} → identityˡ' {A} {A} {idᴿ}
  ; equiv = λ {A} {B} → isEquivalence F₁ equiv
  ; ∘-resp-≈ = λ {A} {B} {C} {f} {h} {g} {i} f≈h g≈i →
     let open SetoidReasoning hom-setoid in
     begin
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
      assoc' : ∀ {A B C D} {f : A ⇒ᴿ B} {g : B ⇒ᴿ C} {h : C ⇒ᴿ D} → F₁ ((h ∘ᴿ g) ∘ᴿ f) ≈ F₁ (h ∘ᴿ (g ∘ᴿ f))
      assoc' {f = f} {g} {h} =
        let open SetoidReasoning hom-setoid in
        begin
          F₁ ((h ∘ᴿ g) ∘ᴿ f)   ≈⟨ homomorphism ⟩
          F₁ (h ∘ᴿ g) ∘ F₁ f   ≈⟨ ∘-resp-≈ˡ homomorphism ⟩
          (F₁ h ∘ F₁ g) ∘ F₁ f ≈⟨ assoc ⟩
          F₁ h ∘ (F₁ g ∘ F₁ f) ≈˘⟨ ∘-resp-≈ʳ homomorphism ⟩
          F₁ h ∘ F₁ (g ∘ᴿ f)   ≈˘⟨ homomorphism ⟩
          F₁ (h ∘ᴿ (g ∘ᴿ f))   ∎
      identityˡ' : ∀ {A B} {f : A ⇒ᴿ B} → F₁ (idᴿ ∘ᴿ f) ≈ F₁ f
      identityˡ' {A} {B} {f} =
        let open SetoidReasoning hom-setoid in
        begin
          F₁ (idᴿ ∘ᴿ f) ≈⟨ homomorphism ⟩
          F₁ idᴿ ∘ F₁ f ≈⟨ ∘-resp-≈ˡ identity ⟩
          id ∘ F₁ f     ≈⟨ identityˡ ⟩
          F₁ f          ∎
      identityʳ' : ∀ {A B} {f : A ⇒ᴿ B} → F₁ (f ∘ᴿ idᴿ) ≈ F₁ f
      identityʳ' {A} {B} {f} =
        let open SetoidReasoning hom-setoid in
        begin
          F₁ (f ∘ᴿ idᴿ) ≈⟨ homomorphism ⟩
          F₁ f ∘ F₁ idᴿ ≈⟨ ∘-resp-≈ʳ identity ⟩
          F₁ f ∘ id     ≈⟨ identityʳ ⟩
          F₁ f          ∎

open import Categories.Category.Concrete
open import Categories.Functor.Properties using (Faithful)

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
  ; F-resp-≈ = id′
  } where open RawFunctor F

faithful : (F : RawFunctor U V) → Faithful (Forget F)
faithful F _ _ = id′  -- trivial from definition of _≈_ for RawFunctorCategory.

-- Generalization of Concrete from Categories.Category.Concrete.
-- Maybe move into agda-categories.
record RelativelyConcrete (C : Category o ℓ e) (D : Category o′ ℓ′ e′)
        : Set (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′) where
  field
    concretize : Functor C D
    conc-faithful : Faithful concretize

relativelyConcrete : ∀ {F : RawFunctor U V} → RelativelyConcrete (RawFunctorCategory F) V
relativelyConcrete {F = F} = record { concretize = Forget F ; conc-faithful = faithful F }
