-- Relatively concrete categories, i.e., defined by a forgetful functor to a known category.
-- Inspired by <https://github.com/JacquesCarette/TheoriesAndDataStructures/>.

open import Level
open import Relation.Binary using (Rel)
import Relation.Binary.Reasoning.Setoid as SetoidReasoning

open import Categories.Category.Core

record RawCategory (o ℓ e : Level) : Set (suc (o ⊔ ℓ ⊔ e)) where
  infix  4 _≈'_ _⇒'_
  infixr 9 _∘'_

  field
    Obj' : Set o
    _⇒'_ : Rel Obj' ℓ
    _≈'_ : ∀ {A B} → Rel (A ⇒' B) e

    id'  : ∀ {A} → (A ⇒' A)
    _∘'_ : ∀ {A B C} → (B ⇒' C) → (A ⇒' B) → (A ⇒' C)

-- TODO: replace "'" with "ᴿ".

private
  variable
    o ℓ e o′ ℓ′ e′ : Level

record RawFunctor (C : RawCategory o ℓ e) (D : Category o′ ℓ′ e′) : Set (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′) where
  eta-equality
  private module C = RawCategory C ; open C
  private module D =    Category D ; open D
  -- open C renaming (Obj to Obj₁; _≈_ to _≈₁_; _⇒_ to _⇒₁_ ; _∘_ to _∘₁_)
  -- open D renaming (Obj to Obj₂; _≈_ to _≈₂_; _⇒_ to _⇒₂_ ; _∘_ to _∘₂_)

  field
    F₀ : Obj' → Obj
    F₁ : ∀ {A B : Obj'} → (A ⇒' B) → (F₀ A ⇒ F₀ B)

    identity     : ∀ {A} → F₁ (id' {A}) ≈ id 
    homomorphism : ∀ {X Y Z} {f : X ⇒' Y } {g : Y ⇒' Z} →
                     F₁ (g ∘' f) ≈ F₁ g ∘ F₁ f
    F-resp-≈     : ∀ {A B} {f g : A ⇒' B} → f ≈' g → F₁ f ≈ F₁ g

RelativelyConcrete : ∀ {U : RawCategory o ℓ e} {V : Category o′ ℓ′ e′} → RawFunctor U V → Category _ _ _
RelativelyConcrete {U = U} {V} F = record
  { Obj = Obj'
  ; _⇒_ = _⇒'_
  ; _≈_ = λ f g → F₁ f ≈ F₁ g
  ; id = id'
  ; _∘_ = _∘'_
  ; assoc = λ {A} {B} {C} {D} {f} {g} {h} →
              let open SetoidReasoning hom-setoid in
              begin
                F₁ ((h ∘' g) ∘' f)   ≈⟨ homomorphism ⟩
                F₁ (h ∘' g) ∘ F₁ f   ≈⟨ ∘-resp-≈ˡ homomorphism ⟩
                (F₁ h ∘ F₁ g) ∘ F₁ f ≈⟨ assoc ⟩
                F₁ h ∘ (F₁ g ∘ F₁ f) ≈˘⟨ ∘-resp-≈ʳ homomorphism ⟩
                F₁ h ∘ F₁ (g ∘' f)   ≈˘⟨ homomorphism ⟩
                F₁ (h ∘' (g ∘' f))   ∎
  ; sym-assoc = ? -- Equiv.sym assoc
  ; identityˡ = {!!}
  ; identityʳ = {!!}
  ; identity² = {!!}
  ; equiv = {!!}
  ; ∘-resp-≈ = {!!}
  } where
      open RawCategory U
      open    Category V
      open RawFunctor  F

-- private
--   variable
--     o ℓ e : Level

-- record Concrete (C : Category o ℓ e) (ℓ′ e′ : Level) : Set (o ⊔ ℓ ⊔ e ⊔ suc (ℓ′ ⊔ e′)) where
--   field
--     concretize : Functor C (Setoids ℓ′ e′)
--     conc-faithful : Faithful concretize
