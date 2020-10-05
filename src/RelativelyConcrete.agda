-- Relatively concrete categories, i.e., defined by a forgetful functor to a known category.
-- Inspired by <https://github.com/JacquesCarette/TheoriesAndDataStructures/>.

open import Level
open import Function using (_on_)
open import Relation.Binary using (Rel;IsEquivalence)
import Relation.Binary.Reasoning.Setoid as SetoidReasoning

open import Categories.Category.Core

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

record RawFunctor (C : RawCategory o ℓ e) (D : Category o′ ℓ′ e′) : Set (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′) where
  eta-equality
  private module C = RawCategory C ; open C
  private module D =    Category D ; open D

  field
    F₀ : Objᴿ → Obj
    F₁ : ∀ {A B : Objᴿ} → (A ⇒ᴿ B) → (F₀ A ⇒ F₀ B)

    identity     : ∀ {A} → F₁ (idᴿ {A}) ≈ id 
    homomorphism : ∀ {X Y Z} {f : X ⇒ᴿ Y } {g : Y ⇒ᴿ Z} →
                     F₁ (g ∘ᴿ f) ≈ F₁ g ∘ F₁ f
    F-resp-≈     : ∀ {A B} {f g : A ⇒ᴿ B} → f ≈ᴿ g → F₁ f ≈ F₁ g

RelativelyConcrete : ∀ {U : RawCategory o ℓ e} {V : Category o′ ℓ′ e′} → RawFunctor U V → Category _ _ _
RelativelyConcrete {U = U} {V} F = record
  { Obj = Objᴿ
  ; _⇒_ = _⇒ᴿ_
  ; _≈_ = _≈_ on F₁
          -- λ f g → F₁ f ≈ F₁ g
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

-- private
--   variable
--     o ℓ e : Level

-- record Concrete (C : Category o ℓ e) (ℓ′ e′ : Level) : Set (o ⊔ ℓ ⊔ e ⊔ suc (ℓ′ ⊔ e′)) where
--   field
--     concretize : Functor C (Setoids ℓ′ e′)
--     conc-faithful : Faithful concretize
