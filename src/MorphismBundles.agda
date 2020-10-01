{-# OPTIONS --without-K --safe #-}

open import Level

module MorphismBundles where

open import Function using (id ; _∘_)
open import Function.Equality renaming (id to ⟶-id; _∘_ to _⟶-∘_ )
open import Agda.Builtin.Sigma
open import Relation.Binary
open import Relation.Binary.Definitions
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Bundles using (Setoid)
open import Algebra.Core
open import Algebra.Bundles
open import Algebra.Structures
open import Algebra.Morphism.Structures

import Function.Definitions as FunctionDefinitions

import Relation.Binary.Reasoning.Setoid as SetoidReasoning

private
  variable
    a ℓ : Level

module _ (M₁ M₂ : Magma a ℓ) where
  private
    module M₁ = Magma M₁
    module M₂ = Magma M₂
    module F = FunctionDefinitions M₁._≈_ M₂._≈_

  record MagmaHomomorphism : Set (a ⊔ ℓ) where
    field
      setoidM : M₁.setoid ⟶ M₂.setoid
    ⟦_⟧ : M₁.Carrier → M₂.Carrier
    ⟦ x ⟧ = setoidM ⟨$⟩ x
    field
      isMagmaHomomorphism : IsMagmaHomomorphism M₁.rawMagma M₂.rawMagma ⟦_⟧
    open IsMagmaHomomorphism isMagmaHomomorphism public

  record MagmaMonomorphism : Set (a ⊔ ℓ) where
    field magmaHomomorphism : MagmaHomomorphism
    open MagmaHomomorphism magmaHomomorphism public
    field injective : F.Injective ⟦_⟧

  record MagmaIsomorphism : Set (a ⊔ ℓ) where
    field magmaMonomorphism : MagmaMonomorphism
    open MagmaMonomorphism magmaMonomorphism public
    field surjective : F.Surjective ⟦_⟧


id-homo : {A : Magma a ℓ} → MagmaHomomorphism A A
id-homo {A = A} = record
  { setoidM = ⟶-id
  ; isMagmaHomomorphism = record
     { isRelHomomorphism = record { cong = id }
     ; homo = λ _ _ → Magma.refl A
     }
  }

infixr 9 _∘-homo_
_∘-homo_ : ∀ {a ℓ} {A B C : Magma a ℓ}
         → MagmaHomomorphism B C → MagmaHomomorphism A B → MagmaHomomorphism A C
_∘-homo_ {a} {ℓ} {A} {B} {C} G F = record
  { setoidM = G.setoidM ⟶-∘ F.setoidM
  ; isMagmaHomomorphism = record
    { isRelHomomorphism = record { cong = G.⟦⟧-cong ∘ F.⟦⟧-cong }
    ; homo = λ x y →
      let open SetoidReasoning C.setoid in
      begin
        g (f (x A.∙ y))     ≈⟨ G.⟦⟧-cong (F.homo x y) ⟩
        g (f x B.∙ f y)     ≈⟨ G.homo (f x) (f y) ⟩
        g (f x) C.∙ g (f y) ∎
    }
  } where
      module A = Magma A
      module B = Magma B
      module C = Magma C
      module F = MagmaHomomorphism F ; f = F.⟦_⟧
      module G = MagmaHomomorphism G ; g = G.⟦_⟧

-- Injective f = ∀ {x y} → f x ≈₂ f y → x ≈₁ y

id-mono : {A : Magma a ℓ} → MagmaMonomorphism A A
id-mono = record { magmaHomomorphism = id-homo ; injective = id }

_∘-mono_ : ∀ {a ℓ} {A B C : Magma a ℓ}
         → MagmaMonomorphism B C → MagmaMonomorphism A B → MagmaMonomorphism A C
G ∘-mono F = record
  { magmaHomomorphism = G.magmaHomomorphism ∘-homo F.magmaHomomorphism
  ; injective = F.injective ∘ G.injective
  } where
      module F = MagmaMonomorphism F
      module G = MagmaMonomorphism G


-- Surjective f = ∀ y → ∃ λ x → f x ≈₂ y

id-iso : {A : Magma a ℓ} → MagmaIsomorphism A A
id-iso {A = A} = record { magmaMonomorphism = id-mono ; surjective = _, refl }
  where open Magma A

_∘-iso_ : ∀ {a ℓ} {A B C : Magma a ℓ}
        → MagmaIsomorphism B C → MagmaIsomorphism A B → MagmaIsomorphism A C
_∘-iso_ {a} {ℓ} {A} {B} {C} G F = record
  { magmaMonomorphism = G.magmaMonomorphism ∘-mono F.magmaMonomorphism
  ; surjective = -- G.surjective ∘ F.surjective  -- in an appropriate sense
                 λ z → let (y , gy≈z) = G.surjective z
                           (x , fx≈y) = F.surjective y
                           open SetoidReasoning C.setoid
                           gfx≈z : g (f x) C.≈ z
                           gfx≈z = begin
                                     g (f x) ≈⟨ G.⟦⟧-cong fx≈y ⟩
                                     g y     ≈⟨ gy≈z ⟩
                                     z       ∎
                        in
                           (x , gfx≈z)
  } where
      module C = Magma C
      module F = MagmaIsomorphism F ; f = F.⟦_⟧
      module G = MagmaIsomorphism G ; g = G.⟦_⟧


-- The id and _∘_ for surjectived closely resemble the corresponding
-- definitions in generalized automatic differentiation. TODO: investigate!

-- Maybe injectivity and surjectivity are more easily defined via setoid.

{-

-- Next, identity and composition for magma homomorphism, monomorphism, and isomorphism.
-- Also associativity and whatever else we need for a Category instance.
-- We'll use these morphisms for Semigroup as well as Magma.
-- Refactor so we can add injective and surjective to these definitions more succinctly.
-- Then Monoid, Group, etc.

id-homo : {A : Semigroup c ℓ} → SemigroupMorphism A A
id-homo {A} = record
  { setoidM = ⟶-id
  ; isSemigroupMorphism = record
     { ⟦⟧-cong = id
     ; ∙-homo = λ _ _ → Semigroup.refl A
     }
  }

infixr 9 _∘-homo_
_∘-homo_ : ∀ {A B C : Semigroup c ℓ}
         → SemigroupMorphism B C → SemigroupMorphism A B → SemigroupMorphism A C
_∘-homo_ {A} {B} {C} G F = record
  { setoidM = G.setoidM ⟶-∘ F.setoidM
  ; isSemigroupMorphism = record
      { ⟦⟧-cong = G.⟦⟧-cong ∘ F.⟦⟧-cong
      ; ∙-homo = λ x y →
        -- G.⟦ F.⟦ x A.∙ y ⟧ ⟧ C.≈ G.⟦ F.⟦ x ⟧ ⟧ C.∙ G.⟦ F.⟦ y ⟧ ⟧
        begin
          G.⟦ F.⟦ x A.∙ y ⟧ ⟧              ≈⟨ G.⟦⟧-cong (F.∙-homo x y) ⟩
          G.⟦ F.⟦ x ⟧ B.∙ F.⟦ y ⟧ ⟧        ≈⟨ G.∙-homo (F.⟦ x ⟧) (F.⟦ y ⟧) ⟩
          G.⟦ F.⟦ x ⟧ ⟧ C.∙ G.⟦ F.⟦ y ⟧ ⟧  ∎
      }
  } where
      module F = SemigroupMorphism F
      module G = SemigroupMorphism G
      module A = Semigroup A
      module B = Semigroup B
      module C = Semigroup C
      open SetoidReasoning C.setoid

infix 4 _≈ᴴ_
_≈ᴴ_ : ∀ {A B : Semigroup c ℓ} → Rel (SemigroupMorphism A B) (c ⊔ ℓ)
_≈ᴴ_ {A} {B} f g = ∀ x y → x A.≈ y → ⟦ f ⟧ x B.≈ ⟦ g ⟧ y
 where module A = Semigroup A
       module B = Semigroup B

-- -- Equivalently? Not quite.
-- _≈ᴴ_ {A} {B} f g = Setoid._≈_ (A.setoid ⇨ B.setoid) F.setoidM G.setoidM
--  where
--    module A = Semigroup A
--    module B = Semigroup B
--    module F = SemigroupMorphism f
--    module G = SemigroupMorphism g

-- ≈ᴴ-refl : ∀ {A B : Semigroup c ℓ} → {f : SemigroupMorphism A B} → f ≈ᴴ f
≈ᴴ-refl : ∀ {A B : Semigroup c ℓ} → Reflexive {A = SemigroupMorphism A B} _≈ᴴ_
≈ᴴ-refl {_} {_} {f} = λ _ _ → F.⟦⟧-cong
 where module F = SemigroupMorphism f

≈ᴴ-sym : ∀ {A B : Semigroup c ℓ} → {f g : SemigroupMorphism A B}
       → f ≈ᴴ g → g ≈ᴴ f
≈ᴴ-sym {A} {B} {f} {g} f≈g x y x≈y = B.sym (f≈g y x (A.sym x≈y))
 where
   module A = Semigroup A
   module B = Semigroup B
   module F = SemigroupMorphism f
   module G = SemigroupMorphism g


∘-assoc : ∀ {A B C D : Semigroup c ℓ}
        → {h : SemigroupMorphism C D} → {g : SemigroupMorphism B C} → {f : SemigroupMorphism A B}
        → (h ∘-homo g) ∘-homo f ≈ᴴ h ∘-homo (g ∘-homo f)
∘-assoc {A} {B} {C} {D} {h} {g} {f} =
  λ x y x~y →
  -- ⟦ ((h ∘-homo g) ∘-homo f) ⟧ x D.≈ ⟦ h ∘-homo (g ∘-homo f) ⟧ y
  begin
    ⟦ (h ∘-homo g) ∘-homo f ⟧ x  ≈⟨ {!!} ⟩
    ⟦ (h ∘-homo g) ∘-homo f ⟧ x  ≈⟨ {!!} ⟩
    ⟦ h ∘-homo (g ∘-homo f) ⟧ y    ∎

 -- begin
 --    (h ∘-homo g) ∘-homo f   ≈⟨ ? ⟩
 --    h ∘-homo (g ∘-homo f)      ∎

  where
    module F = SemigroupMorphism f
    module G = SemigroupMorphism g
    module A = Semigroup A
    module B = Semigroup B
    module C = Semigroup C
    module D = Semigroup D
    open SetoidReasoning D.setoid

-- ∘-assoc : ∀ {A B C D : Semigroup c ℓ}
--         → {h : SemigroupMorphism C D} → {g : SemigroupMorphism B C} → {f : SemigroupMorphism A B}
--         → (h ∘-homo g) ∘-homo f ≈ᴴ h ∘-homo (g ∘-homo f)
-- ∘-assoc {A} {B} {C} {D} {h} {g} {f} =
--  begin
--     (h ∘-homo g) ∘-homo f   ≈⟨ ? ⟩
--     h ∘-homo (g ∘-homo f)      ∎
--   where
--     module F = SemigroupMorphism f
--     module G = SemigroupMorphism g
--     module A = Semigroup A
--     module B = Semigroup B
--     module C = Semigroup C
--     module D = Semigroup D
--     open SetoidReasoning D.setoid


open import Categories.Category.Core

Semigroups : Category (suc c ⊔ suc ℓ) (suc c ⊔ suc ℓ) (c ⊔ ℓ)
Semigroups = record
  { Obj = Semigroup c ℓ
  ; _⇒_ = SemigroupMorphism
  ; _≈_ = _≈ᴴ_
  ; id = id-homo
  ; _∘_ = _∘-homo_
  ; assoc = {!!}
  ; sym-assoc = {!!}
  ; identityˡ = {!!}
  ; identityʳ = {!!}
  ; identity² = {!!}
  ; equiv = {!!}
  ; ∘-resp-≈ = {!!}
  }

-}
