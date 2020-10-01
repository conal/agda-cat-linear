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

-- infix 4 _≈-homo_
-- _≈-homo_ : ∀ {a ℓ} → {A B : Magma a ℓ} → Rel (MagmaHomomorphism A B) {!!}
-- _≈-homo_ {_} {_} {A} {B} F G = ∀ {x y} → x A.≈ y → F.⟦ x ⟧ B.≈ G.⟦ y ⟧
--  where
--    module A = Magma A
--    module B = Magma B
--    module F = MagmaHomomorphism F
--    module G = MagmaHomomorphism G

-- I don't think we really need y here, given ⟦_⟧-cong.

infix 4 _≈-homo_
_≈-homo_ : ∀ {a ℓ} → {A B : Magma a ℓ} → Rel (MagmaHomomorphism A B) (a ⊔ ℓ)
_≈-homo_ {_} {_} {A} {B} F G = ∀ {x} → F.⟦ x ⟧ B.≈ G.⟦ x ⟧
 where
   module A = Magma A
   module B = Magma B
   module F = MagmaHomomorphism F
   module G = MagmaHomomorphism G

≈-homo-refl : ∀ {a ℓ} → {A B : Magma a ℓ} → Reflexive {A = MagmaHomomorphism A B} _≈-homo_
≈-homo-refl {B = B} = Magma.refl B

≈-homo-sym : ∀ {a ℓ} → {A B : Magma a ℓ} → {F G : MagmaHomomorphism A B}
           → (F ≈-homo G) → (G ≈-homo F)
≈-homo-sym {B = B} f≈g = Magma.sym B f≈g

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
_∘-homo_ {_} {_} {A} {B} {C} G F = record
  { setoidM = G.setoidM ⟶-∘ F.setoidM
  ; isMagmaHomomorphism = record
    { isRelHomomorphism = record { cong = G.⟦⟧-cong ∘ F.⟦⟧-cong }
    ; homo = λ x y → let open SetoidReasoning C.setoid in
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

∘-assoc : ∀ {a ℓ} {A B C D : Magma a ℓ}
        → {h : MagmaHomomorphism C D} → {g : MagmaHomomorphism B C} → {f : MagmaHomomorphism A B}
        → (h ∘-homo g) ∘-homo f ≈-homo h ∘-homo (g ∘-homo f)
∘-assoc {D = D} = Magma.refl D

-- Injective f = ∀ {x y} → f x ≈₂ f y → x ≈₁ y

id-mono : {A : Magma a ℓ} → MagmaMonomorphism A A
id-mono = record { magmaHomomorphism = id-homo ; injective = id }

infixr 9 _∘-mono_
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

infixr 9 _∘-iso_
_∘-iso_ : ∀ {a ℓ} {A B C : Magma a ℓ}
        → MagmaIsomorphism B C → MagmaIsomorphism A B → MagmaIsomorphism A C
_∘-iso_ {_} {_} {A} {B} {C} G F = record
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


-- The id and _∘_ for surjective closely resemble the corresponding
-- definitions in generalized automatic differentiation. TODO: investigate!

-- Maybe injectivity and surjectivity are more easily defined via setoid.

-- Next, identity and composition for magma homomorphism, monomorphism, and isomorphism.
-- Also associativity and whatever else we need for a Category instance.
-- We'll use these morphisms for Semigroup as well as Magma.
-- Refactor so we can add injective and surjective to these definitions more succinctly.
-- Then Monoid, Group, etc.

open import Categories.Category.Core

-- Magmas : ∀ {a ℓ} → Category (suc a ⊔ suc ℓ) (suc a ⊔ suc ℓ) (a ⊔ ℓ)
Magmas : ∀ {a ℓ} → Category (suc a ⊔ suc ℓ) (a ⊔ ℓ) (a ⊔ ℓ)
Magmas {a} {ℓ} = record
  { Obj = Magma a ℓ
  ; _⇒_ = MagmaHomomorphism
  ; _≈_ = _≈-homo_
  ; id = id-homo
  ; _∘_ = _∘-homo_
  ; assoc = ∘-assoc
  ; sym-assoc = λ {A} {B} {C} {D} {f} {g} {h} {x} → Magma.refl D
  ; identityˡ = λ {A} {B} {f} {x} → Magma.refl B
  ; identityʳ = λ {A} {B} {f} {x} → Magma.refl B
  ; identity² = λ {A} {x} → Magma.refl A
  ; equiv = {!!}
  ; ∘-resp-≈ = {!!}
  }

