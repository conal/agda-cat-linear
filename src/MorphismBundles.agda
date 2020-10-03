{-# OPTIONS --without-K --safe #-}

open import Level

module MorphismBundles {a ℓ : Level} where

open import Function using (id ; _∘_)
open import Function.Equality renaming (id to ⟶-id; _∘_ to _⟶-∘_ )
open import Agda.Builtin.Sigma
open import Relation.Binary
open import Relation.Binary.Definitions
open import Relation.Binary.Core using (Rel)
open import Algebra.Core
open import Algebra.Bundles
open import Algebra.Structures
open import Algebra.Morphism.Structures

import Function.Definitions as FunctionDefinitions

import Relation.Binary.Reasoning.Setoid as SetoidReasoning

module _ (A B : Magma a ℓ) where
  private
    module A = Magma A
    module B = Magma B
    module F = FunctionDefinitions A._≈_ B._≈_

  record MagmaHomomorphism : Set (a ⊔ ℓ) where
    field
      ⟦_⟧ : A.Carrier → B.Carrier
      isMagmaHomomorphism : IsMagmaHomomorphism A.rawMagma B.rawMagma ⟦_⟧
    open IsMagmaHomomorphism isMagmaHomomorphism public

  record MagmaMonomorphism : Set (a ⊔ ℓ) where
    field magmaHomomorphism : MagmaHomomorphism
    open MagmaHomomorphism magmaHomomorphism public
    field injective : F.Injective ⟦_⟧

  record MagmaIsomorphism : Set (a ⊔ ℓ) where
    field magmaMonomorphism : MagmaMonomorphism
    open MagmaMonomorphism magmaMonomorphism public
    field surjective : F.Surjective ⟦_⟧

-- I don't think we really need y here, given ⟦_⟧-cong.

infix 4 _≈-homo_
_≈-homo_ : ∀ {A B : Magma a ℓ} → Rel (MagmaHomomorphism A B) (a ⊔ ℓ)
_≈-homo_ {A} {B} F G = ∀ {x} → F.⟦ x ⟧ B.≈ G.⟦ x ⟧
 where
   module A = Magma A
   module B = Magma B
   module F = MagmaHomomorphism F
   module G = MagmaHomomorphism G

≈-homo-equiv : ∀ {A B : Magma a ℓ} → IsEquivalence (_≈-homo_ {A} {B})
≈-homo-equiv {A} {B} = record
  { refl  = refl
  ; sym   = λ f≈g → sym f≈g
  ; trans = λ f≈g g≈h → trans f≈g g≈h
  } where open Magma B

-- Eta-reduced versions of sym and trans don't type-check.  

id-homo : {A : Magma a ℓ} → MagmaHomomorphism A A
id-homo {A = A} = record
  { ⟦_⟧ = id
  ; isMagmaHomomorphism = record
     { isRelHomomorphism = record { cong = id }
     ; homo = λ _ _ → Magma.refl A
     }
  }

infixr 9 _∘-homo_
_∘-homo_ : ∀ {A B C : Magma a ℓ}
         → MagmaHomomorphism B C → MagmaHomomorphism A B → MagmaHomomorphism A C
_∘-homo_ {A} {B} {C} G F = record
  { ⟦_⟧ = G.⟦_⟧ ∘ F.⟦_⟧
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

∘-assoc : ∀ {A B C D : Magma a ℓ}
        → {f : MagmaHomomorphism A B} → {g : MagmaHomomorphism B C} → {h : MagmaHomomorphism C D}
        → (h ∘-homo g) ∘-homo f ≈-homo h ∘-homo (g ∘-homo f)
∘-assoc {D = D} = Magma.refl D

-- Injective f = ∀ {x y} → f x ≈₂ f y → x ≈₁ y

id-mono : {A : Magma a ℓ} → MagmaMonomorphism A A
id-mono = record { magmaHomomorphism = id-homo ; injective = id }

infixr 9 _∘-mono_
_∘-mono_ : ∀ {A B C : Magma a ℓ}
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
_∘-iso_ : ∀ {A B C : Magma a ℓ}
        → MagmaIsomorphism B C → MagmaIsomorphism A B → MagmaIsomorphism A C
_∘-iso_ {A} {B} {C} G F = record
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

-- Magmas : ∀ Category (suc a ⊔ suc ℓ) (suc a ⊔ suc ℓ) (a ⊔ ℓ)
Magmas : Category (suc a ⊔ suc ℓ) (a ⊔ ℓ) (a ⊔ ℓ)
Magmas = record
  { Obj = Magma a ℓ
  ; _⇒_ = MagmaHomomorphism
  ; _≈_ = _≈-homo_
  ; id = id-homo
  ; _∘_ = _∘-homo_
  ; assoc = λ {A B C D} {f g h} → ∘-assoc {A} {B} {C} {D} {f} {g} {h}
  ; sym-assoc = λ {A B C D} → Magma.refl D
  ; identityˡ = λ {A B} → Magma.refl B
  ; identityʳ = λ {A B} → Magma.refl B
  ; identity² = λ {A} → Magma.refl A
  ; equiv = ≈-homo-equiv
  ; ∘-resp-≈ = λ {A B C} {F H} {G I} f≈h g≈i → λ {x} →
      let module C = Magma C
          module F = MagmaHomomorphism F ; f = F.⟦_⟧
          module G = MagmaHomomorphism G ; g = G.⟦_⟧
          module H = MagmaHomomorphism H ; h = H.⟦_⟧
          module I = MagmaHomomorphism I ; i = I.⟦_⟧
          open SetoidReasoning C.setoid
      in
        begin
          f (g x)  ≈⟨ F.⟦⟧-cong g≈i ⟩
          f (i x)  ≈⟨ f≈h ⟩
          h (i x)  ∎
  }

