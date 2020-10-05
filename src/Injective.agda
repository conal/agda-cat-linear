-- Injectivity proofs as a category

-- Oh! I found Function.Injection in stdlib. Start over.

open import Level

module Injective (a ℓ : Level) where

open import Relation.Binary
open import Function hiding (_↣_)
open import Function.Definitions
open import Function.Equality hiding (setoid) renaming (id to ⟶-id; _∘_ to _⟶-∘_)

import Relation.Binary.Reasoning.Setoid as SetoidReasoning

open import Categories.Category.Core 

infixr 0 _↣_
record _↣_ (A : Setoid a ℓ) (B : Setoid a ℓ) : Set (a ⊔ ℓ) where
  field
    arr : A ⟶ B
    injective : Injective (Setoid._≈_ A) (Setoid._≈_ B) (arr ⟨$⟩_)
  open Π arr public
  open Setoid
  ⟦_⟧ : Carrier A → Carrier B
  ⟦ a ⟧ = arr ⟨$⟩ a

open _↣_
open import Categories.Category.Instance.Setoids

private module S = Category (Setoids a ℓ)

infix 4 _≈-equiv_
_≈-equiv_ : ∀ {A B : Setoid a ℓ} → Rel (A ↣ B) (a ⊔ ℓ)
_≈-equiv_ {A} {B} f g = Setoid._≈_ (A ⇨ B) (_↣_.arr f) (_↣_.arr g) -- ignoring proofs for now

≈-is : ∀ {A B} → IsEquivalence (_≈-equiv_ {A} {B})
≈-is {A} {B} = record
  { refl  = λ {f : A ↣ B} x≈y → _↣_.cong f x≈y
  ; sym   = λ {f : A ↣ B} {g : A ↣ B} f≈g {x} {y} x≈y →
              let module A = Setoid A
                  module F = _↣_ f ; f = F.⟦_⟧
                  module G = _↣_ g ; g = G.⟦_⟧
                  open SetoidReasoning B
              in
                begin
                  g x   ≈˘⟨ f≈g (A.sym x≈y)  ⟩
                  f y   ∎
  ; trans = λ {f : A ↣ B} {g : A ↣ B} {h : A ↣ B} f≈g g≈h {x} {y} x≈y →
              let module A = Setoid A
                  module F = _↣_ f ; f = F.⟦_⟧
                  module G = _↣_ g ; g = G.⟦_⟧
                  module H = _↣_ h ; h = H.⟦_⟧
                  open SetoidReasoning B
              in
                begin
                  f x ≈⟨ f≈g A.refl ⟩
                  g x ≈⟨ g≈h x≈y ⟩
                  h y ∎
  }
 where
   open Setoid

infixr 9 _∘ᴵ_
_∘ᴵ_ : ∀ {A B C} → B ↣ C → A ↣ B → A ↣ C
_∘ᴵ_ (record { arr = g′ ; injective = gᴵ})
     (record { arr = f′ ; injective = fᴵ}) =
  record { arr = g′ S.∘ f′ ; injective = fᴵ ∘ gᴵ }

∘ᴵ-assoc : ∀ {A B C D} {f : A ↣ B} {g : B ↣ C} {h : C ↣ D} → (h ∘ᴵ g) ∘ᴵ f ≈-equiv h ∘ᴵ (g ∘ᴵ f)
∘ᴵ-assoc {A} {B} {C} {D}
      { (record { arr = f′ ; injective = fᴵ}) }
      { (record { arr = g′ ; injective = gᴵ}) }
      { (record { arr = h′ ; injective = hᴵ}) } =
  S.assoc {f = f′} {g = g′} {h = h′}

Injectives : Category (suc a ⊔ suc ℓ) (a ⊔ ℓ) (a ⊔ ℓ)
Injectives = record
  { Obj = Setoid a ℓ
  ; _⇒_ = _↣_
  ; _≈_ = _≈-equiv_
  ; id = record { arr = ⟶-id ; injective = id }
  ; _∘_ = _∘ᴵ_
  ; assoc = λ {A B C D} {(record { arr = f′ ; injective = fᴵ})
                         (record { arr = g′ ; injective = gᴵ})
                         (record { arr = h′ ; injective = hᴵ})} →
                 S.assoc {f = f′} {g = g′} {h = h′}
  ; sym-assoc = λ {A B C D} {(record { arr = f′ ; injective = fᴵ})
                             (record { arr = g′ ; injective = gᴵ})
                             (record { arr = h′ ; injective = hᴵ})} →
                 S.sym-assoc {f = f′} {g = g′} {h = h′}
  ; identityˡ = λ {A B} {(record { arr = f′ ; injective = fᴵ})} → S.identityˡ {f = f′}
  ; identityʳ = λ {A B} {(record { arr = f′ ; injective = fᴵ})} → S.identityʳ {f = f′}
  ; identity² = λ {A} → S.identity² {A}
  ; equiv = ≈-is
  ; ∘-resp-≈ = λ {A B C} {f h} {g i} → λ f≈h g≈i {x} {y} x≈y →
               let module B = Setoid B
                   module F = _↣_ f ; f = F.⟦_⟧
                   module G = _↣_ g ; g = G.⟦_⟧
                   module H = _↣_ h ; h = H.⟦_⟧
                   module I = _↣_ i ; i = I.⟦_⟧
                   open SetoidReasoning C
                 in
                   begin
                      f (g x)  ≈⟨ f≈h B.refl ⟩
                      h (g x)  ≈⟨ H.cong (g≈i x≈y) ⟩
                      h (i y)  ∎
  }
