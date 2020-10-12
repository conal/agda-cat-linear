-- Experiments in functorial properties, homomorphism, and algebraic categories.

module H where

open import Level
open import Data.Product
open import Relation.Unary using (Pred; _∩_)
open import Data.Unit.Polymorphic
open import Algebra using (Op₁; Op₂)

open import Categories.Category.Core

module _ {o ℓ e} (C : Category o ℓ e) where

  open Category C

  private
    variable
      X Y Z : Obj

  ArrProp : Set (o ⊔ ℓ ⊔ suc e)
  ArrProp = ∀ {X Y} → Pred (X ⇒ Y) e

  private
    variable
      P Q : ArrProp

  IsFunctorial : ArrProp → Set (o ⊔ ℓ ⊔ e)
  IsFunctorial P = (∀ {X : Obj} → P (id {X}))
                 × (∀ {X Y Z} {g : Y ⇒ Z} {f : X ⇒ Y} → P g → P f → P (g ∘ f))

  -- Can I replace IsFunctorial with a category of some sort (or many)? Then
  -- functorial-∩ corresponds to product of categories and functorial-U to the
  -- terminal category (I think).

  record Functorial : Set (o ⊔ ℓ ⊔ suc e) where
    field
      prop : ArrProp
      isFunctorial : IsFunctorial prop

  UF : Functorial
  UF = record { prop = λ _ → ⊤ ; isFunctorial = tt , λ _ _ → tt }

  infixr 7 _∩_
  _∩F_ : Op₂ Functorial
  (record { prop = P ; isFunctorial = (Pid , _P∘_)})
    ∩F (record { prop = Q ; isFunctorial = (Qid , _Q∘_) }) = 
   record { prop = P ∩ Q
          ; isFunctorial = (Pid , Qid) , (λ (Pg , Qg) (Pf , Qf) → Pg P∘ Pf , Qg Q∘ Qf)
          }

open import Function.Equality using (Π; _⟨$⟩_; _⟶_)
open import Relation.Binary
open import Function.Bundles
open import Relation.Binary.Reasoning.MultiSetoid

open import Categories.Category.Instance.Setoids

open Setoid using (Carrier; refl)

private
  variable
    c : Level
    S : Setoid c c

-- TODO: Generalize from Setoid c c to Setoid c ℓ. Might need Functorial to
-- loosen up. Try generalizing Functorial to Category anyway, introducing
-- another level argument.

H₀ : (∀ S → Carrier S) → Functorial (Setoids c c)
H₀ op = record
  { prop = λ {X Y} f′ → let ∙ = op X ; ∘ = op Y
                            open Π f′ renaming (_⟨$⟩_ to f)
                            open Setoid Y using (_≈_) in
                          f ∙ ≈ ∘
  ; isFunctorial =
      (λ {X} → refl X) ,
      (λ {X Y Z} {g′ f′} gᴴ fᴴ →
         let open Π g′ renaming (_⟨$⟩_ to g; cong to cong-g)
             open Π f′ renaming (_⟨$⟩_ to f)
             ∙ = op X ; ∘ = op Y ; ⋆ = op Z in
           begin⟨ Z ⟩
             g (f ∙) ≈⟨ cong-g fᴴ ⟩
             g ∘     ≈⟨ gᴴ ⟩
             ⋆       ∎)
  }

H₁ : (∀ S → Op₁ (Carrier S)) → Functorial (Setoids c c)
H₁ op = record
  { prop = λ {X Y} f′ → let ∙_ = op X ; ∘_ = op Y
                            open Π f′ renaming (_⟨$⟩_ to f)
                            open Setoid Y using (_≈_) in ∀ x →
                          f (∙ x) ≈ ∘ f x
  ; isFunctorial =
      (λ {X} _ → refl X) ,
      (λ {X Y Z} {g′ f′} gᴴ fᴴ →
         let open Π g′ renaming (_⟨$⟩_ to g; cong to cong-g)
             open Π f′ renaming (_⟨$⟩_ to f)
             ∙_ = op X ; ∘_ = op Y ; ⋆_ = op Z in λ x →
           begin⟨ Z ⟩
             g (f (∙ x)) ≈⟨ cong-g (fᴴ x) ⟩
             g (∘ f x)   ≈⟨ gᴴ (f x) ⟩
             ⋆ g (f x)   ∎)
  }

H₂ : (∀ S → Op₂ (Carrier S)) → Functorial (Setoids c c)
H₂ op = record
  { prop = λ {X Y} f′ → let _∙_ = op X ; _∘_ = op Y
                            open Π f′ renaming (_⟨$⟩_ to f)
                            open Setoid Y in ∀ x y →
                          f (x ∙ y) ≈ f x ∘ f y
  ; isFunctorial =
      (λ {X} _ _ → refl X) ,
      (λ {X Y Z} {g′ f′} gᴴ fᴴ →
         let open Π g′ renaming (_⟨$⟩_ to g; cong to cong-g)
             open Π f′ renaming (_⟨$⟩_ to f)
             _∙_ = op X ; _∘_ = op Y ; _⋆_ = op Z in λ x y →
           begin⟨ Z ⟩
             g (f (x ∙ y))      ≈⟨ cong-g (fᴴ x y) ⟩
             g (f x ∘ f y)      ≈⟨ gᴴ (f x) (f y) ⟩
             g (f x) ⋆ g (f y)  ∎)
  }


