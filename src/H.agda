-- Experiments in functorial properties, homomorphism, and algebraic categories.

module H where

open import Level
open import Data.Product
open import Relation.Unary using (Pred; _∩_; _∈_)
open import Data.Unit.Polymorphic
open import Algebra using (Op₁; Op₂)

open import Categories.Category.Core

module _ {o ℓ e} (C : Category o ℓ e) where

  open Category C

  private
    variable
      X Y Z : Obj

  record Functorial : Set (o ⊔ ℓ ⊔ suc e) where
    infixr 9 _∘M_
    field
      ℳ : ∀ {X Y} → Pred (X ⇒ Y) e   -- A family of sets of morphisms
      Mid : ∀ {X} → id {X} ∈ ℳ
      _∘M_  : ∀ {X Y Z} {g : Y ⇒ Z} {f : X ⇒ Y} → g ∈ ℳ → f ∈ ℳ → g ∘ f ∈ ℳ

  UF : Functorial
  UF = record { ℳ = λ _ → ⊤ ; Mid = tt ; _∘M_ = λ _ _ → tt }

  infixr 7 _∩F_
  _∩F_ : Op₂ Functorial
  (record { ℳ = Q ; Mid = Qid ; _∘M_ = _∘Q_ })
    ∩F (record { ℳ = R ; Mid = Rid ; _∘M_ = _∘R_ }) = 
   record { ℳ = Q ∩ R
          ; Mid = (Qid , Rid)
          ; _∘M_ = λ (Qg , Rg) (Qf , Rf) → Qg ∘Q Qf , Rg ∘R Rf
          }

  -- Can I replace Functorial with a category of some sort (or many)? Then _∩F_
  -- corresponds to product of categories and UF to the terminal category (I
  -- think).

  SubCategoryM : Functorial → Category o (ℓ ⊔ e) e
  SubCategoryM F = SubCategory record
    { U = λ A → A
    ; R = ℳ
    ; Rid = Mid
    ; _∘R_ = _∘M_
    } where open Functorial F
            open import Categories.Category.SubCategory C

-------------------------------------------------------------------------------
-- | Homomorphisms as functorial properties
-------------------------------------------------------------------------------

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

-- TODO: Fix definitions below to extract the setoid and the operation from
-- something else, which will be a monoid, ring, etc.

H₀ : (∀ S → Carrier S) → Functorial (Setoids c c)
H₀ op = record
  { ℳ = λ {X Y} f′ → let ∙ = op X ; ∘ = op Y
                         open Π f′ renaming (_⟨$⟩_ to f)
                         open Setoid Y using (_≈_) in
                       f ∙ ≈ ∘
  ; Mid = λ {X} → refl X
  ; _∘M_ = λ {X Y Z} {g′ f′} gᴴ fᴴ →
             let open Π g′ renaming (_⟨$⟩_ to g; cong to cong-g)
                 open Π f′ renaming (_⟨$⟩_ to f)
                 ∙ = op X ; ∘ = op Y ; ⋆ = op Z in
               begin⟨ Z ⟩
                 g (f ∙) ≈⟨ cong-g fᴴ ⟩
                 g ∘     ≈⟨ gᴴ ⟩
                 ⋆       ∎
  }

H₁ : (∀ S → Op₁ (Carrier S)) → Functorial (Setoids c c)
H₁ op = record
  { ℳ = λ {X Y} f′ → let ∙_ = op X ; ∘_ = op Y
                         open Π f′ renaming (_⟨$⟩_ to f)
                         open Setoid Y using (_≈_) in ∀ x →
                       f (∙ x) ≈ ∘ f x
  ; Mid = λ {X} _ → refl X
  ; _∘M_ = λ {X Y Z} {g′ f′} gᴴ fᴴ →
             let open Π g′ renaming (_⟨$⟩_ to g; cong to cong-g)
                 open Π f′ renaming (_⟨$⟩_ to f)
                 ∙_ = op X ; ∘_ = op Y ; ⋆_ = op Z in λ x →
               begin⟨ Z ⟩
                 g (f (∙ x)) ≈⟨ cong-g (fᴴ x) ⟩
                 g (∘ f x)   ≈⟨ gᴴ (f x) ⟩
                 ⋆ g (f x)   ∎
  }

H₂ : (∀ S → Op₂ (Carrier S)) → Functorial (Setoids c c)
H₂ op = record
  { ℳ = λ {X Y} f′ → let _∙_ = op X ; _∘_ = op Y
                         open Π f′ renaming (_⟨$⟩_ to f)
                         open Setoid Y in ∀ x y →
                       f (x ∙ y) ≈ f x ∘ f y
  ; Mid = λ {X} _ _ → refl X
  ; _∘M_ = λ {X Y Z} {g′ f′} gᴴ fᴴ →
             let open Π g′ renaming (_⟨$⟩_ to g; cong to cong-g)
                 open Π f′ renaming (_⟨$⟩_ to f)
                 _∙_ = op X ; _∘_ = op Y ; _⋆_ = op Z in λ x y →
               begin⟨ Z ⟩
                 g (f (x ∙ y))      ≈⟨ cong-g (fᴴ x y) ⟩
                 g (f x ∘ f y)      ≈⟨ gᴴ (f x) (f y) ⟩
                 g (f x) ⋆ g (f y)  ∎
  }


