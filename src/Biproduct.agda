{-# OPTIONS --without-K --safe #-}

open import Categories.Category.Core using (Category)

module Biproduct {o ℓ e} (𝒞 : Category o ℓ e) where

open import Level

open import Relation.Binary.PropositionalEquality using (_≡_)
open import Algebra.Core using (Op₂)
open import Algebra.Structures using (IsMonoid)

open Category 𝒞
open import Categories.Category.Cartesian 𝒞
open import Categories.Category.Cocartesian 𝒞

open import Categories.Object.Initial 𝒞

open Equiv using (sym)
open HomReasoning
open import Categories.Morphism 𝒞
open import Categories.Morphism.Reasoning 𝒞

open import Misc using (id≅)

private
  variable
    A B C : Obj

  Op⇒₀ : Set (o ⊔ ℓ)
  Op⇒₀ = ∀ {A B} → A ⇒ B

  Op⇒₂ : Set (o ⊔ ℓ)
  Op⇒₂ = ∀ {A B} → Op₂ (A ⇒ B)

record IsPreadditive (_⊹_ : Op⇒₂) (𝟎 : Op⇒₀) : Set (levelOfTerm 𝒞) where
  field
    ⊹-zero-isMonoid : IsMonoid (_≈_ {A} {B}) _⊹_ 𝟎

    distrib-⊹ˡ : ∀ {A B C} {f g : A ⇒ B} {h : B ⇒ C} → h ∘ (f ⊹ g) ≈ (h ∘ f) ⊹ (h ∘ g)
    distrib-⊹ʳ : ∀ {A B C} {f g : B ⇒ C} {h : A ⇒ B} → (f ⊹ g) ∘ h ≈ (f ∘ h) ⊹ (g ∘ h)
    distrib-𝟎ˡ : ∀ {A B C} {g : B ⇒ C} → g ∘ 𝟎 ≈ 𝟎 {A} {C}
    distrib-𝟎ʳ : ∀ {A B C} {f : A ⇒ B} → 𝟎 ∘ f ≈ 𝟎 {A} {C}

  module monoid {A} {B} = IsMonoid (⊹-zero-isMonoid {A} {B})

  ⊹-identityˡ : ∀ {A B} {f : A ⇒ B} → 𝟎 ⊹ f ≈ f
  ⊹-identityˡ {f = f} = monoid.identityˡ f

  ⊹-identityʳ : ∀ {A B} {f : A ⇒ B} → f ⊹ 𝟎 ≈ f
  ⊹-identityʳ {f = f} = monoid.identityʳ f

  ⊹-assoc : ∀ {A B} {f g h : A ⇒ B} → (f ⊹ g) ⊹ h ≈ f ⊹ (g ⊹ h)
  ⊹-assoc {f = f} {g} {h} = monoid.assoc f g h
  
  ⊹-resp-≈  :  ∀ {A B} {f h g i : A ⇒ B} → f ≈ h → g ≈ i → f ⊹ g ≈ h ⊹ i
  ⊹-resp-≈ = monoid.∙-cong

record Preadditive : Set (levelOfTerm 𝒞) where
  infixl 6 _⊹_
  field
    _⊹_ : Op⇒₂
    𝟎 : Op⇒₀
    isPreadditive : IsPreadditive _⊹_ 𝟎
  open IsPreadditive isPreadditive public

-- A bicartesian category is cartesian and cocartesian
record Bicartesian : Set (levelOfTerm 𝒞) where
  field
    cartesian   : Cartesian
    cocartesian : Cocartesian
  open   Cartesian   cartesian public
  open Cocartesian cocartesian public

record IsBiproduct (bi : Bicartesian) (pre : Preadditive) (A B : Obj)
       : Set (levelOfTerm 𝒞) where
  open Bicartesian bi
  open Preadditive pre

  field
    +⇔× : A + B ≅ A × B

  module +⇔× = _≅_ +⇔×
  open +⇔×  -- privately

  from′ : A + B ⇒ A × B
  from′ = ⟨ [ id {A} , 𝟎 ] , [ 𝟎 , id ] ⟩
  -- [ ⟨ id , 𝟎 ⟩ , ⟨ 𝟎 , id ⟩ ]

  field
    from≈ : from ≈ from′

    from∘i₁≈ : from ∘ i₁ ≈ ⟨ id , 𝟎 ⟩
    from∘i₂≈ : from ∘ i₂ ≈ ⟨ 𝟎 , id ⟩

  π₁∘i₁ : π₁ ∘ from ∘ i₁ ≈ id
  π₁∘i₁ =
    begin
      π₁ ∘ from ∘ i₁  ≈⟨ ∘-resp-≈ʳ from∘i₁≈ ⟩
      π₁ ∘ ⟨ id , 𝟎 ⟩ ≈⟨ project₁ ⟩
      id              ∎

  π₁∘i₂ : π₁ ∘ from ∘ i₂ ≈ 𝟎
  π₁∘i₂ =
    begin
      π₁ ∘ from ∘ i₂  ≈⟨ ∘-resp-≈ʳ from∘i₂≈ ⟩
      π₁ ∘ ⟨ 𝟎 , id ⟩ ≈⟨ project₁ ⟩
      𝟎               ∎

  π₂∘i₁ : π₂ ∘ from ∘ i₁ ≈ 𝟎
  π₂∘i₁ =
    begin
      π₂ ∘ from ∘ i₁  ≈⟨ ∘-resp-≈ʳ from∘i₁≈ ⟩
      π₂ ∘ ⟨ id , 𝟎 ⟩ ≈⟨ project₂ ⟩
      𝟎               ∎

  π₂∘i₂ : π₂ ∘ from ∘ i₂ ≈ id
  π₂∘i₂ =
    begin
      π₂ ∘ from ∘ i₂  ≈⟨ ∘-resp-≈ʳ from∘i₂≈ ⟩
      π₂ ∘ ⟨ 𝟎 , id ⟩ ≈⟨ project₂ ⟩
      id              ∎

  -- A few more lemmas. I don't know which will be useful.

  π₁∘from≈ : π₁ ∘ from ≈ [ id , 𝟎 ]
  π₁∘from≈ = begin
               π₁ ∘ from                        ≈⟨ ∘-resp-≈ʳ from≈ ⟩
               π₁ ∘ ⟨ [ id , 𝟎 ] , [ 𝟎 , id ] ⟩ ≈⟨ project₁ ⟩
               [ id , 𝟎 ]                       ∎

  π₂∘from≈ : π₂ ∘ from ≈ [ 𝟎 , id ]
  π₂∘from≈ = begin
               π₂ ∘ from                        ≈⟨ ∘-resp-≈ʳ from≈ ⟩
               π₂ ∘ ⟨ [ id , 𝟎 ] , [ 𝟎 , id ] ⟩ ≈⟨ project₂ ⟩
               [ 𝟎 , id ]                       ∎

  π₁≈ : π₁ ≈ [ id , 𝟎 ] ∘ to
  π₁≈ = begin
          π₁               ≈˘⟨ cancelʳ isoʳ ⟩
          (π₁ ∘ from) ∘ to ≈⟨ ∘-resp-≈ˡ π₁∘from≈ ⟩
          [ id , 𝟎 ] ∘ to  ∎

  π₂≈ : π₂ ≈ [ 𝟎 , id ] ∘ to
  π₂≈ = begin
          π₂               ≈˘⟨ cancelʳ isoʳ ⟩
          (π₂ ∘ from) ∘ to ≈⟨ ∘-resp-≈ˡ π₂∘from≈ ⟩
          [ 𝟎 , id ] ∘ to  ∎

  i₁≈ : i₁ ≈ to ∘ ⟨ id , 𝟎 ⟩
  i₁≈ = begin
          i₁               ≈˘⟨ cancelˡ isoˡ ⟩
          to ∘ (from ∘ i₁) ≈⟨ ∘-resp-≈ʳ from∘i₁≈ ⟩
          to ∘ ⟨ id , 𝟎 ⟩  ∎

  i₂≈ : i₂ ≈ to ∘ ⟨ 𝟎 , id ⟩
  i₂≈ = begin
          i₂               ≈˘⟨ cancelˡ isoˡ ⟩
          to ∘ (from ∘ i₂) ≈⟨ ∘-resp-≈ʳ from∘i₂≈ ⟩
          to ∘ ⟨ 𝟎 , id ⟩  ∎

  -- []-bi : {f : A ⇒ C} {g : B ⇒ C} → [ f , g ] ≈ (f ∘ π₁ ⊹ g ∘ π₂) ∘ from
  -- []-bi {f = f} {g} =
  --   begin
  --     [ f , g ] ≈⟨ {!!} ⟩
  --     f ∘ π₁ ∘ from ⊹ g ∘ π₂ ∘ from  ≈⟨ ⊹-resp-≈ {!!} {!!}  ⟩
  --     (f ∘ π₁) ∘ from ⊹ (g ∘ π₂) ∘ from  ≈˘⟨ distrib-⊹ʳ ⟩
  --     (f ∘ π₁ ⊹ g ∘ π₂) ∘ from  ∎

-- A biproduct category is bicartesian, has a zero object, and compatible
-- products and coproducts.
record Biproduct : Set (levelOfTerm 𝒞) where
  field
    bicartesian : Bicartesian
    preadditive : Preadditive
    isBiproduct : ∀ {A B} → IsBiproduct bicartesian preadditive A B
  -- open Bicartesian bicartesian public
  -- open Preadditive preadditive public
  -- open IsBiproduct isBiproduct public

-- open Biproduct public

-- Use a cartesian and preadditive structure to define a cocartesian, and
-- biproduct.
record PreadditiveCartesian : Set (levelOfTerm 𝒞) where
  field
    cartesian : Cartesian
    preadditive : Preadditive
  open Cartesian   cartesian   public
  open Preadditive preadditive public
  field
    -- Extra help needed for the proofs
    unique-𝟎 : ∀ (f : ⊤ ⇒ A) → 𝟎 ≈ f
    ⟨⟩⊹⟨⟩ : ∀ {f h : A ⇒ B} {g i : A ⇒ C} → ⟨ f , g ⟩ ⊹ ⟨ h , i ⟩ ≈ ⟨ f ⊹ h , g ⊹ i ⟩

  cocartesian : Cocartesian
  cocartesian = record
    { initial = record
        { ⊥ = ⊤
        ; ⊥-is-initial = record
           { ! = 𝟎
           ; !-unique = unique-𝟎 
           }
        }
    ; coproducts = record
       { coproduct = λ {A B} → record
           { A+B = A × B
           ; i₁ = ⟨ id , 𝟎 ⟩
           ; i₂ = ⟨ 𝟎 , id ⟩
           ; [_,_] = λ {C} f g → f ∘ π₁ ⊹ g ∘ π₂
           ; inject₁ = λ {C} {f : A ⇒ C} {g : B ⇒ C} →
               begin
                 (f ∘ π₁ ⊹ g ∘ π₂) ∘ ⟨ id , 𝟎 ⟩
                   ≈⟨ distrib-⊹ʳ ⟩
                 (f ∘ π₁) ∘ ⟨ id , 𝟎 ⟩ ⊹ (g ∘ π₂) ∘ ⟨ id , 𝟎 ⟩
                   ≈⟨ ⊹-resp-≈ assoc assoc ⟩
                 f ∘ π₁ ∘ ⟨ id , 𝟎 ⟩ ⊹ g ∘ (π₂ ∘ ⟨ id , 𝟎 ⟩)
                   ≈⟨ ⊹-resp-≈ (∘-resp-≈ʳ project₁) (∘-resp-≈ʳ project₂) ⟩
                 f ∘ id ⊹ g ∘ 𝟎
                   ≈⟨ ⊹-resp-≈ identityʳ distrib-𝟎ˡ ⟩
                 f ⊹ 𝟎
                   ≈⟨ ⊹-identityʳ ⟩
                 f
                   ∎
           ; inject₂ = λ {C} {f : A ⇒ C} {g : B ⇒ C} →
               begin
                 (f ∘ π₁ ⊹ g ∘ π₂) ∘ ⟨ 𝟎 , id ⟩
                   ≈⟨ distrib-⊹ʳ ⟩
                 (f ∘ π₁) ∘ ⟨ 𝟎 , id ⟩ ⊹ (g ∘ π₂) ∘ ⟨ 𝟎 , id ⟩
                   ≈⟨ ⊹-resp-≈ assoc assoc ⟩
                 f ∘ π₁ ∘ ⟨ 𝟎 , id ⟩ ⊹ g ∘ (π₂ ∘ ⟨ 𝟎 , id ⟩)
                   ≈⟨ ⊹-resp-≈ (∘-resp-≈ʳ project₁) (∘-resp-≈ʳ project₂) ⟩
                 f ∘ 𝟎 ⊹ g ∘ id
                   ≈⟨ ⊹-resp-≈ distrib-𝟎ˡ identityʳ ⟩
                 𝟎 ⊹ g
                   ≈⟨ ⊹-identityˡ ⟩
                 g
                   ∎
           ; unique = λ {C} {h : A × B ⇒ C} {f : A ⇒ C} {g : B ⇒ C}
                        (eq₁ : h ∘ ⟨ id , 𝟎 ⟩ ≈ f) (eq₂ : h ∘ ⟨ 𝟎 , id ⟩ ≈ g) → 
               begin
                 f ∘ π₁ ⊹ g ∘ π₂
                   ≈⟨ ⊹-resp-≈ (∘-resp-≈ˡ (sym eq₁)) (∘-resp-≈ˡ (sym eq₂)) ⟩
                 (h ∘ ⟨ id , 𝟎 ⟩) ∘ π₁ ⊹ (h ∘ ⟨ 𝟎 , id ⟩) ∘ π₂
                   ≈⟨ ⊹-resp-≈ assoc assoc ⟩
                 h ∘ (⟨ id , 𝟎 ⟩ ∘ π₁) ⊹ h ∘ (⟨ 𝟎 , id ⟩ ∘ π₂)
                   ≈˘⟨ distrib-⊹ˡ ⟩
                 h ∘ ( ⟨ id , 𝟎 ⟩ ∘ π₁ ⊹ ⟨ 𝟎 , id ⟩ ∘ π₂)
                   ≈⟨ ∘-resp-≈ʳ (⊹-resp-≈ ⟨⟩∘ ⟨⟩∘) ⟩
                 h ∘ (⟨ id ∘ π₁ , 𝟎 ∘ π₁ ⟩ ⊹ ⟨ 𝟎 ∘ π₂ , id ∘ π₂ ⟩)
                   ≈⟨ ∘-resp-≈ʳ (⊹-resp-≈ (⟨⟩-cong₂ identityˡ distrib-𝟎ʳ)
                                          (⟨⟩-cong₂ distrib-𝟎ʳ identityˡ)) ⟩
                 h ∘ (⟨ π₁ , 𝟎 ⟩ ⊹ ⟨ 𝟎 , π₂ ⟩)
                   ≈⟨ ∘-resp-≈ʳ ⟨⟩⊹⟨⟩ ⟩
                 h ∘ ⟨ π₁ ⊹ 𝟎 , 𝟎 ⊹ π₂ ⟩
                   ≈⟨ ∘-resp-≈ʳ (⟨⟩-cong₂ ⊹-identityʳ ⊹-identityˡ) ⟩
                 h ∘ ⟨ π₁ , π₂ ⟩
                   ≈⟨ ∘-resp-≈ʳ η ⟩
                 h ∘ id
                   ≈⟨ identityʳ ⟩
                 h
                   ∎
           } }
    }

  open Cocartesian cocartesian public

  bicartesian : Bicartesian
  bicartesian = record { cartesian = cartesian ; cocartesian = cocartesian }

  biproduct : Biproduct
  biproduct = record
    { bicartesian = bicartesian
    ; preadditive = preadditive
    ; isBiproduct = λ {A B} → record
        { +⇔× = id≅
        ; from≈ = sym (
            begin
              ⟨ [ id , 𝟎 ] , [ 𝟎 , id ] ⟩
                ≡⟨⟩  -- [_,_] definition above
              ⟨ id ∘ π₁ ⊹ 𝟎 ∘ π₂ , 𝟎 ∘ π₁ ⊹ id ∘ π₂ ⟩
                ≈⟨ ⟨⟩-cong₂ (⊹-resp-≈ identityˡ distrib-𝟎ʳ)
                            (⊹-resp-≈ distrib-𝟎ʳ identityˡ) ⟩
              ⟨ π₁ ⊹ 𝟎 , 𝟎 ⊹ π₂ ⟩
                ≈⟨ ⟨⟩-cong₂ ⊹-identityʳ ⊹-identityˡ ⟩
              ⟨ π₁ , π₂ ⟩
                ≈⟨ η ⟩
              id
                ∎)
        ; from∘i₁≈ = identityˡ
        ; from∘i₂≈ = identityˡ
        }
    }

-- TODO: Define PreadditiveCocartesian that starts with a cocartesian. Use
-- duality, turning the cocartesian into a cartesian for the opposite category.
-- Similarly, dualize bicartesian to a bicartesian, and a biproduct to a
-- biproduct.


