{-# OPTIONS --without-K --safe #-}

-- Algebraic categories via homomorphisms and SubCat structures

open import Level

module AlgebraicCats (c ℓ : Level) where

open import Algebra.Bundles
open import Algebra.Module.Bundles

open import Categories.Category.Core

private variable r ℓr s ℓs : Level

module _ where
  open import Categories.Category.Instance.Setoids using (Setoids)
  open import Category.Sub (Setoids c ℓ) as Sub using (_∩_; ⋂) -- renaming (SubCat.SubCategory to ⟨_⟩)
  open Sub.SubCat renaming (SubCategory to ⟨_⟩)
  import Category.Homomorphisms as H

  -- Temporarily comment out most categories to speed up reloading
{-
  Magmas          = ⟨ H₂ _∙_                    ⟩ where open Magma          ; open H setoid
  Monoids         = ⟨ H₂ _∙_ ∩ H₀ ε             ⟩ where open Monoid         ; open H setoid
  Groups          = ⟨ H₂ _∙_ ∩ H₀ ε ∩ H₁ _⁻¹    ⟩ where open Group          ; open H setoid
  Lattices        = ⟨ H₂ _∨_ ∩ H₂ _∧_           ⟩ where open Lattice        ; open H setoid
  NearSemirings   = ⟨ H₂ _*_ ∩ H₂ _+_ ∩ H₀ 0#   ⟩ where open NearSemiring   ; open H setoid
  Rings           = ⟨ H₂ _*_ ∩ H₂ _+_ ∩ H₁ (-_) ⟩ where open Ring           ; open H setoid
  BooleanAlgebras = ⟨ H₂ _∨_ ∩ H₂ _∧_ ∩ H₁ ¬_   ⟩ where open BooleanAlgebra ; open H setoid
 -}

  SemiringWithoutAnnihilatingZeros = ⟨ H₂ _*_ ∩ H₂ _+_ ∩ H₀ 0# ∩ H₀ 1# ⟩
    where open SemiringWithoutAnnihilatingZero ; open H setoid

  module _ (R : Semiring r ℓr) where
    open Semiring R
    LeftSemimodules = ⟨ H₂ _+ᴹ_ ∩ H₀ 0ᴹ ∩ Hₗ _*ₗ_ ⟩
      where open LeftSemimodule {semiring = R} ; open H ≈ᴹ-setoid ; open Action Carrier
{-
    RightSemimodules = ⟨ H₂ _+ᴹ_ ∩ H₀ 0ᴹ ∩ Hᵣ _*ᵣ_ ⟩
      where open RightSemimodule {semiring = R} ; open H ≈ᴹ-setoid ; open Action Carrier

  module _ (R : Ring r ℓr) where
    open Ring R
    LeftModules  = ⟨ H₂ _+ᴹ_ ∩ H₀ 0ᴹ ∩ Hₗ _*ₗ_ ⟩
      where open LeftModule  {ring = R} ; open H ≈ᴹ-setoid ; open Action Carrier
    RightModules = ⟨ H₂ _+ᴹ_ ∩ H₀ 0ᴹ ∩ Hᵣ _*ᵣ_ ⟩
      where open RightModule {ring = R} ; open H ≈ᴹ-setoid ; open Action Carrier

  module _ (R : Semiring r ℓr) (S : Semiring s ℓs) where
    open Semiring R renaming (Carrier to setoidₗ)
    open Semiring S renaming (Carrier to setoidᵣ)
    Bisemimodules = ⟨ H₂ _+ᴹ_ ∩ H₀ 0ᴹ ∩ Hₗ _*ₗ_ ∩ Hᵣ _*ᵣ_ ⟩
      where open Bisemimodule {R-semiring = R} {S-semiring = S} ; open H ≈ᴹ-setoid
            open Action setoidₗ using (Hₗ)
            open Action setoidᵣ using (Hᵣ)

  module _ (R : Ring r ℓr) (S : Ring s ℓs) where
    open Ring R renaming (Carrier to setoidₗ)
    open Ring S renaming (Carrier to setoidᵣ)
    Bimodules = ⟨ H₂ _+ᴹ_ ∩ H₀ 0ᴹ ∩ Hₗ _*ₗ_ ∩ Hᵣ _*ᵣ_ ⟩
      where open Bimodule {R-ring = R} {S-ring = S} ; open H ≈ᴹ-setoid
            open Action setoidₗ using (Hₗ)
            open Action setoidᵣ using (Hᵣ)

  module _ (R : CommutativeSemiring r ℓr) where
    open CommutativeSemiring R
    Semimodules = ⟨ H₂ _+ᴹ_ ∩ H₀ 0ᴹ ∩ Hₗ _*ₗ_ ∩ Hᵣ _*ᵣ_ ⟩
      where open Semimodule {commutativeSemiring = R} ; open H ≈ᴹ-setoid
            open Action Carrier

  module _ (R : CommutativeRing r ℓr) where
    open CommutativeRing R
    Modules = ⟨ H₂ _+ᴹ_ ∩ H₀ 0ᴹ ∩ Hₗ _*ₗ_ ∩ Hᵣ _*ᵣ_ ⟩
      where open Module {commutativeRing = R} ; open H ≈ᴹ-setoid ; open Action Carrier
-}

module _ where
  open import Category.Sub using () renaming (FullSubCategory to _⇰_)
 
{-
  Semigroups                     = Magmas        ⇰ Semigroup.magma
  Bands                          = Magmas        ⇰ Band.magma
  CommutativeSemigroups          = Magmas        ⇰ CommutativeSemigroup.magma
  Semilattices                   = Magmas        ⇰ Semilattice.magma
  SelectiveMagmas                = Magmas        ⇰ SelectiveMagma.magma
  CommutativeMonoids             = Monoids       ⇰ CommutativeMonoid.monoid
  BoundedLattices                = Monoids       ⇰ BoundedLattice.monoid
  IdempotentCommutativeMonoids   = Monoids       ⇰ IdempotentCommutativeMonoid.monoid
  AbelianGroups                  = Groups        ⇰ AbelianGroup.group
  DistributiveLattices           = Lattices      ⇰ DistributiveLattice.lattice
  SemiringWithoutOnes            = NearSemirings ⇰ SemiringWithoutOne.nearSemiring
  CommutativeSemiringWithoutOnes = NearSemirings ⇰ CommutativeSemiringWithoutOne.nearSemiring
  CommutativeRings               = Rings         ⇰ CommutativeRing.ring
-}

  Semirings = SemiringWithoutAnnihilatingZeros ⇰ Semiring.semiringWithoutAnnihilatingZero
  CommutativeSemirings = SemiringWithoutAnnihilatingZeros
                           ⇰ CommutativeSemiring.semiringWithoutAnnihilatingZero


-------------------------------------------------------------------------------
-- | Cartesian categories. Start with a few, and then generalize.
-------------------------------------------------------------------------------

module _ (R : Semiring r ℓr) where
  open Semiring R using (Carrier)
  -- open import Function using (const)
  open import Data.Unit.Polymorphic
  open import Data.Product using (_,_)
  open import Relation.Binary.Bundles using (Setoid)
  import Algebra.Module.Construct.Zero as Z
  import Algebra.Module.Construct.DirectProduct    as P

  open import Categories.Category.Cartesian
  open import Categories.Category.Monoidal.Instance.Setoids
  open import Categories.Category.Instance.Setoids using (Setoids)

  open import Category.Sub (Setoids c ℓ) using (_∩_; ⋂)
  open import Cartesian.Sub (Setoids-CartesianCategory c ℓ) as Sub hiding (_∩_)
  open Sub.SubCart using (SubCartesian)
  import Category.Homomorphisms as H
  open import Misc
  
  setoid = LeftSemimodule.≈ᴹ-setoid {semiring = R}
  lsm = LeftSemimodules R

  open import Relation.Binary.PropositionalEquality using (_≡_)
  LeftSemimodule-CartOps : Ops setoid
  LeftSemimodule-CartOps = record 
    { ⊤ᴵ = Z.leftSemimodule
    ; ⊤≡ = refl
    ; _×ᴵ_ = P.leftSemimodule
    ; ×≡ = refl
    } where open _≡_

  LeftSemimodules-Cartesian : Cartesian lsm
  LeftSemimodules-Cartesian = SubCartesian {ops = LeftSemimodule-CartOps} record
    { subCat = subCat
    ; R! = (λ _ _ → tt) , tt , (λ _ _ → tt)
    ; Rπ₁ = λ {a₁ a₂} → let open Setoid (≈ᴹ-setoid a₁) in
                          (λ _ _ → refl) , refl , (λ _ _ → refl)
    ; Rπ₂ = λ {a₁ a₂} → let open Setoid (≈ᴹ-setoid a₂) in
                          (λ _ _ → refl) , refl , (λ _ _ → refl)
    ; R⟨_,_⟩ = λ (_+₁_ , 0₁ , _*₁_) (_+₂_ , 0₂ , _*₂_) →
                 (λ x y → x +₁ y , x +₂ y) , (0₁ , 0₂) , (λ s x → s *₁ x , s *₂ x)
    } where
        open LeftSemimodule {semiring = R} ; open H ≈ᴹ-setoid ; open Action Carrier
        subCat = H₂ _+ᴹ_ ∩ H₀ 0ᴹ ∩ Hₗ _*ₗ_

  -- For Cocartesian, Bicartesian, and Biproduct, use the Cartesian-to-Biproduct
  -- construction.

  open import Categories.Category.Cocartesian 
  open import Categories.Object.Initial

  open import Function.Equality
  open import Relation.Binary.Reasoning.MultiSetoid

  open import Biproduct lsm
  open LeftSemimodule using (≈ᴹ-sym; ≈ᴹ-refl)

  LSM-Preadditive : Preadditive
  LSM-Preadditive = record
    { _⊹_ = λ {A B} (f′ , f+ , f0 , f*) (g′ , g+ , g0 , g*) →
       let open Π f′ renaming (_⟨$⟩_ to f ; cong to f-cong)
           open Π g′ renaming (_⟨$⟩_ to g ; cong to g-cong)
           module A = LeftSemimodule A
           module B = LeftSemimodule B
       in record
         { _⟨$⟩_ = λ x → f x B.+ᴹ g x
         ; cong = λ {x y} x≈y →
             begin⟨ B.≈ᴹ-setoid ⟩
               f x B.+ᴹ g x  ≈⟨ B.+ᴹ-cong (f-cong x≈y) (g-cong x≈y) ⟩
               f y B.+ᴹ g y  ∎
         }
        , (λ x y →
             -- (f + g) (x+y) ≈ (f + g) x + (f + g) y
             begin⟨ B.≈ᴹ-setoid ⟩
               f (x A.+ᴹ y) B.+ᴹ g (x A.+ᴹ y)
                 ≈⟨ B.+ᴹ-cong (f+ x y) (g+ x y) ⟩
               (f x B.+ᴹ f y) B.+ᴹ (g x B.+ᴹ g y)
                 ≈˘⟨ B.+ᴹ-assoc (f x B.+ᴹ f y) (g x) (g y) ⟩
               ((f x B.+ᴹ f y) B.+ᴹ g x) B.+ᴹ g y
                 ≈⟨ B.+ᴹ-congʳ (B.+ᴹ-assoc (f x) (f y) (g x)) ⟩
               (f x B.+ᴹ (f y B.+ᴹ g x)) B.+ᴹ g y
                 -- The only use of commutativity!
                 ≈⟨ B.+ᴹ-congʳ (B.+ᴹ-congˡ (B.+ᴹ-comm (f y) (g x))) ⟩
               (f x B.+ᴹ (g x B.+ᴹ f y)) B.+ᴹ g y
                 ≈˘⟨ B.+ᴹ-congʳ (B.+ᴹ-assoc (f x) (g x) (f y)) ⟩
               ((f x B.+ᴹ g x) B.+ᴹ f y) B.+ᴹ g y
                 ≈⟨ B.+ᴹ-assoc (f x B.+ᴹ g x) (f y) (g y) ⟩
               (f x B.+ᴹ g x) B.+ᴹ (f y B.+ᴹ g y)
                 ∎ )
          , ( -- (f + g) 0 ≈ 0
             begin⟨ B.≈ᴹ-setoid ⟩
              f A.0ᴹ B.+ᴹ g A.0ᴹ ≈⟨ B.+ᴹ-cong f0 g0 ⟩
              B.0ᴹ B.+ᴹ B.0ᴹ     ≈⟨ B.+ᴹ-identityʳ B.0ᴹ ⟩
              B.0ᴹ               ∎)
          , ( -- (f + g) (s *ₗ x) ≈ s *ₗ (f + g) x
             λ s x →
               begin⟨ B.≈ᴹ-setoid ⟩
                 f (s A.*ₗ x) B.+ᴹ g (s A.*ₗ x)
                   ≈⟨ B.+ᴹ-cong (f* s x) (g* s x) ⟩
                 s B.*ₗ f x B.+ᴹ s B.*ₗ g x
                   ≈˘⟨ B.*ₗ-distribˡ s (f x) (g x) ⟩
                 s B.*ₗ (f x B.+ᴹ g x)
                   ∎)
    ; 𝟎 = λ {A B} → let module B = LeftSemimodule B in
          const B.0ᴹ
        , (λ x y → B.≈ᴹ-sym (B.+ᴹ-identityʳ B.0ᴹ))
        , B.≈ᴹ-refl
        , (λ s x → B.≈ᴹ-sym (B.*ₗ-zeroʳ s))
    ; isPreadditive = record
        { ⊹-zero-isMonoid = λ {A B} → let module A = LeftSemimodule A
                                          module B = LeftSemimodule B
                                      in record  
           { isSemigroup = record
              { isMagma = record
                 { isEquivalence = Category.equiv lsm {A}{B}
                 ; ∙-cong = λ f≈g h≈i x≈y → B.+ᴹ-cong (f≈g x≈y) (h≈i x≈y)
                 }
              ; assoc = λ (f′ , _) (g′ , _) (h′ , _) → λ {x y} x≈y →
                  let open Π f′ renaming (_⟨$⟩_ to f ; cong to f-cong)
                      open Π g′ renaming (_⟨$⟩_ to g ; cong to g-cong)
                      open Π h′ renaming (_⟨$⟩_ to h ; cong to h-cong)
                  in
                    begin⟨ B.≈ᴹ-setoid ⟩
                      (f x B.+ᴹ g x) B.+ᴹ h x ≈⟨ B.+ᴹ-assoc (f x) (g x) (h x)⟩
                      f x B.+ᴹ (g x B.+ᴹ h x) ≈⟨ B.+ᴹ-cong (f-cong x≈y)
                                                   (B.+ᴹ-cong (g-cong x≈y)
                                                              (h-cong x≈y)) ⟩
                      f y B.+ᴹ (g y B.+ᴹ h y) ∎
              }
           ; identity = (λ (f′ , _) {x y} x≈y →
                            let open Π f′ renaming (_⟨$⟩_ to f; cong to f-cong) in
                            begin⟨ B.≈ᴹ-setoid ⟩
                              B.0ᴹ B.+ᴹ f x ≈⟨ B.+ᴹ-identityˡ (f x) ⟩
                              f x ≈⟨ f-cong x≈y ⟩
                              f y  ∎)
                      , (λ (f′ , _) {x y} x≈y →
                            let open Π f′ renaming (_⟨$⟩_ to f; cong to f-cong) in
                            begin⟨ B.≈ᴹ-setoid ⟩
                              f x B.+ᴹ B.0ᴹ ≈⟨ B.+ᴹ-identityʳ (f x) ⟩
                              f x ≈⟨ f-cong x≈y ⟩
                              f y  ∎)
           }
        -- distrib-⊹ˡ : ∀ {A B C} {f g : A ⇒ B} {h : B ⇒ C} → h ∘ (f ⊹ g) ≈ (h ∘ f) ⊹ (h ∘ g)
        ; distrib-⊹ˡ = λ {A B C} {(f′ , _) (g′ , _) (h′ , h+ , _)} {x y} x≈y →
            let module B = LeftSemimodule B
                module C = LeftSemimodule C
                open Π f′ renaming (_⟨$⟩_ to f ; cong to f-cong)
                open Π g′ renaming (_⟨$⟩_ to g ; cong to g-cong)
                open Π h′ renaming (_⟨$⟩_ to h ; cong to h-cong)
            in
            begin⟨ C.≈ᴹ-setoid ⟩
              h (f x B.+ᴹ g x)     ≈⟨ h+ (f x) (g x) ⟩
              h (f x) C.+ᴹ h (g x) ≈⟨ C.+ᴹ-cong (h-cong (f-cong x≈y))
                                                (h-cong (g-cong x≈y)) ⟩
              h (f y) C.+ᴹ h (g y) ∎
        -- distrib-⊹ʳ : ∀ {A B C} {f g : B ⇒ C} {h : A ⇒ B} → (f ⊹ g) ∘ h ≈ (f ∘ h) ⊹ (g ∘ h)
        ; distrib-⊹ʳ = λ {A B C} {(f′ , _) (g′ , _) (h′ , _)} {x y} x≈y →
            let module C = LeftSemimodule C
                open Π f′ renaming (_⟨$⟩_ to f ; cong to f-cong)
                open Π g′ renaming (_⟨$⟩_ to g ; cong to g-cong)
                open Π h′ renaming (_⟨$⟩_ to h ; cong to h-cong)
            in
            begin⟨ C.≈ᴹ-setoid ⟩
              f (h x) C.+ᴹ g (h x) ≈⟨ C.+ᴹ-cong (f-cong (h-cong x≈y))
                                                (g-cong (h-cong x≈y)) ⟩
              f (h y) C.+ᴹ g (h y) ∎
        -- distrib-𝟎ˡ : ∀ {A B C} {g : B ⇒ C} → g ∘ 𝟎 ≈ 𝟎 {A} {C}
        ; distrib-𝟎ˡ = λ {A B C} {(_ , _ , g0 , _)} x≈y → g0
        -- distrib-𝟎ʳ : ∀ {A B C} {f : A ⇒ B} → 𝟎 ∘ f ≈ 𝟎 {A} {C}
        ; distrib-𝟎ʳ = λ {A B C} x≈y → ≈ᴹ-refl C
        }
    }
  
  LeftSemimodules-PreadditiveCartesian : PreadditiveCartesian
  LeftSemimodules-PreadditiveCartesian = record
    { cartesian = LeftSemimodules-Cartesian
    ; preadditive = LSM-Preadditive
    -- unique-𝟎 : ∀ (f : ⊤ ⇒ A) → 𝟎 ≈ f
    ; unique-𝟎 = λ {A} (f′ , _ , f0 , _) {x y} x≈y → ≈ᴹ-sym A f0
    -- ⟨⟩⊹⟨⟩ : ∀ {(f h : A ⇒ B} {g i : A ⇒ C} → ⟨ f , g ⟩ ⊹ ⟨ h , i ⟩ ≈ ⟨ f ⊹ h , g ⊹ i ⟩
    ; ⟨⟩⊹⟨⟩ = λ {A B C} {(f′  , _) (h′  , _) (g′  , _) (i′  , _)} {x y} x≈y →
       let B×C = P.leftSemimodule B C
           module B   = LeftSemimodule B
           module C   = LeftSemimodule C
           module B×C = LeftSemimodule B×C
           open Π f′ renaming (_⟨$⟩_ to f ; cong to f-cong)
           open Π g′ renaming (_⟨$⟩_ to g ; cong to g-cong)
           open Π h′ renaming (_⟨$⟩_ to h ; cong to h-cong)
           open Π i′ renaming (_⟨$⟩_ to i ; cong to i-cong)
       in
         begin⟨ B×C.≈ᴹ-setoid ⟩
           f x B.+ᴹ h x , g x C.+ᴹ i x
             ≈⟨ B.+ᴹ-cong (f-cong x≈y) (h-cong x≈y)
              , C.+ᴹ-cong (g-cong x≈y) (i-cong x≈y) ⟩
           f y B.+ᴹ h y , g y C.+ᴹ i y ∎
    }

-- TODO: eliminate the redundant SubCat construction and associated imports.
-- Return to the style of Old.Algebraic2
        
