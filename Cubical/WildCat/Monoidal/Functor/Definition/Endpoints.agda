open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Sigma renaming (_×_ to _×'_)
open import Cubical.WildCat.Base
open import Cubical.WildCat.Functor
open import Cubical.WildCat.Product
open import Cubical.WildCat.Product.Functor

open import Cubical.WildCat.Monoidal.Base
open import Cubical.WildCat.Monoidal.Definition.IsMonoidal
open import Cubical.WildCat.Monoidal.Functor.Definition.Structure

open import Cubical.WildCat.AsLU2C.Instances

module Cubical.WildCat.Monoidal.Functor.Definition.Endpoints
  {ℓC ℓC' ℓD ℓD' : Level}
  (MC : MonoidalWildCat ℓC ℓC')
  (MD : MonoidalWildCat ℓD ℓD') 
  (F : WildFunctor (MC .fst) (MD .fst))
  (mStr : MonoidalFunctorStr MC MD F) where

private
  module MC = isMonoidalWildCat (MC .snd)
  module MD = isMonoidalWildCat (MD .snd)
  module F = WildFunctor F
  module ⊗D = WildFunctor MD._⊗_
  C = MC .fst
  D = MD .fst

open NotWC C
open NotWC D
open MonoidalFunctorStr mStr
open WildNatTrans
open WildNatIso


private
  _⨾_ = comp-WildFunctor
  _⊗ᶜ₀_ = curry (MC._⊗_ .WildFunctor.F-ob)
  _⊗ᶜ₁_ = λ {x y} → curry (MC._⊗_ .WildFunctor.F-hom {x} {y})
  infix 50 _⊗ᶜ₀_ _⊗ᶜ₁_ _⊗ᵈ₁_ _⊗ᵈ₂_
  _⊗ᵈ₁_ = λ {x y} → curry (MD._⊗_ .WildFunctor.F-hom {x} {y})
  _⊗ᵈ₂_ = λ {x y : WildCat.ob D ×' WildCat.ob D}
    {f g : (D × D) [ x , y ]}
    (p : f .fst ≡ g .fst) (q : f .snd ≡ g .snd)
    → cong ⊗D.F-hom (≡-× p q)

open F using () renaming (F-ob to F₀; F-hom to F₁)
open WildNatTrans F-⊗ using ()
  renaming (N-ob to F-⊗₀; N-hom to F-⊗□)
open WildNatTrans (trans MC.⊗lUnit) using ()
  renaming (N-ob to ⊗lUᶜ₀; N-hom to ⊗lUᶜ□)
open WildNatTrans (trans MC.⊗rUnit) using ()
  renaming (N-ob to ⊗rUᶜ₀; N-hom to ⊗rUᶜ□)
open WildNatTrans (trans MC.⊗assoc) using ()
  renaming (N-ob to ⊗asᶜ₀; N-hom to ⊗asᶜ□)
open WildNatTrans (trans MD.⊗lUnit) using ()
  renaming (N-ob to ⊗lUᵈ₀; N-hom to ⊗lUᵈ□)
open WildNatTrans (trans MD.⊗rUnit) using ()
  renaming (N-ob to ⊗rUᵈ₀; N-hom to ⊗rUᵈ□)
open WildNatTrans (trans MD.⊗assoc) using ()
  renaming (N-ob to ⊗asᵈ₀; N-hom to ⊗asᵈ□)

-- In the schematic composites below, 1_F is the identity natural
-- transformation on F, and F-𝟙 is viewed as a constant transformation.

-- ((F-𝟙 ×₂ 1_F) ▹ MD._⊗_)
--   ⋆ ((Eₗ ◃ F-⊗) ⋆ (MC.⊗lUnit ▹ F))
-- where Eₗ(x) = (MC.𝟙 , x) and Eₗ(f) = (id , f).
F-⊗lUnitₗ : WildNatTrans C D (F ⨾ restrFunctorₗ MD._⊗_ MD.𝟙) F
F-⊗lUnitₗ .N-ob x =
  F-𝟙 ⊗ᵈ₁ id ⋆ (F-⊗₀ (MC.𝟙 , x) ⋆ F₁ (⊗lUᶜ₀ x))
F-⊗lUnitₗ .N-hom {x} {y} f =
  sym (⋆Assoc _ _ _)
  ∙ (sym (⊗D.F-seq (id , F₁ f) (F-𝟙 , id))
    ∙ ⋆IdL F-𝟙 ⊗ᵈ₂ ⋆IdR (F₁ f)
    ∙ sym (⋆IdR F-𝟙) ⊗ᵈ₂ sym (⋆IdL (F₁ f))
    ∙ (F-𝟙 ◃ sym F.F-id) ⊗ᵈ₂ refl
    ∙ ⊗D.F-seq (F-𝟙 , id) (F₁ id , F₁ f))
    ▹ (F-⊗₀ (MC.𝟙 , y) ⋆ F₁ (⊗lUᶜ₀ y))
  ∙ ⋆Assoc _ _ _
  ∙ F-𝟙 ⊗ᵈ₁ id ◃ (sym (⋆Assoc _ _ _)
    ∙ F-⊗□ (id , f) ▹ F₁ (⊗lUᶜ₀ y)
    ∙ ⋆Assoc _ _ _
    ∙ F-⊗₀ (MC.𝟙 , x) ◃ (sym (F.F-seq (id ⊗ᶜ₁ f) (⊗lUᶜ₀ y))
      ∙ cong F₁ (⊗lUᶜ□ f)
      ∙ F.F-seq (⊗lUᶜ₀ x) f)
    ∙ sym (⋆Assoc _ _ _))
  ∙ sym (⋆Assoc _ _ _)

-- F ◃ MD.⊗lUnit
F-⊗lUnitᵣ : WildNatTrans C D (F ⨾ restrFunctorₗ MD._⊗_ MD.𝟙) F
F-⊗lUnitᵣ .N-ob x = ⊗lUᵈ₀ (F₀ x)
F-⊗lUnitᵣ .N-hom f = ⊗lUᵈ□ (F₁ f)

-- ((1_F ×₂ F-𝟙) ▹ MD._⊗_)
--   ⋆ ((Eᵣ ◃ F-⊗) ⋆ (MC.⊗rUnit ▹ F))
-- where Eᵣ(x) = (x , MC.𝟙) and Eᵣ(f) = (f , id).
F-⊗rUnitₗ : WildNatTrans C D (F ⨾ restrFunctorᵣ MD._⊗_ MD.𝟙) F
F-⊗rUnitₗ .N-ob x =
  id ⊗ᵈ₁ F-𝟙 ⋆ (F-⊗₀ (x , MC.𝟙) ⋆ F₁ (⊗rUᶜ₀ x))
F-⊗rUnitₗ .N-hom {x} {y} f =
  sym (⋆Assoc _ _ _)
  ∙ (sym (⊗D.F-seq (F₁ f , id) (id , F-𝟙))
    ∙ ⋆IdR (F₁ f) ⊗ᵈ₂ ⋆IdL F-𝟙
    ∙ sym (⋆IdL (F₁ f)) ⊗ᵈ₂ sym (⋆IdR F-𝟙)
    ∙ refl ⊗ᵈ₂ (F-𝟙 ◃ sym F.F-id)
    ∙ ⊗D.F-seq (id , F-𝟙) (F₁ f , F₁ id))
    ▹ (F-⊗₀ (y , MC.𝟙) ⋆ F₁ (⊗rUᶜ₀ y))
  ∙ ⋆Assoc _ _ _
  ∙ id ⊗ᵈ₁ F-𝟙 ◃ (sym (⋆Assoc _ _ _)
    ∙ F-⊗□ (f , id) ▹ F₁ (⊗rUᶜ₀ y)
    ∙ ⋆Assoc _ _ _
    ∙ F-⊗₀ (x , MC.𝟙) ◃ (sym (F.F-seq (f ⊗ᶜ₁ id) (⊗rUᶜ₀ y))
      ∙ cong F₁ (⊗rUᶜ□ f)
      ∙ F.F-seq (⊗rUᶜ₀ x) f)
    ∙ sym (⋆Assoc _ _ _))
  ∙ sym (⋆Assoc _ _ _)

-- F ◃ MD.⊗rUnit
F-⊗rUnitᵣ : WildNatTrans C D (F ⨾ restrFunctorᵣ MD._⊗_ MD.𝟙) F
F-⊗rUnitᵣ .N-ob x = ⊗rUᵈ₀ (F₀ x)
F-⊗rUnitᵣ .N-hom f = ⊗rUᵈ□ (F₁ f)

F-⊗assoc-source F-⊗assoc-target : WildFunctor (C × (C × C)) D
F-⊗assoc-source = (F ×₁ (F ×₁ F)) ⨾ assocₗ MD._⊗_
F-⊗assoc-target = assocᵣ MC._⊗_ ⨾ F

-- ((F ×₁ (F ×₁ F)) ◃ MD.⊗assoc)
--   ⋆ ((Q ◃ ((F-⊗ ×₂ 1_F) ▹ MD._⊗_)) ⋆ (P ◃ F-⊗))
-- where Q = ProdAssoc and P = ProdAssoc ⨾ (MC._⊗_ ×₁ idWildFunctor C).
F-⊗assocₗ : WildNatTrans (C × (C × C)) D F-⊗assoc-source F-⊗assoc-target
F-⊗assocₗ .N-ob (x , y , z) =
  ⊗asᵈ₀ (F₀ x , F₀ y , F₀ z)
    ⋆ (F-⊗₀ (x , y) ⊗ᵈ₁ id ⋆ F-⊗₀ (x ⊗ᶜ₀ y , z))
F-⊗assocₗ .N-hom {(x , y , z)} {(x′ , y′ , z′)} (f , g , h) =
  sym (⋆Assoc _ _ _)
  ∙ ⊗asᵈ□ (F₁ f , F₁ g , F₁ h)
    ▹ (F-⊗₀ (x′ , y′) ⊗ᵈ₁ id ⋆ F-⊗₀ (x′ ⊗ᶜ₀ y′ , z′))
  ∙ ⋆Assoc _ _ _
  ∙ ⊗asᵈ₀ (F₀ x , F₀ y , F₀ z) ◃ (sym (⋆Assoc _ _ _)
    ∙ (sym (⊗D.F-seq (F₁ f ⊗ᵈ₁ F₁ g , F₁ h) (F-⊗₀ (x′ , y′) , id))
      ∙ refl ⊗ᵈ₂ ⋆IdR (F₁ h)
      ∙ F-⊗□ (f , g) ⊗ᵈ₂ sym (⋆IdL (F₁ h))
      ∙ ⊗D.F-seq (F-⊗₀ (x , y) , id) (F₁ (f ⊗ᶜ₁ g) , F₁ h))
      ▹ F-⊗₀ (x′ ⊗ᶜ₀ y′ , z′)
    ∙ ⋆Assoc _ _ _
    ∙ F-⊗₀ (x , y) ⊗ᵈ₁ id ◃ F-⊗□ (f ⊗ᶜ₁ g , h)
    ∙ sym (⋆Assoc _ _ _))
  ∙ sym (⋆Assoc _ _ _)

-- ((1_F ×₂ F-⊗) ▹ MD._⊗_)
--   ⋆ (((idWildFunctor C ×₁ MC._⊗_) ◃ F-⊗) ⋆ (MC.⊗assoc ▹ F))
F-⊗assocᵣ : WildNatTrans (C × (C × C)) D F-⊗assoc-source F-⊗assoc-target
F-⊗assocᵣ .N-ob (x , y , z) =
  id ⊗ᵈ₁ F-⊗₀ (y , z)
    ⋆ (F-⊗₀ (x , y ⊗ᶜ₀ z) ⋆ F₁ (⊗asᶜ₀ (x , y , z)))
F-⊗assocᵣ .N-hom {(x , y , z)} {(x′ , y′ , z′)} (f , g , h) =
  sym (⋆Assoc _ _ _)
  ∙ (sym (⊗D.F-seq (F₁ f , F₁ g ⊗ᵈ₁ F₁ h) (id , F-⊗₀ (y′ , z′)))
    ∙ ⋆IdR (F₁ f) ⊗ᵈ₂ refl
    ∙ sym (⋆IdL (F₁ f)) ⊗ᵈ₂ F-⊗□ (g , h)
    ∙ ⊗D.F-seq (id , F-⊗₀ (y , z)) (F₁ f , F₁ (g ⊗ᶜ₁ h)))
    ▹ (F-⊗₀ (x′ , y′ ⊗ᶜ₀ z′) ⋆ F₁ (⊗asᶜ₀ (x′ , y′ , z′)))
  ∙ ⋆Assoc _ _ _
  ∙ id ⊗ᵈ₁ F-⊗₀ (y , z) ◃ (sym (⋆Assoc _ _ _)
    ∙ F-⊗□ (f , g ⊗ᶜ₁ h) ▹ F₁ (⊗asᶜ₀ (x′ , y′ , z′))
    ∙ ⋆Assoc _ _ _
    ∙ F-⊗₀ (x , y ⊗ᶜ₀ z) ◃ (sym (F.F-seq (f ⊗ᶜ₁ (g ⊗ᶜ₁ h)) (⊗asᶜ₀ (x′ , y′ , z′)))
      ∙ cong F₁ (⊗asᶜ□ (f , g , h))
      ∙ F.F-seq (⊗asᶜ₀ (x , y , z)) ((f ⊗ᶜ₁ g) ⊗ᶜ₁ h))
    ∙ sym (⋆Assoc _ _ _))
  ∙ sym (⋆Assoc _ _ _)
