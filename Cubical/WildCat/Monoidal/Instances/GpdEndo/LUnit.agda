open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Path
open import Cubical.Functions.FunExtEquiv

open import Cubical.WildCat.Base hiding (_[_,_])
open import Cubical.WildCat.Functor hiding (_$_)
open import Cubical.WildCat.NaturalTransformation.Base

module Cubical.WildCat.Monoidal.Instances.GpdEndo.LUnit 
  (ℓ : Level) where

open import Cubical.Bicategory.Base
open import Cubical.Bicategory.Copresheaf.EndoConstructions ℓ
open import Cubical.Bicategory.Copresheaf ℓ
open import Cubical.Bicategory.Instances.Copresheaf ℓ

open import Prelude.Reassoc
open import Prelude.ExtraGpdLaws

open BicatSyntax {{...}}

private
  _⊗₀_ = compEndo₀
  _⊗₁_ = compEndo₁
  GpdEndoBicat = CopshBicat GPD

module _ (F : GpdEndo) where
  open WildNatTrans
  open IsPseudonat

  private module F = Copresheaf F

  iMG-lUnit-ob : PseudonatTrans (idEndo ⊗₀ F) F
  iMG-lUnit-ob .fst .N-ob X = idfun _
  iMG-lUnit-ob .fst .N-hom f = refl
  iMG-lUnit-ob .snd .N-hom-id = refl
  iMG-lUnit-ob .snd .N-hom-seq f g = 
      reassoc 
        (refl′ ∙′ ↑ F.F-seq f g)
        ((refl′ ∙′ ↑ F.F-seq f g) ∙′ refl′ ∙′ refl′)
        refl

module _ {F G : GpdEndo} (α : PseudonatTrans F G) where

  open Bicategory GPD using () renaming (str to ⟨GPD⟩)

  open BicatSynInstBC GPD
  open BicatSynInstBC GpdEndoBicat
  
  open WildNatTrans (α .fst) using ()
    renaming (N-ob to α₀; N-hom to α□)

  private
    λ₀ = iMG-lUnit-ob
    module F = Copresheaf F
    module G = Copresheaf G

  open BicatReassoc ⟨GPD⟩

  iMG-lUnit-hom : (idPseudonatTrans idEndo ⊗₁ α) ⋆ λ₀ G ≡ λ₀ F ⋆ α
  iMG-lUnit-hom = PseudonatTrans≡ $ makeNatTransPath 
    (funExt λ X → F.F-id ▹ α₀ X) 
    λ f → aux f
    where
    aux : 
      ∀ {x y} (f : GPD [ x , y ])
      → Square
        (((sym (F.F-seq f id) ∙ refl ∙ F.F-seq id f) ▹ α₀ y
            ∙ F.F₁ id ◃ α□ f) 
          ∙ refl)
        (refl ∙ α□ f)
        (F.F₁ f ◃ F.F-id ▹ α₀ y)
        (F.F-id ▹ α₀ x ▹ G.F₁ f)
    aux {x} {y} f = compPath→Square aux'
      where
      aux' :
        F.F₁ f ◃ F.F-id ▹ α₀ y
        ∙ refl ∙ α□ f
        ≡ (((sym (F.F-seq f id) ∙ refl ∙ F.F-seq id f) ▹ α₀ y
            ∙ F.F₁ id ◃ α□ f) 
          ∙ refl)
        ∙ F.F-id ▹ α₀ x ▹ G.F₁ f
      aux' =
          F.F₁ f ◃ F.F-id ▹ α₀ y
          ∙ refl ∙ α□ f
        ≡⟨ ∙r cong (_▹ α₀ y) (sym (invUniq (F.F-IdR f))) ⟩
          sym (F.F-seq f id) ▹ α₀ y
          ∙ refl ∙ α□ f
        ≡⟨ ∙l ∙r cong (_▹ α₀ y) (sym (F.F-IdL f)) ⟩
          sym (F.F-seq f id) ▹ α₀ y
          ∙ (F.F-seq id f
            ∙ F.F-id ▹ F.F₁ f) ▹ α₀ y
          ∙ α□ f
        ≡⟨ reass₁ ⟩
          sym (F.F-seq f id) ▹ α₀ y
          ∙ F.F-seq id f ▹ α₀ y
          ∙ (F.F-id ▹ F.F₁ f ▹ α₀ y
            ∙ α□ f)
        ≡⟨ ∙l ∙l sym (whisk-interchange (F.F-id {x = x}) (α□ f)) ⟩
          sym (F.F-seq f id) ▹ α₀ y
          ∙ F.F-seq id f ▹ α₀ y
          ∙ (F.F₁ id ◃ α□ f
            ∙ F.F-id ▹ α₀ x ▹ G.F₁ f)
        ≡⟨ reass₂ ⟩
          (((sym (F.F-seq f id) ∙ refl ∙ F.F-seq id f) ▹ α₀ y
              ∙ F.F₁ id ◃ α□ f)
            ∙ refl)
          ∙ F.F-id ▹ α₀ x ▹ G.F₁ f
        ∎
        where
        reass₁ = reassoc
          ( ↑ sym (F.F-seq f id) ▹′ α₀ y
          ∙′ (↑ F.F-seq id f ∙′ ↑ (F.F-id {x = x}) ▹′ F.F₁ f) ▹′ α₀ y
          ∙′ ↑ α□ f )
          ( ↑ sym (F.F-seq f id) ▹′ α₀ y
          ∙′ ↑ F.F-seq id f ▹′ α₀ y
          ∙′ (↑ (F.F-id {x = x}) ▹′ F.F₁ f ▹′ α₀ y
            ∙′ ↑ α□ f) )
          refl
        reass₂ = reassoc
          ( ↑ sym (F.F-seq f id) ▹′ α₀ y
          ∙′ ↑ F.F-seq id f ▹′ α₀ y
          ∙′ (F.F₁ id ◃′ ↑ α□ f
            ∙′ ↑ (F.F-id {x = x}) ▹′ α₀ x ▹′ G.F₁ f) )
          ( (((↑ sym (F.F-seq f id) ∙′ refl′ ∙′ ↑ F.F-seq id f) ▹′ α₀ y
              ∙′ F.F₁ id ◃′ ↑ α□ f)
            ∙′ refl′)
          ∙′ ↑ (F.F-id {x = x}) ▹′ α₀ x ▹′ G.F₁ f )
          refl

module _ (F : GpdEndo) where
  open WildNatTrans
  open IsPseudonat
  open wildIsIso

  private module F = Copresheaf F
 
  iMG-lUnit-isIs : wildIsIso {C = GpdEndoWildCat} (iMG-lUnit-ob F)
  iMG-lUnit-isIs .inv' .fst .N-ob _ = idfun _
  iMG-lUnit-isIs .inv' .fst .N-hom _ = refl
  iMG-lUnit-isIs .inv' .snd .N-hom-id = sym (lUnit _ ∙ lUnit _)
  iMG-lUnit-isIs .inv' .snd .N-hom-seq f g = reassoc
    (refl′ ∙′ refl′ ∙′ ↑ F.F-seq f g)
    (↑ F.F-seq f g ∙′ refl′ ∙′ refl′)
    refl
  iMG-lUnit-isIs .sect = PseudonatTrans≡ $ makeNatTransPath
    refl 
    λ f → sym (lUnit _)
  iMG-lUnit-isIs .retr = PseudonatTrans≡ $ makeNatTransPath
    refl
    λ f → sym (lUnit _)

open WildNatIso
open WildNatTrans
open wildIsIso

iMG-lUnit : WildNatIso _ _ 
  (restrFunctorₗ compEndo idEndo) 
  (idWildFunctor _)
iMG-lUnit .trans .N-ob = iMG-lUnit-ob
iMG-lUnit .trans .N-hom = iMG-lUnit-hom
iMG-lUnit .isIs = iMG-lUnit-isIs
