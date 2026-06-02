open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Path
open import Cubical.Functions.FunExtEquiv

open import Cubical.WildCat.Base
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
      reassoc (F.F-seq f g ∷ nil)
        (refl′ ◆ tm)
        ((refl′ ◆ tm) ◆ refl′ ◆ refl′)

module _ {F G : GpdEndo} (α : PseudonatTrans F G) where
  open Bicategory GpdEndoBicat using ()
    renaming (_⋆_ to _⨾_)
  open Bicategory GPD using (id; _◃_; _▹_)
    renaming (str to ⟨GPD⟩; Hom[_,_] to GPD[_,_])
  
  open WildNatTrans (α .fst) using ()
    renaming (N-ob to α₀; N-hom to α□)

  private
    λ₀ = iMG-lUnit-ob
    module F = Copresheaf F
    module G = Copresheaf G

  open 2CellLaws ⟨GPD⟩

  iMG-lUnit-hom : (idPseudonatTrans idEndo ⊗₁ α) ⨾ λ₀ G ≡ λ₀ F ⨾ α
  iMG-lUnit-hom = PseudonatTrans≡ $ makeNatTransPath 
    (funExt λ X → F.F-id ▹ α₀ X) 
    λ f → aux f
    where
    aux : 
      ∀ {x y} (f : GPD[ x , y ])
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
        ≡⟨ ∙l ∙r cong (_▹ α₀ y) (sym (F.F-IdL f)) ⟩ 
          F.F₁ f ◃ F.F-id ▹ α₀ y 
          ∙ (F.F-seq id f
            ∙ F.F-id ▹ F.F₁ f) ▹ α₀ y
          ∙ id ◃ α□ f
        ≡⟨ ∙l ∙r ▹-∙ _ _ ⟩ 
          F.F₁ f ◃ F.F-id ▹ α₀ y 
          ∙ (F.F-seq id f ▹ α₀ y
            ∙ F.F-id ▹ F.F₁ f ▹ α₀ y)
          ∙ id ◃ α□ f
        ≡⟨ ∙l sym assoc-inf ⟩ 
          F.F₁ f ◃ F.F-id ▹ α₀ y 
          ∙ F.F-seq id f ▹ α₀ y
          ∙ F.F-id ▹ F.F₁ f ▹ α₀ y
          ∙ id ◃ α□ f
        ≡⟨ ∙l ∙l sym (whisk-interchange F.F-id (α□ f)) ⟩
          F.F₁ f ◃ F.F-id ▹ α₀ y 
          ∙ F.F-seq id f ▹ α₀ y
          ∙ F.F₁ id ◃ α□ f 
          ∙ F.F-id ▹ α₀ x ▹ G.F₁ f
        ≡⟨ ∙r cong (_▹ α₀ y) (sym (invUniq (F.F-IdR f))) ⟩ 
          sym (F.F-seq f id) ▹ α₀ y 
          ∙ F.F-seq id f ▹ α₀ y
          ∙ F.F₁ id ◃ α□ f 
          ∙ F.F-id ▹ α₀ x ▹ G.F₁ f
        ≡⟨ reassoc
            ( sym (F.F-seq f id) ▹ α₀ y 
            ∷ F.F-seq id f ▹ α₀ y
            ∷ F.F₁ id ◃ α□ f 
            ∷ F.F-id ▹ α₀ x ▹ G.F₁ f
            ∷ nil )
            (tm ◆ tm ◆ tm ◆ tm)
            ((((tm ◆ tm) ◆ tm) ◆ refl′) ◆ tm)
           ⟩ 
          (((sym (F.F-seq f id) ▹ α₀ y ∙ F.F-seq id f ▹ α₀ y)
              ∙ F.F₁ id ◃ α□ f) 
            ∙ refl)
          ∙ F.F-id ▹ α₀ x ▹ G.F₁ f
        ≡⟨ ∙r ∙r ∙r sym (▹-∙ _ _) ⟩ 
          (((sym (F.F-seq f id) ∙ F.F-seq id f) ▹ α₀ y
              ∙ F.F₁ id ◃ α□ f) 
            ∙ refl)
          ∙ F.F-id ▹ α₀ x ▹ G.F₁ f
        ≡⟨ ∙r ∙r ∙r cong (_▹ α₀ y) (∙l lUnit (F.F-seq id f)) ⟩ 
          (((sym (F.F-seq f id) ∙ refl ∙ F.F-seq id f) ▹ α₀ y
              ∙ F.F₁ id ◃ α□ f) 
            ∙ refl)
          ∙ F.F-id ▹ α₀ x ▹ G.F₁ f
        ∎

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
    (F.F-seq f g ∷ nil)
    (refl′ ◆ refl′ ◆ tm)
    (tm ◆ refl′ ◆ refl′)
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
