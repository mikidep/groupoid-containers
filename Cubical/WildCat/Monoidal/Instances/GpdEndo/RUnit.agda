open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Path
open import Cubical.Functions.FunExtEquiv

open import Cubical.WildCat.Base
open import Cubical.WildCat.Functor hiding (_$_)
open import Cubical.WildCat.NaturalTransformation.Base

module Cubical.WildCat.Monoidal.Instances.GpdEndo.RUnit 
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

  iMG-rUnit-ob : PseudonatTrans (F ⊗₀ idEndo) F
  iMG-rUnit-ob .fst .N-ob X = idfun _
  iMG-rUnit-ob .fst .N-hom f = refl
  iMG-rUnit-ob .snd .N-hom-id = sym (lUnit _) ∙ rUnit _
  iMG-rUnit-ob .snd .N-hom-seq f g = 
    reassoc
      (F.F-seq f g ∷ nil)
      (refl′ ◆ tm)
      ((tm ◆ refl′) ◆ refl′ ◆ refl′)

module _ {F G : GpdEndo} (α : PseudonatTrans F G) where
  open Bicategory GpdEndoBicat using ()
    renaming (_⋆_ to _⨾_)
  open Bicategory GPD using (id; _◃_; _▹_)
    renaming (str to ⟨GPD⟩; Hom[_,_] to GPD[_,_])
  
  open WildNatTrans (α .fst) using ()
    renaming (N-ob to α₀; N-hom to α□)

  private
    ρ₀ = iMG-rUnit-ob
    module F = Copresheaf F
    module G = Copresheaf G

  open 2CellLaws ⟨GPD⟩

  iMG-rUnit-hom : (α ⊗₁ idPseudonatTrans idEndo) ⨾ ρ₀ G ≡ ρ₀ F ⨾ α
  iMG-rUnit-hom = PseudonatTrans≡ $ makeNatTransPath 
    refl 
    λ f → reassoc
      (α□ f ∷ nil)
      (((refl′ ◆ tm ◆ refl′) ◆ refl′) ◆ refl′)
      (refl′ ◆ tm)
  
module _ (F : GpdEndo) where
  open WildNatTrans
  open IsPseudonat
  open wildIsIso

  private module F = Copresheaf F
 
  iMG-rUnit-isIs : wildIsIso {C = GpdEndoWildCat} (iMG-rUnit-ob F)
  iMG-rUnit-isIs .inv' .fst .N-ob _ = idfun _
  iMG-rUnit-isIs .inv' .fst .N-hom _ = refl
  iMG-rUnit-isIs .inv' .snd .N-hom-id = sym (rUnit _ ∙ lUnit _)
  iMG-rUnit-isIs .inv' .snd .N-hom-seq f g = reassoc
    (F.F-seq f g ∷ nil)
    (refl′ ◆ tm ◆ refl′)
    (tm ◆ refl′ ◆ refl′)
  iMG-rUnit-isIs .sect = PseudonatTrans≡ $ makeNatTransPath
    refl λ f → sym (lUnit _)
  iMG-rUnit-isIs .retr = PseudonatTrans≡ $ makeNatTransPath
    refl λ f → sym (lUnit _)

open WildNatIso
open WildNatTrans
open wildIsIso

iMG-rUnit : WildNatIso _ _ 
  (restrFunctorᵣ compEndo idEndo) 
  (idWildFunctor _)
iMG-rUnit .trans .N-ob = iMG-rUnit-ob
iMG-rUnit .trans .N-hom = iMG-rUnit-hom
iMG-rUnit .isIs = iMG-rUnit-isIs
