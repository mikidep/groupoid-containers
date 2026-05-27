open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.WildCat.BraidedSymmetricMonoidal
open import Cubical.WildCat.Product renaming (_×_ to ProdCat)
open import Cubical.WildCat.NaturalTransformation.Base

open import Cubical.Bicategory.Base 
open import Cubical.Bicategory.Copresheaf ℓ-zero
open import Cubical.Bicategory.Instances.Copresheaf ℓ-zero
open import Cubical.Bicategory.Copresheaf.EndoConstructions ℓ-zero

module Cubical.WildCat.Monoidal.Instances.GpdEndo where

open import Cubical.WildCat.Monoidal.Instances.GpdEndo.LUnit ℓ-zero
open import Cubical.WildCat.Monoidal.Instances.GpdEndo.RUnit ℓ-zero
open import Cubical.WildCat.Monoidal.Instances.GpdEndo.Assoc ℓ-zero

module _ where
  open import Cubical.Foundations.GroupoidLaws
  open import Prelude.ExtraGpdLaws
  open import Prelude.Reassoc

  open isMonoidalWildCat
  open Bicategory GPD using (id; _◃_; _▹_)
    renaming (str to ⟨GPD⟩; Hom[_,_] to GPD[_,_])

  isMonoidalGpdEndo : isMonoidalWildCat GpdEndoWildCat
  isMonoidalGpdEndo ._⊗_ = compEndo
  isMonoidalGpdEndo .𝟙 = idEndo
  isMonoidalGpdEndo .⊗assoc = iMG-assoc
  isMonoidalGpdEndo .⊗lUnit = iMG-lUnit
  isMonoidalGpdEndo .⊗rUnit = iMG-rUnit
  isMonoidalGpdEndo .triang F G = 2NatTrans≡ $ makeNatTransPath refl 
    λ f → 
      refl 
      ∙ (sym (G.F-seq (F₁ f) id) 
        ∙ refl ∙ G.F-seq id (F₁ f)) 
      ∙ refl
    ≡⟨ reassoc 
        ( sym (G.F-seq (F₁ f) id) 
        ∷ G.F-seq id (F₁ f) 
        ∷ nil ) 
        (refl′ ◆ (tm ◆ refl′ ◆ tm) ◆ refl′)
        (((tm ◆ refl′) ◆ refl′ ◆ refl′ ◆ tm) ◆ refl′)
      ⟩
      ((sym (G.F-seq (F₁ f) id) ∙ refl) ∙ refl ∙ refl ∙ G.F-seq id (F₁ f)) 
      ∙ refl
    ≡⟨ ∙r ∙r sym (symDistr _ _) ⟩
      (sym (refl ∙ G.F-seq (F₁ f) id) ∙ refl ∙ refl ∙ G.F-seq id (F₁ f)) 
      ∙ refl
    ∎
    where
    module F = Copresheaf F
    module G = Copresheaf G
    open F using (F₁)
  isMonoidalGpdEndo .⊗pentagon F G H K = 2NatTrans≡ $ makeNatTransPath 
    (funExt λ X →
      _ ◃ K.F-id
      ∙ K₂ (H₂ (G.F-id))
      ∙ K₂ (H.F-id)
      ∙ K.F-id) 
    {! !}
    where
    module F = Copresheaf F
    module G = Copresheaf G
    module H = Copresheaf H
    module K = Copresheaf K
    open G using () renaming (F₁ to G₁; F₂ to G₂)
    open H using () renaming (F₁ to H₁; F₂ to H₂)
    open K using () renaming (F₁ to K₁; F₂ to K₂)
