open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws

module Cubical.WildCat.Monoidal.Instances.Container.Extent where

open import Cubical.WildCat.Functor using (WildNatTrans)

open import Cubical.Bicategory.Functor using (Functor)
open import Cubical.Bicategory.Copresheaf ℓ-zero
open import Cubical.Bicategory.Instances.Container
open import Cubical.Bicategory.Copresheaf.EndoConstructions ℓ-zero
open import Cubical.WildCat.Monoidal.Functor
open import Cubical.WildCat.Monoidal.Instances.GpdCont
open import Cubical.WildCat.Monoidal.Instances.GpdEndo

open IsStrongMonoidal
open IsMonoidal
open WildNatTrans
open IsPseudonat

module E = Functor Extent.Extent


Extent : StrongMonoidalFunctor 
  GpdContWildCat GpdEndoWildCat 
  isMonoidalGpdCont isMonoidalGpdEndo
Extent .fst = E.str 
Extent .snd .isMonoidal .F-𝟙 .fst .N-ob (X , _) x = _ , λ _ → x
Extent .snd .isMonoidal .F-𝟙 .fst .N-hom f = refl
Extent .snd .isMonoidal .F-𝟙 .snd .N-hom-id = sym (lUnit _)
Extent .snd .isMonoidal .F-𝟙 .snd .N-hom-seq f g = lUnit _
Extent .snd .isMonoidal .F-⊗ .N-ob (F , G) = {! !}
Extent .snd .isMonoidal .F-⊗ .N-hom = {! !}
Extent .snd .isMonoidal .F-⊗lUnit = {! !}
Extent .snd .isMonoidal .F-⊗rUnit = {! !}
Extent .snd .isMonoidal .F-⊗assoc = {! !}
Extent .snd .isIsoF-𝟙 = {! !}
Extent .snd .isIsoF-⊗ = {! !}
