open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Path

module Cubical.WildCat.Monoidal.Instances.Container.Extent where

open import Cubical.WildCat.Functor using (WildNatTrans)

open import Cubical.Bicategory.Base
open import Cubical.Bicategory.Functor using (Functor)
open import Cubical.Bicategory.Copresheaf ℓ-zero
open import Cubical.Bicategory.Instances.Container
open import Cubical.Bicategory.Copresheaf.EndoConstructions ℓ-zero
open import Cubical.WildCat.Base
open import Cubical.WildCat.NaturalTransformation.Base
open import Cubical.WildCat.Monoidal.Functor
open import Cubical.WildCat.Monoidal.Instances.GpdCont
open import Cubical.WildCat.Monoidal.Instances.GpdEndo

open IsStrongMonoidal
open IsMonoidal
open WildNatTrans
open IsPseudonat
open wildIsIso

module E = Functor Extent.Extent
module GPD = Bicategory GPD
open GPD using (_▹_)
open 2CellLaws GPD.str

Extent : StrongMonoidalFunctor 
  GpdContWildCat GpdEndoWildCat 
  isMonoidalGpdCont isMonoidalGpdEndo
Extent .fst = E.str 
Extent .snd .isMonoidal .F-𝟙 .fst .N-ob (X , _) x = _ , λ _ → x
Extent .snd .isMonoidal .F-𝟙 .fst .N-hom f = refl
Extent .snd .isMonoidal .F-𝟙 .snd .N-hom-id = sym (lUnit _)
Extent .snd .isMonoidal .F-𝟙 .snd .N-hom-seq f g = lUnit _
Extent .snd .isMonoidal .F-⊗ .N-ob (F , G) .fst .N-ob X (s , v) = 
  -- s : S′
  --        v            fst
  -- P′ s -----> ⟦F⟧ X -------> S
  -- so this is ⟦G⟧₁ fst : ⟦G⟧ (⟦F⟧ X) ---> ⟦G⟧ S
  -- (s , v » fst) 
  ⟦G⟧.F₁ {x = ⟦F⟧.F₀ X} {y = F.S , F.isGpdS } fst (s , v)
  , λ { (p , q) → v p .snd q }
  where
  open import Prelude
  module F = Container F
  module ⟦F⟧ = Copresheaf (E.F₀ F)
  module ⟦G⟧ = Copresheaf (E.F₀ G)
Extent .snd .isMonoidal .F-⊗ .N-ob (F , G) .fst .N-hom _ = refl
Extent .snd .isMonoidal .F-⊗ .N-ob (F , G) .snd .N-hom-id {X} = 
    sym (▹-∙ {k = F-⊗X} refl refl) 
  where
  F-⊗X = Extent .snd .isMonoidal .F-⊗ .N-ob (F , G) .fst .N-ob X
Extent .snd .isMonoidal .F-⊗ .N-ob (F , G) .snd .N-hom-seq = {! !}
Extent .snd .isMonoidal .F-⊗ .N-hom {x = F , G} {y = H , K} (f , g) = 
    PseudonatTrans≡ (makeNatTransPath aux₁ {! !})
  where
  open import Cubical.Functions.FunExtEquiv
  aux₁ : {! _ !}
  aux₁ = funExt₂ λ { X (s , v) → {!  !} }
Extent .snd .isMonoidal .F-⊗lUnit = {! !}
Extent .snd .isMonoidal .F-⊗rUnit = {! !}
Extent .snd .isMonoidal .F-⊗assoc = {! !}
Extent .snd .isIsoF-𝟙 = {! !}
Extent .snd .isIsoF-⊗ F G .inv' .fst .N-ob X ((s , v) , w) = 
  s , λ p → v p , λ q → w (p , q)
Extent .snd .isIsoF-⊗ F G .inv' .fst .N-hom = {! !}
Extent .snd .isIsoF-⊗ F G .inv' .snd = {! !}
Extent .snd .isIsoF-⊗ F G .sect = {! !}
Extent .snd .isIsoF-⊗ F G .retr = {! !}
