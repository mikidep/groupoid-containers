open import Cubical.Foundations.Prelude
open import Cubical.Data.Unit

open import Cubical.WildCat.Base
open import Cubical.WildCat.Monoidal.Base
open import Cubical.WildCat.Functor
open import Cubical.WildCat.Product 
open import Cubical.Data.Sigma hiding (_×_)

open import Cubical.Container.Base
import Cubical.Container.Constructions as CC

open import Cubical.WildCat.Instances.Container

module Cubical.WildCat.Monoidal.Instances.Container where

open CC.Extent 

iMC-𝟙 = CC.Monoidal.𝟙
iMC-⊗₀ = CC.Monoidal._⊗₀_
iMC-⊗₁ = CC.Monoidal._⊗₁_

open WildFunctor
open import Cubical.Foundations.Function

iMC-⊗ : WildFunctor
  (ContainerWildCat × ContainerWildCat)
  ContainerWildCat
iMC-⊗ .F-ob = uncurry iMC-⊗₀
iMC-⊗ .F-hom = uncurry iMC-⊗₁
iMC-⊗ .F-id = refl
iMC-⊗ .F-seq _ _ = refl

open WildNatTrans
open WildNatIso
open wildIsIso

open import Prelude

iMC-⊗lUnit : WildNatIso _ _ (restrFunctorₗ iMC-⊗ iMC-𝟙) (idWildFunctor ContainerWildCat)
iMC-⊗lUnit .trans .N-ob = CC.Monoidal.lUnit
iMC-⊗lUnit .trans .N-hom f = refl
iMC-⊗lUnit .isIs F .inv' = CC.Monoidal.lUnit⁻ F
iMC-⊗lUnit .isIs _ .sect = refl
iMC-⊗lUnit .isIs _ .retr = refl

iMC-⊗rUnit : WildNatIso _ _ (restrFunctorᵣ iMC-⊗ iMC-𝟙) (idWildFunctor ContainerWildCat)
iMC-⊗rUnit .trans .N-ob = CC.Monoidal.rUnit
iMC-⊗rUnit .trans .N-hom f = refl
iMC-⊗rUnit .isIs F .inv' = CC.Monoidal.rUnit⁻ F
iMC-⊗rUnit .isIs _ .sect = refl
iMC-⊗rUnit .isIs _ .retr = refl

iMC-⊗assoc : WildNatIso _ _ (assocₗ iMC-⊗) (assocᵣ iMC-⊗)
iMC-⊗assoc .trans .N-ob (F , G , H) = CC.Monoidal.assoc F G H
iMC-⊗assoc .trans .N-hom f = refl
iMC-⊗assoc .isIs (F , G , H) .inv' = CC.Monoidal.assoc⁻ F G H
iMC-⊗assoc .isIs _ .sect = refl
iMC-⊗assoc .isIs _ .retr = refl

open isMonoidalWildCat

isMonoidalContainer : isMonoidalWildCat ContainerWildCat
isMonoidalContainer ._⊗_ = iMC-⊗
isMonoidalContainer .𝟙 = iMC-𝟙
isMonoidalContainer .⊗assoc = iMC-⊗assoc
isMonoidalContainer .⊗lUnit = iMC-⊗lUnit
isMonoidalContainer .⊗rUnit = iMC-⊗rUnit
isMonoidalContainer .triang _ _ = refl
isMonoidalContainer .⊗pentagon _ _ _ _ = refl

MonoidalContainer : MonoidalWildCat _ _
MonoidalContainer = ContainerWildCat , isMonoidalContainer
