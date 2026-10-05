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
open CC.Monoidal
open CC.Morphisms

open WildFunctor
open import Cubical.Foundations.Function

open WildNatTrans
open WildNatIso
open wildIsIso

open import Prelude

private module iMC where
  _⊗_ : WildFunctor 
    (ContainerWildCat × ContainerWildCat) 
    ContainerWildCat
  _⊗_ .F-ob = uncurry _⨾₀_
  _⊗_ .F-hom = uncurry _⨾₁_
  _⊗_ .F-id = refl
  _⊗_ .F-seq _ _ = refl

  𝟙 : Container
  𝟙 = 𝕀

  ⊗lUnit : WildNatIso _ _ (restrFunctorₗ _⊗_ 𝕀) (idWildFunctor _)
  ⊗lUnit .trans .N-ob X = ⨾lUnit {X}
  ⊗lUnit .trans .N-hom f = refl
  ⊗lUnit .isIs F .inv' = ⨾lUnit⁻ {F}
  ⊗lUnit .isIs _ .sect = refl
  ⊗lUnit .isIs _ .retr = refl

  ⊗rUnit : WildNatIso _ _ (restrFunctorᵣ _⊗_ 𝕀) (idWildFunctor _)
  ⊗rUnit .trans .N-ob X = ⨾rUnit {X}
  ⊗rUnit .trans .N-hom f = refl
  ⊗rUnit .isIs F .inv' = ⨾rUnit⁻ {F}
  ⊗rUnit .isIs _ .sect = refl
  ⊗rUnit .isIs _ .retr = refl

  ⊗assoc : WildNatIso _ _ (assocₗ _⊗_) (assocᵣ _⊗_)
  ⊗assoc .trans .N-ob (F , G , H) = ⨾assoc {F} {G} {H}
  ⊗assoc .trans .N-hom f = refl
  ⊗assoc .isIs (F , G , H) .inv' = ⨾assoc⁻ {F} {G} {H}
  ⊗assoc .isIs _ .sect = refl
  ⊗assoc .isIs _ .retr = refl

isMonoidalContainer : isMonoidalWildCat ContainerWildCat
isMonoidalContainer = record where
  open iMC using (⊗assoc; ⊗lUnit; ⊗rUnit)
  ⊗triangle _ _ = refl
  ⊗pentagon _ _ _ _ = refl

