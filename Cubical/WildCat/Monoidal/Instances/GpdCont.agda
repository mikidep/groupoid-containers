open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Unit

open import Cubical.Container.Base as WC using (CMor)
import Cubical.Container.Constructions as CC
open import Cubical.Bicategory.Copresheaf ℓ-zero
open import Cubical.Bicategory.Instances.Container

open import Cubical.WildCat.Base 
open import Cubical.WildCat.Functor 
open import Cubical.WildCat.Product 
open import Cubical.WildCat.Monoidal.Base

import Cubical.WildCat.Monoidal.Instances.Container as MW

module Cubical.WildCat.Monoidal.Instances.GpdCont where

open Container
open IsGpdContainer
open CC.Monoidal

module iMWC = isMonoidalWildCat MW.isMonoidalContainer


private module iMC where
  𝟙 : Container
  𝟙 .str = 𝕀
  𝟙 .isGpdContainer .isGpdS = isSet→isGroupoid isSetUnit
  𝟙 .isGpdContainer .isGpdP = isSet→isGroupoid isSetUnit

  open Extent using ()
    renaming (Ext-ob to ⟦_⟧)

  module _ (F G : Container) where
    open Copresheaf (⟦ G ⟧) using ()
      renaming (F₀ to ⟦G⟧)

    _⊗₀_ : Container
    _⊗₀_ .str = F .str ⨾₀ G .str
    _⊗₀_ .isGpdContainer .isGpdS = ⟦G⟧ (F .S , F .isGpdS) .snd
    _⊗₀_ .isGpdContainer .isGpdP = isGroupoidΣ 
      (G .isGpdP) 
      λ _ → F .isGpdP

  open WildFunctor
  open import Cubical.Foundations.Function

  _⊗_ : WildFunctor
    (GpdContWildCat × GpdContWildCat)
    GpdContWildCat
  _⊗_ .F-ob = uncurry _⊗₀_
  _⊗_ .F-hom = uncurry _⨾₁_
  _⊗_ .F-id = refl
  _⊗_ .F-seq _ _ = refl

  open WildNatTrans
  open WildNatIso
  open wildIsIso

  open import Prelude

  ⊗lUnit : WildNatIso _ _ (restrFunctorₗ _⊗_ 𝟙) (idWildFunctor _)
  ⊗lUnit .trans .N-ob _ = ⨾lUnit
  ⊗lUnit .trans .N-hom f = refl
  ⊗lUnit .isIs _ .inv' = ⨾lUnit⁻
  ⊗lUnit .isIs _ .sect = refl
  ⊗lUnit .isIs _ .retr = refl

  ⊗rUnit : WildNatIso _ _ (restrFunctorᵣ _⊗_ 𝟙) (idWildFunctor _)
  ⊗rUnit .trans .N-ob _ = ⨾rUnit
  ⊗rUnit .trans .N-hom f = refl
  ⊗rUnit .isIs _ .inv' = ⨾rUnit⁻
  ⊗rUnit .isIs _ .sect = refl
  ⊗rUnit .isIs _ .retr = refl

  ⊗assoc : WildNatIso _ _ (assocₗ _⊗_) (assocᵣ _⊗_)
  ⊗assoc .trans .N-ob _ = ⨾assoc
  ⊗assoc .trans .N-hom f = refl
  ⊗assoc .isIs _ .inv' = ⨾assoc⁻
  ⊗assoc .isIs _ .sect = refl
  ⊗assoc .isIs _ .retr = refl

open isMonoidalWildCat

isMonoidalGpdCont : isMonoidalWildCat GpdContWildCat
isMonoidalGpdCont = record where
  open iMC using (_⊗_; 𝟙; ⊗assoc; ⊗lUnit; ⊗rUnit)
  ⊗triangle _ _ = refl
  ⊗pentagon _ _ _ _ = refl

MonoidalGpdCont : MonoidalWildCat _ _
MonoidalGpdCont = GpdContWildCat , isMonoidalGpdCont

