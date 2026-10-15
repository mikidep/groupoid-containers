{-# OPTIONS --allow-unsolved-metas #-}
open import Cubical.Foundations.Prelude

module Cubical.Bicategory.Copresheaf.Pseudonat.AsFunctor (ℓ : Level) where

open import Cubical.Bicategory.Base
open import Cubical.Bicategory.Copresheaf.Base ℓ
open import Cubical.Bicategory.Product.Base
open import Cubical.Bicategory.Instances.Walking
open import Cubical.Bicategory.Product.Copresheaf ℓ

open import Cubical.Foundations.GroupoidLaws

private
  variable
    ℓC ℓC' : Level

module _ {C : Bicategory ℓC ℓC'} where

  record PseudonatTrans (F G : Copresheaf C) 
      : Type (ℓ-max (ℓ-max ℓC ℓC') (ℓ-suc ℓ)) where
    field
      htpy : Copresheaf (Walking × C)
      bdry₀ : restrFunctorₗ htpy 𝟘 ≡ F
      bdry₁ : restrFunctorₗ htpy 𝟙 ≡ G

  open import Cubical.WildCat.Functor using (WildFunctor)
  open import CubicalCompat.WildCat.Functor
  open import Cubical.Data.Unit

  open PseudonatTrans
  open Copresheaf
  open WildFunctor
  open Is2Copresheaf
  
  import Cubical.Bicategory.Copresheaf.Pseudonat.Base ℓ as TB

  open import Cubical.Foundations.Isomorphism
  open Iso
  open TB.IsPseudonat

  module _ (F G : Copresheaf C) where
    private module F = Copresheaf F
    private module G = Copresheaf G

    PN-Iso : Iso (TB.PseudonatTrans F G) (PseudonatTrans F G)
    PN-Iso .fun α = goal where
      goal : _
      goal .htpy .str .F-ob (𝟘 , x) = F.F₀ x
      goal .htpy .str .F-ob (𝟙 , x) = G.F₀ x
      goal .htpy .str .F-hom = {! !}
      goal .htpy .str .F-id = {! !}
      goal .htpy .str .F-seq = {! !}
      goal .htpy .is2Copresheaf = {! !}
      goal .bdry₀ = {! !}
      goal .bdry₁ = {! !}
    PN-Iso .inv = {! !}
    PN-Iso .rightInv = {! !}
    PN-Iso .leftInv = {! !}

  idNat : (F : Copresheaf C) → PseudonatTrans F F
  idNat F .htpy .str .F-ob (i , c) = F .F₀ c 
  idNat F .htpy .str .F-hom (_ , f) = F .F₁ f
  idNat F .htpy .str .F-id  = F .F-id
  idNat F .htpy .str .F-seq (_ , f) (_ , g) = F .F-seq f g
  idNat F .htpy .is2Copresheaf .F-IdL (_ , f) = F .F-IdL f
  idNat F .htpy .is2Copresheaf .F-IdR (_ , f) = F .F-IdR f
  idNat F .htpy .is2Copresheaf .F-Assoc (_ , f) (_ , g) (_ , h) = F .F-Assoc f g h
  idNat F .bdry₀ = {! !}
    where
    module F = Copresheaf F
    str≡ :  restrFunctorₗ (idNat F .htpy) 𝟘 .str ≡ F .str
    str≡ = WildFunctor≡ 
      (λ c → refl)
      (λ f → refl)
      (λ {x} → refl)
      (λ f g → sym (lUnit (F.F-seq f g))) 
  idNat F .bdry₁ = {! !}


