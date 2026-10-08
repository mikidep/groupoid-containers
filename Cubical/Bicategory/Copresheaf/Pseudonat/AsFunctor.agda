open import Cubical.Foundations.Prelude

module Cubical.Bicategory.Copresheaf.Pseudonat.AsFunctor (ℓ : Level) where

open import Cubical.Bicategory.Base
open import Cubical.Bicategory.Copresheaf.Base ℓ
open import Cubical.Bicategory.Product.Base
open import Cubical.Bicategory.Instances.Walking
open import Cubical.Bicategory.Product.Copresheaf ℓ

private
  variable
    ℓC ℓC' : Level

module _ {C : Bicategory ℓC ℓC'} where

  record Pseudonat (F G : Copresheaf C) 
      : Type (ℓ-max (ℓ-max ℓC ℓC') (ℓ-suc ℓ)) where
    field
      htpy : Copresheaf (Walking × C)
      bdry₀ : restrFunctorₗ htpy 𝟘 ≡ F
      bdry₁ : restrFunctorₗ htpy 𝟙 ≡ G

  open import Cubical.WildCat.Functor using (WildFunctor)
  open import CubicalCompat.WildCat.Functor
  open import Cubical.Data.Unit

  open Pseudonat
  open Copresheaf
  open WildFunctor
  open Is2Copresheaf

  idNat : (F : Copresheaf C) → Pseudonat F F
  idNat F .htpy .str .F-ob (i , c) = F .F₀ c 
  idNat F .htpy .str .F-hom (_ , f) = F .F₁ f
  idNat F .htpy .str .F-id  = F .F-id
  idNat F .htpy .str .F-seq (_ , f) (_ , g) = F .F-seq f g
  idNat F .htpy .is2Copresheaf .F-IdL (_ , f) = F .F-IdL f
  idNat F .htpy .is2Copresheaf .F-IdR (_ , f) = F .F-IdR f
  idNat F .htpy .is2Copresheaf .F-Assoc (_ , f) (_ , g) (_ , h) = F .F-Assoc f g h
  idNat F .bdry₀ = {! !}
    where
    str≡ :  restrFunctorₗ (idNat F .htpy) 𝟘 .str ≡ F .str
    str≡ = WildFunctor≡ 
      (λ c → refl)
      (λ f → refl)
      (λ {x} → refl)
      λ { f g i j x → {! !} }
  idNat F .bdry₁ = {! !}


