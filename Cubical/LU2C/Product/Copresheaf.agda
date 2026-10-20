{-# OPTIONS --allow-unsolved-metas --no-qualified-instances #-}
open import Cubical.Foundations.Prelude
open import Cubical.Data.Unit

open import Cubical.WildCat.Functor as WF
  using (WildFunctor)
open import Cubical.Data.Sigma renaming (_×_ to _×'_)
open import Cubical.LU2C.Base
open import Cubical.LU2C.Product.Base

module Cubical.LU2C.Product.Copresheaf (ℓ : Level) where

open import Cubical.LU2C.Copresheaf.Base ℓ

open LU2CSyntax {{...}} 

open Copresheaf using (str; is2Copresheaf)
open WildFunctor
open Is2Copresheaf

private variable
  ℓC ℓC' ℓD ℓD' : Level 

module _ 
  {C : LU2C ℓC ℓC'}
  {D : LU2C ℓD ℓD'}
  where

  open LU2CSyn2C C
  open LU2CSyn2C D
  open LU2CSyn2C HGpd

  private 
    module C = LU2C C
    module D = LU2C D
    module G = LU2C HGpd

  restrFunctorₗ : (F : Copresheaf (C × D)) (c : C.ob) → Copresheaf D
  restrFunctorₗ F c .str = Str
    where
    module F = Copresheaf F
    open F using (F₀; F₁) renaming (str to ⟨F⟩)
    Str : WildFunctor _ _
    Str .F-ob d = F₀ (c , d)
    Str .F-hom f = F₁ (id , f)
    Str .F-id = F.F-id
    Str .F-seq f g = 
      cong (λ x → F₁ (x , f ⋆ g)) (sym (⋆IdL id))
      ∙ F.F-seq (id , f) (id , g)
  restrFunctorₗ F c .is2Copresheaf .F-IdL f = ?
  restrFunctorₗ F c .is2Copresheaf .F-IdR = {! !}
  restrFunctorₗ F c .is2Copresheaf .F-Assoc = {! !}

  restrFunctorᵣ : (F : Copresheaf (C × D)) (d : D.ob) → Copresheaf C
  restrFunctorᵣ F d .str = WF.restrFunctorᵣ (F .str) d
  restrFunctorᵣ F d .is2Copresheaf .F-IdL f = {! !}
  restrFunctorᵣ F d .is2Copresheaf .F-IdR = {! !}
  restrFunctorᵣ F d .is2Copresheaf .F-Assoc = {! !}
