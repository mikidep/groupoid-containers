open import Cubical.Foundations.Prelude

open import Cubical.Foundations.Function
open import Cubical.Foundations.GroupoidLaws
open import Prelude.ExtraGpdLaws

open import Cubical.WildCat.Functor hiding (_$_)
open import Cubical.WildCat.Product renaming (_×_ to ProdCat)

module Cubical.Bicategory.Copresheaf.EndoConstructions.WhiskL_
  (ℓ : Level) where

open import Cubical.Bicategory.Base
open import Cubical.Bicategory.Copresheaf.Base ℓ
  using (Copresheaf; GPD; Is2Copresheaf)
open import Cubical.Bicategory.Copresheaf.Pseudonat.AsFunctor ℓ
open import Cubical.Bicategory.Instances.Copresheaf ℓ
open import Cubical.Bicategory.Copresheaf.EndoConstructions.Base ℓ
open import Cubical.Bicategory.Copresheaf.EndoConstructions.Composite ℓ
import Cubical.Bicategory.Pseudofunctor as PF

open Copresheaf using (str; is2Copresheaf)
open WildFunctor
open Is2Copresheaf

open BicatSyntax {{...}}
open BicatSynInstBC GPD

module _ (F : GpdEndo) {G H : GpdEndo}
  (α : PseudonatTrans G H) where
  open import Prelude

  private module F = Copresheaf F
  private module G = Copresheaf G
  private module H = Copresheaf H

  open F using (F₀; F₁; F₂)
  open G using () renaming 
    ( F₀ to    G₀
    ; F₁ to    G₁
    ; F₂ to    G₂
    )
  open H using () renaming 
    ( F₀ to    H₀
    ; F₁ to    H₁
    ; F₂ to    H₂
    )

  private _⨾₀_ = compEndo₀
  private _⨾ʷ₀_ = comp-WildFunctor

  open import Cubical.WildCat.Product.Functor
  open import CubicalCompat.WildCat.Functor
  open import Cubical.Bicategory.Instances.Walking

  open PseudonatTrans
  -- α : 0→1 × GPD → GPD
  -- α 0 ≡ G
  -- α 1 ≡ H
  -- (id 0→1 ×₁ F) ⨾ α
  whiskL-pseudonat : PseudonatTrans (F ⨾₀ G) (F ⨾₀ H)
  whiskL-pseudonat .htpy .str = (idWildFunctor _ ×₁ F .str) ⨾ʷ₀ α .htpy .str
  whiskL-pseudonat .htpy .is2Copresheaf = {! !}
  whiskL-pseudonat .bdry₀ = {! !}
    where
    str≡ :  restrFunctorₗ (whiskL-pseudonat .htpy .str) 𝟘 ≡ (F ⨾₀ G) .str
    -- str≡ i .F-ob X = α .bdry₀ i .str .F-ob (F₀ X)
    -- str≡ i .F-hom f = α .bdry₀ i .str .F-hom (F₁ f)
    -- str≡ i .F-id = {! !}
    -- str≡ i .F-seq = {! !}
    
    open import Cubical.Foundations.Path
    str≡ = WildFunctor≡ 
      (λ X i → α .bdry₀ i .str .F-ob (F₀ X)) 
      (λ f i → α .bdry₀ i .str .F-hom (F₁ f)) 
      (λ {X} i → {! α .bdry₀ i .str .F-id {F₀ X} !}) 
      {! !}

  whiskL-pseudonat .bdry₁ = {! !}
