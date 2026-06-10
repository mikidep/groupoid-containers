open import Cubical.Foundations.Prelude
open import Cubical.Data.Unit

open import Cubical.WildCat.Base
open import Cubical.WildCat.Functor
open import Cubical.Data.Sigma renaming (_×_ to _×'_)
open import Cubical.WildCat.Product

module Cubical.WildCat.Product.Functor where

private variable
  ℓA ℓA' ℓB ℓB' ℓC ℓC' ℓD ℓD' : Level 
  A : WildCat ℓA ℓA'
  B : WildCat ℓB ℓB'
  C : WildCat ℓC ℓC'
  D : WildCat ℓD ℓD'

module _ where
  open WildFunctor

  ProdFst : WildFunctor (A × B) A
  ProdFst .F-ob = fst
  ProdFst .F-hom = fst
  ProdFst .F-id = refl
  ProdFst .F-seq f g = refl

  ProdSnd : WildFunctor (A × B) B
  ProdSnd .F-ob = snd
  ProdSnd .F-hom = snd
  ProdSnd .F-id = refl
  ProdSnd .F-seq f g = refl

module _ (F : WildFunctor A C)
  (G : WildFunctor A D) where
  
  open WildFunctor
  private
    module F = WildFunctor F
    module G = WildFunctor G

  ProdCatMapInto : WildFunctor A (C × D)
  ProdCatMapInto .F-ob X = F.F-ob X , G.F-ob X
  ProdCatMapInto .F-hom f = F.F-hom f , G.F-hom f
  ProdCatMapInto .F-id = ≡-× F.F-id G.F-id
  ProdCatMapInto .F-seq f g = ≡-× (F.F-seq f g) (G.F-seq f g)

module _ (F : WildFunctor A C)
  (G : WildFunctor B D) where

  open WildFunctor
  private
    module F = WildFunctor F
    module G = WildFunctor G

  -- wanted it to be def.d with universal property
  -- but that would introduce extra refl's
  ProdFunctor : WildFunctor (A × B) (C × D)
  ProdFunctor .F-ob (X , Y) = F.F-ob X , G.F-ob Y
  ProdFunctor .F-hom (f , g) = F.F-hom f , G.F-hom g
  ProdFunctor .F-id = ≡-× F.F-id G.F-id
  ProdFunctor .F-seq (f , f') (g , g') = 
    ≡-× (F.F-seq f g) (G.F-seq f' g')
