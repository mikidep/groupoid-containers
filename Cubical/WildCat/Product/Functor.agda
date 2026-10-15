open import Cubical.Foundations.Prelude
open import Cubical.Data.Unit

open import Cubical.WildCat.Base
open import Cubical.WildCat.Functor
open import Cubical.Data.Sigma hiding (_×_)
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

  Fst : WildFunctor (A × B) A
  Fst .F-ob = fst
  Fst .F-hom = fst
  Fst .F-id = refl
  Fst .F-seq f g = refl

  Snd : WildFunctor (A × B) B
  Snd .F-ob = snd
  Snd .F-hom = snd
  Snd .F-id = refl
  Snd .F-seq f g = refl

  ProdAssoc : WildFunctor (A × (B × C)) ((A × B) × C)
  ProdAssoc .F-ob (a , b , c) = (a , b) , c
  ProdAssoc .F-hom (f , g , h) = (f , g) , h
  ProdAssoc .F-id = refl
  ProdAssoc .F-seq f g = refl

module _ (F : WildFunctor A C)
  (G : WildFunctor A D) where
  
  open WildFunctor
  private
    module F = WildFunctor F
    module G = WildFunctor G

  ⟨_,_⟩₁ : WildFunctor A (C × D)
  ⟨_,_⟩₁ .F-ob X = F.F-ob X , G.F-ob X
  ⟨_,_⟩₁ .F-hom f = F.F-hom f , G.F-hom f
  ⟨_,_⟩₁ .F-id = ≡-× F.F-id G.F-id
  ⟨_,_⟩₁ .F-seq f g = ≡-× (F.F-seq f g) (G.F-seq f g)

module _ (F : WildFunctor A C)
  (G : WildFunctor B D) where

  open WildFunctor
  private
    module F = WildFunctor F
    module G = WildFunctor G

  -- wanted it to be def.d with universal property
  -- but that would introduce extra refl's
  _×₁_ : WildFunctor (A × B) (C × D)
  _×₁_ .F-ob (X , Y) = F.F-ob X , G.F-ob Y
  _×₁_ .F-hom (f , g) = F.F-hom f , G.F-hom g
  _×₁_ .F-id = ≡-× F.F-id G.F-id
  _×₁_ .F-seq (f , f') (g , g') = ≡-× (F.F-seq f g) (G.F-seq f' g')

module _ 
  {F F′ : WildFunctor A C}
  {G G′ : WildFunctor B D} 
  (α : WildNatTrans _ _ F F′)
  (β : WildNatTrans _ _ G G′)
  where

  open WildNatTrans α renaming
    ( N-ob to α₀
    ; N-hom to α□
    )
  open WildNatTrans β renaming
    ( N-ob to β₀
    ; N-hom to β□
    )

  _×₂_ : WildNatTrans _ _ (F ×₁ G) (F′ ×₁ G′)
  _×₂_ = record where
    N-ob (x , y) = α₀ x , β₀ y
    N-hom (f , g) = ≡-× (α□ f) (β□ g)
