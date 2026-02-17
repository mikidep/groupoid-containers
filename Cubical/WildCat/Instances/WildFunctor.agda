{-# OPTIONS --allow-unsolved-metas #-}

module Cubical.WildCat.Instances.WildFunctor where

open import Cubical.Foundations.Prelude

open import Cubical.WildCat.Base
open import Cubical.WildCat.Functor
open import CubicalCompat.WildCat.Functor
open import Cubical.WildCat.NaturalTransformation.Base

open WildCat

private
  variable
    ℓC ℓC′ ℓD ℓD′ : Level

module _ (C : WildCat ℓC ℓC′) (D : WildCat ℓD ℓD′) where
  open WildNatTrans

  WildFunctorCat : WildCat _ _
  ob WildFunctorCat = WildFunctor C D
  Hom[_,_] WildFunctorCat A B = WildNatTrans _ _ A B
  WildCat.id WildFunctorCat = idWildNatTrans
  _⋆_ WildFunctorCat α β = compWildNatTrans _ _ _ α β
  ⋆IdL WildFunctorCat α = 
    makeNatTransPath
      (funExt λ x → D .⋆IdL (α .N-ob x))
      {! !}
  ⋆IdR WildFunctorCat α =
    makeNatTransPath
      (funExt λ x → D .⋆IdR (α .N-ob x))
      {! !}
  ⋆Assoc WildFunctorCat α β γ =
    makeNatTransPath
      (funExt λ x → D .⋆Assoc (α .N-ob x) (β .N-ob x) (γ .N-ob x))
      {! !}

