{-# OPTIONS --allow-unsolved-metas #-}

module Cubical.WildCat.Instances.WildCopresheaf where

open import Cubical.Foundations.Prelude

open import Cubical.WildCat.Base
open import Cubical.WildCat.Functor
open import Cubical.WildCat.Instances.Types
open import CubicalCompat.WildCat.Functor
open import Cubical.WildCat.NaturalTransformation.Base

open WildCat

private
  variable
    ℓC ℓC′ : Level

module _ (ℓ : Level) where
  TYPE = TypeCat ℓ

  module _ (C : WildCat ℓC ℓC′) where
    open WildNatTrans


    idWildNatTransTypes : {F : WildFunctor C TYPE} → WildNatTrans _ _ F F
    idWildNatTransTypes .N-ob x = TYPE .id
    idWildNatTransTypes .N-hom f = refl


    module _
      (F G H : WildFunctor C TYPE) where
      open import Prelude
    
      -- Not sure how worth this is
      compWildNatTransTypes : WildNatTrans _ _ F G → WildNatTrans _ _ G H → WildNatTrans _ _ F H
      N-ob (compWildNatTransTypes η γ) X = N-ob η X » N-ob γ X
      N-hom (compWildNatTransTypes η γ) {x = x} {y = y} f = 
        cong (_» (N-ob γ y)) (N-hom η f)
        ∙ cong (N-ob η x »_) (N-hom γ f)

    WildCopshCat : WildCat _ _
    ob WildCopshCat = WildFunctor C TYPE
    Hom[_,_] WildCopshCat A B = WildNatTrans _ _ A B
    WildCat.id WildCopshCat = idWildNatTransTypes
    _⋆_ WildCopshCat α β = compWildNatTransTypes _ _ _ α β
    ⋆IdL WildCopshCat α = 
      makeNatTransPath
        (funExt λ x → TYPE .⋆IdL (α .N-ob x))
        {! !}
    ⋆IdR WildCopshCat α =
      makeNatTransPath
        (funExt λ x → TYPE .⋆IdR (α .N-ob x))
        {! !}
    ⋆Assoc WildCopshCat α β γ =
      makeNatTransPath
        (funExt λ x → TYPE .⋆Assoc (α .N-ob x) (β .N-ob x) (γ .N-ob x))
        {! !}

