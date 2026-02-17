module CubicalCompat.WildCat.Functor where

open import Cubical.Foundations.Prelude

open import Cubical.WildCat.Base
open import Cubical.WildCat.Functor

private
  variable
    ℓ ℓ' : Level
    ℓC ℓC' ℓD ℓD' ℓE ℓE' : Level

open WildCat
open WildNatTrans

idWildNatTrans : {C : WildCat ℓC ℓC'} {D : WildCat ℓD ℓD'} {F : WildFunctor C D} → WildNatTrans _ _ F F
idWildNatTrans {D = D} .N-ob x = D .id
idWildNatTrans {D = D} .N-hom f = D .⋆IdR _ ∙ sym (D .⋆IdL _)

