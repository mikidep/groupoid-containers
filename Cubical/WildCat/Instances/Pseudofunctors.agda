open import Cubical.Foundations.Prelude

open import Cubical.LU2C.Base
open import Cubical.LU2C.Pseudofunctor
open import Cubical.WildCat.FullSub
open import Cubical.WildCat.Instances.WildFunctLU2C 

module Cubical.WildCat.Instances.Pseudofunctors where

private
  variable
    ℓC ℓC' ℓD ℓD' : Level


module _ (C : LU2C ℓC ℓC') (D : LU2C ℓD ℓD') where

  open LU2C using () renaming (str to ⟨_⟩)

  PseudoWC = FullSubWildCat 
    (WildFunctWC ⟨ C ⟩ D) 
    (IsPseudofunctor C D)
