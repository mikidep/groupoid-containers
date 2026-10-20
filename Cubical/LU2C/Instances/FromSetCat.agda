module Cubical.LU2C.Instances.FromSetCat where

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base

open import Cubical.LU2C.Base
open import Cubical.LU2C.Pseudofunctor
open import Cubical.WildCat.Instances.NonWild
open import Cubical.WildCat.Functor

open import Cubical.Foundations.HLevels

module _ {ℓ ℓ' : Level} (C : Category ℓ ℓ') where

  open LU2C
  open Category
  open IsLU2C

  AsLU2C : LU2C ℓ ℓ'
  AsLU2C .str = AsWildCat C
  AsLU2C .isLU2C .triangle _ _ = C .isSetHom _ _ _ _
  AsLU2C .isLU2C .pentagon _ _ _ _ = C .isSetHom _ _ _ _
  AsLU2C .isLU2C .isGpdHom = isSet→isGroupoid (C .isSetHom)

module _ {ℓC ℓC' ℓD ℓD' : Level} {C : Category ℓC ℓC'} {D : Category ℓD ℓD'} (F : Functor C D) where

  open Pseudofunctor
  open WildFunctor
  open Pseudofunctor

  -- AsWildFunctor : WildFunctor (AsWildCat C) (AsWildCat D)
  -- F-ob AsWildFunctor = F-ob F
  -- F-hom AsWildFunctor = F-hom F
  -- F-id AsWildFunctor = F-id F
  -- F-seq AsWildFunctor = F-seq F
