module Cubical.Bicategory.Instances.FromSetCat where

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base

open import Cubical.Bicategory.Base
open import Cubical.Bicategory.Pseudofunctor
open import Cubical.WildCat.Instances.NonWild
open import Cubical.WildCat.Functor

open import Cubical.Foundations.HLevels

module _ {ℓ ℓ' : Level} (C : Category ℓ ℓ') where

  open Bicategory
  open Category
  open IsBicategory

  AsBicat : Bicategory ℓ ℓ'
  AsBicat .str = AsWildCat C
  AsBicat .isBicat .triangle _ _ = C .isSetHom _ _ _ _
  AsBicat .isBicat .pentagon _ _ _ _ = C .isSetHom _ _ _ _
  AsBicat .isBicat .isGpdHom = isSet→isGroupoid (C .isSetHom)

module _ {ℓC ℓC' ℓD ℓD' : Level} {C : Category ℓC ℓC'} {D : Category ℓD ℓD'} (F : Functor C D) where

  open Pseudofunctor
  open WildFunctor
  open Pseudofunctor

  -- AsWildFunctor : WildFunctor (AsWildCat C) (AsWildCat D)
  -- F-ob AsWildFunctor = F-ob F
  -- F-hom AsWildFunctor = F-hom F
  -- F-id AsWildFunctor = F-id F
  -- F-seq AsWildFunctor = F-seq F
