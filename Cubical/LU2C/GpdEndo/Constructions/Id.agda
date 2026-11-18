open import Cubical.Foundations.Prelude

open import Cubical.WildCat.Functor

open import Cubical.LU2C.GpdEndo.Base

module Cubical.LU2C.GpdEndo.Constructions.Id {ℓ : Level}
  where

open GpdEndoConv

Id : GpdEndo {ℓ}
Id .fst = idWildFunctor _
Id .snd = fromStrict record where
  F-IdL f = refl
  F-IdR f = refl
  F-Assoc f g h = refl
