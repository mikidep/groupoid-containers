open import Cubical.Foundations.Prelude

open import Cubical.WildCat.Base
open import Cubical.WildCat.Monoidal.Base

open import Cubical.WildCat.Monoidal.Instances.Terminal

module Cubical.WildCat.Monoidal.Monoid
  {ℓC ℓC' : Level} 
  (MC : MonoidalWildCat ℓC ℓC')
  where

open import Cubical.WildCat.Monoidal.Functor 

Monoid = MonoidalFunctor MonoidalTerminal MC

