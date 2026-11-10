open import Cubical.Foundations.Prelude

open import Cubical.WildCat.Monoidal.Base
open import Cubical.WildCat.Monoidal.Definition.IsMonoidal
open import Cubical.WildCat.Functor

module Cubical.WildCat.Monoidal.Functor
  {ℓC ℓC' ℓD ℓD' : Level}
  (MC : MonoidalWildCat ℓC ℓC')
  (MD : MonoidalWildCat ℓD ℓD') where

open import Cubical.WildCat.Monoidal.Functor.Definition.Structure MC MD 
open import Cubical.WildCat.Monoidal.Functor.Definition.IsMonoidal MC MD

MonoidalFunctor = Σ _ IsMonoidal
StrongMonoidalFunctor = Σ _ IsStrongMonoidal
