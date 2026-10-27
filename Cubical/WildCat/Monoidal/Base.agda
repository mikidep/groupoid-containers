open import Cubical.Foundations.Prelude

open import Cubical.WildCat.Base
open import Cubical.WildCat.Monoidal.Definition.IsMonoidal

module Cubical.WildCat.Monoidal.Base where

MonoidalWildCat : (ℓ ℓ' : Level) → Type (ℓ-suc (ℓ-max ℓ ℓ'))
MonoidalWildCat ℓ ℓ' =
  Σ[ C ∈ WildCat ℓ ℓ' ] isMonoidalWildCat C
