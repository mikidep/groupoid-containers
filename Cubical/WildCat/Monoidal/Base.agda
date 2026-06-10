open import Cubical.Foundations.Prelude

open import Cubical.WildCat.Base

module Cubical.WildCat.Monoidal.Base where

open import Cubical.WildCat.BraidedSymmetricMonoidal
  using (isMonoidalWildCat) public

MonoidalWildCat : (ℓ ℓ' : Level) → Type (ℓ-suc (ℓ-max ℓ ℓ'))
MonoidalWildCat ℓ ℓ' =
  Σ[ C ∈ WildCat ℓ ℓ' ] isMonoidalWildCat C
