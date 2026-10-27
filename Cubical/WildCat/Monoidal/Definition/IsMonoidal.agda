open import Cubical.Foundations.Prelude

open import Cubical.WildCat.Base
open import Cubical.WildCat.Monoidal.Definition.Structure
open import Cubical.WildCat.Monoidal.Definition.Endpoints 

module Cubical.WildCat.Monoidal.Definition.IsMonoidal
  {ℓ ℓ' : Level} (M : WildCat ℓ ℓ') where

record isMonoidalWildCat : Type (ℓ-max ℓ ℓ') where
  field
    mStr : MonoidalStr M
    ⊗triangle : ⊗triangleₗ mStr ≡ ⊗triangleᵣ mStr
    ⊗pentagon : ⊗pentagonₗ mStr ≡ ⊗pentagonᵣ mStr
  open MonoidalStr mStr public
