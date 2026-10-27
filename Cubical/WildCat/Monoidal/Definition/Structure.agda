open import Cubical.Foundations.Prelude

open import Cubical.WildCat.Base
open import Cubical.WildCat.Product
open import Cubical.WildCat.Functor

module Cubical.WildCat.Monoidal.Definition.Structure
  {ℓ ℓ' : Level} (M : WildCat ℓ ℓ') where

open WildCat M

record MonoidalStr : Type (ℓ-max ℓ ℓ') where
  field
    _⊗_ : WildFunctor (M × M) M
    𝟙 : ob

    ⊗assoc : WildNatIso (M × (M × M)) M (assocₗ _⊗_) (assocᵣ _⊗_)

    ⊗lUnit : WildNatIso M M (restrFunctorₗ _⊗_ 𝟙) (idWildFunctor M)
    ⊗rUnit : WildNatIso M M (restrFunctorᵣ _⊗_ 𝟙) (idWildFunctor M)
