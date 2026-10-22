open import Cubical.Foundations.Prelude

open import Cubical.WildCat.Base

module Cubical.WildCat.AsLU2C.Instances
  {ℓC ℓC' : Level}
  where

record Notation (C : WildCat ℓC ℓC') : Type (ℓ-max ℓC ℓC') where
  open import Cubical.WildCat.AsLU2C.Notation C public

open Notation {{...}} public

module NotWC (C : WildCat ℓC ℓC') where
  instance
    NotC : Notation C
    NotC = record { }
