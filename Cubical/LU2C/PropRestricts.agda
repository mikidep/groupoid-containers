open import Cubical.Foundations.Prelude
-- open import Cubical.Foundations.Powerset
open import Cubical.Foundations.HLevels
open import Cubical.WildCat.Base
open import Cubical.WildCat.Functor
open import Cubical.WildCat.Product

open import Cubical.WildCat.WithPred 
  -- hiding (ℙ)
open import Cubical.LU2C.Base

module Cubical.LU2C.PropRestricts where

private
  variable
    ℓC ℓC' ℓD ℓD' : Level

module _ 
  (WC : WildCat ℓC ℓC')
  (P : ℙ (WC .WildCat.ob))
  (restricts : IsLU2C (ΣPredWildCat WC P))
  where

  PropRestricts : LU2C _ _
  PropRestricts = record where
    str = ΣPredWildCat WC P
    isLU2C = restricts
