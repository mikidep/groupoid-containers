open import Cubical.Foundations.Prelude

open import Cubical.WildCat.Base
open import Cubical.WildCat.Functor
open import Cubical.WildCat.Product
open import Cubical.WildCat.Product.Functor
open import Cubical.WildCat.Monoidal.Base
open import Cubical.WildCat.Monoidal.Definition.IsMonoidal

module Cubical.WildCat.Monoidal.Functor.Definition.Structure
  {ℓC ℓC' ℓD ℓD' : Level}
  (MC : MonoidalWildCat ℓC ℓC')
  (MD : MonoidalWildCat ℓD ℓD') 
  (F : WildFunctor (MC .fst) (MD .fst))
  where

private
  C = MC .fst
  D = MD .fst
  module MC = isMonoidalWildCat (MC .snd)
  module MD = isMonoidalWildCat (MD .snd)

record MonoidalFunctorStr 
  : Type (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓD ℓD')) where
  field
    F-𝟙 : D [ MD.𝟙 , F .WildFunctor.F-ob MC.𝟙 ]
    F-⊗ : WildNatTrans (C × C) D
      (comp-WildFunctor (F ×₁ F) MD._⊗_)
      (comp-WildFunctor MC._⊗_ F)
