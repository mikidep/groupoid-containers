
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Reflection.StrictEquiv

open import Cubical.Container.Base
open import Cubical.Container.Monoid.Definition
open import Cubical.Container.Monoid.PsMndCont

open import Prelude.Shapes

module Cubical.Container.Monoid.Equivalence.Equiv
  (T : Container) where

open import Cubical.Container.Monoid.Equivalence.To T
open import Cubical.Container.Monoid.Equivalence.From T

unquoteDecl PsMndCont≃Pseudomonoid = 
  declStrictEquiv PsMndCont≃Pseudomonoid 
    PsMndCont→Pseudomonoid 
    Pseudomonoid→PsMndCont
