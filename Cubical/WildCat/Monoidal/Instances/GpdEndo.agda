open import Cubical.Foundations.Prelude

open import Cubical.WildCat.BraidedSymmetricMonoidal
open import Cubical.WildCat.Product renaming (_×_ to ProdCat)

open import Cubical.Bicategory.Copresheaf ℓ-zero using (GPD)
open import Cubical.Bicategory.Instances.Copresheaf ℓ-zero

module Cubical.WildCat.Monoidal.Instances.GpdEndo where

GpdEndoWildCat = CopshWildCat GPD

module _ where
  open isMonoidalWildCat

  isMonoidalGpdEndo : isMonoidalWildCat GpdEndoWildCat
  isMonoidalGpdEndo ._⊗_ = {! !}
  isMonoidalGpdEndo .𝟙 = {! !}
  isMonoidalGpdEndo .⊗assoc = {! !}
  isMonoidalGpdEndo .⊗lUnit = {! !}
  isMonoidalGpdEndo .⊗rUnit = {! !}
  isMonoidalGpdEndo .triang = {! !}
  isMonoidalGpdEndo .⊗pentagon = {! !}
