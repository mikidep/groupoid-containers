open import Cubical.Foundations.Prelude

open import Cubical.WildCat.BraidedSymmetricMonoidal
open import Cubical.WildCat.Product renaming (_×_ to ProdCat)

open import Cubical.Bicategory.Copresheaf ℓ-zero using (GPD)
open import Cubical.Bicategory.Instances.Copresheaf ℓ-zero
open import Cubical.Bicategory.Copresheaf.EndoConstructions ℓ-zero

module Cubical.WildCat.Monoidal.Instances.GpdEndo where

module _ where
  open isMonoidalWildCat

  isMonoidalGpdEndo : isMonoidalWildCat GpdEndoWildCat
  isMonoidalGpdEndo ._⊗_ = compEndo
  isMonoidalGpdEndo .𝟙 = idEndo
  isMonoidalGpdEndo .⊗assoc = {! !}
  isMonoidalGpdEndo .⊗lUnit = {! !}
  isMonoidalGpdEndo .⊗rUnit = {! !}
  isMonoidalGpdEndo .triang = {! !}
  isMonoidalGpdEndo .⊗pentagon = {! !}
