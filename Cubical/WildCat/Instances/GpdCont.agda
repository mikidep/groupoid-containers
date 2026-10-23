open import Cubical.Foundations.Prelude

open import Cubical.WildCat.Base
open import Cubical.WildCat.FullSub

open import Cubical.Container.Base
open import Cubical.Container.GpdCont
open import Cubical.WildCat.Instances.Container

module Cubical.WildCat.Instances.GpdCont where

GpdContWildCat : WildCat _ _
GpdContWildCat = FullSubWildCat 
  ContainerWildCat 
  IsGpdCont
