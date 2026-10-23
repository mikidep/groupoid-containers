open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Unit

open import Cubical.Container.Base
open import Cubical.Container.GpdCont

import Cubical.Container.Constructions as CC
open CC.Monoidal

open import Cubical.WildCat.Instances.GpdCont
open import Cubical.WildCat.Monoidal.Base
open import Cubical.WildCat.Monoidal.FullSub

open import Cubical.WildCat.Monoidal.Instances.Container

module Cubical.WildCat.Monoidal.Instances.GpdCont where

MonGpdCont : MonoidalWildCat _ _
MonGpdCont .fst = GpdContWildCat
MonGpdCont .snd = isMonFullSub 
  MonContainer 
  IsGpdCont
  record where
    P𝟙 = isGpd𝕀
    P⊗ = isGpd⨾
