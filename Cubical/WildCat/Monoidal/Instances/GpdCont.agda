open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Unit

open import Cubical.Container.Base
-- import Cubical.Container.Constructions as CC
-- open import Cubical.Bicategory.Copresheaf ℓ-zero
-- open import Cubical.Bicategory.Instances.Container
--
-- open import Cubical.WildCat.Base 
-- open import Cubical.WildCat.Functor 
-- open import Cubical.WildCat.Product 

import Cubical.Container.Constructions as CC
open CC.Monoidal

open import Cubical.WildCat.Instances.GpdCont
open import Cubical.WildCat.Monoidal.Base
open import Cubical.WildCat.Monoidal.WithPred

open import Cubical.WildCat.Monoidal.Instances.Container

module Cubical.WildCat.Monoidal.Instances.GpdCont where

open IsGpdContainer

isGpd𝕀 : IsGpdContainer 𝕀 
isGpd𝕀 .isGpdS = isSet→isGroupoid isSetUnit
isGpd𝕀 .isGpdP = isSet→isGroupoid isSetUnit

module _ {F G : Container} 
  (isGpdF : IsGpdContainer F)
  (isGpdG : IsGpdContainer G)
  where

  isGpd⨾ : IsGpdContainer (F ⨾₀ G) 
  isGpd⨾ .isGpdS = isGpd⟦-⟧₀ isGpdG (isGpdF .isGpdS)
  isGpd⨾ .isGpdP = isGroupoidΣ 
    (isGpdG .isGpdP) 
    λ _ → isGpdF .isGpdP

MonGpdCont : MonoidalWildCat _ _
MonGpdCont .fst = GpdContWildCat
MonGpdCont .snd = isMonΣPred 
  MonContainer 
  IsGpdContainer
  record where
    P𝟙 = isGpd𝕀
    P⊗ = isGpd⨾
