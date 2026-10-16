open import Cubical.Foundations.Prelude

open import Cubical.WildCat.Base
open import Cubical.WildCat.WithPred

open import Cubical.Container.Base
open import Cubical.WildCat.Instances.Container

module Cubical.WildCat.Instances.GpdCont where

record IsGpdContainer (F : Container) : Type₁ where
  open Container F
  field
    isGpdS : isGroupoid S
    isGpdP : ∀ {s : S} → isGroupoid (P s)


module _ {X : Type} {F : Container} (isGpdF : IsGpdContainer F) where
  open import Cubical.Foundations.HLevels
  open import Cubical.Container.Constructions as CC
  open CC.Extent
  open IsGpdContainer isGpdF

  isGpd⟦-⟧₀ : isGroupoid X → isGroupoid (⟦ F ⟧₀ X)
  isGpd⟦-⟧₀ isGpdX = isGroupoidΣ isGpdS λ _ → isGroupoidΠ λ _ → isGpdX

module _ {F : Container} where
  open IsGpdContainer
  open import Cubical.Foundations.HLevels

  isPropIsGpdContainer : isProp (IsGpdContainer F)
  isPropIsGpdContainer Fis Gis i .isGpdS = isPropIsGroupoid (Fis .isGpdS) (Gis .isGpdS) i
  isPropIsGpdContainer Fis Gis i .isGpdP {s} = isPropIsGroupoid (Fis .isGpdP {s}) (Gis .isGpdP {s}) i

GpdContWildCat : WildCat _ _
GpdContWildCat = ΣPredWildCat 
  ContainerWildCat 
  IsGpdContainer
