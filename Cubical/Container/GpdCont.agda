open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Unit

open import Cubical.Container.Base
open import Cubical.Container.Constructions as CC
open CC.Monoidal
open CC.Extent

module Cubical.Container.GpdCont where

record IsGpdCont (F : Container) : Type₁ where
  open Container F
  field
    isGpdS : isGroupoid S
    isGpdP : ∀ {s : S} → isGroupoid (P s)

module _ {X : Type} {F : Container} (isGpdF : IsGpdCont F) where
  open IsGpdCont
  isGpd⟦-⟧₀ : isGroupoid X → isGroupoid (⟦ F ⟧₀ X)
  isGpd⟦-⟧₀ isGpdX = isGroupoidΣ (isGpdF .isGpdS) 
    λ _ → isGroupoidΠ λ _ → isGpdX

isPropIsGpdCont : {F : Container} → isProp (IsGpdCont F)
isPropIsGpdCont Fis Gis i = record where
  open IsGpdCont
  isGpdS = isPropIsGroupoid (Fis .isGpdS) (Gis .isGpdS) i
  isGpdP {s} = isPropIsGroupoid (Fis .isGpdP {s}) (Gis .isGpdP {s}) i

isGpd𝕀 : IsGpdCont 𝕀 
isGpd𝕀 = record where
  isGpdS = isSet→isGroupoid isSetUnit
  isGpdP = isSet→isGroupoid isSetUnit

module _ {F G : Container} 
  (isGpdF : IsGpdCont F)
  (isGpdG : IsGpdCont G)
  where

  open IsGpdCont isGpdF
  open IsGpdCont isGpdG 
    renaming (isGpdS to isGpdS′; isGpdP to isGpdP′)

  open import Cubical.Reflection.RecordEquiv
  open import Cubical.Foundations.Isomorphism
  open import Cubical.Foundations.Equiv

  isGpd⇒ : isGroupoid (F ⇒ G)
  isGpd⇒ = isOfHLevelRespectEquiv 3
    (invEquiv ContHomEquivΣ)
    (isGroupoidΣ (isGroupoidΠ λ _ → isGpdS′)
      λ _ → isGroupoidΠ2 λ s _ → isGpdP {s}
    )
    where
    unquoteDecl ContHomIsoΣ = declareRecordIsoΣ ContHomIsoΣ (quote _⇒_)
    ContHomEquivΣ = isoToEquiv (ContHomIsoΣ {F} {G})

  isGpd⨾ : IsGpdCont (F ⨾₀ G) 
  isGpd⨾ = record where
    isGpdS = isGpd⟦-⟧₀ isGpdG isGpdS
    isGpdP = isGroupoidΣ isGpdP′ λ _ → isGpdP
