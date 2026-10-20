open import Cubical.Foundations.Prelude
open import Cubical.LU2C.Base
open import Cubical.LU2C.PropRestricts
open import Cubical.WildCat.Instances.Types
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.HLevels

module Cubical.LU2C.Instances.Groupoids (ℓ : Level) where

HGpd : LU2C (ℓ-suc ℓ) ℓ
HGpd = PropRestricts (TypeCat ℓ) (λ X → Lift (isGroupoid X)) 
  record where
  triangle f g = sym (lUnit _)
  pentagon f g h k = cong (refl ∙_) (sym (lUnit _))
  isGpdHom {b = (X , lift isGpdX)} = isGroupoidΠ λ _ → isGpdX
