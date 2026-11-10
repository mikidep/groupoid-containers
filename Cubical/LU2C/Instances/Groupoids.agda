open import Cubical.Foundations.Prelude 
open import Cubical.LU2C.Base
open import Cubical.LU2C.PropRestricts
open import Cubical.WildCat.Functor
open import Cubical.WildCat.Instances.Types
open import Cubical.WildCat.AsLU2C.Instances
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.HLevels

module Cubical.LU2C.Instances.Groupoids (ℓ : Level) where

open import Cubical.WildCat.Base
open import Cubical.WildCat.FullSub

private
  ⟨HGpd⟩ = FullSubWildCat (TypeCat ℓ) (λ X → Lift (isGroupoid X)) 
  module ⟨HGpd⟩ = WildCat ⟨HGpd⟩

open import Reflection.InferSigma using (inferΣ)
HGpdIsGpdHom : {@(tactic inferΣ ⟨HGpd⟩.ob) a b : ⟨HGpd⟩.ob}
  → isGroupoid (⟨HGpd⟩.Hom[ a , b ])
HGpdIsGpdHom {b = (X , lift isGpdX)} = isGroupoidΠ λ _ → isGpdX

HGpd : LU2C (ℓ-suc ℓ) ℓ
HGpd = PropRestricts (TypeCat ℓ) (λ X → Lift (isGroupoid X)) 
  record where
  triangle f g = sym (lUnit _)
  pentagon f g h k = cong (refl ∙_) (sym (lUnit _))
  isGpdHom = HGpdIsGpdHom

module NotHGpd where
  open NotWC (TypeCat ℓ) public

module NotHGpdFunct {ℓD ℓD' : Level} 
  {D : WildCat ℓD ℓD'} 
  (F : WildFunctor ⟨HGpd⟩ D)
  where

  open import Cubical.WildCat.FullSub.Functor.Notation
    {ℓD = ℓD} {ℓD'}
    {C = TypeCat ℓ}
    {P = λ X → Lift (isGroupoid X)}
    {D} F
    public
