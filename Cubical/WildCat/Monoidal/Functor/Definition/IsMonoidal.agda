open import Cubical.Foundations.Prelude

open import Cubical.WildCat.Base
open import Cubical.WildCat.Functor

open import Cubical.WildCat.Monoidal.Base

module Cubical.WildCat.Monoidal.Functor.Definition.IsMonoidal
  {ℓC ℓC' ℓD ℓD' : Level}
  (MC : MonoidalWildCat ℓC ℓC')
  (MD : MonoidalWildCat ℓD ℓD') 
  (F : WildFunctor (MC .fst) (MD .fst))
  where

open import Cubical.WildCat.Monoidal.Functor.Definition.Structure MC MD F
open import Cubical.WildCat.Monoidal.Functor.Definition.Endpoints MC MD F

private
  C = MC .fst
  D = MD .fst

record IsMonoidal 
  : Type (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓD ℓD')) where
  field
    mStr : MonoidalFunctorStr
    F-⊗lUnit : F-⊗lUnitₗ mStr ≡ F-⊗lUnitᵣ mStr
    F-⊗rUnit : F-⊗rUnitₗ mStr ≡ F-⊗rUnitᵣ mStr
    F-⊗assoc : F-⊗assocₗ mStr ≡ F-⊗assocᵣ mStr
  open MonoidalFunctorStr mStr public

record IsStrongMonoidal 
  : Type (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓD ℓD')) where
  field
    isMonoidal : IsMonoidal
  open IsMonoidal isMonoidal public
  field
    isIsoF-𝟙 : wildIsIso {C = D} F-𝟙
    isIsoF-⊗ : (x y : WildCat.ob C) → wildIsIso {C = D} (F-⊗ .WildNatTrans.N-ob (x , y))
