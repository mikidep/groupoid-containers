open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.HLevels
open import Cubical.WildCat.Base

module Cubical.WildCat.WithPred where

private
  variable
    ℓ ℓ' ℓ'' : Level

open WildCat

module _ {C : WildCat ℓ ℓ'} where
  obWithProp : (P : C .ob → Type ℓ'') → Type (ℓ-max ℓ ℓ'')
  obWithProp P = Σ[ x ∈ C .ob ] P x

ΣPropCat : (C : WildCat ℓ ℓ') (P : C .ob → Type ℓ'') → WildCat (ℓ-max ℓ ℓ'') ℓ'
ob (ΣPropCat C P) = obWithProp {C = C} P
Hom[_,_] (ΣPropCat C P) x y = C [ fst x , fst y ]
id (ΣPropCat C P) = id C
_⋆_ (ΣPropCat C P) = _⋆_ C
⋆IdL (ΣPropCat C P) = ⋆IdL C
⋆IdR (ΣPropCat C P) = ⋆IdR C
⋆Assoc (ΣPropCat C P) = ⋆Assoc C
