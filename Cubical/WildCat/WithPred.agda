open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Powerset
open import Cubical.WildCat.Base

module Cubical.WildCat.WithPred where

private
  variable
    ℓ ℓ' : Level

open WildCat

ΣPropCat : (C : WildCat ℓ ℓ') (P : ℙ (ob C)) → WildCat ℓ ℓ'
ob (ΣPropCat C P) = Σ[ x ∈ ob C ] x ∈ P
Hom[_,_] (ΣPropCat C P) x y = C [ fst x , fst y ]
id (ΣPropCat C P) = id C
_⋆_ (ΣPropCat C P) = _⋆_ C
⋆IdL (ΣPropCat C P) = ⋆IdL C
⋆IdR (ΣPropCat C P) = ⋆IdR C
⋆Assoc (ΣPropCat C P) = ⋆Assoc C
