open import Cubical.Foundations.Prelude
-- open import Cubical.Foundations.Powerset
open import Cubical.Foundations.HLevels
open import Cubical.WildCat.Base
open import Cubical.WildCat.Functor
open import Cubical.WildCat.Product

module Cubical.WildCat.WithPred where

private
  variable
    ℓC ℓC' ℓD ℓD' : Level

open WildCat

ℙ : Type ℓC → Type (ℓ-suc ℓC)
ℙ X = X → Type _

ΣPredWildCat : (C : WildCat ℓC ℓC') (P : ℙ (C .ob)) → WildCat ℓC ℓC'
ob (ΣPredWildCat C P) = Σ _ P
Hom[_,_] (ΣPredWildCat C P) x y = C [ fst x , fst y ]
id (ΣPredWildCat C P) = id C
_⋆_ (ΣPredWildCat C P) = _⋆_ C
⋆IdL (ΣPredWildCat C P) = ⋆IdL C
⋆IdR (ΣPredWildCat C P) = ⋆IdR C
⋆Assoc (ΣPredWildCat C P) = ⋆Assoc C

module _ {C : WildCat ℓC ℓC'} {D : WildCat ℓD ℓD'} 
  {P : ℙ (C .ob)} {Q : ℙ (D .ob)} where
  open WildFunctor
  
  -- Functoriality on full subcategories defined by propositions
  ΣPredWildFunct : (F : WildFunctor C D)
               → (∀ c → P c → Q (F .F-ob c))
               → WildFunctor (ΣPredWildCat C P) (ΣPredWildCat D Q)
  ΣPredWildFunct F FPres .F-ob (c , c∈P) = F .F-ob c , FPres c c∈P
  ΣPredWildFunct F FPres .F-hom = F .F-hom
  ΣPredWildFunct F FPres .F-id = F .F-id
  ΣPredWildFunct F FPres .F-seq = F .F-seq
