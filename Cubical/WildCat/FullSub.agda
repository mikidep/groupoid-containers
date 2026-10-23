open import Cubical.Foundations.Prelude 
open import Cubical.WildCat.Base
open import Cubical.WildCat.Functor

module Cubical.WildCat.FullSub where

private
  variable
    ℓC ℓC' ℓD ℓD' : Level

open WildCat using (ob)

ℙ : Type ℓC → Type (ℓ-suc ℓC)
ℙ X = X → Type _

module _ (C : WildCat ℓC ℓC') where
  private module C = WildCat C

  FullSubWildCat : (P : ℙ (C .ob)) → WildCat ℓC ℓC'
  FullSubWildCat P = record where
    ob = Σ _ P
    Hom[_,_] x y = C.Hom[ fst x , fst y ]
    id = C.id
    _⋆_ = C._⋆_
    ⋆IdL = C.⋆IdL
    ⋆IdR = C.⋆IdR
    ⋆Assoc = C.⋆Assoc

module _ {C : WildCat ℓC ℓC'} {D : WildCat ℓD ℓD'} 
  {P : ℙ (C .ob)} {Q : ℙ (D .ob)} where
  open WildFunctor
  
  -- Functoriality on full subcategories defined by propositions
  FullSubWildFunct : (F : WildFunctor C D)
               → (∀ c → P c → Q (F .F-ob c))
               → WildFunctor (FullSubWildCat C P) (FullSubWildCat D Q)
  FullSubWildFunct F FPres .F-ob (c , c∈P) = F .F-ob c , FPres c c∈P
  FullSubWildFunct F FPres .F-hom {(x , _)} {(y , _)} = F .F-hom
  FullSubWildFunct F FPres .F-id {(x , _)} = F .F-id
  FullSubWildFunct F FPres .F-seq {(x , _)} {(y , _)} {(z , _)}= F .F-seq
