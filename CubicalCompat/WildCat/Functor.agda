module CubicalCompat.WildCat.Functor where

open import Cubical.Foundations.Prelude

open import Cubical.WildCat.Base
open import Cubical.WildCat.Functor

private
  variable
    ℓC ℓC' ℓD ℓD' : Level

open WildCat
open WildNatTrans

idWildNatTrans : {C : WildCat ℓC ℓC'} {D : WildCat ℓD ℓD'} {F : WildFunctor C D} → WildNatTrans _ _ F F
idWildNatTrans {D = D} .N-ob x = D .id
idWildNatTrans {D = D} .N-hom f = D .⋆IdR _ ∙ sym (D .⋆IdL _)

-- open import CubicalCompat.Reflection.RecordEquiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv

-- unquoteDecl WildFunctorIsoΣ = declareRecordIsoΣ WildFunctorIsoΣ (quote WildFunctor)
-- WildFunctorEquivΣ = isoToEquiv WildFunctorIsoΣ

module _ {C : WildCat ℓC ℓC'} {D : WildCat ℓD ℓD'} {F G : WildFunctor C D} where
  open WildFunctor

  WildFunctor≡ :
    (F-ob≡ : (c : C .ob) → F .F-ob c ≡ G .F-ob c)
    (F-hom≡ : {x y : C .ob} (f : C [ x , y ]) 
      → PathP 
        (λ i → D [ F-ob≡ x i , F-ob≡ y i ])
        (F .F-hom f)
        (G .F-hom f)) 
    (F-id≡ : {x : C .ob} 
      → PathP
        (λ i → F-hom≡ {y = x} (id C) i ≡ id D)
        (F .F-id {x})
        (G .F-id {x}))
    (F-seq≡ : {x y z : C .ob} (f : C [ x , y ]) (g : C [ y , z ])
      → PathP
        (λ i → F-hom≡ (f ⋆⟨ C ⟩ g) i ≡ (F-hom≡ f i) ⋆⟨ D ⟩ (F-hom≡ g i))
        (F .F-seq f g)
        (G .F-seq f g))
    → F ≡ G
  WildFunctor≡ F-ob≡ F-hom≡ F-id≡ F-seq≡ i .F-ob c = F-ob≡ c i
  WildFunctor≡ F-ob≡ F-hom≡ F-id≡ F-seq≡ i .F-hom f = F-hom≡ f i
  WildFunctor≡ F-ob≡ F-hom≡ F-id≡ F-seq≡ i .F-id = F-id≡ i
  WildFunctor≡ F-ob≡ F-hom≡ F-id≡ F-seq≡ i .F-seq f g = F-seq≡ f g i
    
