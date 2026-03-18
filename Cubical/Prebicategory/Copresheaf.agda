{-# OPTIONS --lossy-unification #-}

open import Cubical.Foundations.Prelude

module Cubical.Prebicategory.Copresheaf (ℓ : Level) where

open import Cubical.Prebicategory.Base
open import Cubical.Prebicategory.Functor 
  hiding (is2NatTrans; 2NatTrans)
open import Cubical.Prebicategory.Instances.Groupoids

open import Cubical.WildCat.Base
open import Cubical.WildCat.Functor

private
  variable
    ℓC ℓC′ : Level

GPD = GpdPrebicat ℓ

Copresheaf : Prebicategory ℓC ℓC′ → Type _
Copresheaf C = Functor C GPD

module _ {C : Prebicategory ℓC ℓC′} where
  module _ {F G : Copresheaf C}
    (α : WildNatTrans _ _ F G) where

    open Prebicategory C using () 
      renaming (Hom[_,_] to C[_,_]; id to idᶜ; _⋆_ to _⋆ᶜ_)
    open Prebicategory GPD using (_◃_; _▹_) 
      renaming (
        _⋆_ to _⋆ᵈ_; 
        id to idᵈ
      )
    open WildNatTrans α using ()
      renaming (N-ob to α₀; N-hom to α□)
    open WildFunctor F using (F-id; F-seq)
      renaming (F-hom to F₁)
    open WildFunctor G using ()
      renaming (F-hom to G₁; F-id to G-id; F-seq to G-seq)

    record is2NatTrans : Type (ℓ-max (ℓ-max ℓC ℓC′) (ℓ-suc ℓ)) where
      field
        N-hom-id :
          ∀ {X} 
          →   α□ (idᶜ {X})
              ∙ (α₀ X ◃ G-id)
            ≡ (F-id ▹ α₀ X) 
        N-hom-seq : 
          ∀ {X} {Y} {Z} (f : C[ X , Y ]) (g : C[ Y , Z ])
          →   α□ (f ⋆ᶜ g) 
              ∙ (α₀ X ◃ G-seq f g) 
            ≡ (F-seq f g ▹ α₀ Z)
              ∙ (F₁ f ◃ α□ g)
              ∙ (α□ f ▹ G₁ g)

  module _ (F G : Copresheaf C) where
    2NatTrans = Σ (WildNatTrans _ _ F G) is2NatTrans 

  module _ {F G : Copresheaf C}
    {α β : 2NatTrans F G} where

    open import Cubical.Data.Sigma using (ΣPathP)

    make2NatTransPath :
      α .fst ≡ β .fst
      → α ≡ β
    make2NatTransPath α≡β = ΣPathP ({! !} , {! !})
    -- Strategy:
    -- prove is2NatTrans is a proposition
    -- find the appropriate lemma
