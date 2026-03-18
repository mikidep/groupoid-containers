open import Prelude

-- Pseudofunctor?

module Cubical.Prebicategory.Functor where

open import Cubical.Prebicategory.Base
open import Cubical.WildCat.Base
open import Cubical.WildCat.Functor

private
  variable
    ℓC ℓC' ℓD ℓD' : Level

Functor : Prebicategory ℓC ℓC' → Prebicategory ℓD ℓD'
  → Type (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓD ℓD'))
Functor C D = WildFunctor (C .str) (D .str)
  where open Prebicategory

module _ {C : Prebicategory ℓC ℓC'} {D : Prebicategory ℓD ℓD'}
  where

  module _ {F G : Functor C D}
    (α : WildNatTrans _ _ F G) where

    open Prebicategory C using () 
      renaming (Hom[_,_] to C[_,_]; id to idᶜ; _⋆_ to _⋆ᶜ_)
    open Prebicategory D using (_◃_; _▹_) 
      renaming (
        _⋆_ to _⋆ᵈ_; 
        id to idᵈ; 
        ⋆IdL to D-⋆IdL;
        ⋆IdR to D-⋆IdR;
        ⋆Assoc to D-⋆Assoc
      )
    open WildNatTrans α using ()
      renaming (N-ob to α₀; N-hom to α□)
    open WildFunctor F using (F-id; F-seq)
      renaming (F-hom to F₁)
    open WildFunctor G using ()
      renaming (F-hom to G₁; F-id to G-id; F-seq to G-seq)

    record is2NatTrans : Type (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓD ℓD')) where
      field
        N-hom-id :
          ∀ {X} 
          →   α□ (idᶜ {X})
              ∙ (α₀ X ◃ G-id)
              ∙ D-⋆IdR (α₀ X)
            ≡ (F-id ▹ α₀ X) 
              ∙ D-⋆IdL (α₀ X)
        N-hom-seq : 
          ∀ {X} {Y} {Z} (f : C[ X , Y ]) (g : C[ Y , Z ])
          →   α□ (f ⋆ᶜ g) 
              ∙ (α₀ X ◃ G-seq f g) 
            ≡ (F-seq f g ▹ α₀ Z)
              ∙ D-⋆Assoc (F₁ f) (F₁ g) (α₀ Z)
              ∙ (F₁ f ◃ α□ g)
              ∙ sym (D-⋆Assoc (F₁ f) (α₀ Y) (G₁ g))
              ∙ (α□ f ▹ G₁ g)
              ∙ D-⋆Assoc (α₀ X) (G₁ f) (G₁ g)
    
  module _ (F G : Functor C D) where
    2NatTrans = Σ (WildNatTrans _ _ F G) is2NatTrans 
