{-# OPTIONS --lossy-unification #-}
open import Prelude

-- Pseudofunctor?

module Cubical.Prebicategory.Functor where

open import Cubical.Prebicategory.Base
open import Cubical.WildCat.Base
open import Cubical.WildCat.Functor

private
  variable
    ℓC ℓC' ℓD ℓD' : Level

module _ (C : Prebicategory ℓC ℓC') 
  (D : Prebicategory ℓD ℓD') where

  open Prebicategory C using () 
    renaming (
      str to ⟨C⟩;
      Hom[_,_] to C[_,_]; 
      id to idᶜ; 
      _⋆_ to _⋆ᶜ_;
      ⋆IdL to C-⋆IdL;
      ⋆IdR to C-⋆IdR;
      ⋆Assoc to C-⋆Assoc
    )
  open Prebicategory D using (_◃_; _▹_) 
    renaming (
      str to ⟨D⟩;
      _⋆_ to _⋆ᵈ_; 
      id to idᵈ; 
      ⋆IdL to D-⋆IdL;
      ⋆IdR to D-⋆IdR;
      ⋆Assoc to D-⋆Assoc
    )

  record Is2Functor 
    (F : WildFunctor ⟨C⟩ ⟨D⟩)
    : Type (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓD ℓD')) where
    open WildFunctor F using (
        F-id;
        F-seq
      ) renaming (
        F-ob to F₀; F-hom to F₁
      )
    field
      F-IdL : ∀ {x y} {f : C[ x , y ]} 
        → F-seq idᶜ f
          ∙ (F-id ▹ F₁ f)
          ∙ D-⋆IdL (F₁ f) 
          ≡ cong F₁ (C-⋆IdL f)
      F-IdR : ∀ {x y} {f : C[ x , y ]} 
        → F-seq f idᶜ 
          ∙ (F₁ f ◃ F-id)
          ∙ D-⋆IdR (F₁ f)
          ≡ cong F₁ (C-⋆IdR f)
      F-Assoc : ∀ {x y z w} 
        {f : C[ x , y ]} 
        {g : C[ y , z ]} 
        {h : C[ z , w ]} 
        → F-seq (f ⋆ᶜ g) h
          ∙ (F-seq f g ▹ F₁ h)
          ∙ D-⋆Assoc (F₁ f) (F₁ g) (F₁ h)
          ≡ cong F₁ (C-⋆Assoc f g h)
          ∙ F-seq f (g ⋆ᶜ h)
          ∙ (F₁ f ◃ F-seq g h)

  record Functor 
    : Type (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓD ℓD')) where
    field
      str : WildFunctor ⟨C⟩ ⟨D⟩
      is2Functor : Is2Functor str
    open WildFunctor str public
    open Is2Functor is2Functor public

module _ {C : Prebicategory ℓC ℓC'} {D : Prebicategory ℓD ℓD'}
  where

  module _ (F G : Functor C D) where
    WildNatTransU : Type _
    WildNatTransU = WildNatTrans _ _ (F .str) (G .str)
      where open Functor

  module _ {F G : Functor C D}
    (α : WildNatTransU F G) where

    open Prebicategory C using () 
      renaming (Hom[_,_] to C[_,_]; id to idᶜ; _⋆_ to _⋆ᶜ_)
    open Prebicategory D using (_◃_; _▹_) 
      renaming (
        str to ⟨D⟩;
        _⋆_ to _⋆ᵈ_; 
        id to idᵈ; 
        ⋆IdL to D-⋆IdL;
        ⋆IdR to D-⋆IdR;
        ⋆Assoc to D-⋆Assoc
      )
    open WildNatTrans α using ()
      renaming (N-ob to α₀; N-hom to α□)
    open Functor F using (F-id; F-seq)
      renaming (F-hom to F₁)
    open Functor G using ()
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
    2NatTrans = Σ (WildNatTransU F G) is2NatTrans 
