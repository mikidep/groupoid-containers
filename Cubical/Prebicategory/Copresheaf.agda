{-# OPTIONS --lossy-unification #-}

open import Cubical.Foundations.Prelude

module Cubical.Prebicategory.Copresheaf (ℓ : Level) where

open import Cubical.Prebicategory.Base
open import Cubical.Prebicategory.Functor 
  hiding (WildNatTransU; is2NatTrans; 2NatTrans)
open import Cubical.Prebicategory.Instances.Groupoids

open import Cubical.WildCat.Base
open import Cubical.WildCat.Functor
open import Cubical.WildCat.Instances.WildCopresheaf as WC

private
  variable
    ℓC ℓC′ : Level

GPD = GpdPrebicat ℓ

module _ (C : Prebicategory ℓC ℓC′) where
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
  open Prebicategory GPD using (_◃_; _▹_) 
    renaming (
      str to ⟨GPD⟩;
      _⋆_ to _⋆ᵈ_; 
      id to idᵈ; 
      ⋆IdL to D-⋆IdL;
      ⋆IdR to D-⋆IdR;
      ⋆Assoc to D-⋆Assoc
    )
  record Is2Copresheaf 
    (F : WildFunctor ⟨C⟩ ⟨GPD⟩)
    : Type (ℓ-max (ℓ-max ℓC ℓC′) (ℓ-suc ℓ)) where
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
          ≡ cong F₁ (C-⋆IdL f)
      F-IdR : ∀ {x y} {f : C[ x , y ]} 
        → F-seq f idᶜ 
          ∙ (F₁ f ◃ F-id)
          ≡ cong F₁ (C-⋆IdR f)
      F-Assoc : ∀ {x y z w} 
        {f : C[ x , y ]} 
        {g : C[ y , z ]} 
        {h : C[ z , w ]} 
        → F-seq (f ⋆ᶜ g) h
          ∙ (F-seq f g ▹ F₁ h)
          ≡ cong F₁ (C-⋆Assoc f g h)
          ∙ F-seq f (g ⋆ᶜ h)
          ∙ (F₁ f ◃ F-seq g h)

  record Copresheaf 
    : Type (ℓ-max (ℓ-max ℓC ℓC′) (ℓ-suc ℓ)) where
    field
      str : WildFunctor ⟨C⟩ ⟨GPD⟩
      is2Copresheaf : Is2Copresheaf str
    open WildFunctor str public
    open Is2Copresheaf is2Copresheaf public

module _ {C : Prebicategory ℓC ℓC′} where
  module _ (F G : Copresheaf C) where
    WildNatTransU : Type _
    WildNatTransU = WildNatTrans _ _ (F .str) (G .str)
      where open Copresheaf

  module _ {F G : Copresheaf C}
    (α : WildNatTransU F G) where

    open Prebicategory C using () 
      renaming (Hom[_,_] to C[_,_]; id to idᶜ; _⋆_ to _⋆ᶜ_)
    open Prebicategory GPD using (_◃_; _▹_) 
      renaming (
        _⋆_ to _⋆ᵈ_; 
        id to idᵈ;
        isGpdHom to isGpdHomGPD
      )
    open WildNatTrans α using ()
      renaming (N-ob to α₀; N-hom to α□)
    open Copresheaf F using (F-id; F-seq)
      renaming (F-hom to F₁)
    open Copresheaf G using ()
      renaming (F-hom to G₁; F-id to G-id; F-seq to G-seq)

    record is2NatTrans : Type (ℓ-max (ℓ-max ℓC ℓC′) (ℓ-suc ℓ)) where
      field
        N-hom-nat : 
          ∀ {X} {Y} 
            (f g : C[ X , Y ])
            (f≡g : f ≡ g)
          →   α□ f ∙ (α₀ X ◃ cong G₁ f≡g)
            ≡ (cong F₁ f≡g ▹ α₀ Y) ∙ α□ g
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

    open import Cubical.Foundations.HLevels
    open is2NatTrans
    isProp-is2NatTrans : isProp is2NatTrans
    isProp-is2NatTrans αis βis i .N-hom-id {X} = aux i
      where
      aux : αis .N-hom-id {X} ≡ βis .N-hom-id 
      aux = isGpdHomGPD _ _ _ _ (αis .N-hom-id) (βis .N-hom-id)
    isProp-is2NatTrans αis βis i .N-hom-seq f g = aux i
      where
      aux : αis .N-hom-seq f g ≡ βis .N-hom-seq f g
      aux = isGpdHomGPD _ _ _ _ (αis .N-hom-seq f g) (βis .N-hom-seq f g)

  module _ (F G : Copresheaf C) where
    2NatTrans = Σ (WildNatTransU F G) is2NatTrans 

  module _ {F G : Copresheaf C}
    {α β : 2NatTrans F G} where

    make2NatTransPath :
      α .fst ≡ β .fst
      → α ≡ β
    make2NatTransPath = Σ≡Prop isProp-is2NatTrans
      where open import Cubical.Data.Sigma.Properties

  module _ (F : Copresheaf C) where
    open Prebicategory
    open WildNatTrans

    wid = WC.idWildNatTransTypes

    open import Cubical.Foundations.Function
    open is2NatTrans
    open import Cubical.Foundations.GroupoidLaws

    id2NatTrans : 2NatTrans F F
    id2NatTrans .fst .N-ob X = idfun _
    id2NatTrans .fst .N-hom _ = refl
    id2NatTrans .snd .N-hom-id = sym (lUnit _) 
    id2NatTrans .snd .N-hom-seq f g = 
      sym (lUnit _) 
      ∙ rUnit _ 
      ∙ cong (F-seq f g ∙_) (rUnit _)
      where
      open Copresheaf F using (F-seq)

  module _ {F G H : Copresheaf C}
    (α : 2NatTrans F G)
    (β : 2NatTrans G H) where

    open WildNatTrans
    open WildNatTrans (fst α) using ()
      renaming (N-ob to α₀; N-hom to α□)
    open WildNatTrans (fst β) using ()
      renaming (N-ob to β₀; N-hom to β□)
    open is2NatTrans
    open Prebicategory GPD renaming (_⋆_ to _»_)

    comp2NatTrans : 2NatTrans F H
    comp2NatTrans .fst .N-ob X = α₀ X » β₀ X
    comp2NatTrans .fst .N-hom {X} {Y} f = 
      (α□ f ▹ β₀ Y) ∙ (α₀ X ◃ β□ f)
    comp2NatTrans .snd .N-hom-id {X} = 
        idfun
        (
          ((α□ idᶜ ▹ β₀ X) ∙ (α₀ X ◃ β□ idᶜ)) ∙ (comp₀ X ◃ H-id)
          ≡ (F-id ▹ α₀ X) ▹ β₀ X
        )
        {!   !} 
      where 
        open Prebicategory C using ()
          renaming (id to idᶜ)
        open Copresheaf F using (F-id)
        open Copresheaf H using ()
          renaming (F-id to H-id)
        open import Prelude using (idfun)
        open WildNatTrans (comp2NatTrans .fst)
          renaming (N-ob to comp₀; N-hom to comp□)
    comp2NatTrans .snd .N-hom-seq = {! !}
