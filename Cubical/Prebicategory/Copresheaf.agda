{-# OPTIONS --allow-unsolved-metas #-}

open import Cubical.Foundations.Prelude

module Cubical.Prebicategory.Copresheaf (ℓ : Level) where

open import Cubical.Prebicategory.Base
open import Cubical.Prebicategory.Instances.Groupoids

open import Cubical.WildCat.Base
open import Cubical.WildCat.Functor
open import Cubical.WildCat.Instances.WildCopresheaf as WC

private
  variable
    ℓC ℓC′ : Level

GPD = GpdPrebicat ℓ
-- In GPD, whiskering
-- commutes with composition
-- definitionally, i.e.
-- f ⋆ g ◃ p ≡def f ◃ g ◃ p
-- and viceversa 

open Prebicategory GPD using () 
  renaming (
    str to ⟨GPD⟩;
    Hom[_,_] to D[_,_];
    _⋆_ to _⋆ᵈ_; 
    id to idᵈ;
    isGpdHom to isGpdHomGPD;
    ⋆IdL to D-⋆IdL;
    ⋆IdR to D-⋆IdR;
    ⋆Assoc to D-⋆Assoc
  )
open Whiskering ⟨GPD⟩
open 2CellLaws ⟨GPD⟩

module 2FunctNotation {C : WildCat ℓC ℓC′}
  (F : WildFunctor C ⟨GPD⟩) where
  open WildCat C using () 
    renaming (Hom[_,_] to C[_,_])

  open WildFunctor F using (
      F-id;
      F-seq
    ) renaming (
      F-ob to F₀; F-hom to F₁
    ) public
  F₂ : ∀ {X} {Y} {f g : C[ X , Y ]}
    (f≡g : f ≡ g)
    → F₁ f ≡ F₁ g
  F₂ = cong F₁

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
  
  record Is2Copresheaf 
    (F : WildFunctor ⟨C⟩ ⟨GPD⟩)
    : Type (ℓ-max (ℓ-max ℓC ℓC′) (ℓ-suc ℓ)) where
    open 2FunctNotation F
    field
      F-IdL : ∀ {x y} {f : C[ x , y ]} 
        → F-seq idᶜ f
          ∙ F-id ▹ F₁ f
          ≡ cong F₁ (C-⋆IdL f)
      F-IdR : ∀ {x y} {f : C[ x , y ]} 
        → F-seq f idᶜ 
          ∙ F₁ f ◃ F-id
          ≡ F₂ (C-⋆IdR f)
      F-Assoc : ∀ {x y z w} 
        {f : C[ x , y ]} 
        {g : C[ y , z ]} 
        {h : C[ z , w ]} 
        → F-seq (f ⋆ᶜ g) h
          ∙ F-seq f g ▹ F₁ h
          ≡ F₂ (C-⋆Assoc f g h)
          ∙ F-seq f (g ⋆ᶜ h)
          ∙ F₁ f ◃ F-seq g h

  record Copresheaf 
    : Type (ℓ-max (ℓ-max ℓC ℓC′) (ℓ-suc ℓ)) where
    field
      str : WildFunctor ⟨C⟩ ⟨GPD⟩
      is2Copresheaf : Is2Copresheaf str
    open 2FunctNotation str public
    open Is2Copresheaf is2Copresheaf public

module _ {C : Prebicategory ℓC ℓC′} where
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

  module _ {F G : WildFunctor ⟨C⟩ ⟨GPD⟩}
    (α : WildNatTrans _ _ F G) where

    open WildNatTrans α using ()
      renaming (N-ob to α₀; N-hom to α□)
    open 2FunctNotation F using (F-id; F-seq; F₁; F₂)
    open 2FunctNotation G using ()
      renaming (
        F₁ to G₁;
        F-id to G-id;
        F-seq to G-seq;
        F₂ to G₂
      )

    record is2NatTrans : Type (ℓ-max (ℓ-max ℓC ℓC′) (ℓ-suc ℓ)) where
      field
        N-hom-nat : 
          ∀ {X} {Y} 
            (f g : C[ X , Y ])
            (f≡g : f ≡ g)
          →   α□ f ∙ α₀ X ◃ G₂ f≡g
            ≡ F₂ f≡g ▹ α₀ Y ∙ α□ g
        N-hom-id :
          ∀ {X} 
          →   α□ (idᶜ {X})
              ∙ α₀ X ◃ G-id
            ≡ F-id ▹ α₀ X 
        N-hom-seq : 
          ∀ {X} {Y} {Z} (f : C[ X , Y ]) (g : C[ Y , Z ])
          →   α□ (f ⋆ᶜ g) 
              ∙ α₀ X ◃ G-seq f g 
            ≡ F-seq f g ▹ α₀ Z
              ∙ F₁ f ◃ α□ g
              ∙ α□ f ▹ G₁ g

    open import Cubical.Foundations.HLevels
    open is2NatTrans
    isPropIs2NatTrans : isProp is2NatTrans
    isPropIs2NatTrans αis βis i .N-hom-nat f g f≡g = aux i
      where
      aux : αis .N-hom-nat f g f≡g ≡ βis .N-hom-nat f g f≡g
      aux = isGpdHomGPD _ _ _ _ (αis .N-hom-nat f g f≡g) (βis .N-hom-nat f g f≡g)
    isPropIs2NatTrans αis βis i .N-hom-id {X} = aux i
      where
      aux : αis .N-hom-id {X} ≡ βis .N-hom-id 
      aux = isGpdHomGPD _ _ _ _ (αis .N-hom-id) (βis .N-hom-id)
    isPropIs2NatTrans αis βis i .N-hom-seq f g = aux i
      where
      aux : αis .N-hom-seq f g ≡ βis .N-hom-seq f g
      aux = isGpdHomGPD _ _ _ _ (αis .N-hom-seq f g) (βis .N-hom-seq f g)

  module _ (F G : Copresheaf C) where
    open Copresheaf using () renaming (str to ⟨_⟩)
    2NatTrans = Σ (WildNatTrans _ _ ⟨ F ⟩ ⟨ G ⟩) is2NatTrans

  module _ {F G : Copresheaf C}
    {α β : 2NatTrans F G} where

    open import Cubical.Data.Sigma.Properties
    open import Cubical.Foundations.Equiv

    make2NatTransPath :
      α .fst ≡ β .fst → α ≡ β
    make2NatTransPath = Σ≡Prop isPropIs2NatTrans 

    make2NatTransPathEquiv :
      (α .fst ≡ β .fst) ≃ (α ≡ β)
    make2NatTransPathEquiv = Σ≡PropEquiv isPropIs2NatTrans 

  module _ (F : Copresheaf C) where
    open Copresheaf F using (F₁; F₂; F-seq)
    open WildNatTrans
    open import Cubical.WildCat.Instances.WildCopresheaf as W

    wid = WC.idWildNatTransTypes

    open import Cubical.Foundations.Function
    open is2NatTrans
    open import Cubical.Foundations.GroupoidLaws

    id2NatTrans : 2NatTrans F F
    id2NatTrans .fst .N-ob X = idfun _
    id2NatTrans .fst .N-hom _ = refl
    id2NatTrans .snd .N-hom-nat f g f≡g = sym (lUnit _) ∙ rUnit _
    id2NatTrans .snd .N-hom-id = sym (lUnit _) 
    id2NatTrans .snd .N-hom-seq f g = 
      sym (lUnit _) 
      ∙ rUnit _ 
      ∙ cong (F-seq f g ∙_) (rUnit _)

  module _ {F G H : Copresheaf C}
    (α : 2NatTrans F G)
    (β : 2NatTrans G H) where

    open WildNatTrans
    open WildNatTrans (fst α) using ()
      renaming (N-ob to α₀; N-hom to α□)
    open WildNatTrans (fst β) using ()
      renaming (N-ob to β₀; N-hom to β□)
    open is2NatTrans

    open Copresheaf F using (F₀; F₁; F₂; F-id; F-seq)
    open Copresheaf G using ()
      renaming (F₀ to G₀; F₁ to G₁; F₂ to G₂; F-id to G-id; F-seq to G-seq)
    open Copresheaf H using ()
      renaming (F₀ to H₀; F₁ to H₁; F₂ to H₂; F-id to H-id; F-seq to H-seq)

    comp2NatTrans : 2NatTrans F H
    comp2NatTrans .fst .N-ob X = α₀ X ⋆ᵈ β₀ X
    comp2NatTrans .fst .N-hom {x = X} {y = Y} f = 
      α□ f ▹ β₀ Y ∙ α₀ X ◃ β□ f
    comp2NatTrans .snd .N-hom-nat {X} {Y} f g f≡g =
        (α□ f ▹ β₀ Y ∙ α₀ X ◃ β□ f) ∙ α₀ X ◃ β₀ X ◃ H₂ f≡g
      ≡⟨ sym (assoc _ _ _) ⟩ 
        α□ f ▹ β₀ Y ∙ α₀ X ◃ β□ f ∙ α₀ X ◃ β₀ X ◃ H₂ f≡g
      ≡⟨ cong (λ x → α□ f ▹ β₀ Y ∙ x) (sym (◃-∙ (β□ f) (β₀ X ◃ H₂ f≡g))) ⟩ 
        α□ f ▹ β₀ Y ∙ α₀ X ◃ (β□ f ∙ β₀ X ◃ H₂ f≡g)
      ≡⟨ cong (λ x → α□ f ▹ β₀ Y ∙ α₀ X ◃ x) (β .snd .N-hom-nat _ _ _) ⟩ 
        α□ f ▹ β₀ Y ∙ α₀ X ◃ (G₂ f≡g ▹ β₀ Y ∙ β□ g)
      ≡⟨ cong (λ x → α□ f ▹ β₀ Y ∙ x) (◃-∙ (G₂ f≡g ▹ β₀ Y) (β□ g)) ⟩ 
        α□ f ▹ β₀ Y ∙ α₀ X ◃ G₂ f≡g ▹ β₀ Y ∙ α₀ X ◃ β□ g
      ≡⟨ assoc _ _ _ ⟩ 
        (α□ f ▹ β₀ Y ∙ α₀ X ◃ G₂ f≡g ▹ β₀ Y) ∙ α₀ X ◃ β□ g
      ≡⟨ cong (_∙ α₀ X ◃ β□ g) (sym (▹-∙ (α□ f) (α₀ X ◃ G₂ f≡g))) ⟩ 
        (α□ f ∙ α₀ X ◃ G₂ f≡g) ▹ β₀ Y ∙ α₀ X ◃ β□ g
      ≡⟨ cong (λ x → x ▹ β₀ Y ∙ α₀ X ◃ β□ g) (α .snd .N-hom-nat _ _ _) ⟩ 
        (F₂ f≡g ▹ α₀ Y ∙ α□ g) ▹ β₀ Y ∙ α₀ X ◃ β□ g
      ≡⟨ cong (_∙ α₀ X ◃ β□ g) (▹-∙ (F₂ f≡g ▹ α₀ Y) (α□ g)) ⟩ 
        (F₂ f≡g ▹ α₀ Y ▹ β₀ Y ∙ α□ g ▹ β₀ Y) ∙ α₀ X ◃ β□ g 
      ≡⟨ sym (assoc _ _ _) ⟩ 
        F₂ f≡g ▹ α₀ Y ▹ β₀ Y ∙ α□ g ▹ β₀ Y ∙ α₀ X ◃ β□ g 
      ∎
      where
        open import Cubical.Foundations.GroupoidLaws
    comp2NatTrans .snd .N-hom-id {X} = 
        (α□ idᶜ ▹ β₀ X ∙ α₀ X ◃ β□ idᶜ) ∙ α₀ X ◃ β₀ X ◃ H-id
      ≡⟨ sym (assoc _ _ _) ⟩ 
        α□ idᶜ ▹ β₀ X ∙ α₀ X ◃ β□ idᶜ ∙ α₀ X ◃ β₀ X ◃ H-id
      ≡⟨ cong (α□ idᶜ ▹ β₀ X ∙_) (◃-∙ (β□ idᶜ) (β₀ X ◃ H-id)) ⟩ 
        α□ idᶜ ▹ β₀ X ∙ α₀ X ◃ (β□ idᶜ ∙ β₀ X ◃ H-id)
      ≡⟨ cong (λ x → α□ idᶜ ▹ β₀ X ∙ α₀ X ◃ x) (β .snd .N-hom-id) ⟩ 
        α□ idᶜ ▹ β₀ X ∙ α₀ X ◃ G-id ▹ β₀ X
      ≡⟨ sym (▹-∙ (α□ idᶜ) (α₀ X ◃ G-id)) ⟩ 
        (α□ idᶜ ∙ α₀ X ◃ G-id) ▹ β₀ X
      ≡⟨ cong (_▹ β₀ X) (α .snd .N-hom-id) ⟩ 
        F-id ▹ α₀ X ▹ β₀ X
      ∎
      where 
        open import Cubical.Foundations.GroupoidLaws
    comp2NatTrans .snd .N-hom-seq {X} {Y} {Z} f g = 
        (α□ (f ⋆ᶜ g) ▹ β₀ Z ∙ α₀ X ◃ β□ (f ⋆ᶜ g)) 
        ∙ α₀ X ◃ β₀ X ◃ H-seq f g
      ≡⟨ {! !} ⟩ 
        (F-seq f g ▹ α₀ Z ▹ β₀ Z ∙ F₁ f ◃ α□ g ▹ β₀ Z) 
        ∙ {! !} 
        ∙ α₀ X ◃ β□ f ▹ H₁ g
      ≡⟨ cong (λ x → (F-seq f g ▹ α₀ Z ▹ β₀ Z ∙ F₁ f ◃ α□ g ▹ β₀ Z) 
            ∙ x ∙ α₀ X ◃ β□ f ▹ H₁ g) 
          (sym (whisk-interchange (α□ f) (β□ g))) ⟩ 
        (F-seq f g ▹ α₀ Z ▹ β₀ Z ∙ F₁ f ◃ α□ g ▹ β₀ Z) 
        ∙ (F₁ f ◃ α₀ Y ◃ β□ g ∙ α□ f ▹ β₀ Y ▹ H₁ g) 
        ∙ α₀ X ◃ β□ f ▹ H₁ g
      ≡⟨ {! !} ⟩ -- assoc
        (F-seq f g ▹ α₀ Z ▹ β₀ Z ∙ F₁ f ◃ α□ g ▹ β₀ Z) 
        ∙ F₁ f ◃ α₀ Y ◃ β□ g
        ∙ α□ f ▹ β₀ Y ▹ H₁ g 
        ∙ α₀ X ◃ β□ f ▹ H₁ g
      ≡⟨ {! !} ⟩ -- assoc
        ((F-seq f g ▹ α₀ Z ▹ β₀ Z ∙ F₁ f ◃ α□ g ▹ β₀ Z) 
          ∙ F₁ f ◃ α₀ Y ◃ β□ g)
        ∙ α□ f ▹ β₀ Y ▹ H₁ g 
        ∙ α₀ X ◃ β□ f ▹ H₁ g
      ≡⟨ {! !} ⟩ -- assoc
        (F-seq f g ▹ α₀ Z ▹ β₀ Z 
          ∙ F₁ f ◃ α□ g ▹ β₀ Z 
          ∙ F₁ f ◃ α₀ Y ◃ β□ g) 
        ∙ α□ f ▹ β₀ Y ▹ H₁ g 
        ∙ α₀ X ◃ β□ f ▹ H₁ g
      ≡⟨ {! !} ⟩ -- ▹-∙
        (F-seq f g ▹ α₀ Z ▹ β₀ Z 
          ∙ F₁ f ◃ α□ g ▹ β₀ Z 
          ∙ F₁ f ◃ α₀ Y ◃ β□ g) 
        ∙ (α□ f ▹ β₀ Y ∙ α₀ X ◃ β□ f) ▹ H₁ g
      ≡⟨ {! !} ⟩ -- ▹-∙
        F-seq f g ▹ α₀ Z ▹ β₀ Z 
          ∙ F₁ f ◃ (α□ g ▹ β₀ Z ∙ α₀ Y ◃ β□ g) 
          ∙ (α□ f ▹ β₀ Y ∙ α₀ X ◃ β□ f) ▹ H₁ g
      ∎
      where 
        open import Cubical.Foundations.GroupoidLaws
