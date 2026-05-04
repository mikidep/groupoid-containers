open import Cubical.Foundations.Prelude

module Cubical.Prebicategory.Copresheaf.Pseudonat.Constructions 
  (ℓ : Level) where

open import Cubical.WildCat.Functor using (WildNatTrans)

open import Cubical.Prebicategory.Base
open import Cubical.Prebicategory.Copresheaf.Base ℓ
open import Cubical.Prebicategory.Copresheaf.Pseudonat.Base ℓ

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
private
  variable
    ℓC ℓC' : Level

module _ {C : Prebicategory ℓC ℓC'} where
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

  module _ (F : Copresheaf C) where
    open Copresheaf F using (F₁; F₂; F-seq)
      renaming (str to ⟨F⟩)
    open WildNatTrans

    open import Cubical.Foundations.Function
    open Is2NatTrans
    open import Cubical.Foundations.GroupoidLaws

    idWildNatTrans : WildNatTrans _ _ ⟨F⟩ ⟨F⟩ 
    idWildNatTrans .N-ob X = idfun _
    idWildNatTrans .N-hom _ = refl
    {-# INLINE idWildNatTrans #-}

    id2NatTrans : 2NatTrans F F
    id2NatTrans .fst = idWildNatTrans
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
    open Is2NatTrans
    
    open Copresheaf F using (F₀; F₁; F₂; F-id; F-seq)
      renaming (str to ⟨F⟩)
    open Copresheaf G using ()
      renaming (
        str to ⟨G⟩; 
        F₀ to    G₀;
        F₁ to    G₁;
        F₂ to    G₂;
        F-id to  G-id;
        F-seq to G-seq
      )
    open Copresheaf H using ()
      renaming (
        str to ⟨H⟩; 
        F₀ to    H₀;
        F₁ to    H₁;
        F₂ to    H₂;
        F-id to  H-id;
        F-seq to H-seq
      )

    open import Cubical.Foundations.GroupoidLaws
    open WildNatTrans

    compWildNatTrans : WildNatTrans _ _ ⟨F⟩ ⟨H⟩
    compWildNatTrans .N-ob X = α₀ X ⋆ᵈ β₀ X
    compWildNatTrans .N-hom {x = X} {y = Y} f = 
      α□ f ▹ β₀ Y ∙ α₀ X ◃ β□ f
    {-# INLINE compWildNatTrans #-}

    comp2NatTrans : 2NatTrans F H
    comp2NatTrans .fst = compWildNatTrans
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
    comp2NatTrans .snd .N-hom-seq {X} {Y} {Z} f g = 
        (α□ (f ⋆ᶜ g) ▹ β₀ Z ∙ α₀ X ◃ β□ (f ⋆ᶜ g)) 
        ∙ α₀ X ◃ β₀ X ◃ H-seq f g
      ≡⟨ sym (assoc _ _ _) ⟩
        α□ (f ⋆ᶜ g) ▹ β₀ Z 
        ∙ α₀ X ◃ β□ (f ⋆ᶜ g) 
        ∙ α₀ X ◃ β₀ X ◃ H-seq f g
      ≡⟨ cong (α□ (f ⋆ᶜ g) ▹ β₀ Z ∙_) 
          (sym (◃-∙ (β□ (f ⋆ᶜ g)) (β₀ X ◃ H-seq f g))) ⟩
        α□ (f ⋆ᶜ g) ▹ β₀ Z 
        ∙ α₀ X ◃ (β□ (f ⋆ᶜ g) ∙ β₀ X ◃ H-seq f g)
      ≡⟨ cong (λ x → α□ (f ⋆ᶜ g) ▹ β₀ Z ∙ α₀ X ◃ x) 
          (β .snd .N-hom-seq f g) ⟩
        α□ (f ⋆ᶜ g) ▹ β₀ Z 
        ∙ α₀ X ◃ (G-seq f g ▹ β₀ Z
          ∙ G₁ f ◃ β□ g ∙ β□ f ▹ H₁ g)
      ≡⟨ cong (α□ (f ⋆ᶜ g) ▹ β₀ Z ∙_) 
          (◃-∙ (G-seq f g ▹ β₀ Z) (G₁ f ◃ β□ g ∙ β□ f ▹ H₁ g)) ⟩
        α□ (f ⋆ᶜ g) ▹ β₀ Z 
        ∙ α₀ X ◃ G-seq f g ▹ β₀ Z
        ∙ α₀ X ◃ (G₁ f ◃ β□ g ∙ β□ f ▹ H₁ g)
      ≡⟨ cong (λ x → α□ (f ⋆ᶜ g) ▹ β₀ Z ∙ α₀ X ◃ G-seq f g ▹ β₀ Z ∙ x)
          (◃-∙ (G₁ f ◃ β□ g ) (β□ f ▹ H₁ g)) ⟩
        α□ (f ⋆ᶜ g) ▹ β₀ Z 
        ∙ α₀ X ◃ G-seq f g ▹ β₀ Z
        ∙ α₀ X ◃ G₁ f ◃ β□ g 
        ∙ α₀ X ◃ β□ f ▹ H₁ g
      ≡⟨ assoc _ _ _ ⟩
        (α□ (f ⋆ᶜ g) ▹ β₀ Z ∙ α₀ X ◃ G-seq f g ▹ β₀ Z)
        ∙ α₀ X ◃ G₁ f ◃ β□ g 
        ∙ α₀ X ◃ β□ f ▹ H₁ g
      ≡⟨ cong (_∙ α₀ X ◃ G₁ f ◃ β□ g ∙ α₀ X ◃ β□ f ▹ H₁ g)
          (sym (▹-∙ (α□ (f ⋆ᶜ g)) (α₀ X ◃ G-seq f g))) ⟩
        (α□ (f ⋆ᶜ g) ∙ α₀ X ◃ G-seq f g) ▹ β₀ Z
        ∙ α₀ X ◃ G₁ f ◃ β□ g 
        ∙ α₀ X ◃ β□ f ▹ H₁ g
      ≡⟨ cong (λ x → x ▹ β₀ Z 
            ∙ α₀ X ◃ G₁ f ◃ β□ g ∙ α₀ X ◃ β□ f ▹ H₁ g)
          (α .snd .N-hom-seq f g) ⟩
        (F-seq f g ▹ α₀ Z ∙ F₁ f ◃ α□ g ∙ α□ f ▹ G₁ g) ▹ β₀ Z
        ∙ α₀ X ◃ G₁ f ◃ β□ g 
        ∙ α₀ X ◃ β□ f ▹ H₁ g
      ≡⟨ cong (_∙ α₀ X ◃ G₁ f ◃ β□ g ∙ α₀ X ◃ β□ f ▹ H₁ g)
          (▹-∙ (F-seq f g ▹ α₀ Z) (F₁ f ◃ α□ g ∙ α□ f ▹ G₁ g)) ⟩
        (F-seq f g ▹ α₀ Z ▹ β₀ Z 
          ∙ (F₁ f ◃ α□ g ∙ α□ f ▹ G₁ g) ▹ β₀ Z)
        ∙ α₀ X ◃ G₁ f ◃ β□ g 
        ∙ α₀ X ◃ β□ f ▹ H₁ g
      ≡⟨ cong (λ x → (F-seq f g ▹ α₀ Z ▹ β₀ Z ∙ x)
        ∙ α₀ X ◃ G₁ f ◃ β□ g 
        ∙ α₀ X ◃ β□ f ▹ H₁ g)
          (▹-∙ (F₁ f ◃ α□ g) (α□ f ▹ G₁ g)) ⟩
        (F-seq f g ▹ α₀ Z ▹ β₀ Z 
          ∙ F₁ f ◃ α□ g ▹ β₀ Z 
          ∙ α□ f ▹ G₁ g ▹ β₀ Z)
        ∙ α₀ X ◃ G₁ f ◃ β□ g
        ∙ α₀ X ◃ β□ f ▹ H₁ g
      ≡⟨ cong (_∙ α₀ X ◃ G₁ f ◃ β□ g ∙ α₀ X ◃ β□ f ▹ H₁ g) 
          (assoc _ _ _) ⟩
        ((F-seq f g ▹ α₀ Z ▹ β₀ Z 
            ∙ F₁ f ◃ α□ g ▹ β₀ Z) 
          ∙ α□ f ▹ G₁ g ▹ β₀ Z)
        ∙ α₀ X ◃ G₁ f ◃ β□ g
        ∙ α₀ X ◃ β□ f ▹ H₁ g
      ≡⟨ sym (assoc _ _ _) ⟩ 
        (F-seq f g ▹ α₀ Z ▹ β₀ Z 
          ∙ F₁ f ◃ α□ g ▹ β₀ Z) 
        ∙ α□ f ▹ G₁ g ▹ β₀ Z
        ∙ α₀ X ◃ G₁ f ◃ β□ g
        ∙ α₀ X ◃ β□ f ▹ H₁ g
      ≡⟨ sym (assoc _ _ _) ⟩
        F-seq f g ▹ α₀ Z ▹ β₀ Z 
        ∙ F₁ f ◃ α□ g ▹ β₀ Z 
        ∙ α□ f ▹ G₁ g ▹ β₀ Z 
        ∙ α₀ X ◃ G₁ f ◃ β□ g 
        ∙ α₀ X ◃ β□ f ▹ H₁ g
      ≡⟨ cong (λ x → F-seq f g ▹ α₀ Z ▹ β₀ Z 
            ∙ F₁ f ◃ α□ g ▹ β₀ Z ∙ x)
          (assoc _ _ _) ⟩
        F-seq f g ▹ α₀ Z ▹ β₀ Z 
        ∙ F₁ f ◃ α□ g ▹ β₀ Z 
        ∙ (α□ f ▹ G₁ g ▹ β₀ Z ∙ α₀ X ◃ G₁ f ◃ β□ g) 
        ∙ α₀ X ◃ β□ f ▹ H₁ g
      ≡⟨ cong (λ x → F-seq f g ▹ α₀ Z ▹ β₀ Z 
            ∙ F₁ f ◃ α□ g ▹ β₀ Z 
            ∙ x ∙ α₀ X ◃ β□ f ▹ H₁ g) 
          (sym (whisk-interchange (α□ f) (β□ g))) ⟩ 
        F-seq f g ▹ α₀ Z ▹ β₀ Z 
        ∙ F₁ f ◃ α□ g ▹ β₀ Z 
        ∙ (F₁ f ◃ α₀ Y ◃ β□ g 
          ∙ α□ f ▹ β₀ Y ▹ H₁ g) 
        ∙ α₀ X ◃ β□ f ▹ H₁ g
      ≡⟨ cong (λ x → F-seq f g ▹ α₀ Z ▹ β₀ Z 
            ∙ F₁ f ◃ α□ g ▹ β₀ Z ∙ x)
          (sym (assoc _ _ _)) ⟩
        F-seq f g ▹ α₀ Z ▹ β₀ Z 
        ∙ F₁ f ◃ α□ g ▹ β₀ Z 
        ∙ F₁ f ◃ α₀ Y ◃ β□ g 
        ∙ α□ f ▹ β₀ Y ▹ H₁ g 
        ∙ α₀ X ◃ β□ f ▹ H₁ g
      ≡⟨ cong (F-seq f g ▹ α₀ Z ▹ β₀ Z ∙_) (assoc _ _ _) ⟩
        F-seq f g ▹ α₀ Z ▹ β₀ Z 
        ∙ (F₁ f ◃ α□ g ▹ β₀ Z 
          ∙ F₁ f ◃ α₀ Y ◃ β□ g) 
        ∙ α□ f ▹ β₀ Y ▹ H₁ g 
        ∙ α₀ X ◃ β□ f ▹ H₁ g
      ≡⟨ cong (λ x → F-seq f g ▹ α₀ Z ▹ β₀ Z 
          ∙ (F₁ f ◃ α□ g ▹ β₀ Z ∙ F₁ f ◃ α₀ Y ◃ β□ g) ∙ x)
          (sym (▹-∙ (α□ f ▹ β₀ Y) (α₀ X ◃ β□ f))) ⟩ 
        F-seq f g ▹ α₀ Z ▹ β₀ Z 
        ∙ (F₁ f ◃ α□ g ▹ β₀ Z ∙ F₁ f ◃ α₀ Y ◃ β□ g) 
        ∙ (α□ f ▹ β₀ Y ∙ α₀ X ◃ β□ f) ▹ H₁ g
      ≡⟨ cong (λ x → F-seq f g ▹ α₀ Z ▹ β₀ Z 
            ∙ x ∙ (α□ f ▹ β₀ Y ∙ α₀ X ◃ β□ f) ▹ H₁ g) 
          (◃-∙ (α□ g ▹ β₀ Z) (α₀ Y ◃ β□ g)) ⟩
        F-seq f g ▹ α₀ Z ▹ β₀ Z 
          ∙ F₁ f ◃ (α□ g ▹ β₀ Z ∙ α₀ Y ◃ β□ g) 
          ∙ (α□ f ▹ β₀ Y ∙ α₀ X ◃ β□ f) ▹ H₁ g
      ∎

