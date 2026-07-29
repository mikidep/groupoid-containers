open import Cubical.Foundations.Prelude

module Cubical.Bicategory.Copresheaf.Pseudonat.Constructions
  (ℓ : Level) where

open import Cubical.WildCat.Functor using (WildNatTrans)

open import Cubical.Bicategory.Base
open import Cubical.Bicategory.Copresheaf.Base ℓ
open import Cubical.Bicategory.Copresheaf.Pseudonat.Base ℓ

open Bicategory GPD using ()
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

module _ {C : Bicategory ℓC ℓC'} where
  private module C = Bicategory C

  open C using ()
    renaming (
      str to ⟨C⟩;
      Hom[_,_] to C[_,_];
      id to idᶜ;
      _⋆_ to _⋆ᶜ_
    )

  module _ (F : Copresheaf C) where
    open Copresheaf F using (F₁; F₂; F-seq)
      renaming (str to ⟨F⟩)
    open WildNatTrans

    open import Cubical.Foundations.Function
    open IsPseudonat
    open import Cubical.Foundations.GroupoidLaws
    open import Prelude.ExtraGpdLaws

    idWildNatTrans : WildNatTrans _ _ ⟨F⟩ ⟨F⟩
    idWildNatTrans .N-ob X = idfun _
    idWildNatTrans .N-hom _ = refl
    {-# INLINE idWildNatTrans #-}

    idPseudonatTrans : PseudonatTrans F F
    idPseudonatTrans .fst = idWildNatTrans
    idPseudonatTrans .snd .N-hom-id = sym (lUnit _)
    idPseudonatTrans .snd .N-hom-seq f g =
      sym (lUnit _)
      ∙ rUnit _
      ∙ cong (F-seq f g ∙_) (rUnit _)

  module _ {F G H : Copresheaf C}
    (α : PseudonatTrans F G)
    (β : PseudonatTrans G H) where

    open WildNatTrans
    open WildNatTrans (fst α) using ()
      renaming (N-ob to α₀; N-hom to α□)
    open WildNatTrans (fst β) using ()
      renaming (N-ob to β₀; N-hom to β□)
    open IsPseudonat

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
    open import Prelude.ExtraGpdLaws
    open import Prelude.Reassoc
    open BicatReassoc ⟨GPD⟩

    open WildNatTrans

    compWildNatTrans : WildNatTrans _ _ ⟨F⟩ ⟨H⟩
    compWildNatTrans .N-ob X = α₀ X ⋆ᵈ β₀ X
    compWildNatTrans .N-hom {x = X} {y = Y} f =
      α□ f ▹ β₀ Y ∙ α₀ X ◃ β□ f
    {-# INLINE compWildNatTrans #-}

    compPseudonatTrans : PseudonatTrans F H
    compPseudonatTrans .fst = compWildNatTrans
    compPseudonatTrans .snd .N-hom-id {X} =
        (α□ idᶜ ▹ β₀ X ∙ α₀ X ◃ β□ idᶜ) ∙ α₀ X ◃ β₀ X ◃ H-id
      ≡⟨ reassoc 
            ( (↑ α□ idᶜ ▹′ β₀ X ∙′ α₀ X ◃′ ↑ β□ idᶜ) ∙′ α₀ X ◃′ β₀ X ◃′ ↑ H-id )
            ( ↑ α□ idᶜ ▹′ β₀ X ∙′ α₀ X ◃′ (↑ β□ idᶜ ∙′ β₀ X ◃′ ↑ H-id) )
            refl ⟩
        α□ idᶜ ▹ β₀ X ∙ α₀ X ◃ (β□ idᶜ ∙ β₀ X ◃ H-id)
      ≡⟨ cong (λ x → α□ idᶜ ▹ β₀ X ∙ α₀ X ◃ x) (β .snd .N-hom-id) ⟩
        α□ idᶜ ▹ β₀ X ∙ α₀ X ◃ G-id ▹ β₀ X
      ≡⟨ sym (▹-∙ (α□ idᶜ) (α₀ X ◃ G-id)) ⟩
        (α□ idᶜ ∙ α₀ X ◃ G-id) ▹ β₀ X
      ≡⟨ cong (_▹ β₀ X) (α .snd .N-hom-id) ⟩
        F-id ▹ α₀ X ▹ β₀ X
      ∎
    compPseudonatTrans .snd .N-hom-seq {X} {Y} {Z} f g =
        (α□ (f ⋆ᶜ g) ▹ β₀ Z ∙ α₀ X ◃ β□ (f ⋆ᶜ g))
        ∙ α₀ X ◃ β₀ X ◃ H-seq f g
      ≡⟨ reassoc 
            ( (↑ α□ (f ⋆ᶜ g) ▹′ β₀ Z ∙′ α₀ X ◃′ ↑ β□ (f ⋆ᶜ g))
            ∙′ α₀ X ◃′ β₀ X ◃′ ↑ H-seq f g )
            ( ↑ α□ (f ⋆ᶜ g) ▹′ β₀ Z
            ∙′ α₀ X ◃′ (↑ β□ (f ⋆ᶜ g) ∙′ β₀ X ◃′ ↑ H-seq f g) )
            refl ⟩
        α□ (f ⋆ᶜ g) ▹ β₀ Z
        ∙ α₀ X ◃ (β□ (f ⋆ᶜ g) ∙ β₀ X ◃ H-seq f g)
      ≡⟨ cong (λ x → α□ (f ⋆ᶜ g) ▹ β₀ Z ∙ α₀ X ◃ x)
          (β .snd .N-hom-seq f g) ⟩
        α□ (f ⋆ᶜ g) ▹ β₀ Z
        ∙ α₀ X ◃ (G-seq f g ▹ β₀ Z
          ∙ G₁ f ◃ β□ g ∙ β□ f ▹ H₁ g)
      ≡⟨ reassoc
            ( ↑ α□ (f ⋆ᶜ g) ▹′ β₀ Z
            ∙′ α₀ X ◃′ (↑ G-seq f g ▹′ β₀ Z
              ∙′ G₁ f ◃′ ↑ β□ g ∙′ ↑ β□ f ▹′ H₁ g) )
            ( (↑ α□ (f ⋆ᶜ g) ∙′ α₀ X ◃′ ↑ G-seq f g) ▹′ β₀ Z
            ∙′ α₀ X ◃′ G₁ f ◃′ ↑ β□ g
            ∙′ α₀ X ◃′ ↑ β□ f ▹′ H₁ g )
            refl ⟩
        (α□ (f ⋆ᶜ g) ∙ α₀ X ◃ G-seq f g) ▹ β₀ Z
        ∙ α₀ X ◃ G₁ f ◃ β□ g
        ∙ α₀ X ◃ β□ f ▹ H₁ g
      ≡⟨ cong (λ x → x ▹ β₀ Z
            ∙ α₀ X ◃ G₁ f ◃ β□ g ∙ α₀ X ◃ β□ f ▹ H₁ g)
          (α .snd .N-hom-seq f g) ⟩
        (F-seq f g ▹ α₀ Z 
          ∙ F₁ f ◃ α□ g ∙ α□ f ▹ G₁ g) ▹ β₀ Z
        ∙ α₀ X ◃ G₁ f ◃ β□ g
        ∙ α₀ X ◃ β□ f ▹ H₁ g
      ≡⟨ reassoc
            ( (↑ F-seq f g ▹′ α₀ Z 
              ∙′ F₁ f ◃′ ↑ α□ g ∙′ ↑ α□ f ▹′ G₁ g) ▹′ β₀ Z
            ∙′ α₀ X ◃′ G₁ f ◃′ ↑ β□ g
            ∙′ α₀ X ◃′ ↑ β□ f ▹′ H₁ g )
            ( ↑ F-seq f g ▹′ α₀ Z ▹′ β₀ Z
            ∙′ F₁ f ◃′ ↑ α□ g ▹′ β₀ Z
            ∙′ (↑ α□ f ▹′ G₁ g ▹′ β₀ Z 
              ∙′ α₀ X ◃′ G₁ f ◃′ ↑ β□ g)
            ∙′ α₀ X ◃′ ↑ β□ f ▹′ H₁ g )
            refl ⟩
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
      ≡⟨ reassoc 
            ( ↑ F-seq f g ▹′ α₀ Z ▹′ β₀ Z
            ∙′ F₁ f ◃′ ↑ α□ g ▹′ β₀ Z
            ∙′ (F₁ f ◃′ α₀ Y ◃′ ↑ β□ g
              ∙′ ↑ α□ f ▹′ β₀ Y ▹′ H₁ g)
            ∙′ α₀ X ◃′ ↑ β□ f ▹′ H₁ g )
            ( ↑ F-seq f g ▹′ α₀ Z ▹′ β₀ Z
            ∙′ F₁ f ◃′ (↑ α□ g ▹′ β₀ Z ∙′ α₀ Y ◃′ ↑ β□ g)
            ∙′ (↑ α□ f ▹′ β₀ Y ∙′ α₀ X ◃′ ↑ β□ f) ▹′ H₁ g )
            refl ⟩
        F-seq f g ▹ α₀ Z ▹ β₀ Z
        ∙ F₁ f ◃ (α□ g ▹ β₀ Z ∙ α₀ Y ◃ β□ g)
        ∙ (α□ f ▹ β₀ Y ∙ α₀ X ◃ β□ f) ▹ H₁ g
      ∎

