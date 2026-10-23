open import Cubical.Foundations.Prelude

open import Cubical.LU2C.Base
open import Cubical.WildCat.FullSub.Notation
open import Cubical.WildCat.AsLU2C.Properties

module Cubical.LU2C.Copresheaf.Pseudonat.Constructions
  {ℓ ℓC ℓC' : Level} 
  {C : LU2C ℓC ℓC'}
  where

open import Cubical.WildCat.Functor hiding (compWildNatTrans)

open import Cubical.LU2C.Instances.Groupoids ℓ
open import Cubical.LU2C.Copresheaf.Base ℓ
open import Cubical.LU2C.Copresheaf.Pseudonat.Base

open import Prelude.Reassoc

open LU2C HGpd using () renaming (str to ⟨HGpd⟩)
open LU2CReassoc ⟨HGpd⟩

open Not2C HGpd
open Not2C C

private ⟨_⟩ = fst

module _ (F : Copresheaf C) where
  open Not2P F
  open WildNatTrans

  open import Cubical.Foundations.Function
  open IsPseudonat
  open import Cubical.Foundations.GroupoidLaws
  open import Prelude.ExtraGpdLaws

  -- this and the other are here because they are stricter
  -- than the general counterpart
  idWildNatTrans : WildNatTrans _ _ ⟨ F ⟩ ⟨ F ⟩
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

  open Not2P F using (F₀; F₁; F₂; F-id; F-seq)
  open Not2P G using ()
    renaming (
      F₀ to    G₀;
      F₁ to    G₁;
      F₂ to    G₂;
      F-id to  G-id;
      F-seq to G-seq
    )
  open Not2P H using ()
    renaming (
      F₀ to    H₀;
      F₁ to    H₁;
      F₂ to    H₂;
      F-id to  H-id;
      F-seq to H-seq
    )

  open import Cubical.Foundations.GroupoidLaws
  open import Prelude.ExtraGpdLaws

  open WildNatTrans

  compWildNatTrans : WildNatTrans _ _ ⟨ F ⟩ ⟨ H ⟩
  compWildNatTrans .N-ob X = α₀ X ⋆ β₀ X
  compWildNatTrans .N-hom {x = X} {y = Y} f =
    α□ f ▹ β₀ Y ∙ α₀ X ◃ β□ f
  {-# INLINE compWildNatTrans #-}

  compPseudonatTrans : PseudonatTrans F H
  compPseudonatTrans .fst = compWildNatTrans
  compPseudonatTrans .snd .N-hom-id {X} =
      (α□ id ▹ β₀ X ∙ α₀ X ◃ β□ id) ∙ α₀ X ◃ β₀ X ◃ H-id
    ≡⟨ reass₁ ⟩
      α□ id ▹ β₀ X ∙ α₀ X ◃ (β□ id ∙ β₀ X ◃ H-id)
    ≡⟨ ∙l cong (α₀ X ◃_) (β .snd .N-hom-id) ⟩
      α□ id ▹ β₀ X ∙ α₀ X ◃ G-id ▹ β₀ X
    ≡⟨ reass₂ ⟩
      (α□ id ∙ α₀ X ◃ G-id) ▹ β₀ X
    ≡⟨ cong (_▹ β₀ X) (α .snd .N-hom-id) ⟩
      F-id ▹ α₀ X ▹ β₀ X
    ∎
    where
    reass₁ = reassoc 
      ((↑ α□ id ▹′ β₀ X ∙′ α₀ X ◃′ ↑ β□ id) ∙′ α₀ X ◃′ β₀ X ◃′ ↑ H-id)
      (↑ α□ id ▹′ β₀ X ∙′ α₀ X ◃′ (↑ β□ id ∙′ β₀ X ◃′ ↑ H-id))
      refl
    reass₂ = reassoc 
      (↑ α□ id ▹′ β₀ X ∙′ α₀ X ◃′ ↑ G-id ▹′ β₀ X)
      ((↑ α□ id ∙′ α₀ X ◃′ ↑ G-id) ▹′ β₀ X)
      refl
  compPseudonatTrans .snd .N-hom-seq {X} {Y} {Z} f g =
      (α□ (f ⋆ g) ▹ β₀ Z ∙ α₀ X ◃ β□ (f ⋆ g))
      ∙ α₀ X ◃ β₀ X ◃ H-seq f g
    ≡⟨ reass₁ ⟩
      α□ (f ⋆ g) ▹ β₀ Z
      ∙ α₀ X ◃ (β□ (f ⋆ g) ∙ β₀ X ◃ H-seq f g)
    ≡⟨ ∙l cong (α₀ X ◃_) (β .snd .N-hom-seq f g) ⟩
      α□ (f ⋆ g) ▹ β₀ Z
      ∙ α₀ X ◃ (G-seq f g ▹ β₀ Z
        ∙ G₁ f ◃ β□ g ∙ β□ f ▹ H₁ g)
    ≡⟨ reass₂ ⟩
      (α□ (f ⋆ g) ∙ α₀ X ◃ G-seq f g) ▹ β₀ Z
      ∙ α₀ X ◃ G₁ f ◃ β□ g
      ∙ α₀ X ◃ β□ f ▹ H₁ g
    ≡⟨ ∙r cong (_▹ β₀ Z) (α .snd .N-hom-seq f g) ⟩
      (F-seq f g ▹ α₀ Z 
        ∙ F₁ f ◃ α□ g ∙ α□ f ▹ G₁ g) ▹ β₀ Z
      ∙ α₀ X ◃ G₁ f ◃ β□ g
      ∙ α₀ X ◃ β□ f ▹ H₁ g
    ≡⟨ reass₃ ⟩
      F-seq f g ▹ α₀ Z ▹ β₀ Z
      ∙ F₁ f ◃ α□ g ▹ β₀ Z
      ∙ (α□ f ▹ G₁ g ▹ β₀ Z ∙ α₀ X ◃ G₁ f ◃ β□ g)
      ∙ α₀ X ◃ β□ f ▹ H₁ g
    ≡⟨ ∙l ∙l ∙r sym (whisk-interchange 
        {C = ⟨HGpd⟩}
        {b = G₀ Y}
        (α□ f) (β□ g)) ⟩
      F-seq f g ▹ α₀ Z ▹ β₀ Z
      ∙ F₁ f ◃ α□ g ▹ β₀ Z
      ∙ (F₁ f ◃ α₀ Y ◃ β□ g
        ∙ α□ f ▹ β₀ Y ▹ H₁ g)
      ∙ α₀ X ◃ β□ f ▹ H₁ g
    ≡⟨ reass₄ ⟩
      F-seq f g ▹ α₀ Z ▹ β₀ Z
      ∙ F₁ f ◃ (α□ g ▹ β₀ Z ∙ α₀ Y ◃ β□ g)
      ∙ (α□ f ▹ β₀ Y ∙ α₀ X ◃ β□ f) ▹ H₁ g
    ∎
    where
    reass₁ = reassoc 
      ((↑ α□ (f ⋆ g) ▹′ β₀ Z ∙′ α₀ X ◃′ ↑ β□ (f ⋆ g))
        ∙′ α₀ X ◃′ β₀ X ◃′ ↑ H-seq f g)
      (↑ α□ (f ⋆ g) ▹′ β₀ Z
        ∙′ α₀ X ◃′ (↑ β□ (f ⋆ g) ∙′ β₀ X ◃′ ↑ H-seq f g))
      refl
    reass₂ = reassoc
      ( ↑ α□ (f ⋆ g) ▹′ β₀ Z
      ∙′ α₀ X ◃′ (↑ G-seq f g ▹′ β₀ Z
        ∙′ G₁ f ◃′ ↑ β□ g ∙′ ↑ β□ f ▹′ H₁ g) )
      ( (↑ α□ (f ⋆ g) ∙′ α₀ X ◃′ ↑ G-seq f g) ▹′ β₀ Z
      ∙′ α₀ X ◃′ G₁ f ◃′ ↑ β□ g
      ∙′ α₀ X ◃′ ↑ β□ f ▹′ H₁ g )
      refl
    reass₃ = reassoc
      ( (↑ F-seq f g ▹′ α₀ Z 
        ∙′ F₁ f ◃′ ↑ α□ g ∙′ ↑ α□ f ▹′ G₁ g) ▹′ β₀ Z
      ∙′ α₀ X ◃′ G₁ f ◃′ ↑ β□ g
      ∙′ α₀ X ◃′ ↑ β□ f ▹′ H₁ g )
      ( ↑ F-seq f g ▹′ α₀ Z ▹′ β₀ Z
      ∙′ F₁ f ◃′ ↑ α□ g ▹′ β₀ Z
      ∙′ (↑ α□ f ▹′ G₁ g ▹′ β₀ Z 
        ∙′ α₀ X ◃′ G₁ f ◃′ ↑ β□ g)
      ∙′ α₀ X ◃′ ↑ β□ f ▹′ H₁ g )
      refl
    reass₄ = reassoc 
      ( ↑ F-seq f g ▹′ α₀ Z ▹′ β₀ Z
      ∙′ F₁ f ◃′ ↑ α□ g ▹′ β₀ Z
      ∙′ (F₁ f ◃′ α₀ Y ◃′ ↑ β□ g
        ∙′ ↑ α□ f ▹′ β₀ Y ▹′ H₁ g)
      ∙′ α₀ X ◃′ ↑ β□ f ▹′ H₁ g )
      ( ↑ F-seq f g ▹′ α₀ Z ▹′ β₀ Z
      ∙′ F₁ f ◃′ (↑ α□ g ▹′ β₀ Z ∙′ α₀ Y ◃′ ↑ β□ g)
      ∙′ (↑ α□ f ▹′ β₀ Y ∙′ α₀ X ◃′ ↑ β□ f) ▹′ H₁ g )
      refl
