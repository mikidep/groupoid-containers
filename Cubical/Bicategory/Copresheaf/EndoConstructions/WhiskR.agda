open import Cubical.Foundations.Prelude

open import Cubical.Foundations.Function
open import Cubical.Foundations.GroupoidLaws
open import Prelude.ExtraGpdLaws

open import Cubical.WildCat.Functor hiding (_$_)
open import Cubical.WildCat.Product renaming (_×_ to ProdCat)

module Cubical.Bicategory.Copresheaf.EndoConstructions.WhiskR
  (ℓ : Level) where

open import Cubical.Bicategory.Base
open import Cubical.Bicategory.Copresheaf ℓ 
  using (Copresheaf; GPD; Is2Copresheaf; PseudonatTrans; IsPseudonat)
open import Cubical.Bicategory.Instances.Copresheaf ℓ
open import Cubical.Bicategory.Copresheaf.EndoConstructions.Base ℓ 
open import Cubical.Bicategory.Copresheaf.EndoConstructions.Composite ℓ

open Copresheaf using (str; is2Copresheaf)
open WildFunctor
open Is2Copresheaf

open Bicategory GPD using () renaming (str to ⟨GPD⟩)
open BicatSyntax {{...}}
open BicatSynInstBC GPD

module _ {F H : GpdEndo} (α : PseudonatTrans F H)
  (G : GpdEndo) where

  open import Prelude
  open import Prelude.Reassoc
  open BicatReassoc ⟨GPD⟩

  private module F = Copresheaf F
  private module G = Copresheaf G
  private module H = Copresheaf H

  open F using (F₀; F₁; F₂)
  open G using ()
    renaming (
      F₀ to    G₀;
      F₁ to    G₁;
      F₂ to    G₂;
      F-id to  G-id;
      F-seq to G-seq
    )
  open H using ()
    renaming (
      F₀ to    H₀;
      F₁ to    H₁;
      F₂ to    H₂;
      F-id to  H-id;
      F-seq to H-seq
    )
  
  open WildNatTrans (α .fst) using ()
    renaming (N-ob to α₀; N-hom to α□)

  private _⊗₀_ = compEndo₀

  open WildNatTrans
  open IsPseudonat

  import Cubical.WildCat.Base
  {-# DISPLAY Cubical.WildCat.Base.WildCat._⋆_ f g = f ⋆ g #-}

  whiskR-pseudonat : PseudonatTrans (F ⊗₀ G) (H ⊗₀ G)
  whiskR-pseudonat .fst .N-ob x = G₁ (α₀ x)
  whiskR-pseudonat .fst .N-hom {x} {y} f = goal
    where
    goal = sym (G-seq (F₁ f) (α₀ y)) 
      ∙ G₂ (α□ f) 
      ∙ G-seq (α₀ x) (H₁ f)

  whiskR-pseudonat .snd .N-hom-id {X} =
    -- By vibe
    (sym (G-seq (F₁ id) (α₀ X))
      ∙ G₂ (α□ id)
      ∙ G-seq (α₀ X) (H₁ id))
    ∙ G₁ (α₀ X) ◃ (G₂ H-id ∙ G-id)
        ≡⟨ reass₁ ⟩
    sym (G-seq (F₁ id) (α₀ X))
    ∙ G₂ (α□ id)
    ∙ (G-seq (α₀ X) (H₁ id)
      ∙ G₁ (α₀ X) ◃ G₂ H-id)
    ∙ G₁ (α₀ X) ◃ G-id
        ≡⟨ ∙l ∙l ∙r G.F-seq-nat refl H-id ⟩
    sym (G-seq (F₁ id) (α₀ X))
    ∙ G₂ (α□ id)
    ∙ (G₂ (α₀ X ◃ H-id) ∙ G-seq (α₀ X) id)
    ∙ G₁ (α₀ X) ◃ G-id
        ≡⟨ reass₂ ⟩
    sym (G-seq (F₁ id) (α₀ X))
    ∙ G₂ (α□ id ∙ α₀ X ◃ H-id)
    ∙ (G-seq (α₀ X) id ∙ G₁ (α₀ X) ◃ G-id)
        ≡⟨ ∙l cong₂ _∙_
            (cong G₂ (α .snd .N-hom-id))
            (G.F-IdR (α₀ X)) ⟩
    sym (G-seq (F₁ id) (α₀ X))
    ∙ G₂ (F.F-id ▹ α₀ X)
    ∙ refl
        ≡⟨ ∙l sym (rUnit _) ⟩
    sym (G-seq (F₁ id) (α₀ X))
    ∙ G₂ (F.F-id ▹ α₀ X)
        ≡⟨ ∙l G.F₂-▹ F.F-id ⟩
    sym (G-seq (F₁ id) (α₀ X))
    ∙ G-seq (F₁ id) (α₀ X)
    ∙ G₂ F.F-id ▹ G₁ (α₀ X)
    ∙ sym (G-seq id (α₀ X))
        ≡⟨ reass₃ ⟩
    (sym (G-seq (F₁ id) (α₀ X))
      ∙ G-seq (F₁ id) (α₀ X))
    ∙ G₂ F.F-id ▹ G₁ (α₀ X)
    ∙ sym (G-seq id (α₀ X))
        ≡⟨ ∙r lCancel _ ⟩
    refl
    ∙ G₂ F.F-id ▹ G₁ (α₀ X)
    ∙ sym (G-seq id (α₀ X))
        ≡⟨ sym (lUnit _) ⟩
    G₂ F.F-id ▹ G₁ (α₀ X)
    ∙ sym (G-seq id (α₀ X))
        ≡⟨ ∙l invUniq (G.F-IdL (α₀ X)) ⟩
    G₂ F.F-id ▹ G₁ (α₀ X)
    ∙ G-id ▹ G₁ (α₀ X)
        ≡⟨ reass₄ ⟩
    (G₂ F.F-id ∙ G-id) ▹ G₁ (α₀ X)
        ∎
    where
    reass₁ = reassoc
      ( (↑ sym (G-seq (F₁ id) (α₀ X))
        ∙′ G.F₂′ (↑ α□ id)
        ∙′ ↑ G-seq (α₀ X) (H₁ id))
      ∙′ G₁ (α₀ X) ◃′ (G.F₂′ (↑ H-id) ∙′ ↑ G-id) )
      ( ↑ sym (G-seq (F₁ id) (α₀ X))
      ∙′ G.F₂′ (↑ α□ id)
      ∙′ (↑ G-seq (α₀ X) (H₁ id)
        ∙′ G₁ (α₀ X) ◃′ G.F₂′ (↑ H-id))
      ∙′ G₁ (α₀ X) ◃′ ↑ G-id )
      refl
    reass₂ = reassoc
      ( ↑ sym (G-seq (F₁ id) (α₀ X))
      ∙′ G.F₂′ (↑ α□ id)
      ∙′ (G.F₂′ (α₀ X ◃′ ↑ H-id) ∙′ ↑ G-seq (α₀ X) id)
      ∙′ G₁ (α₀ X) ◃′ ↑ G-id )
      ( ↑ sym (G-seq (F₁ id) (α₀ X))
      ∙′ G.F₂′ (↑ α□ id ∙′ α₀ X ◃′ ↑ H-id)
      ∙′ (↑ G-seq (α₀ X) id ∙′ G₁ (α₀ X) ◃′ ↑ G-id) )
      refl
    reass₃ = reassoc
      ( ↑ sym (G-seq (F₁ id) (α₀ X))
      ∙′ ↑ G-seq (F₁ id) (α₀ X)
      ∙′ G.F₂′ (↑ F.F-id) ▹′ G₁ (α₀ X)
      ∙′ ↑ sym (G-seq id (α₀ X)) )
      ( (↑ sym (G-seq (F₁ id) (α₀ X))
        ∙′ ↑ G-seq (F₁ id) (α₀ X))
      ∙′ G.F₂′ (↑ F.F-id) ▹′ G₁ (α₀ X)
      ∙′ ↑ sym (G-seq id (α₀ X)) )
      refl
    reass₄ = reassoc
      ( G.F₂′ (↑ F.F-id) ▹′ G₁ (α₀ X)
      ∙′ ↑ G-id ▹′ G₁ (α₀ X) )
      ( (G.F₂′ (↑ F.F-id) ∙′ ↑ G-id) ▹′ G₁ (α₀ X) )
      refl
  whiskR-pseudonat .snd .N-hom-seq {X} {Y} {Z} f g =
    -- By vibe
    (sym (G-seq (F₁ (f ⋆ g)) (α₀ Z))
      ∙ G₂ (α□ (f ⋆ g))
      ∙ G-seq (α₀ X) (H₁ (f ⋆ g)))
    ∙ G₁ (α₀ X) ◃ (G₂ (H-seq f g) ∙ G-seq (H₁ f) (H₁ g))
        ≡⟨ reass₁ ⟩
    sym (G-seq (F₁ (f ⋆ g)) (α₀ Z))
    ∙ G₂ (α□ (f ⋆ g))
    ∙ (G-seq (α₀ X) (H₁ (f ⋆ g))
      ∙ G₁ (α₀ X) ◃ G₂ (H-seq f g))
    ∙ G₁ (α₀ X) ◃ G-seq (H₁ f) (H₁ g)
        ≡⟨ ∙l ∙l ∙r G.F-seq-nat refl (H-seq f g) ⟩
    sym (G-seq (F₁ (f ⋆ g)) (α₀ Z))
    ∙ G₂ (α□ (f ⋆ g))
    ∙ (G₂ (α₀ X ◃ H-seq f g) ∙ G-seq (α₀ X) (H₁ f ⋆ H₁ g))
    ∙ G₁ (α₀ X) ◃ G-seq (H₁ f) (H₁ g)
        ≡⟨ reass₂ ⟩
    sym (G-seq (F₁ (f ⋆ g)) (α₀ Z))
    ∙ G₂ (α□ (f ⋆ g) ∙ α₀ X ◃ H-seq f g)
    ∙ (G-seq (α₀ X) (H₁ f ⋆ H₁ g)
      ∙ G₁ (α₀ X) ◃ G-seq (H₁ f) (H₁ g))
        ≡⟨ ∙l ∙r cong G₂ (α .snd .N-hom-seq f g) ⟩
    sym (G-seq (F₁ (f ⋆ g)) (α₀ Z))
    ∙ G₂ (F.F-seq f g ▹ α₀ Z ∙ F₁ f ◃ α□ g ∙ α□ f ▹ H₁ g)
    ∙ (G-seq (α₀ X) (H₁ f ⋆ H₁ g)
      ∙ G₁ (α₀ X) ◃ G-seq (H₁ f) (H₁ g))
        ≡⟨ ∙l ∙l (lUnit _ ∙ sym (G.F-Assoc (α₀ X) (H₁ f) (H₁ g))) ⟩
    sym (G-seq (F₁ (f ⋆ g)) (α₀ Z))
    ∙ G₂ (F.F-seq f g ▹ α₀ Z ∙ F₁ f ◃ α□ g ∙ α□ f ▹ H₁ g)
    ∙ G-seq (α₀ X ⋆ H₁ f) (H₁ g)
    ∙ G-seq (α₀ X) (H₁ f) ▹ G₁ (H₁ g)
        ≡⟨ reass₃ ⟩
    sym (G-seq (F₁ (f ⋆ g)) (α₀ Z))
    ∙ G₂ (F.F-seq f g ▹ α₀ Z)
    ∙ G₂ (F₁ f ◃ α□ g)
    ∙ (G₂ (α□ f ▹ H₁ g) ∙ G-seq (α₀ X ⋆ H₁ f) (H₁ g))
    ∙ G-seq (α₀ X) (H₁ f) ▹ G₁ (H₁ g)
        ≡⟨ ∙l ∙l ∙l ∙r sym (G.F-seq-nat (α□ f) refl) ⟩
    sym (G-seq (F₁ (f ⋆ g)) (α₀ Z))
    ∙ G₂ (F.F-seq f g ▹ α₀ Z)
    ∙ G₂ (F₁ f ◃ α□ g)
    ∙ (G-seq (F₁ f ⋆ α₀ Y) (H₁ g) ∙ G₂ (α□ f) ▹ G₁ (H₁ g))
    ∙ G-seq (α₀ X) (H₁ f) ▹ G₁ (H₁ g)
        ≡⟨ ∙l ∙l ∙l ∙r ∙r shuffleSymRD
            (G.F-Assoc (F₁ f) (α₀ Y) (H₁ g) ∙ sym (lUnit _)) ⟩
    sym (G-seq (F₁ (f ⋆ g)) (α₀ Z))
    ∙ G₂ (F.F-seq f g ▹ α₀ Z)
    ∙ G₂ (F₁ f ◃ α□ g)
    ∙ (((G-seq (F₁ f) (α₀ Y ⋆ H₁ g)
        ∙ G₁ (F₁ f) ◃ G-seq (α₀ Y) (H₁ g))
        ∙ sym (G-seq (F₁ f) (α₀ Y) ▹ G₁ (H₁ g)))
      ∙ G₂ (α□ f) ▹ G₁ (H₁ g))
    ∙ G-seq (α₀ X) (H₁ f) ▹ G₁ (H₁ g)
        ≡⟨ reass₄ ⟩
    sym (G-seq (F₁ (f ⋆ g)) (α₀ Z))
    ∙ G₂ (F.F-seq f g ▹ α₀ Z)
    ∙ (G₂ (F₁ f ◃ α□ g) ∙ G-seq (F₁ f) (α₀ Y ⋆ H₁ g))
    ∙ G₁ (F₁ f) ◃ G-seq (α₀ Y) (H₁ g)
    ∙ sym (G-seq (F₁ f) (α₀ Y) ▹ G₁ (H₁ g))
    ∙ G₂ (α□ f) ▹ G₁ (H₁ g)
    ∙ G-seq (α₀ X) (H₁ f) ▹ G₁ (H₁ g)
        ≡⟨ ∙l ∙l ∙r sym (G.F-seq-nat refl (α□ g)) ⟩
    sym (G-seq (F₁ (f ⋆ g)) (α₀ Z))
    ∙ G₂ (F.F-seq f g ▹ α₀ Z)
    ∙ (G-seq (F₁ f) (F₁ g ⋆ α₀ Z) ∙ G₁ (F₁ f) ◃ G₂ (α□ g))
    ∙ G₁ (F₁ f) ◃ G-seq (α₀ Y) (H₁ g)
    ∙ sym (G-seq (F₁ f) (α₀ Y) ▹ G₁ (H₁ g))
    ∙ G₂ (α□ f) ▹ G₁ (H₁ g)
    ∙ G-seq (α₀ X) (H₁ f) ▹ G₁ (H₁ g)
        ≡⟨ ∙l ∙l ∙r ∙r shuffleSymRD
            (sym (G.F-Assoc (F₁ f) (F₁ g) (α₀ Z) ∙ sym (lUnit _))) ⟩
    sym (G-seq (F₁ (f ⋆ g)) (α₀ Z))
    ∙ G₂ (F.F-seq f g ▹ α₀ Z)
    ∙ (((G-seq (F₁ f ⋆ F₁ g) (α₀ Z)
        ∙ G-seq (F₁ f) (F₁ g) ▹ G₁ (α₀ Z))
        ∙ sym (G₁ (F₁ f) ◃ G-seq (F₁ g) (α₀ Z)))
      ∙ G₁ (F₁ f) ◃ G₂ (α□ g))
    ∙ G₁ (F₁ f) ◃ G-seq (α₀ Y) (H₁ g)
    ∙ sym (G-seq (F₁ f) (α₀ Y) ▹ G₁ (H₁ g))
    ∙ G₂ (α□ f) ▹ G₁ (H₁ g)
    ∙ G-seq (α₀ X) (H₁ f) ▹ G₁ (H₁ g)
        ≡⟨ reass₅ ⟩
    sym (G-seq (F₁ (f ⋆ g)) (α₀ Z))
    ∙ (G₂ (F.F-seq f g ▹ α₀ Z) ∙ G-seq (F₁ f ⋆ F₁ g) (α₀ Z))
    ∙ G-seq (F₁ f) (F₁ g) ▹ G₁ (α₀ Z)
    ∙ sym (G₁ (F₁ f) ◃ G-seq (F₁ g) (α₀ Z))
    ∙ G₁ (F₁ f) ◃ G₂ (α□ g)
    ∙ G₁ (F₁ f) ◃ G-seq (α₀ Y) (H₁ g)
    ∙ sym (G-seq (F₁ f) (α₀ Y) ▹ G₁ (H₁ g))
    ∙ G₂ (α□ f) ▹ G₁ (H₁ g)
    ∙ G-seq (α₀ X) (H₁ f) ▹ G₁ (H₁ g)
        ≡⟨ ∙l ∙r sym (G.F-seq-nat (F.F-seq f g) refl) ⟩
    sym (G-seq (F₁ (f ⋆ g)) (α₀ Z))
    ∙ (G-seq (F₁ (f ⋆ g)) (α₀ Z) ∙ G₂ (F.F-seq f g) ▹ G₁ (α₀ Z))
    ∙ G-seq (F₁ f) (F₁ g) ▹ G₁ (α₀ Z)
    ∙ sym (G₁ (F₁ f) ◃ G-seq (F₁ g) (α₀ Z))
    ∙ G₁ (F₁ f) ◃ G₂ (α□ g)
    ∙ G₁ (F₁ f) ◃ G-seq (α₀ Y) (H₁ g)
    ∙ sym (G-seq (F₁ f) (α₀ Y) ▹ G₁ (H₁ g))
    ∙ G₂ (α□ f) ▹ G₁ (H₁ g)
    ∙ G-seq (α₀ X) (H₁ f) ▹ G₁ (H₁ g)
        ≡⟨ reass₆ ⟩
    (sym (G-seq (F₁ (f ⋆ g)) (α₀ Z)) ∙ G-seq (F₁ (f ⋆ g)) (α₀ Z))
    ∙ G₂ (F.F-seq f g) ▹ G₁ (α₀ Z)
    ∙ G-seq (F₁ f) (F₁ g) ▹ G₁ (α₀ Z)
    ∙ sym (G₁ (F₁ f) ◃ G-seq (F₁ g) (α₀ Z))
    ∙ G₁ (F₁ f) ◃ G₂ (α□ g)
    ∙ G₁ (F₁ f) ◃ G-seq (α₀ Y) (H₁ g)
    ∙ sym (G-seq (F₁ f) (α₀ Y) ▹ G₁ (H₁ g))
    ∙ G₂ (α□ f) ▹ G₁ (H₁ g)
    ∙ G-seq (α₀ X) (H₁ f) ▹ G₁ (H₁ g)
        ≡⟨ ∙r lCancel _ ⟩
    refl
    ∙ G₂ (F.F-seq f g) ▹ G₁ (α₀ Z)
    ∙ G-seq (F₁ f) (F₁ g) ▹ G₁ (α₀ Z)
    ∙ sym (G₁ (F₁ f) ◃ G-seq (F₁ g) (α₀ Z))
    ∙ G₁ (F₁ f) ◃ G₂ (α□ g)
    ∙ G₁ (F₁ f) ◃ G-seq (α₀ Y) (H₁ g)
    ∙ sym (G-seq (F₁ f) (α₀ Y) ▹ G₁ (H₁ g))
    ∙ G₂ (α□ f) ▹ G₁ (H₁ g)
    ∙ G-seq (α₀ X) (H₁ f) ▹ G₁ (H₁ g)
        ≡⟨ reass₇ ⟩
    (G₂ (F.F-seq f g) ∙ G-seq (F₁ f) (F₁ g)) ▹ G₁ (α₀ Z)
    ∙ G₁ (F₁ f) ◃ (sym (G-seq (F₁ g) (α₀ Z))
      ∙ G₂ (α□ g) ∙ G-seq (α₀ Y) (H₁ g))
    ∙ (sym (G-seq (F₁ f) (α₀ Y))
      ∙ G₂ (α□ f) ∙ G-seq (α₀ X) (H₁ f)) ▹ G₁ (H₁ g)
        ∎
    where
    reass₁ = reassoc
      ( (↑ sym (G-seq (F₁ (f ⋆ g)) (α₀ Z))
        ∙′ G.F₂′ (↑ α□ (f ⋆ g))
        ∙′ ↑ G-seq (α₀ X) (H₁ (f ⋆ g)))
      ∙′ G₁ (α₀ X) ◃′ (G.F₂′ (↑ H-seq f g) ∙′ ↑ G-seq (H₁ f) (H₁ g)) )
      ( ↑ sym (G-seq (F₁ (f ⋆ g)) (α₀ Z))
      ∙′ G.F₂′ (↑ α□ (f ⋆ g))
      ∙′ (↑ G-seq (α₀ X) (H₁ (f ⋆ g))
        ∙′ G₁ (α₀ X) ◃′ G.F₂′ (↑ H-seq f g))
      ∙′ G₁ (α₀ X) ◃′ ↑ G-seq (H₁ f) (H₁ g) )
      refl
    reass₂ = reassoc
      ( ↑ sym (G-seq (F₁ (f ⋆ g)) (α₀ Z))
      ∙′ G.F₂′ (↑ α□ (f ⋆ g))
      ∙′ (G.F₂′ (α₀ X ◃′ ↑ H-seq f g)
        ∙′ ↑ G-seq (α₀ X) (H₁ f ⋆ H₁ g))
      ∙′ G₁ (α₀ X) ◃′ ↑ G-seq (H₁ f) (H₁ g) )
      ( ↑ sym (G-seq (F₁ (f ⋆ g)) (α₀ Z))
      ∙′ G.F₂′ (↑ α□ (f ⋆ g) ∙′ α₀ X ◃′ ↑ H-seq f g)
      ∙′ (↑ G-seq (α₀ X) (H₁ f ⋆ H₁ g)
        ∙′ G₁ (α₀ X) ◃′ ↑ G-seq (H₁ f) (H₁ g)) )
      refl
    reass₃ = reassoc
      ( ↑ sym (G-seq (F₁ (f ⋆ g)) (α₀ Z))
      ∙′ G.F₂′ (↑ F.F-seq f g ▹′ α₀ Z
        ∙′ F₁ f ◃′ ↑ α□ g ∙′ ↑ α□ f ▹′ H₁ g)
      ∙′ ↑ G-seq (α₀ X ⋆ H₁ f) (H₁ g)
      ∙′ ↑ G-seq (α₀ X) (H₁ f) ▹′ G₁ (H₁ g) )
      ( ↑ sym (G-seq (F₁ (f ⋆ g)) (α₀ Z))
      ∙′ G.F₂′ (↑ F.F-seq f g ▹′ α₀ Z)
      ∙′ G.F₂′ (F₁ f ◃′ ↑ α□ g)
      ∙′ (G.F₂′ (↑ α□ f ▹′ H₁ g)
        ∙′ ↑ G-seq (α₀ X ⋆ H₁ f) (H₁ g))
      ∙′ ↑ G-seq (α₀ X) (H₁ f) ▹′ G₁ (H₁ g) )
      refl
    reass₄ = reassoc
      ( ↑ sym (G-seq (F₁ (f ⋆ g)) (α₀ Z))
      ∙′ G.F₂′ (↑ F.F-seq f g ▹′ α₀ Z)
      ∙′ G.F₂′ (F₁ f ◃′ ↑ α□ g)
      ∙′ (((↑ G-seq (F₁ f) (α₀ Y ⋆ H₁ g)
          ∙′ G₁ (F₁ f) ◃′ ↑ G-seq (α₀ Y) (H₁ g))
          ∙′ ↑ sym (G-seq (F₁ f) (α₀ Y)) ▹′ G₁ (H₁ g))
        ∙′ G.F₂′ (↑ α□ f) ▹′ G₁ (H₁ g))
      ∙′ ↑ G-seq (α₀ X) (H₁ f) ▹′ G₁ (H₁ g) )
      ( ↑ sym (G-seq (F₁ (f ⋆ g)) (α₀ Z))
      ∙′ G.F₂′ (↑ F.F-seq f g ▹′ α₀ Z)
      ∙′ (G.F₂′ (F₁ f ◃′ ↑ α□ g) ∙′ ↑ G-seq (F₁ f) (α₀ Y ⋆ H₁ g))
      ∙′ G₁ (F₁ f) ◃′ ↑ G-seq (α₀ Y) (H₁ g)
      ∙′ ↑ sym (G-seq (F₁ f) (α₀ Y)) ▹′ G₁ (H₁ g)
      ∙′ G.F₂′ (↑ α□ f) ▹′ G₁ (H₁ g)
      ∙′ ↑ G-seq (α₀ X) (H₁ f) ▹′ G₁ (H₁ g) )
      refl
    reass₅ = reassoc
      ( ↑ sym (G-seq (F₁ (f ⋆ g)) (α₀ Z))
      ∙′ G.F₂′ (↑ F.F-seq f g ▹′ α₀ Z)
      ∙′ (((↑ G-seq (F₁ f ⋆ F₁ g) (α₀ Z)
          ∙′ ↑ G-seq (F₁ f) (F₁ g) ▹′ G₁ (α₀ Z))
          ∙′ G₁ (F₁ f) ◃′ ↑ sym (G-seq (F₁ g) (α₀ Z)))
        ∙′ G₁ (F₁ f) ◃′ G.F₂′ (↑ α□ g))
      ∙′ G₁ (F₁ f) ◃′ ↑ G-seq (α₀ Y) (H₁ g)
      ∙′ ↑ sym (G-seq (F₁ f) (α₀ Y)) ▹′ G₁ (H₁ g)
      ∙′ G.F₂′ (↑ α□ f) ▹′ G₁ (H₁ g)
      ∙′ ↑ G-seq (α₀ X) (H₁ f) ▹′ G₁ (H₁ g) )
      ( ↑ sym (G-seq (F₁ (f ⋆ g)) (α₀ Z))
      ∙′ (G.F₂′ (↑ F.F-seq f g ▹′ α₀ Z)
        ∙′ ↑ G-seq (F₁ f ⋆ F₁ g) (α₀ Z))
      ∙′ ↑ G-seq (F₁ f) (F₁ g) ▹′ G₁ (α₀ Z)
      ∙′ G₁ (F₁ f) ◃′ ↑ sym (G-seq (F₁ g) (α₀ Z))
      ∙′ G₁ (F₁ f) ◃′ G.F₂′ (↑ α□ g)
      ∙′ G₁ (F₁ f) ◃′ ↑ G-seq (α₀ Y) (H₁ g)
      ∙′ ↑ sym (G-seq (F₁ f) (α₀ Y)) ▹′ G₁ (H₁ g)
      ∙′ G.F₂′ (↑ α□ f) ▹′ G₁ (H₁ g)
      ∙′ ↑ G-seq (α₀ X) (H₁ f) ▹′ G₁ (H₁ g) )
      refl
    reass₆ = reassoc
      ( ↑ sym (G-seq (F₁ (f ⋆ g)) (α₀ Z))
      ∙′ (↑ G-seq (F₁ (f ⋆ g)) (α₀ Z) ∙′ G.F₂′ (↑ F.F-seq f g) ▹′ G₁ (α₀ Z))
      ∙′ ↑ G-seq (F₁ f) (F₁ g) ▹′ G₁ (α₀ Z)
      ∙′ G₁ (F₁ f) ◃′ ↑ sym (G-seq (F₁ g) (α₀ Z))
      ∙′ G₁ (F₁ f) ◃′ G.F₂′ (↑ α□ g)
      ∙′ G₁ (F₁ f) ◃′ ↑ G-seq (α₀ Y) (H₁ g)
      ∙′ ↑ sym (G-seq (F₁ f) (α₀ Y)) ▹′ G₁ (H₁ g)
      ∙′ G.F₂′ (↑ α□ f) ▹′ G₁ (H₁ g)
      ∙′ ↑ G-seq (α₀ X) (H₁ f) ▹′ G₁ (H₁ g) )
      ( (↑ sym (G-seq (F₁ (f ⋆ g)) (α₀ Z)) ∙′ ↑ G-seq (F₁ (f ⋆ g)) (α₀ Z))
      ∙′ G.F₂′ (↑ F.F-seq f g) ▹′ G₁ (α₀ Z)
      ∙′ ↑ G-seq (F₁ f) (F₁ g) ▹′ G₁ (α₀ Z)
      ∙′ G₁ (F₁ f) ◃′ ↑ sym (G-seq (F₁ g) (α₀ Z))
      ∙′ G₁ (F₁ f) ◃′ G.F₂′ (↑ α□ g)
      ∙′ G₁ (F₁ f) ◃′ ↑ G-seq (α₀ Y) (H₁ g)
      ∙′ ↑ sym (G-seq (F₁ f) (α₀ Y)) ▹′ G₁ (H₁ g)
      ∙′ G.F₂′ (↑ α□ f) ▹′ G₁ (H₁ g)
      ∙′ ↑ G-seq (α₀ X) (H₁ f) ▹′ G₁ (H₁ g) )
      refl
    reass₇ = reassoc
      ( refl′
      ∙′ G.F₂′ (↑ F.F-seq f g) ▹′ G₁ (α₀ Z)
      ∙′ ↑ G-seq (F₁ f) (F₁ g) ▹′ G₁ (α₀ Z)
      ∙′ G₁ (F₁ f) ◃′ ↑ sym (G-seq (F₁ g) (α₀ Z))
      ∙′ G₁ (F₁ f) ◃′ G.F₂′ (↑ α□ g)
      ∙′ G₁ (F₁ f) ◃′ ↑ G-seq (α₀ Y) (H₁ g)
      ∙′ ↑ sym (G-seq (F₁ f) (α₀ Y)) ▹′ G₁ (H₁ g)
      ∙′ G.F₂′ (↑ α□ f) ▹′ G₁ (H₁ g)
      ∙′ ↑ G-seq (α₀ X) (H₁ f) ▹′ G₁ (H₁ g) )
      ( (G.F₂′ (↑ F.F-seq f g) ∙′ ↑ G-seq (F₁ f) (F₁ g)) ▹′ G₁ (α₀ Z)
      ∙′ G₁ (F₁ f) ◃′ (↑ sym (G-seq (F₁ g) (α₀ Z))
        ∙′ G.F₂′ (↑ α□ g) ∙′ ↑ G-seq (α₀ Y) (H₁ g))
      ∙′ (↑ sym (G-seq (F₁ f) (α₀ Y))
        ∙′ G.F₂′ (↑ α□ f) ∙′ ↑ G-seq (α₀ X) (H₁ f)) ▹′ G₁ (H₁ g) )
      refl
