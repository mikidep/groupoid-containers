open import Cubical.Foundations.Prelude

open import Cubical.Foundations.Function
open import Cubical.Foundations.GroupoidLaws
open import Prelude.ExtraGpdLaws

open import Cubical.WildCat.Functor hiding (_$_)
open import Cubical.WildCat.Product renaming (_×_ to ProdCat)

module Cubical.Bicategory.Copresheaf.EndoConstructions.Composite
  (ℓ : Level) where

open import Cubical.Bicategory.Base
open import Cubical.Bicategory.Copresheaf ℓ
  using (Copresheaf; GPD; Is2Copresheaf; PseudonatTrans; IsPseudonat)
open import Cubical.Bicategory.Copresheaf.EndoConstructions.Base ℓ

open Copresheaf using (str; is2Copresheaf)
open WildFunctor
open Is2Copresheaf

open Bicategory GPD renaming (str to ⟨GPD⟩; Hom[_,_] to GPD[_,_])
open 2CellLaws ⟨GPD⟩

module _ (F G : GpdEndo) where
  open import Prelude.Utils
  open import Prelude.Reassoc
  open BicatReassoc ⟨GPD⟩

  open Copresheaf F using (F₀; F₁; F₂)
  private module F = Copresheaf F
  open Copresheaf G using ()
    renaming (
      F₀ to    G₀;
      F₁ to    G₁;
      F₂ to    G₂;
      F-id to  G-id;
      F-seq to G-seq;
      F-IdL to G-IdL;
      F-IdR to G-IdR;
      F-Assoc to G-Assoc;
      F-seq-nat to G-seq-nat;
      F₂-funct to G₂-funct;
      F₂′ to G₂′
    )
  compEndo₀ : GpdEndo
  compEndo₀ .str .F-ob = F₀ » G₀
  compEndo₀ .str .F-hom = F₁ » G₁
  compEndo₀ .str .F-id = G₂ F.F-id ∙ G-id
  compEndo₀ .str .F-seq f g = G₂ (F.F-seq f g) ∙ G-seq (F₁ f) (F₁ g)
  compEndo₀ .is2Copresheaf .F-IdL f =
      (G₂ (F.F-seq id f) ∙ G-seq (F₁ id) (F₁ f))
      ∙ (G₂ F.F-id ∙ G-id) ▹ G₁ (F₁ f)
    ≡⟨ reass₁ ⟩
      G₂ (F.F-seq id f)
      ∙ (G-seq (F₁ id) (F₁ f) ∙ G₂ F.F-id ▹ G₁ (F₁ f))
      ∙ G-id ▹ G₁ (F₁ f)
    ≡⟨ ∙l ∙r G-seq-nat F.F-id refl ⟩
      G₂ (F.F-seq id f)
      ∙ (G₂ (F.F-id ▹ F₁ f) ∙ G-seq id (F₁ f))
      ∙ G-id ▹ G₁ (F₁ f)
    ≡⟨ reass₂ ⟩
      (G₂ (F.F-seq id f ∙ F.F-id ▹ F₁ f)
        ∙ G-seq id (F₁ f))
      ∙ G-id ▹ G₁ (F₁ f)
    ≡⟨ ∙r ∙r cong G₂ (F.F-IdL f) ⟩
      (refl ∙ G-seq id (F₁ f))
      ∙ G-id ▹ G₁ (F₁ f)
    ≡⟨ sym assoc-inf ⟩
      refl
      ∙ G-seq id (F₁ f)
      ∙ G-id ▹ G₁ (F₁ f)
    ≡⟨ sym (lUnit _) ⟩
      G-seq id (F₁ f) ∙ G-id ▹ G₁ (F₁ f)
    ≡⟨ G-IdL (F₁ f) ⟩
      refl
    ∎
    where
    reass₁ = reassoc
          ( (↑ G₂ (F.F-seq id f) ∙′ ↑ G-seq (F₁ id) (F₁ f))
          ∙′ (↑ G₂ F.F-id ∙′ ↑ G-id) ▹′ G₁ (F₁ f) )
          ( ↑ G₂ (F.F-seq id f)
          ∙′ (↑ G-seq (F₁ id) (F₁ f) ∙′ ↑ G₂ F.F-id ▹′ G₁ (F₁ f))
          ∙′ ↑ G-id ▹′ G₁ (F₁ f) )
          refl
    reass₂ = reassoc
          ( G₂′ (↑ F.F-seq id f)
          ∙′ (G₂′ (↑ F.F-id ▹′ F₁ f) ∙′ ↑ G-seq id (F₁ f))
          ∙′ ↑ G-id ▹′ G₁ (F₁ f) )
          ( (G₂′ (↑ F.F-seq id f ∙′ ↑ F.F-id ▹′ F₁ f)
            ∙′ ↑ G-seq id (F₁ f))
          ∙′ ↑ G-id ▹′ G₁ (F₁ f) )
          refl
  compEndo₀ .is2Copresheaf .F-IdR f =
      (G₂ (F.F-seq f id) ∙ G-seq (F₁ f) (F₁ id))
      ∙ G₁ (F₁ f) ◃ (G₂ F.F-id ∙ G-id)
    ≡⟨ reass₁ ⟩
      (G₂ (F.F-seq f id)
        ∙ G-seq (F₁ f) (F₁ id)
        ∙ G₁ (F₁ f) ◃ G₂ F.F-id)
      ∙ G₁ (F₁ f) ◃ G-id
    ≡⟨ ∙r ∙l G-seq-nat refl F.F-id ⟩
      (G₂ (F.F-seq f id)
        ∙ G₂ (F₁ f ◃ F.F-id)
        ∙ G-seq (F₁ f) id)
      ∙ G₁ (F₁ f) ◃ G-id
    ≡⟨ reass₂ ⟩
      ((G₂ (F.F-seq f id ∙ F₁ f ◃ F.F-id))
        ∙ G-seq (F₁ f) id)
      ∙ G₁ (F₁ f) ◃ G-id
    ≡⟨ ∙r ∙r cong G₂ (F.F-IdR f) ⟩
      (refl ∙ G-seq (F₁ f) id) ∙ G₁ (F₁ f) ◃ G-id
    ≡⟨ sym assoc-inf ⟩
      refl ∙ G-seq (F₁ f) id ∙ G₁ (F₁ f) ◃ G-id
    ≡⟨ sym (lUnit _) ⟩
      G-seq (F₁ f) id ∙ G₁ (F₁ f) ◃ G-id
    ≡⟨ G-IdR (F₁ f) ⟩
      refl
    ∎
    where
    reass₁ = reassoc
      ( (G₂′ (↑ F.F-seq f id) ∙′ ↑ G-seq (F₁ f) (F₁ id))
      ∙′ G₁ (F₁ f) ◃′ (G₂′ (↑ F.F-id) ∙′ ↑ G-id) )
      ( (G₂′ (↑ F.F-seq f id)
        ∙′ ↑ G-seq (F₁ f) (F₁ id)
        ∙′ G₁ (F₁ f) ◃′ G₂′ (↑ F.F-id))
      ∙′ G₁ (F₁ f) ◃′ ↑ G-id )
      refl
    reass₂ = reassoc
      ( (G₂′ (↑ F.F-seq f id)
        ∙′ G₂′ (F₁ f ◃′ ↑ F.F-id)
        ∙′ ↑ G-seq (F₁ f) id)
      ∙′ G₁ (F₁ f) ◃′ ↑ G-id )
      ( ((G₂′ (↑ F.F-seq f id ∙′ F₁ f ◃′ ↑ F.F-id))
        ∙′ ↑ G-seq (F₁ f) id)
      ∙′ G₁ (F₁ f) ◃′ ↑ G-id )
      refl
  compEndo₀ .is2Copresheaf .F-Assoc f g h =
      (G₂ (F.F-seq (f ⋆ g) h)
        ∙ G-seq (F₁ (f ⋆ g)) (F₁ h))
      ∙ (G₂ (F.F-seq f g)
        ∙ G-seq (F₁ f) (F₁ g)) ▹ G₁ (F₁ h)
    ≡⟨ reass₁ ⟩
      G₂ (F.F-seq (f ⋆ g) h)
      ∙ (G-seq (F₁ (f ⋆ g)) (F₁ h)
        ∙ G₂ (F.F-seq f g) ▹ G₁ (F₁ h))
      ∙ G-seq (F₁ f) (F₁ g) ▹ G₁ (F₁ h)
    ≡⟨ ∙l ∙r G-seq-nat _ refl ⟩
      G₂ (F.F-seq (f ⋆ g) h)
      ∙ (G₂ (F.F-seq f g ▹ F₁ h)
        ∙ G-seq (F₁ f ⋆ F₁ g) (F₁ h))
      ∙ G-seq (F₁ f) (F₁ g) ▹ G₁ (F₁ h)
    ≡⟨ reass₂ ⟩
      G₂ (F.F-seq (f ⋆ g) h
        ∙ F.F-seq f g ▹ F₁ h)
      ∙ G-seq (F₁ f ⋆ F₁ g) (F₁ h)
      ∙ G-seq (F₁ f) (F₁ g) ▹ G₁ (F₁ h)
    ≡⟨ ∙r cong G₂ (F.F-Assoc _ _ _) ⟩
      G₂ (refl ∙ F.F-seq f (g ⋆ h)
          ∙ F₁ f ◃ F.F-seq g h)
      ∙ G-seq (F₁ f ⋆ F₁ g) (F₁ h)
      ∙ G-seq (F₁ f) (F₁ g) ▹ G₁ (F₁ h)
    ≡⟨ reass₃ ⟩
      refl ∙ (G₂ (F.F-seq f (g ⋆ h)
        ∙ F₁ f ◃ F.F-seq g h))
      ∙ G-seq (F₁ f ⋆ F₁ g) (F₁ h)
      ∙ G-seq (F₁ f) (F₁ g) ▹ G₁ (F₁ h)
    ≡⟨ ∙l ∙l G-Assoc _ _ _ ⟩
      refl ∙ (G₂ (F.F-seq f (g ⋆ h)
        ∙ F₁ f ◃ F.F-seq g h))
      ∙ refl
      ∙ G-seq (F₁ f) (F₁ g ⋆ F₁ h)
      ∙ G₁ (F₁ f) ◃ G-seq (F₁ g) (F₁ h)
    ≡⟨ reass₄ ⟩
      refl
      ∙ G₂ (F.F-seq f (g ⋆ h))
      ∙ (G₂ (F₁ f ◃ F.F-seq g h)
        ∙ G-seq (F₁ f) (F₁ g ⋆ F₁ h))
      ∙ G₁ (F₁ f) ◃ G-seq (F₁ g) (F₁ h)
    ≡⟨ ∙l ∙l ∙r sym (G-seq-nat refl (F.F-seq g h)) ⟩
      refl
      ∙ G₂ (F.F-seq f (g ⋆ h))
      ∙ (G-seq (F₁ f) (F₁ (g ⋆ h))
        ∙ G₁ (F₁ f) ◃ G₂ (F.F-seq g h))
      ∙ G₁ (F₁ f) ◃ G-seq (F₁ g) (F₁ h)
    ≡⟨ reass₅ ⟩
      refl
      ∙ (G₂ (F.F-seq f (g ⋆ h))
        ∙ G-seq (F₁ f) (F₁ (g ⋆ h)))
      ∙ G₁ (F₁ f) ◃ (G₂ (F.F-seq g h)
        ∙ G-seq (F₁ g) (F₁ h))
    ∎
    where
    reass₁ = reassoc
      ( (↑ G₂ (F.F-seq (f ⋆ g) h)
        ∙′ ↑ G-seq (F₁ (f ⋆ g)) (F₁ h))
      ∙′ (↑ G₂ (F.F-seq f g)
        ∙′ ↑ G-seq (F₁ f) (F₁ g)) ▹′ G₁ (F₁ h) )
      ( ↑ G₂ (F.F-seq (f ⋆ g) h)
      ∙′ (↑ G-seq (F₁ (f ⋆ g)) (F₁ h)
        ∙′ ↑ G₂ (F.F-seq f g) ▹′ G₁ (F₁ h))
      ∙′ ↑ G-seq (F₁ f) (F₁ g) ▹′ G₁ (F₁ h) )
      refl
    reass₂ = reassoc
      ( G₂′ (↑ F.F-seq (f ⋆ g) h)
      ∙′ (G₂′ (↑ F.F-seq f g ▹′ F₁ h)
        ∙′ ↑ G-seq (F₁ f ⋆ F₁ g) (F₁ h))
      ∙′ ↑ G-seq (F₁ f) (F₁ g) ▹′ G₁ (F₁ h) )
      ( G₂′ (↑ F.F-seq (f ⋆ g) h
        ∙′ ↑ F.F-seq f g ▹′ F₁ h)
      ∙′ ↑ G-seq (F₁ f ⋆ F₁ g) (F₁ h)
      ∙′ ↑ G-seq (F₁ f) (F₁ g) ▹′ G₁ (F₁ h) )
      refl
    reass₃ = reassoc
      ( G₂′ (refl′ ∙′ ↑ F.F-seq f (g ⋆ h)
          ∙′ F₁ f ◃′ ↑ F.F-seq g h)
      ∙′ ↑ G-seq (F₁ f ⋆ F₁ g) (F₁ h)
      ∙′ ↑ G-seq (F₁ f) (F₁ g) ▹′ G₁ (F₁ h) )
      ( refl′ ∙′ (G₂′ (↑ F.F-seq f (g ⋆ h)
        ∙′ F₁ f ◃′ ↑ F.F-seq g h))
      ∙′ ↑ G-seq (F₁ f ⋆ F₁ g) (F₁ h)
      ∙′ ↑ G-seq (F₁ f) (F₁ g) ▹′ G₁ (F₁ h) )
      refl
    reass₄ = reassoc
      ( refl′ ∙′ (G₂′ (↑ F.F-seq f (g ⋆ h)
        ∙′ F₁ f ◃′ ↑ F.F-seq g h))
      ∙′ refl′
      ∙′ ↑ G-seq (F₁ f) (F₁ g ⋆ F₁ h)
      ∙′ G₁ (F₁ f) ◃′ ↑ G-seq (F₁ g) (F₁ h) )
      ( refl′
      ∙′ G₂′ (↑ F.F-seq f (g ⋆ h))
      ∙′ (G₂′ (F₁ f ◃′ ↑ F.F-seq g h)
        ∙′ ↑ G-seq (F₁ f) (F₁ g ⋆ F₁ h))
      ∙′ G₁ (F₁ f) ◃′ ↑ G-seq (F₁ g) (F₁ h) )
      refl
    reass₅ = reassoc 
      ( refl′
      ∙′ ↑ G₂ (F.F-seq f (g ⋆ h))
      ∙′ (↑ G-seq (F₁ f) (F₁ (g ⋆ h))
        ∙′ G₁ (F₁ f) ◃′ ↑ G₂ (F.F-seq g h))
      ∙′ G₁ (F₁ f) ◃′ ↑ G-seq (F₁ g) (F₁ h) )
      ( refl′
      ∙′ (↑ G₂ (F.F-seq f (g ⋆ h))
        ∙′ ↑ G-seq (F₁ f) (F₁ (g ⋆ h)))
      ∙′ G₁ (F₁ f) ◃′ (↑ G₂ (F.F-seq g h)
        ∙′ ↑ G-seq (F₁ g) (F₁ h)) )
      refl
