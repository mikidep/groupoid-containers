open import Cubical.Foundations.Prelude

open import Cubical.Foundations.Function
open import Cubical.Foundations.GroupoidLaws

open import Cubical.WildCat.Functor

module Cubical.Bicategory.Copresheaf.EndoConstructions 
  (ℓ : Level) where

open import Cubical.Bicategory.Base
open import Cubical.Bicategory.Copresheaf ℓ 
  using (Copresheaf; GPD; Is2Copresheaf)

GpdEndo = Copresheaf GPD

open Copresheaf using (str; is2Copresheaf)
open WildFunctor
open Is2Copresheaf

open Bicategory GPD renaming (str to ⟨GPD⟩)
open 2CellLaws ⟨GPD⟩

module _ where
  idEndo : GpdEndo
  idEndo .str .F-ob = idfun _
  idEndo .str .F-hom = idfun _
  idEndo .str .F-id = refl
  idEndo .str .F-seq _ _ = refl
  idEndo .is2Copresheaf .F-seq-nat _ _ = sym (lUnit _) ∙ rUnit _
  idEndo .is2Copresheaf .F-IdL _ = sym (lUnit _)
  idEndo .is2Copresheaf .F-IdR _ = sym (rUnit _)
  idEndo .is2Copresheaf .F-Assoc _ _ _ = lUnit _

module _ (F G : GpdEndo) where
  open import Prelude

  open Copresheaf F using (F₀; F₁; F₂)
  module F = Copresheaf F
  open Copresheaf G using ()
    renaming (
      F₀ to    G₀;
      F₁ to    G₁;
      F₂ to    G₂;
      F-id to  G-id;
      F-seq to G-seq;
      F-IdL to G-IdL;
      F-seq-nat to G-seq-nat;
      F₂-funct to G₂-funct
    )

  compEndo₀ : GpdEndo
  compEndo₀ .str .F-ob = F₀ » G₀
  compEndo₀ .str .F-hom = F₁ » G₁
  compEndo₀ .str .F-id = G₂ F.F-id ∙ G-id
  compEndo₀ .str .F-seq f g = G₂ (F.F-seq f g) ∙ G-seq (F₁ f) (F₁ g)
  compEndo₀ .is2Copresheaf .F-seq-nat {f} {f′} {g} {g′} α β = 
      (G₂ (F.F-seq f g) 
        ∙ G-seq (F₁ f) (F₁ g))
      ∙ G₂ (F₂ α) ⋆₂ G₂ (F₂ β)
    ≡⟨ sym (assoc _ _ _) ⟩
      G₂ (F.F-seq f g) 
      ∙ G-seq (F₁ f) (F₁ g)
      ∙ G₂ (F₂ α) ⋆₂ G₂ (F₂ β)
    ≡⟨ cong (G₂ (F.F-seq f g) ∙_) (G-seq-nat _ _) ⟩ 
      G₂ (F.F-seq f g) 
      ∙ G₂ (F₂ α ⋆₂ F₂ β)
      ∙ G-seq (F₁ f′) (F₁ g′)
    ≡⟨ assoc _ _ _ ⟩
      (G₂ (F.F-seq f g) 
        ∙ G₂ (F₂ α ⋆₂ F₂ β))
      ∙ G-seq (F₁ f′) (F₁ g′)
    ≡⟨ cong (_∙ G-seq (F₁ f′) (F₁ g′)) (sym (G₂-funct _ _)) ⟩
      G₂ (F.F-seq f g ∙ F₂ α ⋆₂ F₂ β)
      ∙ G-seq (F₁ f′) (F₁ g′)
    ≡⟨ cong (λ x → G₂ x ∙ G-seq (F₁ f′) (F₁ g′))
        (F.F-seq-nat _ _) ⟩
      G₂ (F₂ (α ⋆₂ β) ∙ F.F-seq f′ g′)
      ∙ G-seq (F₁ f′) (F₁ g′)
    ≡⟨ cong (_∙ G-seq (F₁ f′) (F₁ g′)) (G₂-funct _ _) ⟩
      (G₂ (F₂ (α ⋆₂ β)) 
        ∙ G₂ (F.F-seq f′ g′))
      ∙ G-seq (F₁ f′) (F₁ g′)
    ≡⟨ sym (assoc _ _ _) ⟩
      G₂ (F₂ (α ⋆₂ β)) 
      ∙ G₂ (F.F-seq f′ g′) 
      ∙ G-seq (F₁ f′) (F₁ g′)
    ∎
  compEndo₀ .is2Copresheaf .F-IdL {x} {y} f = 
      (G₂ (F.F-seq id f) ∙ G-seq (F₁ id) (F₁ f)) 
        ∙ (G₂ F.F-id ∙ G-id) ▹ G₁ (F₁ f)
    ≡⟨ sym (assoc _ _ _) ⟩
      G₂ (F.F-seq id f) 
      ∙ G-seq (F₁ id) (F₁ f) 
      ∙ (G₂ F.F-id ∙ G-id) ▹ G₁ (F₁ f)
    ≡⟨ cong (λ x → G₂ (F.F-seq id f) ∙ G-seq (F₁ id) (F₁ f) ∙ x) 
        (▹-∙ _ _) ⟩
      G₂ (F.F-seq id f) 
      ∙ G-seq (F₁ id) (F₁ f) 
      ∙ G₂ F.F-id ▹ G₁ (F₁ f) 
      ∙ G-id ▹ G₁ (F₁ f)
    ≡⟨ cong (G₂ (F.F-seq id f) ∙_) (assoc _ _ _) ⟩
      G₂ (F.F-seq id f) 
      ∙ (G-seq (F₁ id) (F₁ f) ∙ G₂ F.F-id ▹ G₁ (F₁ f))
      ∙ G-id ▹ G₁ (F₁ f)
    ≡⟨ cong (λ x → G₂ (F.F-seq id f) ∙ x ∙ G-id ▹ G₁ (F₁ f)) 
        (G-seq-nat F.F-id refl) ⟩
      G₂ (F.F-seq id f) 
      ∙ (G₂ (F.F-id ▹ F₁ f) ∙ G-seq id (F₁ f))
      ∙ G-id ▹ G₁ (F₁ f)
    ≡⟨ assoc _ _ _ ⟩
      (G₂ (F.F-seq id f) 
        ∙ G₂ (F.F-id ▹ F₁ f) 
        ∙ G-seq id (F₁ f))
      ∙ G-id ▹ G₁ (F₁ f)
    ≡⟨ cong (_∙ G-id ▹ G₁ (F₁ f)) (assoc _ _ _) ⟩
      ((G₂ (F.F-seq id f) ∙ G₂ (F.F-id ▹ F₁ f))
        ∙ G-seq id (F₁ f))
      ∙ G-id ▹ G₁ (F₁ f)
    ≡⟨ cong (λ x → (x ∙ G-seq id (F₁ f)) ∙ G-id ▹ G₁ (F₁ f)) 
        (sym (G₂-funct _ _)) ⟩
      (G₂ (F.F-seq id f ∙ F.F-id ▹ F₁ f)
        ∙ G-seq id (F₁ f))
      ∙ G-id ▹ G₁ (F₁ f)
    ≡⟨ cong (λ x → (G₂ x ∙ G-seq id (F₁ f)) ∙ G-id ▹ G₁ (F₁ f)) 
        (F.F-IdL f) ⟩
      (refl ∙ G-seq id (F₁ f))
      ∙ G-id ▹ G₁ (F₁ f)
    ≡⟨ sym (assoc _ _ _) ⟩
      refl 
      ∙ G-seq id (F₁ f)
      ∙ G-id ▹ G₁ (F₁ f)
    ≡⟨ cong (refl ∙_) (G-IdL (F₁ f)) ⟩
      refl ∙ refl
    ≡⟨ sym (lUnit _) ⟩
      refl
    ∎
  compEndo₀ .is2Copresheaf .F-IdR = {! !}
  compEndo₀ .is2Copresheaf .F-Assoc = {! !}

