open import Cubical.Foundations.Prelude

open import Cubical.Foundations.Function
open import Cubical.Foundations.GroupoidLaws
open import Prelude.ExtraGpdLaws

open import Cubical.WildCat.Functor hiding (_$_)
open import Cubical.WildCat.Product renaming (_×_ to ProdCat)

module Cubical.Bicategory.Copresheaf.EndoConstructions 
  (ℓ : Level) where

open import Cubical.Bicategory.Base
open import Cubical.Bicategory.Copresheaf ℓ 
  using (Copresheaf; GPD; Is2Copresheaf; 2NatTrans; Is2NatTrans)
open import Cubical.Bicategory.Instances.Copresheaf ℓ

GpdEndo = Copresheaf GPD
GpdEndoWildCat = CopshWildCat GPD

open Copresheaf using (str; is2Copresheaf)
open WildFunctor
open Is2Copresheaf

open Bicategory GPD renaming (str to ⟨GPD⟩; Hom[_,_] to GPD[_,_])
open 2CellLaws ⟨GPD⟩

module _ where
  idEndo : GpdEndo
  idEndo .str .F-ob = idfun _
  idEndo .str .F-hom = idfun _
  idEndo .str .F-id = refl
  idEndo .str .F-seq _ _ = refl
  idEndo .is2Copresheaf .F-IdL _ = sym (lUnit _)
  idEndo .is2Copresheaf .F-IdR _ = sym (rUnit _)
  idEndo .is2Copresheaf .F-Assoc _ _ _ = lUnit _

module _ (F G : GpdEndo) where
  open import Prelude

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
      F₂-funct to G₂-funct
    )
  compEndo₀ : GpdEndo
  compEndo₀ .str .F-ob = F₀ » G₀
  compEndo₀ .str .F-hom = F₁ » G₁
  compEndo₀ .str .F-id = G₂ F.F-id ∙ G-id
  compEndo₀ .str .F-seq f g = G₂ (F.F-seq f g) ∙ G-seq (F₁ f) (F₁ g)
  compEndo₀ .is2Copresheaf .F-IdL f = 
      (G₂ (F.F-seq id f) ∙ G-seq (F₁ id) (F₁ f)) 
      ∙ (G₂ F.F-id ∙ G-id) ▹ G₁ (F₁ f)
    ≡⟨ sym assoc-inf ⟩
      G₂ (F.F-seq id f) 
      ∙ G-seq (F₁ id) (F₁ f) 
      ∙ (G₂ F.F-id ∙ G-id) ▹ G₁ (F₁ f)
    ≡⟨ cong (λ x → G₂ (F.F-seq id f) ∙ G-seq (F₁ id) (F₁ f) ∙ x) 
        (▹-∙ _ _) ⟩
      G₂ (F.F-seq id f) 
      ∙ G-seq (F₁ id) (F₁ f) 
      ∙ G₂ F.F-id ▹ G₁ (F₁ f) 
      ∙ G-id ▹ G₁ (F₁ f)
    ≡⟨ cong (G₂ (F.F-seq id f) ∙_) assoc-inf ⟩
      G₂ (F.F-seq id f) 
      ∙ (G-seq (F₁ id) (F₁ f) ∙ G₂ F.F-id ▹ G₁ (F₁ f))
      ∙ G-id ▹ G₁ (F₁ f)
    ≡⟨ cong (λ x → G₂ (F.F-seq id f) ∙ x ∙ G-id ▹ G₁ (F₁ f)) 
        (G-seq-nat F.F-id refl) ⟩
      G₂ (F.F-seq id f) 
      ∙ (G₂ (F.F-id ▹ F₁ f) ∙ G-seq id (F₁ f))
      ∙ G-id ▹ G₁ (F₁ f)
    ≡⟨ assoc-inf ⟩
      (G₂ (F.F-seq id f) 
        ∙ G₂ (F.F-id ▹ F₁ f) 
        ∙ G-seq id (F₁ f))
      ∙ G-id ▹ G₁ (F₁ f)
    ≡⟨ cong (_∙ G-id ▹ G₁ (F₁ f)) assoc-inf ⟩
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
    ≡⟨ sym assoc-inf ⟩
      refl 
      ∙ G-seq id (F₁ f)
      ∙ G-id ▹ G₁ (F₁ f)
    ≡⟨ sym (lUnit _) ⟩
      G-seq id (F₁ f) ∙ G-id ▹ G₁ (F₁ f)
    ≡⟨ G-IdL (F₁ f) ⟩
      refl
    ∎
  compEndo₀ .is2Copresheaf .F-IdR f =
      (G₂ (F.F-seq f id) ∙ G-seq (F₁ f) (F₁ id)) 
      ∙ G₁ (F₁ f) ◃ (G₂ F.F-id ∙ G-id)
    ≡⟨ cong ((G₂ (F.F-seq f id) ∙ G-seq (F₁ f) (F₁ id)) ∙_) 
        (◃-∙ _ _) ⟩
      (G₂ (F.F-seq f id) ∙ G-seq (F₁ f) (F₁ id)) 
      ∙ G₁ (F₁ f) ◃ G₂ F.F-id 
      ∙ G₁ (F₁ f) ◃ G-id
    ≡⟨ assoc-inf ⟩
      ((G₂ (F.F-seq f id) ∙ G-seq (F₁ f) (F₁ id)) 
        ∙ G₁ (F₁ f) ◃ G₂ F.F-id) 
      ∙ G₁ (F₁ f) ◃ G-id
    ≡⟨ cong (_∙ G₁ (F₁ f) ◃ G-id) (sym assoc-inf) ⟩
      (G₂ (F.F-seq f id) 
        ∙ G-seq (F₁ f) (F₁ id) 
        ∙ G₁ (F₁ f) ◃ G₂ F.F-id) 
      ∙ G₁ (F₁ f) ◃ G-id
    ≡⟨ cong (λ x → (G₂ (F.F-seq f id) ∙ x) ∙ G₁ (F₁ f) ◃ G-id) 
        (G-seq-nat refl F.F-id) ⟩
      (G₂ (F.F-seq f id) 
        ∙ G₂ (F₁ f ◃ F.F-id) 
        ∙ G-seq (F₁ f) id)
      ∙ G₁ (F₁ f) ◃ G-id
    ≡⟨ cong (_∙ G₁ (F₁ f) ◃ G-id) assoc-inf ⟩
      ((G₂ (F.F-seq f id) ∙ G₂ (F₁ f ◃ F.F-id)) 
        ∙ G-seq (F₁ f) id)
      ∙ G₁ (F₁ f) ◃ G-id
    ≡⟨ cong (λ x → (x ∙ G-seq (F₁ f) id) ∙ G₁ (F₁ f) ◃ G-id) 
        (sym (G₂-funct _ _)) ⟩
      ((G₂ (F.F-seq f id ∙ F₁ f ◃ F.F-id)) 
        ∙ G-seq (F₁ f) id)
      ∙ G₁ (F₁ f) ◃ G-id
    ≡⟨ cong (λ x → (G₂ x ∙ G-seq (F₁ f) id) ∙ G₁ (F₁ f) ◃ G-id) 
        (F.F-IdR f) ⟩
      (refl ∙ G-seq (F₁ f) id) ∙ G₁ (F₁ f) ◃ G-id
    ≡⟨ sym assoc-inf ⟩
      refl ∙ G-seq (F₁ f) id ∙ G₁ (F₁ f) ◃ G-id
    ≡⟨ sym (lUnit _) ⟩
      G-seq (F₁ f) id ∙ G₁ (F₁ f) ◃ G-id
    ≡⟨ G-IdR (F₁ f) ⟩
      refl
    ∎
  compEndo₀ .is2Copresheaf .F-Assoc f g h = 
      (G₂ (F.F-seq (f ⋆ g) h) 
        ∙ G-seq (F₁ (f ⋆ g)) (F₁ h))
      ∙ (G₂ (F.F-seq f g) 
        ∙ G-seq (F₁ f) (F₁ g)) ▹ G₁ (F₁ h)
    ≡⟨ cong ((G₂ (F.F-seq (f ⋆ g) h) ∙ G-seq (F₁ (f ⋆ g)) (F₁ h)) ∙_)
        (▹-∙ _ _) ⟩
      (G₂ (F.F-seq (f ⋆ g) h) 
        ∙ G-seq (F₁ (f ⋆ g)) (F₁ h))
      ∙ G₂ (F.F-seq f g) ▹ G₁ (F₁ h)
      ∙ G-seq (F₁ f) (F₁ g) ▹ G₁ (F₁ h)
    ≡⟨ sym assoc-inf ⟩
      G₂ (F.F-seq (f ⋆ g) h) 
      ∙ G-seq (F₁ (f ⋆ g)) (F₁ h)
      ∙ G₂ (F.F-seq f g) ▹ G₁ (F₁ h)
      ∙ G-seq (F₁ f) (F₁ g) ▹ G₁ (F₁ h)
    ≡⟨ cong (G₂ (F.F-seq (f ⋆ g) h) ∙_) assoc-inf ⟩
      G₂ (F.F-seq (f ⋆ g) h) 
      ∙ (G-seq (F₁ (f ⋆ g)) (F₁ h)
        ∙ G₂ (F.F-seq f g) ▹ G₁ (F₁ h))
      ∙ G-seq (F₁ f) (F₁ g) ▹ G₁ (F₁ h)
    ≡⟨ cong (λ x → G₂ (F.F-seq (f ⋆ g) h) ∙ x
          ∙ G-seq (F₁ f) (F₁ g) ▹ G₁ (F₁ h))
        (G-seq-nat _ refl) ⟩
      G₂ (F.F-seq (f ⋆ g) h) 
      ∙ (G₂ (F.F-seq f g ▹ F₁ h) 
        ∙ G-seq (F₁ f ⋆ F₁ g) (F₁ h))
      ∙ G-seq (F₁ f) (F₁ g) ▹ G₁ (F₁ h)
    ≡⟨ cong (G₂ (F.F-seq (f ⋆ g) h) ∙_) (sym assoc-inf) ⟩
      G₂ (F.F-seq (f ⋆ g) h) 
      ∙ G₂ (F.F-seq f g ▹ F₁ h) 
      ∙ G-seq (F₁ f ⋆ F₁ g) (F₁ h)
      ∙ G-seq (F₁ f) (F₁ g) ▹ G₁ (F₁ h)
    ≡⟨ assoc-inf ⟩
      (G₂ (F.F-seq (f ⋆ g) h) 
        ∙ G₂ (F.F-seq f g ▹ F₁ h)) 
      ∙ G-seq (F₁ f ⋆ F₁ g) (F₁ h)
      ∙ G-seq (F₁ f) (F₁ g) ▹ G₁ (F₁ h)
    ≡⟨ cong (_∙ G-seq (F₁ f ⋆ F₁ g) (F₁ h)
          ∙ G-seq (F₁ f) (F₁ g) ▹ G₁ (F₁ h)) 
        (sym (G₂-funct _ _)) ⟩
      G₂ (F.F-seq (f ⋆ g) h 
        ∙ F.F-seq f g ▹ F₁ h) 
      ∙ G-seq (F₁ f ⋆ F₁ g) (F₁ h)
      ∙ G-seq (F₁ f) (F₁ g) ▹ G₁ (F₁ h)
    ≡⟨ cong (λ x → G₂ x ∙ G-seq (F₁ f ⋆ F₁ g) (F₁ h)
          ∙ G-seq (F₁ f) (F₁ g) ▹ G₁ (F₁ h)) 
        (F.F-Assoc _ _ _) ⟩
      G₂ (refl ∙ F.F-seq f (g ⋆ h)
          ∙ F₁ f ◃ F.F-seq g h) 
      ∙ G-seq (F₁ f ⋆ F₁ g) (F₁ h)
      ∙ G-seq (F₁ f) (F₁ g) ▹ G₁ (F₁ h)
    ≡⟨ cong (_∙ G-seq (F₁ f ⋆ F₁ g) (F₁ h)
          ∙ G-seq (F₁ f) (F₁ g) ▹ G₁ (F₁ h)) 
        (G₂-funct _ _) ⟩
      (refl ∙ G₂ (F.F-seq f (g ⋆ h)
          ∙ F₁ f ◃ F.F-seq g h)) 
      ∙ G-seq (F₁ f ⋆ F₁ g) (F₁ h)
      ∙ G-seq (F₁ f) (F₁ g) ▹ G₁ (F₁ h)
    ≡⟨ sym assoc-inf ⟩
      refl ∙ (G₂ (F.F-seq f (g ⋆ h)
        ∙ F₁ f ◃ F.F-seq g h)) 
      ∙ G-seq (F₁ f ⋆ F₁ g) (F₁ h)
      ∙ G-seq (F₁ f) (F₁ g) ▹ G₁ (F₁ h)
    ≡⟨ cong (λ x → refl ∙ (G₂ (F.F-seq f (g ⋆ h)
          ∙ F₁ f ◃ F.F-seq g h)) ∙ x) 
        (G-Assoc _ _ _) ⟩
      refl ∙ (G₂ (F.F-seq f (g ⋆ h)
        ∙ F₁ f ◃ F.F-seq g h)) 
      ∙ refl
      ∙ G-seq (F₁ f) (F₁ g ⋆ F₁ h)
      ∙ G₁ (F₁ f) ◃ G-seq (F₁ g) (F₁ h)
    ≡⟨ cong (λ x → refl ∙ (G₂ (F.F-seq f (g ⋆ h)
          ∙ F₁ f ◃ F.F-seq g h)) ∙ x) 
        (sym (lUnit _)) ⟩
      refl ∙ (G₂ (F.F-seq f (g ⋆ h)
        ∙ F₁ f ◃ F.F-seq g h)) 
      ∙ G-seq (F₁ f) (F₁ g ⋆ F₁ h)
      ∙ G₁ (F₁ f) ◃ G-seq (F₁ g) (F₁ h)
    ≡⟨ cong (λ x → refl ∙ x 
          ∙ G-seq (F₁ f) (F₁ g ⋆ F₁ h)
          ∙ G₁ (F₁ f) ◃ G-seq (F₁ g) (F₁ h))
        (G₂-funct _ _) ⟩
      refl ∙ (G₂ (F.F-seq f (g ⋆ h))
        ∙ G₂ (F₁ f ◃ F.F-seq g h)) 
      ∙ G-seq (F₁ f) (F₁ g ⋆ F₁ h)
      ∙ G₁ (F₁ f) ◃ G-seq (F₁ g) (F₁ h)
    ≡⟨ cong (refl ∙_) (sym assoc-inf) ⟩
      refl 
      ∙ G₂ (F.F-seq f (g ⋆ h))
      ∙ G₂ (F₁ f ◃ F.F-seq g h) 
      ∙ G-seq (F₁ f) (F₁ g ⋆ F₁ h)
      ∙ G₁ (F₁ f) ◃ G-seq (F₁ g) (F₁ h)
    ≡⟨ cong (λ x → refl ∙ G₂ (F.F-seq f (g ⋆ h)) ∙ x) 
        assoc-inf ⟩
      refl 
      ∙ G₂ (F.F-seq f (g ⋆ h))
      ∙ (G₂ (F₁ f ◃ F.F-seq g h) 
        ∙ G-seq (F₁ f) (F₁ g ⋆ F₁ h))
      ∙ G₁ (F₁ f) ◃ G-seq (F₁ g) (F₁ h)
    ≡⟨ cong (λ x → refl ∙ G₂ (F.F-seq f (g ⋆ h)) 
          ∙ x ∙ G₁ (F₁ f) ◃ G-seq (F₁ g) (F₁ h)) 
        (sym (G-seq-nat refl (F.F-seq g h))) ⟩
      refl 
      ∙ G₂ (F.F-seq f (g ⋆ h))
      ∙ (G-seq (F₁ f) (F₁ (g ⋆ h))
        ∙ G₁ (F₁ f) ◃ G₂ (F.F-seq g h))
      ∙ G₁ (F₁ f) ◃ G-seq (F₁ g) (F₁ h)
    ≡⟨ cong (λ x → refl ∙ G₂ (F.F-seq f (g ⋆ h)) ∙ x) 
        (sym assoc-inf) ⟩
      refl 
      ∙ G₂ (F.F-seq f (g ⋆ h))
      ∙ G-seq (F₁ f) (F₁ (g ⋆ h))
      ∙ G₁ (F₁ f) ◃ G₂ (F.F-seq g h)
      ∙ G₁ (F₁ f) ◃ G-seq (F₁ g) (F₁ h)
    ≡⟨ cong (refl ∙_) assoc-inf ⟩
      refl 
      ∙ (G₂ (F.F-seq f (g ⋆ h))
        ∙ G-seq (F₁ f) (F₁ (g ⋆ h)))
      ∙ G₁ (F₁ f) ◃ G₂ (F.F-seq g h)
      ∙ G₁ (F₁ f) ◃ G-seq (F₁ g) (F₁ h)
    ≡⟨ cong (λ x → refl ∙ (G₂ (F.F-seq f (g ⋆ h))
          ∙ G-seq (F₁ f) (F₁ (g ⋆ h))) ∙ x) 
        (sym (◃-∙ _ _)) ⟩
      refl 
      ∙ (G₂ (F.F-seq f (g ⋆ h)) 
        ∙ G-seq (F₁ f) (F₁ (g ⋆ h))) 
      ∙ G₁ (F₁ f) ◃ (G₂ (F.F-seq g h) 
        ∙ G-seq (F₁ g) (F₁ h))
    ∎

module _ {F G H K : GpdEndo}
  (α : 2NatTrans F H)
  (β : 2NatTrans G K) where
  open import Prelude

  private module F = Copresheaf F
  private module G = Copresheaf G
  private module H = Copresheaf H
  private module K = Copresheaf K

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
  open K using ()
    renaming (
      F₀ to    K₀;
      F₁ to    K₁;
      F₂ to    K₂;
      F-id to  K-id;
      F-seq to K-seq
    )
  
  open WildNatTrans (α .fst) using ()
    renaming (N-ob to α₀; N-hom to α□)
  open WildNatTrans (β .fst) using ()
    renaming (N-ob to β₀; N-hom to β□)

  private _⊗₀_ = compEndo₀

  open WildNatTrans
  open Is2NatTrans

  α▹G : 2NatTrans (F ⊗₀ G) (H ⊗₀ G)
  α▹G .fst .N-ob x = G₁ (α₀ x)
  α▹G .fst .N-hom {x} {y} f = 
    sym (G-seq (F₁ f) (α₀ y)) 
    ∙ G₂ (α□ f) 
    ∙ G-seq (α₀ x) (H₁ f)
  α▹G .snd .N-hom-id {X} = goal
    where
    sq₁ : G₂ (α□ id ∙ α₀ X ◃ H-id) 
          ≡ G₂ (F.F-id ▹ α₀ X)
    sq₁ = cong G₂ (α .snd .N-hom-id)
    sq₂ : G₂ (α□ id) 
          ∙ G-seq (α₀ X) (H₁ id)
          ∙ G₁ (α₀ X) ◃ G₂ H-id 
          ∙ sym (G-seq (α₀ X) id)
          ≡ G-seq (F₁ id) (α₀ X)
          ∙ G₂ F.F-id ▹ G₁ (α₀ X)
          ∙ sym (G-seq id (α₀ X))
    sq₂ = ∙l (sym (G.F₂-◃ H-id))
      ∙ sym (G.F₂-funct _ _)
      ∙ sq₁
      ∙ G.F₂-▹ F.F-id
    sq₃ : G₂ (α□ id) 
          ∙ G-seq (α₀ X) (H₁ id)
          ∙ G₁ (α₀ X) ◃ G₂ H-id 
          ∙ G₁ (α₀ X) ◃ G-id
          ≡ (G-seq (F₁ id) (α₀ X))
          ∙ G₂ F.F-id ▹ G₁ (α₀ X)
          ∙ G-id ▹ G₁ (α₀ X)
    sq₃ = 
      ∙l ∙l ∙l sym (invUniq (G.F-IdR (α₀ X)))
      ∙ sq₂ 
      ∙ ∙l ∙l invUniq (G.F-IdL (α₀ X)) 
    sq₄ : G₂ (α□ id) 
          ∙ G-seq (α₀ X) (H₁ id)
          ∙ G₁ (α₀ X) ◃ (G₂ H-id ∙ G-id)
          ≡ G-seq (F₁ id) (α₀ X)
          ∙ (G₂ F.F-id ∙ G-id) ▹ G₁ (α₀ X)
    sq₄ = 
      ∙l ∙l ◃-∙ (G₂ H-id) G-id
      ∙ sq₃
      ∙ ∙l sym (▹-∙ _ G-id) 
    goal : (sym (G-seq (F₁ id) (α₀ X))
             ∙ G₂ (α□ id) 
             ∙ G-seq (α₀ X) (H₁ id))
           ∙ G₁ (α₀ X) ◃ (G₂ H-id ∙ G-id)
           ≡ (G₂ F.F-id ∙ G-id) ▹ G₁ (α₀ X)
    goal =
      sym assoc-inf
      ∙ ∙l sym assoc-inf
      ∙ shuffleSymL sq₄
  α▹G .snd .N-hom-seq {X} {Y} {Z} f g = goal
    where
    open import Prelude.Reassoc
    sq₁ : G₂ (α□ (f » g) 
            ∙ α₀ X ◃ H-seq f g) 
          ≡ G₂ (F.F-seq f g ▹ α₀ Z 
            ∙ F₁ f ◃ α□ g 
            ∙ α□ f ▹ H₁ g)
    sq₁ = cong G₂ (α .snd .N-hom-seq f g)
    sq₂ : G₂ (α□ (f » g)) 
          ∙ G₂ (α₀ X ◃ H-seq f g) 
          ≡ G₂ (F.F-seq f g ▹ α₀ Z) 
          ∙ G₂ (F₁ f ◃ α□ g) 
          ∙ G₂ (α□ f ▹ H₁ g)
    sq₂ = sym (G.F₂-funct _ _)
      ∙ sq₁
      ∙ G.F₂-funct _ _
      ∙ ∙l (G.F₂-funct _ _)
    sq₃ : G₂ (α□ (f » g)) 
          ∙ G-seq (α₀ X) (H₁ (f » g))
          ∙ G₁ (α₀ X) ◃ G₂ (H-seq f g)
          ∙ sym (G-seq (α₀ X) (H₁ f » H₁ g))
          ≡ (G-seq (F₁ (f » g)) (α₀ Z)
            ∙ G₂ (F.F-seq f g) ▹ G₁ (α₀ Z) 
            ∙ sym (G-seq (F₁ f » F₁ g) (α₀ Z)))
          ∙ (G-seq (F₁ f) (F₁ g » α₀ Z)
            ∙ G₁ (F₁ f) ◃ G₂ (α□ g)
            ∙ sym (G-seq (F₁ f) (α₀ Y » H₁ g)))
          ∙ G-seq (F₁ f » α₀ Y) (H₁ g)
          ∙ G₂ (α□ f) ▹ G₁ (H₁ g) 
          ∙ sym (G-seq (α₀ X » H₁ f) (H₁ g))
    sq₃ = ∙l sym (G.F₂-◃ (H-seq f g))
      ∙ sq₂
      ∙ cong₂ _∙_
        (G.F₂-▹ (F.F-seq f g))
        (cong₂ _∙_
          (G.F₂-◃ (α□ g))
          (G.F₂-▹ (α□ f)))
    sq₄ = ∙l ∙l ∙l aux₁
      ∙ sq₃
      ∙ ∙r ∙l ∙l {! !}
      ∙ ∙l ∙r ∙l ∙l {! !}
      ∙ ∙l ∙l ∙l ∙l {! !}
      ∙ {! !}
      ∙ {! !}
      where
      aux₁₀ = sym $ cong sym $ shuffleSymR $ sym $ 
        G.F-Assoc (α₀ X) (H₁ f) (H₁ g) ∙ sym (lUnit _)
      aux₁ = ∙l sym (symDistr _ _) ∙ sym (symDistr _ _) ∙ aux₁₀
      
    goal : (sym (G-seq (F₁ (f » g)) (α₀ Z)) 
             ∙ G₂ (α□ (f » g)) 
             ∙ G-seq (α₀ X) (H₁ (f » g)))
           ∙ G₁ (α₀ X) ◃ (G₂ (H-seq f g) 
             ∙ G-seq (H₁ f) (H₁ g))
           ≡ (G₂ (F.F-seq f g) 
             ∙ G-seq (F₁ f) (F₁ g)) ▹ G₁ (α₀ Z)
           ∙ G₁ (F₁ f) ◃ (sym (G-seq (F₁ g) (α₀ Z)) 
             ∙ G₂ (α□ g) 
             ∙ G-seq (α₀ Y) (H₁ g))
           ∙ (sym (G-seq (F₁ f) (α₀ Y)) 
             ∙ G₂ (α□ f) 
             ∙ G-seq (α₀ X) (H₁ f)) ▹ G₁ (H₁ g)
    goal = {! !}

  H◃β : 2NatTrans (H ⊗₀ G) (H ⊗₀ K)
  H◃β = {! !}

  compEndo₁ : 2NatTrans (F ⊗₀ G) (H ⊗₀ K)
  compEndo₁ = α▹G ⋆ᵉ H◃β
    where 
    open Bicategory (CopshBicat GPD) using ()
      renaming (_⋆_ to _⋆ᵉ_)

compEndo : WildFunctor 
  (ProdCat GpdEndoWildCat GpdEndoWildCat) GpdEndoWildCat
compEndo .F-ob = uncurry compEndo₀
compEndo .F-hom {x = F , G} {y = H , K} = uncurry compEndo₁
compEndo .F-id = {! !}
compEndo .F-seq = {! !}
