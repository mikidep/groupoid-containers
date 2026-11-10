open import Cubical.Foundations.Prelude

open import Cubical.Foundations.Function
open import Cubical.Foundations.GroupoidLaws
open import Prelude.ExtraGpdLaws

open import Cubical.WildCat.Functor hiding (_$_)
open import Cubical.WildCat.Product renaming (_×_ to ProdCat)

module Cubical.LU2C.Copresheaf.EndoConstructions.Composite
  (ℓ : Level) where

open import Cubical.LU2C.Base
open import Cubical.LU2C.Copresheaf ℓ
open import Cubical.LU2C.Instances.Groupoids ℓ
open import Cubical.LU2C.Copresheaf.EndoConstructions.Base ℓ

open import Cubical.WildCat.AsLU2C.Instances

open WildFunctor
open Is2Copresheaf

-- open LU2C HGpd using () renaming (str to ⟨HGpd⟩)
open import Cubical.WildCat.Instances.Types
open NotHGpd

module _ (F G : GpdEndo) where
  open import Prelude.Utils
  open import Reflection.Reassoc

  private module F = Not2P F
  open F using (F₀; F₁; F₂)
  private module G = Not2P G
  open G using ()
    renaming (
      F₀ to    G₀;
      F₁ to    G₁;
      F₂ to    G₂;
      F₂′ to G₂′
    )
  compEndo₀ : GpdEndo
  compEndo₀ .fst .F-ob = F₀ » G₀
  compEndo₀ .fst .F-hom = F₁ » G₁
  compEndo₀ .fst .F-id = G₂ F.F-id ∙ G.F-id
  compEndo₀ .fst .F-seq f g = G₂ (F.F-seq f g) ∙ G.F-seq (F₁ f) (F₁ g)
  compEndo₀ .snd .F-IdL f =
      (G₂ (F.F-seq id f) ∙ G.F-seq (F₁ id) (F₁ f))
      ∙ (G₂ F.F-id ∙ G.F-id) ▹ G₁ (F₁ f)
    ≡⟨ reassoc! ⟩
      G₂ (F.F-seq id f)
      ∙ (G.F-seq (F₁ id) (F₁ f) ∙ G₂ F.F-id ▹ G₁ (F₁ f))
      ∙ G.F-id ▹ G₁ (F₁ f)
    ≡⟨ ∙l ∙r G.F-seq-nat F.F-id refl ⟩
      G₂ (F.F-seq id f)
      ∙ (G₂ (F.F-id ▹ F₁ f) ∙ G.F-seq id (F₁ f))
      ∙ G.F-id ▹ G₁ (F₁ f)
    ≡⟨ reassoc! ⟩
      (G₂ (F.F-seq id f ∙ F.F-id ▹ F₁ f)
        ∙ G.F-seq id (F₁ f))
      ∙ G.F-id ▹ G₁ (F₁ f)
    ≡⟨ ∙r ∙r cong G₂ (F.F-IdL f) ⟩
      (refl ∙ G.F-seq id (F₁ f))
      ∙ G.F-id ▹ G₁ (F₁ f)
    ≡⟨ reassoc! ⟩
      G.F-seq id (F₁ f) ∙ G.F-id ▹ G₁ (F₁ f)
    ≡⟨ G.F-IdL (F₁ f) ⟩
      refl
    ∎
  compEndo₀ .snd .F-IdR f =
      (G₂ (F.F-seq f id) ∙ G.F-seq (F₁ f) (F₁ id))
      ∙ G₁ (F₁ f) ◃ (G₂ F.F-id ∙ G.F-id)
    ≡⟨ reassoc! ⟩
      (G₂ (F.F-seq f id)
        ∙ G.F-seq (F₁ f) (F₁ id)
        ∙ G₁ (F₁ f) ◃ G₂ F.F-id)
      ∙ G₁ (F₁ f) ◃ G.F-id
    ≡⟨ ∙r ∙l G.F-seq-nat refl F.F-id ⟩
      (G₂ (F.F-seq f id)
        ∙ G₂ (F₁ f ◃ F.F-id)
        ∙ G.F-seq (F₁ f) id)
      ∙ G₁ (F₁ f) ◃ G.F-id
    ≡⟨ reassoc! ⟩
      ((G₂ (F.F-seq f id ∙ F₁ f ◃ F.F-id))
        ∙ G.F-seq (F₁ f) id)
      ∙ G₁ (F₁ f) ◃ G.F-id
    ≡⟨ ∙r ∙r cong G₂ (F.F-IdR f) ⟩
      (refl ∙ G.F-seq (F₁ f) id) ∙ G₁ (F₁ f) ◃ G.F-id
    -- ≡⟨ sym assoc-inf ⟩
    --   refl ∙ G.F-seq (F₁ f) id ∙ G₁ (F₁ f) ◃ G.F-id
    -- ≡⟨ sym (lUnit _) ⟩
    ≡⟨ reassoc! ⟩
      G.F-seq (F₁ f) id ∙ G₁ (F₁ f) ◃ G.F-id
    ≡⟨ G.F-IdR (F₁ f) ⟩
      refl
    ∎
  compEndo₀ .snd .F-Assoc f g h =
      (G₂ (F.F-seq (f ⋆ g) h)
        ∙ G.F-seq (F₁ (f ⋆ g)) (F₁ h))
      ∙ (G₂ (F.F-seq f g)
        ∙ G.F-seq (F₁ f) (F₁ g)) ▹ G₁ (F₁ h)
    ≡⟨ reassoc! ⟩
      G₂ (F.F-seq (f ⋆ g) h)
      ∙ (G.F-seq (F₁ (f ⋆ g)) (F₁ h)
        ∙ G₂ (F.F-seq f g) ▹ G₁ (F₁ h))
      ∙ G.F-seq (F₁ f) (F₁ g) ▹ G₁ (F₁ h)
    ≡⟨ ∙l ∙r G.F-seq-nat _ refl ⟩
      G₂ (F.F-seq (f ⋆ g) h)
      ∙ (G₂ (F.F-seq f g ▹ F₁ h)
        ∙ G.F-seq (F₁ f ⋆ F₁ g) (F₁ h))
      ∙ G.F-seq (F₁ f) (F₁ g) ▹ G₁ (F₁ h)
    ≡⟨ reassoc! ⟩
      G₂ (F.F-seq (f ⋆ g) h
        ∙ F.F-seq f g ▹ F₁ h)
      ∙ G.F-seq (F₁ f ⋆ F₁ g) (F₁ h)
      ∙ G.F-seq (F₁ f) (F₁ g) ▹ G₁ (F₁ h)
    ≡⟨ ∙r cong G₂ (F.F-Assoc _ _ _) ⟩
      G₂ (refl ∙ F.F-seq f (g ⋆ h)
          ∙ F₁ f ◃ F.F-seq g h)
      ∙ G.F-seq (F₁ f ⋆ F₁ g) (F₁ h)
      ∙ G.F-seq (F₁ f) (F₁ g) ▹ G₁ (F₁ h)
    ≡⟨ reassoc! ⟩
      refl ∙ (G₂ (F.F-seq f (g ⋆ h)
        ∙ F₁ f ◃ F.F-seq g h))
      ∙ G.F-seq (F₁ f ⋆ F₁ g) (F₁ h)
      ∙ G.F-seq (F₁ f) (F₁ g) ▹ G₁ (F₁ h)
    ≡⟨ ∙l ∙l G.F-Assoc _ _ _ ⟩
      refl ∙ (G₂ (F.F-seq f (g ⋆ h)
        ∙ F₁ f ◃ F.F-seq g h))
      ∙ refl
      ∙ G.F-seq (F₁ f) (F₁ g ⋆ F₁ h)
      ∙ G₁ (F₁ f) ◃ G.F-seq (F₁ g) (F₁ h)
    ≡⟨ reassoc! ⟩
      refl
      ∙ G₂ (F.F-seq f (g ⋆ h))
      ∙ (G₂ (F₁ f ◃ F.F-seq g h)
        ∙ G.F-seq (F₁ f) (F₁ g ⋆ F₁ h))
      ∙ G₁ (F₁ f) ◃ G.F-seq (F₁ g) (F₁ h)
    ≡⟨ ∙l ∙l ∙r sym (G.F-seq-nat refl (F.F-seq g h)) ⟩
      refl
      ∙ G₂ (F.F-seq f (g ⋆ h))
      ∙ (G.F-seq (F₁ f) (F₁ (g ⋆ h))
        ∙ G₁ (F₁ f) ◃ G₂ (F.F-seq g h))
      ∙ G₁ (F₁ f) ◃ G.F-seq (F₁ g) (F₁ h)
    ≡⟨ reassoc! ⟩
      refl
      ∙ (G₂ (F.F-seq f (g ⋆ h))
        ∙ G.F-seq (F₁ f) (F₁ (g ⋆ h)))
      ∙ G₁ (F₁ f) ◃ (G₂ (F.F-seq g h)
        ∙ G.F-seq (F₁ g) (F₁ h))
    ∎
