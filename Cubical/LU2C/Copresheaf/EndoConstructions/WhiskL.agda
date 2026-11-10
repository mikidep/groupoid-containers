open import Cubical.Foundations.Prelude

open import Cubical.Foundations.Function
open import Cubical.Foundations.GroupoidLaws
open import Prelude.ExtraGpdLaws

open import Cubical.WildCat.Functor hiding (_$_)
open import Cubical.WildCat.Product renaming (_×_ to ProdCat)

module Cubical.LU2C.Copresheaf.EndoConstructions.WhiskL
  (ℓ : Level) where

open import Cubical.LU2C.Base
open import Cubical.LU2C.Instances.Groupoids ℓ
open import Cubical.LU2C.Copresheaf ℓ
open import Cubical.LU2C.Instances.Copresheaf ℓ
open import Cubical.LU2C.Copresheaf.EndoConstructions.Base ℓ
open import Cubical.LU2C.Copresheaf.EndoConstructions.Composite ℓ

open import Cubical.WildCat.AsLU2C.Instances
open import Cubical.WildCat.AsLU2C.NaturalTransformation.Properties

open WildFunctor
open Is2Copresheaf

open NotHGpd
open import Reflection.Reassoc

module _ (F : GpdEndo) {G H : GpdEndo}
  (α : PseudonatTrans G H) where

  private module F = Not2P F
  private module G = Not2P G
  private module H = Not2P H

  open F using (F₀; F₁; F₂)
  open G using () renaming 
    ( F₀ to  G₀
    ; F₁ to  G₁
    ; F₂ to  G₂
    )
  open H using () renaming 
    ( F₀ to  H₀
    ; F₁ to  H₁
    ; F₂ to  H₂
    )

  open WildNatTrans (α .fst) using ()
    renaming (N-ob to α₀; N-hom to α□)

  private _⨾₀_ = compEndo₀

  open WildNatTrans
  open IsPseudonat

  whiskL-pseudonat : PseudonatTrans (F ⨾₀ G) (F ⨾₀ H)
  whiskL-pseudonat .fst .N-ob x = α₀ (F₀ x)
  whiskL-pseudonat .fst .N-hom f = α□ (F₁ f)
  whiskL-pseudonat .snd .N-hom-id {X} = goal
    where abstract
    sq₁ :
      α□ id
      ∙ α₀ (F₀ X) ◃ H.F-id
      ≡ G.F-id ▹ α₀ (F₀ X)
    sq₁ = α .snd .N-hom-id {X = F₀ X}
    goal :
      α□ (F₁ id)
      ∙ α₀ (F₀ X) ◃ (H₂ F.F-id ∙ H.F-id)
      ≡ (G₂ F.F-id ∙ G.F-id) ▹ α₀ (F₀ X)
    goal =
        α□ (F₁ id)
        ∙ α₀ (F₀ X) ◃ (H₂ F.F-id ∙ H.F-id)
      -- ≡⟨ reass₁ ⟩
      ≡⟨ reassoc! ⟩
        (α□ (F₁ id)
          ∙ α₀ (F₀ X) ◃ H₂ F.F-id)
        ∙ α₀ (F₀ X) ◃ H.F-id
      ≡⟨ ∙r N-hom-nat (α .fst) F.F-id ⟩
        (G₂ (F.F-id) ▹ α₀ (F₀ X)
          ∙ α□ id)
        ∙ α₀ (F₀ X) ◃ H.F-id
      ≡⟨ sym assoc-inf ⟩
        G₂ (F.F-id) ▹ α₀ (F₀ X)
        ∙ α□ id
        ∙ α₀ (F₀ X) ◃ H.F-id
      ≡⟨ ∙l sq₁ ⟩
        (G₂ F.F-id) ▹ α₀ (F₀ X)
        ∙ G.F-id ▹ α₀ (F₀ X)
      ≡⟨ sym (▹-∙ (G₂ F.F-id) G.F-id) ⟩
        (G₂ F.F-id ∙ G.F-id) ▹ α₀ (F₀ X)
      ∎
      -- where
      -- reass₁ = reassoc
      --   (↑ α□ (F₁ id)
      --     ∙′ α₀ (F₀ X) ◃′ (↑ H₂ F.F-id ∙′ ↑ H.F-id))
      --   ((↑ α□ (F₁ id)
      --       ∙′ α₀ (F₀ X) ◃′ ↑ H₂ F.F-id)
      --     ∙′ α₀ (F₀ X) ◃′ ↑ H.F-id)
      --   refl
  whiskL-pseudonat .snd .N-hom-seq {X} {Y} {Z} f g = goal
    -- TODO: reassoc
    where abstract
    sq₁ :
      α□ (F₁ f » F₁ g)
      ∙ α₀ (F₀ X) ◃ H.F-seq (F₁ f) (F₁ g)
      ≡ G.F-seq (F₁ f) (F₁ g) ▹ α₀ (F₀ Z)
      ∙ G₁ (F₁ f) ◃ α□ (F₁ g)
      ∙ α□ (F₁ f) ▹ H₁ (F₁ g)
    sq₁ = α .snd .N-hom-seq (F₁ f) (F₁ g)
    goal :
      α□ (F₁ (f » g))
      ∙ α₀ (F₀ X) ◃ (H₂ (F.F-seq f g)
        ∙ H.F-seq (F₁ f) (F₁ g))
      ≡ (G₂ (F.F-seq f g)
        ∙ G.F-seq (F₁ f) (F₁ g)) ▹ α₀ (F₀ Z)
      ∙ G₁ (F₁ f) ◃ α□ (F₁ g)
      ∙ α□ (F₁ f) ▹ H₁ (F₁ g)
    goal =
        α□ (F₁ (f » g))
        ∙ α₀ (F₀ X) ◃ (H₂ (F.F-seq f g)
          ∙ H.F-seq (F₁ f) (F₁ g))
      ≡⟨ reassoc! ⟩
      -- ≡⟨ ∙l (◃-∙ _ _) ⟩
      --   α□ (F₁ (f » g))
      --   ∙ α₀ (F₀ X) ◃ H₂ (F.F-seq f g)
      --   ∙ α₀ (F₀ X) ◃ H.F-seq (F₁ f) (F₁ g)
      -- ≡⟨ assoc-inf ⟩
        (α□ (F₁ (f » g))
          ∙ α₀ (F₀ X) ◃ H₂ (F.F-seq f g))
        ∙ α₀ (F₀ X) ◃ H.F-seq (F₁ f) (F₁ g)
      ≡⟨ ∙r N-hom-nat (α .fst) (F.F-seq f g) ⟩
        (G₂ (F.F-seq f g) ▹ α₀ (F₀ Z)
          ∙ α□ (F₁ f » F₁ g))
        ∙ α₀ (F₀ X) ◃ H.F-seq (F₁ f) (F₁ g)
      ≡⟨ sym assoc-inf ⟩
        G₂ (F.F-seq f g) ▹ α₀ (F₀ Z)
        ∙ α□ (F₁ f » F₁ g)
        ∙ α₀ (F₀ X) ◃ H.F-seq (F₁ f) (F₁ g)
      ≡⟨ ∙l sq₁ ⟩
        G₂ (F.F-seq f g) ▹ α₀ (F₀ Z)
        ∙ G.F-seq (F₁ f) (F₁ g) ▹ α₀ (F₀ Z)
        ∙ G₁ (F₁ f) ◃ α□ (F₁ g)
        ∙ α□ (F₁ f) ▹ H₁ (F₁ g)
      ≡⟨ reassoc! ⟩
      -- ≡⟨ assoc-inf ⟩
      --   (G₂ (F.F-seq f g) ▹ α₀ (F₀ Z)
      --     ∙ G.F-seq (F₁ f) (F₁ g) ▹ α₀ (F₀ Z))
      --   ∙ G₁ (F₁ f) ◃ α□ (F₁ g)
      --   ∙ α□ (F₁ f) ▹ H₁ (F₁ g)
      -- ≡⟨ ∙r sym (▹-∙ _ _) ⟩
        (G₂ (F.F-seq f g)
          ∙ G.F-seq (F₁ f) (F₁ g)) ▹ α₀ (F₀ Z)
        ∙ G₁ (F₁ f) ◃ α□ (F₁ g)
        ∙ α□ (F₁ f) ▹ H₁ (F₁ g)
      ∎
