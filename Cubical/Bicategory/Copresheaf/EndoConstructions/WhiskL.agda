open import Cubical.Foundations.Prelude

open import Cubical.Foundations.Function
open import Cubical.Foundations.GroupoidLaws
open import Prelude.ExtraGpdLaws

open import Cubical.WildCat.Functor hiding (_$_)
open import Cubical.WildCat.Product renaming (_×_ to ProdCat)

module Cubical.Bicategory.Copresheaf.EndoConstructions.WhiskL
  (ℓ : Level) where

open import Cubical.Bicategory.Base
open import Cubical.Bicategory.Copresheaf ℓ 
  using (Copresheaf; GPD; Is2Copresheaf; 2NatTrans; Is2NatTrans)
open import Cubical.Bicategory.Instances.Copresheaf ℓ
open import Cubical.Bicategory.Copresheaf.EndoConstructions.Base ℓ 
open import Cubical.Bicategory.Copresheaf.EndoConstructions.Composite ℓ
import Cubical.Bicategory.Functor as PF

open Copresheaf using (str; is2Copresheaf)
open WildFunctor
open Is2Copresheaf

open Bicategory GPD renaming (str to ⟨GPD⟩; Hom[_,_] to GPD[_,_])
open 2CellLaws ⟨GPD⟩

module _ (F : GpdEndo) {G H : GpdEndo}
  (α : 2NatTrans G H) where
  open import Prelude

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
  open Is2NatTrans

  whiskL-pseudonat : 2NatTrans (F ⊗₀ G) (F ⊗₀ H)
  whiskL-pseudonat .fst .N-ob x = α₀ (F₀ x)
  whiskL-pseudonat .fst .N-hom f = α□ (F₁ f)
  whiskL-pseudonat .snd .N-hom-id {X} = goal
    where
    sq₁ :
      α□ id 
      ∙ α₀ (F₀ X) ◃ H-id 
      ≡ G-id ▹ α₀ (F₀ X)
    sq₁ = α .snd .N-hom-id {X = F₀ X}
    goal = 
        α□ (F₁ id) 
        ∙ α₀ (F₀ X) ◃ (H₂ F.F-id ∙ H-id)
      ≡⟨ ∙l ◃-∙ (H₂ F.F-id) H-id ⟩ 
        α□ (F₁ id) 
        ∙ α₀ (F₀ X) ◃ H₂ F.F-id 
        ∙ α₀ (F₀ X) ◃ H-id
      ≡⟨ assoc-inf ⟩ 
        (α□ (F₁ id) 
          ∙ α₀ (F₀ X) ◃ H₂ F.F-id)
        ∙ α₀ (F₀ X) ◃ H-id
      ≡⟨ ∙r PF.N-hom-nat (α .fst) F.F-id ⟩ 
        (G₂ (F.F-id) ▹ α₀ (F₀ X)
          ∙ α□ id)
        ∙ α₀ (F₀ X) ◃ H-id
      ≡⟨ sym assoc-inf ⟩ 
        G₂ (F.F-id) ▹ α₀ (F₀ X)
        ∙ α□ id
        ∙ α₀ (F₀ X) ◃ H-id
      ≡⟨ ∙l sq₁ ⟩ 
        (G₂ F.F-id) ▹ α₀ (F₀ X) 
        ∙ G-id ▹ α₀ (F₀ X)
      ≡⟨ sym (▹-∙ (G₂ F.F-id) G-id) ⟩ 
        (G₂ F.F-id ∙ G-id) ▹ α₀ (F₀ X)
      ∎
  whiskL-pseudonat .snd .N-hom-seq {X} {Y} {Z} f g = goal
    where
    sq₁ :
      α□ (F₁ f » F₁ g) 
      ∙ α₀ (F₀ X) ◃ H-seq (F₁ f) (F₁ g) 
      ≡ G-seq (F₁ f) (F₁ g) ▹ α₀ (F₀ Z) 
      ∙ G₁ (F₁ f) ◃ α□ (F₁ g) 
      ∙ α□ (F₁ f) ▹ H₁ (F₁ g)
    sq₁ = α .snd .N-hom-seq (F₁ f) (F₁ g)
    goal =
        α□ (F₁ (f » g))
        ∙ α₀ (F₀ X) ◃ (H₂ (F.F-seq f g) 
          ∙ H-seq (F₁ f) (F₁ g))
      ≡⟨ ∙l (◃-∙ _ _) ⟩
        α□ (F₁ (f » g))
        ∙ α₀ (F₀ X) ◃ H₂ (F.F-seq f g) 
        ∙ α₀ (F₀ X) ◃ H-seq (F₁ f) (F₁ g)
      ≡⟨ assoc-inf ⟩
        (α□ (F₁ (f » g))
          ∙ α₀ (F₀ X) ◃ H₂ (F.F-seq f g)) 
        ∙ α₀ (F₀ X) ◃ H-seq (F₁ f) (F₁ g)
      ≡⟨ ∙r PF.N-hom-nat (α .fst) (F.F-seq f g) ⟩
        (G₂ (F.F-seq f g) ▹ α₀ (F₀ Z)
          ∙ α□ (F₁ f » F₁ g))
        ∙ α₀ (F₀ X) ◃ H-seq (F₁ f) (F₁ g)
      ≡⟨ sym assoc-inf ⟩
        G₂ (F.F-seq f g) ▹ α₀ (F₀ Z)
        ∙ α□ (F₁ f » F₁ g)
        ∙ α₀ (F₀ X) ◃ H-seq (F₁ f) (F₁ g)
      ≡⟨ ∙l sq₁ ⟩
        G₂ (F.F-seq f g) ▹ α₀ (F₀ Z) 
        ∙ G-seq (F₁ f) (F₁ g) ▹ α₀ (F₀ Z)
        ∙ G₁ (F₁ f) ◃ α□ (F₁ g)
        ∙ α□ (F₁ f) ▹ H₁ (F₁ g)
      ≡⟨ assoc-inf ⟩
        (G₂ (F.F-seq f g) ▹ α₀ (F₀ Z) 
          ∙ G-seq (F₁ f) (F₁ g) ▹ α₀ (F₀ Z))
        ∙ G₁ (F₁ f) ◃ α□ (F₁ g)
        ∙ α□ (F₁ f) ▹ H₁ (F₁ g)
      ≡⟨ ∙r sym (▹-∙ _ _) ⟩
        (G₂ (F.F-seq f g) 
          ∙ G-seq (F₁ f) (F₁ g)) ▹ α₀ (F₀ Z)
        ∙ G₁ (F₁ f) ◃ α□ (F₁ g)
        ∙ α□ (F₁ f) ▹ H₁ (F₁ g)
      ∎


