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

open Bicategory GPD renaming (str to ⟨GPD⟩; Hom[_,_] to GPD[_,_])
open 2CellLaws ⟨GPD⟩

module _ {F H : GpdEndo} (α : PseudonatTrans F H)
  (G : GpdEndo) where

  open import Prelude

  private module F = Copresheaf F
  private module G = Copresheaf G
  private module H = Copresheaf H

  open F using (F₀; F₁; F₂)
  open G using ()
    renaming (
      F₀ to    G₀;
      F₁ to    G₁;
      F₂ to    G₂
    )
  open H using ()
    renaming (
      F₀ to    H₀;
      F₁ to    H₁;
      F₂ to    H₂
    )
  
  open WildNatTrans (α .fst) using ()
    renaming (N-ob to α₀; N-hom to α□)

  private _⊗₀_ = compEndo₀

  open WildNatTrans
  open IsPseudonat

  whiskR-pseudonat : PseudonatTrans (F ⊗₀ G) (H ⊗₀ G)
  whiskR-pseudonat .fst .N-ob x = G₁ (α₀ x)
  whiskR-pseudonat .fst .N-hom {x} {y} f = 
    sym (G.F-seq (F₁ f) (α₀ y)) 
    ∙ G₂ (α□ f) 
    ∙ G.F-seq (α₀ x) (H₁ f)
  whiskR-pseudonat .snd .N-hom-id {X} = goal
    where
    sq₁ : G₂ (α□ id ∙ α₀ X ◃ H.F-id) 
          ≡ G₂ (F.F-id ▹ α₀ X)
    sq₁ = cong G₂ (α .snd .N-hom-id)
    sq₂ : G₂ (α□ id) 
          ∙ G.F-seq (α₀ X) (H₁ id)
          ∙ G₁ (α₀ X) ◃ G₂ H.F-id 
          ∙ sym (G.F-seq (α₀ X) id)
          ≡ G.F-seq (F₁ id) (α₀ X)
          ∙ G₂ F.F-id ▹ G₁ (α₀ X)
          ∙ sym (G.F-seq id (α₀ X))
    sq₂ = ∙l (sym (G.F₂-◃ H.F-id))
      ∙ sym (G.F₂-funct _ _)
      ∙ sq₁
      ∙ G.F₂-▹ F.F-id
    sq₃ : G₂ (α□ id) 
          ∙ G.F-seq (α₀ X) (H₁ id)
          ∙ G₁ (α₀ X) ◃ G₂ H.F-id 
          ∙ G₁ (α₀ X) ◃ G.F-id
          ≡ (G.F-seq (F₁ id) (α₀ X))
          ∙ G₂ F.F-id ▹ G₁ (α₀ X)
          ∙ G.F-id ▹ G₁ (α₀ X)
    sq₃ = 
      ∙l ∙l ∙l sym (invUniq (G.F-IdR (α₀ X)))
      ∙ sq₂ 
      ∙ ∙l ∙l invUniq (G.F-IdL (α₀ X)) 
    sq₄ : G₂ (α□ id) 
          ∙ G.F-seq (α₀ X) (H₁ id)
          ∙ G₁ (α₀ X) ◃ (G₂ H.F-id ∙ G.F-id)
          ≡ G.F-seq (F₁ id) (α₀ X)
          ∙ (G₂ F.F-id ∙ G.F-id) ▹ G₁ (α₀ X)
    sq₄ = 
      ∙l ∙l ◃-∙ (G₂ H.F-id) G.F-id
      ∙ sq₃
      ∙ ∙l sym (▹-∙ _ G.F-id) 
    goal : (sym (G.F-seq (F₁ id) (α₀ X))
             ∙ G₂ (α□ id) 
             ∙ G.F-seq (α₀ X) (H₁ id))
           ∙ G₁ (α₀ X) ◃ (G₂ H.F-id ∙ G.F-id)
           ≡ (G₂ F.F-id ∙ G.F-id) ▹ G₁ (α₀ X)
    goal =
      sym assoc-inf
      ∙ ∙l sym assoc-inf
      ∙ shuffleSymL sq₄
  whiskR-pseudonat .snd .N-hom-seq {X} {Y} {Z} f g = goal
    where
    open import Prelude.Reassoc
    open BicatReassoc ⟨GPD⟩
    goal = 
        (sym (G.F-seq (F₁ (f » g)) (α₀ Z)) 
          ∙ G₂ (α□ (f » g)) 
          ∙ G.F-seq (α₀ X) (H₁ (f » g)))
        ∙ G₁ (α₀ X) ◃ (G₂ (H.F-seq f g) 
          ∙ G.F-seq (H₁ f) (H₁ g))
      ≡⟨ ∙r ∙l ∙r lemma₁ ⟩ 
        (sym (G.F-seq (F₁ (f » g)) (α₀ Z)) 
          ∙ G₂ ((F.F-seq f g ▹ α₀ Z
              ∙ F₁ f ◃ α□ g
              ∙ α□ f ▹ H₁ g)
            ∙ α₀ X ◃ sym (H.F-seq f g)) 
          ∙ G.F-seq (α₀ X) (H₁ (f » g)))
        ∙ G₁ (α₀ X) ◃ (G₂ (H.F-seq f g) 
          ∙ G.F-seq (H₁ f) (H₁ g))
      ≡⟨ reassoc
            ( ((↑ sym (G.F-seq (F₁ (f » g)) (α₀ Z))
              ∙′ G.F₂′ ((↑ F.F-seq f g ▹′ α₀ Z
                ∙′ (F₁ f ◃′ ↑ α□ g
                  ∙′ ↑ α□ f ▹′ H₁ g))
                ∙′ α₀ X ◃′ ↑ sym (H.F-seq f g))
              ∙′ ↑ G.F-seq (α₀ X) (H₁ (f » g)))
            ∙′ G₁ (α₀ X) ◃′ (↑ G₂ (H.F-seq f g)
              ∙′ ↑ G.F-seq (H₁ f) (H₁ g)) ))
            ( (((↑ sym (G.F-seq (F₁ (f » g)) (α₀ Z))
                ∙′ G.F₂′ (↑ F.F-seq f g ▹′ α₀ Z))
              ∙′ G.F₂′ (F₁ f ◃′ ↑ α□ g
                ∙′ ↑ α□ f ▹′ H₁ g)
              ∙′ G.F₂′ (α₀ X ◃′ ↑ sym (H.F-seq f g))
              ∙′ ↑ G.F-seq (α₀ X) (H₁ (f » g)))
            ∙′ G₁ (α₀ X) ◃′ (↑ G₂ (H.F-seq f g)
              ∙′ ↑ G.F-seq (H₁ f) (H₁ g)) ))
            refl ⟩
        ((sym (G.F-seq (F₁ (f » g)) (α₀ Z)) 
            ∙ G₂ (F.F-seq f g ▹ α₀ Z))
          ∙ G₂ (F₁ f ◃ α□ g
            ∙ α□ f ▹ H₁ g)
          ∙ G₂ (α₀ X ◃ sym (H.F-seq f g)) 
          ∙ G.F-seq (α₀ X) (H₁ (f » g)))
        ∙ G₁ (α₀ X) ◃ (G₂ (H.F-seq f g) 
          ∙ G.F-seq (H₁ f) (H₁ g))
      ≡⟨ ∙r ∙r lemma₂ ⟩
        ((G₂ (F.F-seq f g) ▹ G₁ (α₀ Z)
            ∙ sym (G.F-seq (F₁ f » F₁ g) (α₀ Z)))
          ∙ G₂ (F₁ f ◃ α□ g
            ∙ α□ f ▹ H₁ g)
          ∙ G₂ (α₀ X ◃ sym (H.F-seq f g)) 
          ∙ G.F-seq (α₀ X) (H₁ (f » g)))
        ∙ G₁ (α₀ X) ◃ (G₂ (H.F-seq f g) 
          ∙ G.F-seq (H₁ f) (H₁ g))
      ≡⟨ ∙r ∙l ∙l lemma₃ ⟩
        ((G₂ (F.F-seq f g) ▹ G₁ (α₀ Z)
            ∙ sym (G.F-seq (F₁ f » F₁ g) (α₀ Z)))
          ∙ G₂ (F₁ f ◃ α□ g
            ∙ α□ f ▹ H₁ g)
          ∙ G.F-seq (α₀ X) (H₁ f » H₁ g)
          ∙ G₁ (α₀ X) ◃ sym (G₂ (H.F-seq f g)))
        ∙ G₁ (α₀ X) ◃ (G₂ (H.F-seq f g) 
          ∙ G.F-seq (H₁ f) (H₁ g))
      ≡⟨ reassoc
            ( ((↑ G₂ (F.F-seq f g) ▹′ G₁ (α₀ Z)
                ∙′ ↑ sym (G.F-seq (F₁ f » F₁ g) (α₀ Z)))
              ∙′ G.F₂′ (F₁ f ◃′ ↑ α□ g
                ∙′ ↑ α□ f ▹′ H₁ g)
              ∙′ ↑ G.F-seq (α₀ X) (H₁ f » H₁ g)
              ∙′ G₁ (α₀ X) ◃′ ↑ sym (G₂ (H.F-seq f g)))
            ∙′ G₁ (α₀ X) ◃′ (↑ G₂ (H.F-seq f g)
              ∙′ ↑ G.F-seq (H₁ f) (H₁ g)) )
            ( ↑ G₂ (F.F-seq f g) ▹′ G₁ (α₀ Z)
            ∙′ ↑ sym (G.F-seq (F₁ f » F₁ g) (α₀ Z))
            ∙′ G.F₂′ (F₁ f ◃′ ↑ α□ g)
            ∙′ G.F₂′ (↑ α□ f ▹′ H₁ g)
            ∙′ ↑ G.F-seq (α₀ X) (H₁ f » H₁ g)
            ∙′ G₁ (α₀ X) ◃′ ↑ sym (G₂ (H.F-seq f g))
            ∙′ G₁ (α₀ X) ◃′ (↑ G₂ (H.F-seq f g)
              ∙′ ↑ G.F-seq (H₁ f) (H₁ g)) )
            refl ⟩
        G₂ (F.F-seq f g) ▹ G₁ (α₀ Z)
        ∙ sym (G.F-seq (F₁ f » F₁ g) (α₀ Z))
        ∙ G₂ (F₁ f ◃ α□ g)
        ∙ G₂ (α□ f ▹ H₁ g)
        ∙ G.F-seq (α₀ X) (H₁ f » H₁ g)
        ∙ G₁ (α₀ X) ◃ sym (G₂ (H.F-seq f g))
        ∙ G₁ (α₀ X) ◃ (G₂ (H.F-seq f g) 
          ∙ G.F-seq (H₁ f) (H₁ g))
      ≡⟨ cong (λ q →
            G₂ (F.F-seq f g) ▹ G₁ (α₀ Z)
            ∙ q
            ∙ G₂ (F₁ f ◃ α□ g)
            ∙ G₂ (α□ f ▹ H₁ g)
            ∙ G.F-seq (α₀ X) (H₁ f » H₁ g)
            ∙ G₁ (α₀ X) ◃ sym (G₂ (H.F-seq f g))
            ∙ G₁ (α₀ X) ◃ (G₂ (H.F-seq f g)
              ∙ G.F-seq (H₁ f) (H₁ g)))
            lemma₄ ⟩
        G₂ (F.F-seq f g) ▹ G₁ (α₀ Z)
        ∙ ((G.F-seq (F₁ f) (F₁ g) ▹ G₁ (α₀ Z)
            ∙ G₁ (F₁ f) ◃ sym (G.F-seq (F₁ g) (α₀ Z))
            ∙ sym (G.F-seq (F₁ f) (F₁ g » α₀ Z)))
          ∙ G₂ (F₁ f ◃ α□ g)
          ∙ G₂ (α□ f ▹ H₁ g)
          ∙ G.F-seq (α₀ X) (H₁ f » H₁ g)
          ∙ G₁ (α₀ X) ◃ sym (G₂ (H.F-seq f g))
          ∙ G₁ (α₀ X) ◃ (G₂ (H.F-seq f g)
            ∙ G.F-seq (H₁ f) (H₁ g)))
      ≡⟨ reassoc
            ( ↑ G₂ (F.F-seq f g) ▹′ G₁ (α₀ Z)
            ∙′ ((↑ G.F-seq (F₁ f) (F₁ g) ▹′ G₁ (α₀ Z)
                ∙′ G₁ (F₁ f) ◃′ ↑ sym (G.F-seq (F₁ g) (α₀ Z))
                ∙′ ↑ sym (G.F-seq (F₁ f) (F₁ g » α₀ Z)))
              ∙′ G.F₂′ (F₁ f ◃′ ↑ α□ g)
              ∙′ G.F₂′ (↑ α□ f ▹′ H₁ g)
              ∙′ ↑ G.F-seq (α₀ X) (H₁ f » H₁ g)
              ∙′ G₁ (α₀ X) ◃′ ↑ sym (G₂ (H.F-seq f g))
              ∙′ G₁ (α₀ X) ◃′ (↑ G₂ (H.F-seq f g)
                ∙′ ↑ G.F-seq (H₁ f) (H₁ g))) )
            ( ↑ G₂ (F.F-seq f g) ▹′ G₁ (α₀ Z)
            ∙′ (↑ G.F-seq (F₁ f) (F₁ g) ▹′ G₁ (α₀ Z)
              ∙′ G₁ (F₁ f) ◃′ ↑ sym (G.F-seq (F₁ g) (α₀ Z)))
            ∙′ (↑ sym (G.F-seq (F₁ f) (F₁ g » α₀ Z))
              ∙′ G.F₂′ (F₁ f ◃′ ↑ α□ g))
            ∙′ G.F₂′ (↑ α□ f ▹′ H₁ g)
            ∙′ ↑ G.F-seq (α₀ X) (H₁ f » H₁ g)
            ∙′ G₁ (α₀ X) ◃′ ↑ sym (G₂ (H.F-seq f g))
            ∙′ G₁ (α₀ X) ◃′ (↑ G₂ (H.F-seq f g)
              ∙′ ↑ G.F-seq (H₁ f) (H₁ g)) )
            refl ⟩
        G₂ (F.F-seq f g) ▹ G₁ (α₀ Z)
        ∙ (G.F-seq (F₁ f) (F₁ g) ▹ G₁ (α₀ Z)
        ∙ G₁ (F₁ f) ◃ sym (G.F-seq (F₁ g) (α₀ Z)))
        ∙ (sym (G.F-seq (F₁ f) (F₁ g » α₀ Z))
          ∙ G₂ (F₁ f ◃ α□ g))
        ∙ G₂ (α□ f ▹ H₁ g)
        ∙ G.F-seq (α₀ X) (H₁ f » H₁ g)
        ∙ G₁ (α₀ X) ◃ sym (G₂ (H.F-seq f g))
        ∙ G₁ (α₀ X) ◃ (G₂ (H.F-seq f g) 
          ∙ G.F-seq (H₁ f) (H₁ g))
      ≡⟨ cong (λ q →
            G₂ (F.F-seq f g) ▹ G₁ (α₀ Z)
            ∙ (G.F-seq (F₁ f) (F₁ g) ▹ G₁ (α₀ Z)
              ∙ G₁ (F₁ f) ◃ sym (G.F-seq (F₁ g) (α₀ Z)))
            ∙ q
            ∙ G₂ (α□ f ▹ H₁ g)
            ∙ G.F-seq (α₀ X) (H₁ f » H₁ g)
            ∙ G₁ (α₀ X) ◃ sym (G₂ (H.F-seq f g))
            ∙ G₁ (α₀ X) ◃ (G₂ (H.F-seq f g)
              ∙ G.F-seq (H₁ f) (H₁ g)))
            lemma₅ ⟩
        G₂ (F.F-seq f g) ▹ G₁ (α₀ Z)
        ∙ (G.F-seq (F₁ f) (F₁ g) ▹ G₁ (α₀ Z)
        ∙ G₁ (F₁ f) ◃ sym (G.F-seq (F₁ g) (α₀ Z)))

        ∙ (G₁ (F₁ f) ◃ G₂ (α□ g)
          ∙ sym (G.F-seq (F₁ f) (α₀ Y » H₁ g)))

        ∙ G₂ (α□ f ▹ H₁ g)
        ∙ G.F-seq (α₀ X) (H₁ f » H₁ g)
        ∙ G₁ (α₀ X) ◃ sym (G₂ (H.F-seq f g))
        ∙ G₁ (α₀ X) ◃ (G₂ (H.F-seq f g) 
          ∙ G.F-seq (H₁ f) (H₁ g))
      ≡⟨ cong (λ q →
            G₂ (F.F-seq f g) ▹ G₁ (α₀ Z)
            ∙ (G.F-seq (F₁ f) (F₁ g) ▹ G₁ (α₀ Z)
              ∙ G₁ (F₁ f) ◃ sym (G.F-seq (F₁ g) (α₀ Z)))
            ∙ (G₁ (F₁ f) ◃ G₂ (α□ g) ∙ q)
            ∙ G₂ (α□ f ▹ H₁ g)
            ∙ G.F-seq (α₀ X) (H₁ f » H₁ g)
            ∙ G₁ (α₀ X) ◃ sym (G₂ (H.F-seq f g))
            ∙ G₁ (α₀ X) ◃ (G₂ (H.F-seq f g)
              ∙ G.F-seq (H₁ f) (H₁ g)))
            lemma₆ ⟩
        G₂ (F.F-seq f g) ▹ G₁ (α₀ Z)
        ∙ (G.F-seq (F₁ f) (F₁ g) ▹ G₁ (α₀ Z)
        ∙ G₁ (F₁ f) ◃ sym (G.F-seq (F₁ g) (α₀ Z)))
        ∙ (G₁ (F₁ f) ◃ G₂ (α□ g)

          ∙ G₁ (F₁ f) ◃ G.F-seq (α₀ Y) (H₁ g)
            ∙ sym (G.F-seq (F₁ f) (α₀ Y) ▹ G₁ (H₁ g))
            ∙ sym (G.F-seq (F₁ f » α₀ Y) (H₁ g)))

        ∙ G₂ (α□ f ▹ H₁ g)
        ∙ G.F-seq (α₀ X) (H₁ f » H₁ g)
        ∙ G₁ (α₀ X) ◃ sym (G₂ (H.F-seq f g))
        ∙ G₁ (α₀ X) ◃ (G₂ (H.F-seq f g) 
          ∙ G.F-seq (H₁ f) (H₁ g))

      ≡⟨ cong (λ q →
            G₂ (F.F-seq f g) ▹ G₁ (α₀ Z)
            ∙ (G.F-seq (F₁ f) (F₁ g) ▹ G₁ (α₀ Z)
              ∙ G₁ (F₁ f) ◃ sym (G.F-seq (F₁ g) (α₀ Z)))
            ∙ (G₁ (F₁ f) ◃ G₂ (α□ g)
              ∙ G₁ (F₁ f) ◃ G.F-seq (α₀ Y) (H₁ g)
              ∙ sym (G.F-seq (F₁ f) (α₀ Y) ▹ G₁ (H₁ g))
              ∙ sym (G.F-seq (F₁ f » α₀ Y) (H₁ g)))
            ∙ G₂ (α□ f ▹ H₁ g)
            ∙ q)
            lemma₇ ⟩
        G₂ (F.F-seq f g) ▹ G₁ (α₀ Z)
        ∙ (G.F-seq (F₁ f) (F₁ g) ▹ G₁ (α₀ Z)
          ∙ G₁ (F₁ f) ◃ sym (G.F-seq (F₁ g) (α₀ Z)))
        ∙ (G₁ (F₁ f) ◃ G₂ (α□ g)
          ∙ G₁ (F₁ f) ◃ G.F-seq (α₀ Y) (H₁ g)
          ∙ sym (G.F-seq (F₁ f) (α₀ Y) ▹ G₁ (H₁ g))
          ∙ sym (G.F-seq (F₁ f » α₀ Y) (H₁ g)))
        ∙ G₂ (α□ f ▹ H₁ g)
        ∙ G.F-seq (α₀ X » H₁ f) (H₁ g)
        ∙ G.F-seq (α₀ X) (H₁ f) ▹ G₁ (H₁ g)
      ≡⟨ reassoc
            ( ↑ G₂ (F.F-seq f g) ▹′ G₁ (α₀ Z)
            ∙′ (↑ G.F-seq (F₁ f) (F₁ g) ▹′ G₁ (α₀ Z)
              ∙′ G₁ (F₁ f) ◃′ ↑ sym (G.F-seq (F₁ g) (α₀ Z)))
            ∙′ (G₁ (F₁ f) ◃′ ↑ G₂ (α□ g)
              ∙′ G₁ (F₁ f) ◃′ ↑ G.F-seq (α₀ Y) (H₁ g)
              ∙′ ↑ sym (G.F-seq (F₁ f) (α₀ Y) ▹ G₁ (H₁ g))
              ∙′ ↑ sym (G.F-seq (F₁ f » α₀ Y) (H₁ g)))
            ∙′ G.F₂′ (↑ α□ f ▹′ H₁ g)
            ∙′ ↑ G.F-seq (α₀ X » H₁ f) (H₁ g)
            ∙′ ↑ G.F-seq (α₀ X) (H₁ f) ▹′ G₁ (H₁ g) )
            ( ↑ G₂ (F.F-seq f g) ▹′ G₁ (α₀ Z)
            ∙′ ↑ G.F-seq (F₁ f) (F₁ g) ▹′ G₁ (α₀ Z)
            ∙′ G₁ (F₁ f) ◃′ ↑ sym (G.F-seq (F₁ g) (α₀ Z))
            ∙′ G₁ (F₁ f) ◃′ ↑ G₂ (α□ g)
            ∙′ G₁ (F₁ f) ◃′ ↑ G.F-seq (α₀ Y) (H₁ g)
            ∙′ ↑ sym (G.F-seq (F₁ f) (α₀ Y) ▹ G₁ (H₁ g))
            ∙′ ↑ sym (G.F-seq (F₁ f » α₀ Y) (H₁ g))
            ∙′ G.F₂′ (↑ α□ f ▹′ H₁ g)
            ∙′ ↑ G.F-seq (α₀ X » H₁ f) (H₁ g)
            ∙′ ↑ G.F-seq (α₀ X) (H₁ f) ▹′ G₁ (H₁ g) )
            refl ⟩
        G₂ (F.F-seq f g) ▹ G₁ (α₀ Z)
        ∙ G.F-seq (F₁ f) (F₁ g) ▹ G₁ (α₀ Z)
        ∙ G₁ (F₁ f) ◃ sym (G.F-seq (F₁ g) (α₀ Z))
        ∙ G₁ (F₁ f) ◃ G₂ (α□ g)
        ∙ G₁ (F₁ f) ◃ G.F-seq (α₀ Y) (H₁ g)
        ∙ sym (G.F-seq (F₁ f) (α₀ Y)) ▹ G₁ (H₁ g)
        ∙ sym (G.F-seq (F₁ f » α₀ Y) (H₁ g))
        ∙ G₂ (α□ f ▹ H₁ g)
        ∙ G.F-seq (α₀ X » H₁ f) (H₁ g)
        ∙ G.F-seq (α₀ X) (H₁ f) ▹ G₁ (H₁ g)
      ≡⟨ cong (λ q →
            G₂ (F.F-seq f g) ▹ G₁ (α₀ Z)
            ∙ G.F-seq (F₁ f) (F₁ g) ▹ G₁ (α₀ Z)
            ∙ G₁ (F₁ f) ◃ sym (G.F-seq (F₁ g) (α₀ Z))
            ∙ G₁ (F₁ f) ◃ G₂ (α□ g)
            ∙ G₁ (F₁ f) ◃ G.F-seq (α₀ Y) (H₁ g)
            ∙ sym (G.F-seq (F₁ f) (α₀ Y)) ▹ G₁ (H₁ g)
            ∙ q)
            lemma₈ ⟩
        G₂ (F.F-seq f g) ▹ G₁ (α₀ Z)
        ∙ G.F-seq (F₁ f) (F₁ g) ▹ G₁ (α₀ Z)
        ∙ G₁ (F₁ f) ◃ sym (G.F-seq (F₁ g) (α₀ Z)) 
        ∙ G₁ (F₁ f) ◃ G₂ (α□ g) 
        ∙ G₁ (F₁ f) ◃ G.F-seq (α₀ Y) (H₁ g)
        ∙ sym (G.F-seq (F₁ f) (α₀ Y)) ▹ G₁ (H₁ g)
        ∙ G₂ (α□ f) ▹ G₁ (H₁ g)
        ∙ G.F-seq (α₀ X) (H₁ f) ▹ G₁ (H₁ g)
      ≡⟨ reassoc
            ( ↑ G₂ (F.F-seq f g) ▹′ G₁ (α₀ Z)
            ∙′ ↑ G.F-seq (F₁ f) (F₁ g) ▹′ G₁ (α₀ Z)
            ∙′ G₁ (F₁ f) ◃′ ↑ sym (G.F-seq (F₁ g) (α₀ Z))
            ∙′ G₁ (F₁ f) ◃′ ↑ G₂ (α□ g)
            ∙′ G₁ (F₁ f) ◃′ ↑ G.F-seq (α₀ Y) (H₁ g)
            ∙′ ↑ sym (G.F-seq (F₁ f) (α₀ Y)) ▹′ G₁ (H₁ g)
            ∙′ ↑ G₂ (α□ f) ▹′ G₁ (H₁ g)
            ∙′ ↑ G.F-seq (α₀ X) (H₁ f) ▹′ G₁ (H₁ g) )
            ( (↑ G₂ (F.F-seq f g)
                ∙′ ↑ G.F-seq (F₁ f) (F₁ g)) ▹′ G₁ (α₀ Z)
            ∙′ G₁ (F₁ f) ◃′ (↑ sym (G.F-seq (F₁ g) (α₀ Z))
              ∙′ ↑ G₂ (α□ g)
              ∙′ ↑ G.F-seq (α₀ Y) (H₁ g))
            ∙′ (↑ sym (G.F-seq (F₁ f) (α₀ Y))
              ∙′ ↑ G₂ (α□ f)
              ∙′ ↑ G.F-seq (α₀ X) (H₁ f)) ▹′ G₁ (H₁ g) )
            refl ⟩
        (G₂ (F.F-seq f g) 
          ∙ G.F-seq (F₁ f) (F₁ g)) ▹ G₁ (α₀ Z)
          ∙ G₁ (F₁ f) ◃ (sym (G.F-seq (F₁ g) (α₀ Z)) 
            ∙ G₂ (α□ g) 
            ∙ G.F-seq (α₀ Y) (H₁ g))
          ∙ (sym (G.F-seq (F₁ f) (α₀ Y)) 
            ∙ G₂ (α□ f) 
            ∙ G.F-seq (α₀ X) (H₁ f)) ▹ G₁ (H₁ g)
      ∎
      where
      lemma₁ :
        G₂ (α□ (f » g)) 
        ≡ G₂ ((F.F-seq f g ▹ α₀ Z
            ∙ F₁ f ◃ α□ g
            ∙ α□ f ▹ H₁ g)
          ∙ α₀ X ◃ sym (H.F-seq f g))
      lemma₁ = cong G₂ (shuffleSymRD (α .snd .N-hom-seq f g))
      lemma₂ :
        sym (G.F-seq (F₁ (f » g)) (α₀ Z))
        ∙ G₂ (F.F-seq f g ▹ α₀ Z)
        ≡ G₂ (F.F-seq f g) ▹ G₁ (α₀ Z)
        ∙ sym (G.F-seq (F₁ f » F₁ g) (α₀ Z))
      lemma₂ = shuffleSymLU (G.F₂-▹ (F.F-seq f g))
      lemma₃ :
        G₂ (α₀ X ◃ sym (H.F-seq f g)) 
        ∙ G.F-seq (α₀ X) (H₁ (f » g))
        ≡ G.F-seq (α₀ X) (H₁ f » H₁ g)
        ∙ G₁ (α₀ X) ◃ sym (G₂ (H.F-seq f g))
      lemma₃ = sym (G.F-seq-nat refl (sym (H.F-seq f g)))
      lemma₄ :
        sym (G.F-seq (F₁ f » F₁ g) (α₀ Z))
        ≡ G.F-seq (F₁ f) (F₁ g) ▹ G₁ (α₀ Z)
          ∙ G₁ (F₁ f) ◃ sym (G.F-seq (F₁ g) (α₀ Z))
          ∙ sym (G.F-seq (F₁ f) (F₁ g » α₀ Z))
      lemma₄ =
        (cong sym $ shuffleSymRD $
          G.F-Assoc (F₁ f) (F₁ g) (α₀ Z))
        ∙ symDistr _ _
        ∙ ∙l symDistr _ _
        ∙ ∙l sym (rUnit _)
        ∙ ∙l (symDistr _ _)
      lemma₅ :
        sym (G.F-seq (F₁ f) (F₁ g » α₀ Z))
        ∙ G₂ (F₁ f ◃ α□ g)
        ≡ G₁ (F₁ f) ◃ G₂ (α□ g)
        ∙ sym (G.F-seq (F₁ f) (α₀ Y » H₁ g))
      lemma₅ = shuffleSymRD
        (sym assoc-inf ∙ G.F□-◃ (α□ g))
      lemma₆ :
        sym (G.F-seq (F₁ f) (α₀ Y » H₁ g))
        ≡ G₁ (F₁ f) ◃ G.F-seq (α₀ Y) (H₁ g)
          ∙ sym (G.F-seq (F₁ f) (α₀ Y) ▹ G₁ (H₁ g))
          ∙ sym (G.F-seq (F₁ f » α₀ Y) (H₁ g))
      lemma₆ =
        sym (cong sym $ shuffleSymRU $
          G.F-Assoc (F₁ f) (α₀ Y) (H₁ g) ∙ sym (lUnit _))
        ∙ symDistr _ _
        ∙ ∙l symDistr _ _
      cancel-H-seq :
        G₁ (α₀ X) ◃ sym (G₂ (H.F-seq f g))
        ∙ G₁ (α₀ X) ◃ (G₂ (H.F-seq f g)
          ∙ G.F-seq (H₁ f) (H₁ g))
        ≡ G₁ (α₀ X) ◃ G.F-seq (H₁ f) (H₁ g)
      cancel-H-seq =
        ∙l (◃-∙ (G₂ (H.F-seq f g)) (G.F-seq (H₁ f) (H₁ g)))
        ∙ assoc-inf
        ∙ ∙r (lCancel (G₁ (α₀ X) ◃ G₂ (H.F-seq f g)))
        ∙ sym (lUnit _)
      lemma₇ :
        G.F-seq (α₀ X) (H₁ f » H₁ g)
        ∙ G₁ (α₀ X) ◃ sym (G₂ (H.F-seq f g))
        ∙ G₁ (α₀ X) ◃ (G₂ (H.F-seq f g)
          ∙ G.F-seq (H₁ f) (H₁ g))
        ≡ G.F-seq (α₀ X » H₁ f) (H₁ g)
        ∙ G.F-seq (α₀ X) (H₁ f) ▹ G₁ (H₁ g)
      lemma₇ =
        ∙l cancel-H-seq
        ∙ lUnit _
        ∙ sym (G.F-Assoc (α₀ X) (H₁ f) (H₁ g))
      lemma₈ :
        sym (G.F-seq (F₁ f » α₀ Y) (H₁ g))
        ∙ G₂ (α□ f ▹ H₁ g)
        ∙ G.F-seq (α₀ X » H₁ f) (H₁ g)
        ∙ G.F-seq (α₀ X) (H₁ f) ▹ G₁ (H₁ g)
        ≡ G₂ (α□ f) ▹ G₁ (H₁ g)
        ∙ G.F-seq (α₀ X) (H₁ f) ▹ G₁ (H₁ g)
      lemma₈ =
          sym (G.F-seq (F₁ f » α₀ Y) (H₁ g))
          ∙ G₂ (α□ f ▹ H₁ g)
          ∙ G.F-seq (α₀ X » H₁ f) (H₁ g)
          ∙ G.F-seq (α₀ X) (H₁ f) ▹ G₁ (H₁ g)
        ≡⟨ cong (λ q →
              sym (G.F-seq (F₁ f » α₀ Y) (H₁ g))
              ∙ q
              ∙ G.F-seq (α₀ X » H₁ f) (H₁ g)
              ∙ G.F-seq (α₀ X) (H₁ f) ▹ G₁ (H₁ g))
              (G.F₂-▹ (α□ f)) ⟩
          sym (G.F-seq (F₁ f » α₀ Y) (H₁ g))
          ∙ (G.F-seq (F₁ f » α₀ Y) (H₁ g)
            ∙ G₂ (α□ f) ▹ G₁ (H₁ g)
            ∙ sym (G.F-seq (α₀ X » H₁ f) (H₁ g)))
          ∙ G.F-seq (α₀ X » H₁ f) (H₁ g)
          ∙ G.F-seq (α₀ X) (H₁ f) ▹ G₁ (H₁ g)
        ≡⟨ reassoc
          ( ↑ sym (G.F-seq (F₁ f » α₀ Y) (H₁ g))
          ∙′ ((↑ G.F-seq (F₁ f » α₀ Y) (H₁ g)
              ∙′ G.F₂′ (↑ α□ f) ▹′ G₁ (H₁ g)
              ∙′ ↑ sym (G.F-seq (α₀ X » H₁ f) (H₁ g)))
            ∙′ ↑ G.F-seq (α₀ X » H₁ f) (H₁ g)
            ∙′ ↑ G.F-seq (α₀ X) (H₁ f) ▹′ G₁ (H₁ g) ))
          ( ((↑ sym (G.F-seq (F₁ f » α₀ Y) (H₁ g))
              ∙′ ↑ G.F-seq (F₁ f » α₀ Y) (H₁ g))
            ∙′ G.F₂′ (↑ α□ f) ▹′ G₁ (H₁ g))
          ∙′ ((↑ sym (G.F-seq (α₀ X » H₁ f) (H₁ g))
              ∙′ ↑ G.F-seq (α₀ X » H₁ f) (H₁ g))
            ∙′ ↑ G.F-seq (α₀ X) (H₁ f) ▹′ G₁ (H₁ g) ))
          refl ⟩
          ((sym (G.F-seq (F₁ f » α₀ Y) (H₁ g))
              ∙ G.F-seq (F₁ f » α₀ Y) (H₁ g))
            ∙ G₂ (α□ f) ▹ G₁ (H₁ g))
          ∙ ((sym (G.F-seq (α₀ X » H₁ f) (H₁ g))
              ∙ G.F-seq (α₀ X » H₁ f) (H₁ g))
            ∙ G.F-seq (α₀ X) (H₁ f) ▹ G₁ (H₁ g))
        ≡⟨ ∙r (∙r (lCancel (G.F-seq (F₁ f » α₀ Y) (H₁ g)))
              ∙ sym (lUnit _)) ⟩
          G₂ (α□ f) ▹ G₁ (H₁ g)
          ∙ ((sym (G.F-seq (α₀ X » H₁ f) (H₁ g))
              ∙ G.F-seq (α₀ X » H₁ f) (H₁ g))
            ∙ G.F-seq (α₀ X) (H₁ f) ▹ G₁ (H₁ g))
        ≡⟨ ∙l (∙r (lCancel (G.F-seq (α₀ X » H₁ f) (H₁ g)))
              ∙ sym (lUnit _)) ⟩
          G₂ (α□ f) ▹ G₁ (H₁ g)
          ∙ G.F-seq (α₀ X) (H₁ f) ▹ G₁ (H₁ g)
        ∎
