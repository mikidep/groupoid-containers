open import Cubical.Foundations.Prelude

open import Cubical.Foundations.Function
open import Cubical.Foundations.GroupoidLaws
open import Prelude.ExtraGpdLaws

open import Cubical.WildCat.Functor hiding (_$_)
open import Cubical.WildCat.Product renaming (_×_ to ProdCat)

module Cubical.LU2C.Copresheaf.EndoConstructions.WhiskR
  (ℓ : Level) where

open import Cubical.LU2C.Base
open import Cubical.LU2C.Instances.Groupoids ℓ 
open import Cubical.LU2C.Copresheaf ℓ 
open import Cubical.LU2C.Instances.Copresheaf ℓ
open import Cubical.LU2C.Copresheaf.EndoConstructions.Base ℓ 
open import Cubical.LU2C.Copresheaf.EndoConstructions.Composite ℓ

open import Cubical.WildCat.AsLU2C.Instances 

open WildFunctor
open Is2Copresheaf

open LU2C HGpd using () renaming (str to ⟨HGpd⟩)
open NotHGpd

module _ {F H : GpdEndo} (α : PseudonatTrans F H)
  (G : GpdEndo) where

  open import Prelude.Reassoc

  private module F = Not2P F
  private module G = Not2P G
  private module H = Not2P H

  open F using (F₀; F₁; F₂)
  open G using () renaming 
    ( F₀ to G₀
    ; F₁ to G₁
    ; F₂ to G₂
    )
  open H using () renaming 
    ( F₀ to H₀
    ; F₁ to H₁
    ; F₂ to H₂
    )
  
  open WildNatTrans (α .fst) using ()
    renaming (N-ob to α₀; N-hom to α□)

  private _⨾₀_ = compEndo₀

  open WildNatTrans
  open IsPseudonat

  whiskR-pseudonat : PseudonatTrans (F ⨾₀ G) (H ⨾₀ G)
  whiskR-pseudonat .fst .N-ob x = G₁ (α₀ x)
  whiskR-pseudonat .fst .N-hom {x} {y} f = G.F□ (α□ f)
  whiskR-pseudonat .snd .N-hom-id {X} =
    G.F□ (α□ id)
    ∙ G₁ (α₀ X) ◃ (G₂ H.F-id ∙ G.F-id)
        ≡⟨ {! !} ⟩ -- lemma₁
    G.F□ (F.F-id ▹ α₀ X ∙ sym (α₀ X ◃ H.F-id))
    ∙ G₁ (α₀ X) ◃ (G₂ H.F-id ∙ G.F-id)
        ≡⟨ {! !} ⟩ 
    G.F□ (F.F-id ▹ α₀ X)
    ∙ G.F□ (sym (α₀ X ◃ H.F-id))
    ∙ G₁ (α₀ X) ◃ (G₂ H.F-id ∙ G.F-id)
        ≡⟨ {! !} ⟩ 
    (sym (G.F-seq (F₁ id) (α₀ X))
      ∙ G₂ (F.F-id ▹ α₀ X ∙ sym (α₀ X ◃ H.F-id))
      ∙ G.F-seq (α₀ X) (H₁ id))
    ∙ G₁ (α₀ X) ◃ (G₂ H.F-id ∙ G.F-id)
        ≡⟨ {! !} ⟩
    sym (G.F-seq (F₁ id) (α₀ X))
    ∙ G₂ (F.F-id ▹ α₀ X) 
    ∙ G₂ (α₀ X ◃ sym H.F-id)
    ∙ G.F-seq (α₀ X) (H₁ id)
    ∙ G₁ (α₀ X) ◃ G₂ H.F-id 
    ∙ G₁ (α₀ X) ◃ G.F-id
        ≡⟨ {! !} ⟩
    sym (G.F-seq (F₁ id) (α₀ X))
    ∙ G₂ (F.F-id ▹ α₀ X) 
    ∙ G.F-seq (α₀ X) (id {x = H₀ X .fst})
    ∙ G₁ (α₀ X) ◃ sym (G₂ H.F-id)
    ∙ G₁ (α₀ X) ◃ G₂ H.F-id 
    ∙ G₁ (α₀ X) ◃ G.F-id
        ≡⟨ {! !} ⟩
    sym (G.F-seq (F₁ id) (α₀ X))
    ∙ G₂ (F.F-id ▹ α₀ X) 
    ∙ G.F-seq (α₀ X) (id {x = H₀ X .fst})
    ∙ G₁ (α₀ X) ◃ sym (G₂ H.F-id)
    ∙ G₁ (α₀ X) ◃ G₂ H.F-id 
    ∙ G₁ (α₀ X) ◃ G.F-id
        ≡⟨ {! !} ⟩
    (G₂ F.F-id ∙ G.F-id) ▹ G₁ (α₀ X)
        ∎
    where
    lemma₁ : 
      α□ (id {x = X .fst})
      ≡ F.F-id ▹ α₀ X ∙ sym (α₀ X ◃ H.F-id)
    lemma₁ = {! !}
  whiskR-pseudonat .snd .N-hom-seq {X} {Y} {Z} f g =
    -- By vibe
    (sym (G.F-seq (F₁ (f ⋆ g)) (α₀ Z))
      ∙ G₂ (α□ (f ⋆ g))
      ∙ G.F-seq (α₀ X) (H₁ (f ⋆ g)))
    ∙ G₁ (α₀ X) ◃ (G₂ (H.F-seq f g) ∙ G.F-seq (H₁ f) (H₁ g))
        ≡⟨ {! !} ⟩
    sym (G.F-seq (F₁ (f ⋆ g)) (α₀ Z))
    ∙ G₂ (α□ (f ⋆ g))
    ∙ (G.F-seq (α₀ X) (H₁ (f ⋆ g))
      ∙ G₁ (α₀ X) ◃ G₂ (H.F-seq f g))
    ∙ G₁ (α₀ X) ◃ G.F-seq (H₁ f) (H₁ g)
        ≡⟨ ∙l ∙l ∙r G.F-seq-nat refl (H.F-seq f g) ⟩
    sym (G.F-seq (F₁ (f ⋆ g)) (α₀ Z))
    ∙ G₂ (α□ (f ⋆ g))
    ∙ (G₂ (α₀ X ◃ H.F-seq f g) ∙ G.F-seq (α₀ X) (H₁ f ⋆ H₁ g))
    ∙ G₁ (α₀ X) ◃ G.F-seq (H₁ f) (H₁ g)
        ≡⟨ ? ⟩
    sym (G.F-seq (F₁ (f ⋆ g)) (α₀ Z))
    ∙ G₂ (α□ (f ⋆ g) ∙ α₀ X ◃ H.F-seq f g)
    ∙ (G.F-seq (α₀ X) (H₁ f ⋆ H₁ g)
      ∙ G₁ (α₀ X) ◃ G.F-seq (H₁ f) (H₁ g))
        ≡⟨ ∙l ∙r cong G₂ (α .snd .N-hom-seq f g) ⟩
    sym (G.F-seq (F₁ (f ⋆ g)) (α₀ Z))
    ∙ G₂ (F.F-seq f g ▹ α₀ Z ∙ F₁ f ◃ α□ g ∙ α□ f ▹ H₁ g)
    ∙ (G.F-seq (α₀ X) (H₁ f ⋆ H₁ g)
      ∙ G₁ (α₀ X) ◃ G.F-seq (H₁ f) (H₁ g))
        ≡⟨ ∙l ∙l (lUnit _ ∙ sym (G.F-Assoc (α₀ X) (H₁ f) (H₁ g))) ⟩
    sym (G.F-seq (F₁ (f ⋆ g)) (α₀ Z))
    ∙ G₂ (F.F-seq f g ▹ α₀ Z ∙ F₁ f ◃ α□ g ∙ α□ f ▹ H₁ g)
    ∙ G.F-seq (α₀ X ⋆ H₁ f) (H₁ g)
    ∙ G.F-seq (α₀ X) (H₁ f) ▹ G₁ (H₁ g)
        ≡⟨ ? ⟩
    sym (G.F-seq (F₁ (f ⋆ g)) (α₀ Z))
    ∙ G₂ (F.F-seq f g ▹ α₀ Z)
    ∙ G₂ (F₁ f ◃ α□ g)
    ∙ (G₂ (α□ f ▹ H₁ g) ∙ G.F-seq (α₀ X ⋆ H₁ f) (H₁ g))
    ∙ G.F-seq (α₀ X) (H₁ f) ▹ G₁ (H₁ g)
        ≡⟨ ∙l ∙l ∙l ∙r sym (G.F-seq-nat (α□ f) refl) ⟩
    sym (G.F-seq (F₁ (f ⋆ g)) (α₀ Z))
    ∙ G₂ (F.F-seq f g ▹ α₀ Z)
    ∙ G₂ (F₁ f ◃ α□ g)
    ∙ (G.F-seq (F₁ f ⋆ α₀ Y) (H₁ g) ∙ G₂ (α□ f) ▹ G₁ (H₁ g))
    ∙ G.F-seq (α₀ X) (H₁ f) ▹ G₁ (H₁ g)
        ≡⟨ ∙l ∙l ∙l ∙r ∙r shuffleSymRD
            (G.F-Assoc (F₁ f) (α₀ Y) (H₁ g) ∙ sym (lUnit _)) ⟩
    sym (G.F-seq (F₁ (f ⋆ g)) (α₀ Z))
    ∙ G₂ (F.F-seq f g ▹ α₀ Z)
    ∙ G₂ (F₁ f ◃ α□ g)
    ∙ (((G.F-seq (F₁ f) (α₀ Y ⋆ H₁ g)
        ∙ G₁ (F₁ f) ◃ G.F-seq (α₀ Y) (H₁ g))
        ∙ sym (G.F-seq (F₁ f) (α₀ Y) ▹ G₁ (H₁ g)))
      ∙ G₂ (α□ f) ▹ G₁ (H₁ g))
    ∙ G.F-seq (α₀ X) (H₁ f) ▹ G₁ (H₁ g)
        ≡⟨ ? ⟩
    sym (G.F-seq (F₁ (f ⋆ g)) (α₀ Z))
    ∙ G₂ (F.F-seq f g ▹ α₀ Z)
    ∙ (G₂ (F₁ f ◃ α□ g) ∙ G.F-seq (F₁ f) (α₀ Y ⋆ H₁ g))
    ∙ G₁ (F₁ f) ◃ G.F-seq (α₀ Y) (H₁ g)
    ∙ sym (G.F-seq (F₁ f) (α₀ Y) ▹ G₁ (H₁ g))
    ∙ G₂ (α□ f) ▹ G₁ (H₁ g)
    ∙ G.F-seq (α₀ X) (H₁ f) ▹ G₁ (H₁ g)
        ≡⟨ ∙l ∙l ∙r sym (G.F-seq-nat refl (α□ g)) ⟩
    sym (G.F-seq (F₁ (f ⋆ g)) (α₀ Z))
    ∙ G₂ (F.F-seq f g ▹ α₀ Z)
    ∙ (G.F-seq (F₁ f) (F₁ g ⋆ α₀ Z) ∙ G₁ (F₁ f) ◃ G₂ (α□ g))
    ∙ G₁ (F₁ f) ◃ G.F-seq (α₀ Y) (H₁ g)
    ∙ sym (G.F-seq (F₁ f) (α₀ Y) ▹ G₁ (H₁ g))
    ∙ G₂ (α□ f) ▹ G₁ (H₁ g)
    ∙ G.F-seq (α₀ X) (H₁ f) ▹ G₁ (H₁ g)
        ≡⟨ ∙l ∙l ∙r ∙r shuffleSymRD
            (sym (G.F-Assoc (F₁ f) (F₁ g) (α₀ Z) ∙ sym (lUnit _))) ⟩
    sym (G.F-seq (F₁ (f ⋆ g)) (α₀ Z))
    ∙ G₂ (F.F-seq f g ▹ α₀ Z)
    ∙ (((G.F-seq (F₁ f ⋆ F₁ g) (α₀ Z)
        ∙ G.F-seq (F₁ f) (F₁ g) ▹ G₁ (α₀ Z))
        ∙ sym (G₁ (F₁ f) ◃ G.F-seq (F₁ g) (α₀ Z)))
      ∙ G₁ (F₁ f) ◃ G₂ (α□ g))
    ∙ G₁ (F₁ f) ◃ G.F-seq (α₀ Y) (H₁ g)
    ∙ sym (G.F-seq (F₁ f) (α₀ Y) ▹ G₁ (H₁ g))
    ∙ G₂ (α□ f) ▹ G₁ (H₁ g)
    ∙ G.F-seq (α₀ X) (H₁ f) ▹ G₁ (H₁ g)
        ≡⟨ ? ⟩
    sym (G.F-seq (F₁ (f ⋆ g)) (α₀ Z))
    ∙ (G₂ (F.F-seq f g ▹ α₀ Z) ∙ G.F-seq (F₁ f ⋆ F₁ g) (α₀ Z))
    ∙ G.F-seq (F₁ f) (F₁ g) ▹ G₁ (α₀ Z)
    ∙ sym (G₁ (F₁ f) ◃ G.F-seq (F₁ g) (α₀ Z))
    ∙ G₁ (F₁ f) ◃ G₂ (α□ g)
    ∙ G₁ (F₁ f) ◃ G.F-seq (α₀ Y) (H₁ g)
    ∙ sym (G.F-seq (F₁ f) (α₀ Y) ▹ G₁ (H₁ g))
    ∙ G₂ (α□ f) ▹ G₁ (H₁ g)
    ∙ G.F-seq (α₀ X) (H₁ f) ▹ G₁ (H₁ g)
        ≡⟨ ∙l ∙r sym (G.F-seq-nat (F.F-seq f g) refl) ⟩
    sym (G.F-seq (F₁ (f ⋆ g)) (α₀ Z))
    ∙ (G.F-seq (F₁ (f ⋆ g)) (α₀ Z) ∙ G₂ (F.F-seq f g) ▹ G₁ (α₀ Z))
    ∙ G.F-seq (F₁ f) (F₁ g) ▹ G₁ (α₀ Z)
    ∙ sym (G₁ (F₁ f) ◃ G.F-seq (F₁ g) (α₀ Z))
    ∙ G₁ (F₁ f) ◃ G₂ (α□ g)
    ∙ G₁ (F₁ f) ◃ G.F-seq (α₀ Y) (H₁ g)
    ∙ sym (G.F-seq (F₁ f) (α₀ Y) ▹ G₁ (H₁ g))
    ∙ G₂ (α□ f) ▹ G₁ (H₁ g)
    ∙ G.F-seq (α₀ X) (H₁ f) ▹ G₁ (H₁ g)
        ≡⟨ ? ⟩
    (sym (G.F-seq (F₁ (f ⋆ g)) (α₀ Z)) ∙ G.F-seq (F₁ (f ⋆ g)) (α₀ Z))
    ∙ G₂ (F.F-seq f g) ▹ G₁ (α₀ Z)
    ∙ G.F-seq (F₁ f) (F₁ g) ▹ G₁ (α₀ Z)
    ∙ sym (G₁ (F₁ f) ◃ G.F-seq (F₁ g) (α₀ Z))
    ∙ G₁ (F₁ f) ◃ G₂ (α□ g)
    ∙ G₁ (F₁ f) ◃ G.F-seq (α₀ Y) (H₁ g)
    ∙ sym (G.F-seq (F₁ f) (α₀ Y) ▹ G₁ (H₁ g))
    ∙ G₂ (α□ f) ▹ G₁ (H₁ g)
    ∙ G.F-seq (α₀ X) (H₁ f) ▹ G₁ (H₁ g)
        ≡⟨ ∙r lCancel _ ⟩
    refl
    ∙ G₂ (F.F-seq f g) ▹ G₁ (α₀ Z)
    ∙ G.F-seq (F₁ f) (F₁ g) ▹ G₁ (α₀ Z)
    ∙ sym (G₁ (F₁ f) ◃ G.F-seq (F₁ g) (α₀ Z))
    ∙ G₁ (F₁ f) ◃ G₂ (α□ g)
    ∙ G₁ (F₁ f) ◃ G.F-seq (α₀ Y) (H₁ g)
    ∙ sym (G.F-seq (F₁ f) (α₀ Y) ▹ G₁ (H₁ g))
    ∙ G₂ (α□ f) ▹ G₁ (H₁ g)
    ∙ G.F-seq (α₀ X) (H₁ f) ▹ G₁ (H₁ g)
        ≡⟨ ? ⟩
    (G₂ (F.F-seq f g) ∙ G.F-seq (F₁ f) (F₁ g)) ▹ G₁ (α₀ Z)
    ∙ G₁ (F₁ f) ◃ (sym (G.F-seq (F₁ g) (α₀ Z))
      ∙ G₂ (α□ g) ∙ G.F-seq (α₀ Y) (H₁ g))
    ∙ (sym (G.F-seq (F₁ f) (α₀ Y))
      ∙ G₂ (α□ f) ∙ G.F-seq (α₀ X) (H₁ f)) ▹ G₁ (H₁ g)
        ∎
    -- where
    -- reass₁ = reassoc
    --   ( (↑ sym (G.F-seq (F₁ (f ⋆ g)) (α₀ Z))
    --     ∙′ G.F₂′ (↑ α□ (f ⋆ g))
    --     ∙′ ↑ G.F-seq (α₀ X) (H₁ (f ⋆ g)))
    --   ∙′ G₁ (α₀ X) ◃′ (G.F₂′ (↑ H.F-seq f g) ∙′ ↑ G.F-seq (H₁ f) (H₁ g)) )
    --   ( ↑ sym (G.F-seq (F₁ (f ⋆ g)) (α₀ Z))
    --   ∙′ G.F₂′ (↑ α□ (f ⋆ g))
    --   ∙′ (↑ G.F-seq (α₀ X) (H₁ (f ⋆ g))
    --     ∙′ G₁ (α₀ X) ◃′ G.F₂′ (↑ H.F-seq f g))
    --   ∙′ G₁ (α₀ X) ◃′ ↑ G.F-seq (H₁ f) (H₁ g) )
    --   refl
    -- reass₂ = reassoc
    --   ( ↑ sym (G.F-seq (F₁ (f ⋆ g)) (α₀ Z))
    --   ∙′ G.F₂′ (↑ α□ (f ⋆ g))
    --   ∙′ (G.F₂′ (α₀ X ◃′ ↑ H.F-seq f g)
    --     ∙′ ↑ G.F-seq (α₀ X) (H₁ f ⋆ H₁ g))
    --   ∙′ G₁ (α₀ X) ◃′ ↑ G.F-seq (H₁ f) (H₁ g) )
    --   ( ↑ sym (G.F-seq (F₁ (f ⋆ g)) (α₀ Z))
    --   ∙′ G.F₂′ (↑ α□ (f ⋆ g) ∙′ α₀ X ◃′ ↑ H.F-seq f g)
    --   ∙′ (↑ G.F-seq (α₀ X) (H₁ f ⋆ H₁ g)
    --     ∙′ G₁ (α₀ X) ◃′ ↑ G.F-seq (H₁ f) (H₁ g)) )
    --   refl
    -- reass₃ = reassoc
    --   ( ↑ sym (G.F-seq (F₁ (f ⋆ g)) (α₀ Z))
    --   ∙′ G.F₂′ (↑ F.F-seq f g ▹′ α₀ Z
    --     ∙′ F₁ f ◃′ ↑ α□ g ∙′ ↑ α□ f ▹′ H₁ g)
    --   ∙′ ↑ G.F-seq (α₀ X ⋆ H₁ f) (H₁ g)
    --   ∙′ ↑ G.F-seq (α₀ X) (H₁ f) ▹′ G₁ (H₁ g) )
    --   ( ↑ sym (G.F-seq (F₁ (f ⋆ g)) (α₀ Z))
    --   ∙′ G.F₂′ (↑ F.F-seq f g ▹′ α₀ Z)
    --   ∙′ G.F₂′ (F₁ f ◃′ ↑ α□ g)
    --   ∙′ (G.F₂′ (↑ α□ f ▹′ H₁ g)
    --     ∙′ ↑ G.F-seq (α₀ X ⋆ H₁ f) (H₁ g))
    --   ∙′ ↑ G.F-seq (α₀ X) (H₁ f) ▹′ G₁ (H₁ g) )
    --   refl
    -- reass₄ = reassoc
    --   ( ↑ sym (G.F-seq (F₁ (f ⋆ g)) (α₀ Z))
    --   ∙′ G.F₂′ (↑ F.F-seq f g ▹′ α₀ Z)
    --   ∙′ G.F₂′ (F₁ f ◃′ ↑ α□ g)
    --   ∙′ (((↑ G.F-seq (F₁ f) (α₀ Y ⋆ H₁ g)
    --       ∙′ G₁ (F₁ f) ◃′ ↑ G.F-seq (α₀ Y) (H₁ g))
    --       ∙′ ↑ sym (G.F-seq (F₁ f) (α₀ Y)) ▹′ G₁ (H₁ g))
    --     ∙′ G.F₂′ (↑ α□ f) ▹′ G₁ (H₁ g))
    --   ∙′ ↑ G.F-seq (α₀ X) (H₁ f) ▹′ G₁ (H₁ g) )
    --   ( ↑ sym (G.F-seq (F₁ (f ⋆ g)) (α₀ Z))
    --   ∙′ G.F₂′ (↑ F.F-seq f g ▹′ α₀ Z)
    --   ∙′ (G.F₂′ (F₁ f ◃′ ↑ α□ g) ∙′ ↑ G.F-seq (F₁ f) (α₀ Y ⋆ H₁ g))
    --   ∙′ G₁ (F₁ f) ◃′ ↑ G.F-seq (α₀ Y) (H₁ g)
    --   ∙′ ↑ sym (G.F-seq (F₁ f) (α₀ Y)) ▹′ G₁ (H₁ g)
    --   ∙′ G.F₂′ (↑ α□ f) ▹′ G₁ (H₁ g)
    --   ∙′ ↑ G.F-seq (α₀ X) (H₁ f) ▹′ G₁ (H₁ g) )
    --   refl
    -- reass₅ = reassoc
    --   ( ↑ sym (G.F-seq (F₁ (f ⋆ g)) (α₀ Z))
    --   ∙′ G.F₂′ (↑ F.F-seq f g ▹′ α₀ Z)
    --   ∙′ (((↑ G.F-seq (F₁ f ⋆ F₁ g) (α₀ Z)
    --       ∙′ ↑ G.F-seq (F₁ f) (F₁ g) ▹′ G₁ (α₀ Z))
    --       ∙′ G₁ (F₁ f) ◃′ ↑ sym (G.F-seq (F₁ g) (α₀ Z)))
    --     ∙′ G₁ (F₁ f) ◃′ G.F₂′ (↑ α□ g))
    --   ∙′ G₁ (F₁ f) ◃′ ↑ G.F-seq (α₀ Y) (H₁ g)
    --   ∙′ ↑ sym (G.F-seq (F₁ f) (α₀ Y)) ▹′ G₁ (H₁ g)
    --   ∙′ G.F₂′ (↑ α□ f) ▹′ G₁ (H₁ g)
    --   ∙′ ↑ G.F-seq (α₀ X) (H₁ f) ▹′ G₁ (H₁ g) )
    --   ( ↑ sym (G.F-seq (F₁ (f ⋆ g)) (α₀ Z))
    --   ∙′ (G.F₂′ (↑ F.F-seq f g ▹′ α₀ Z)
    --     ∙′ ↑ G.F-seq (F₁ f ⋆ F₁ g) (α₀ Z))
    --   ∙′ ↑ G.F-seq (F₁ f) (F₁ g) ▹′ G₁ (α₀ Z)
    --   ∙′ G₁ (F₁ f) ◃′ ↑ sym (G.F-seq (F₁ g) (α₀ Z))
    --   ∙′ G₁ (F₁ f) ◃′ G.F₂′ (↑ α□ g)
    --   ∙′ G₁ (F₁ f) ◃′ ↑ G.F-seq (α₀ Y) (H₁ g)
    --   ∙′ ↑ sym (G.F-seq (F₁ f) (α₀ Y)) ▹′ G₁ (H₁ g)
    --   ∙′ G.F₂′ (↑ α□ f) ▹′ G₁ (H₁ g)
    --   ∙′ ↑ G.F-seq (α₀ X) (H₁ f) ▹′ G₁ (H₁ g) )
    --   refl
    -- reass₆ = reassoc
    --   ( ↑ sym (G.F-seq (F₁ (f ⋆ g)) (α₀ Z))
    --   ∙′ (↑ G.F-seq (F₁ (f ⋆ g)) (α₀ Z) ∙′ G.F₂′ (↑ F.F-seq f g) ▹′ G₁ (α₀ Z))
    --   ∙′ ↑ G.F-seq (F₁ f) (F₁ g) ▹′ G₁ (α₀ Z)
    --   ∙′ G₁ (F₁ f) ◃′ ↑ sym (G.F-seq (F₁ g) (α₀ Z))
    --   ∙′ G₁ (F₁ f) ◃′ G.F₂′ (↑ α□ g)
    --   ∙′ G₁ (F₁ f) ◃′ ↑ G.F-seq (α₀ Y) (H₁ g)
    --   ∙′ ↑ sym (G.F-seq (F₁ f) (α₀ Y)) ▹′ G₁ (H₁ g)
    --   ∙′ G.F₂′ (↑ α□ f) ▹′ G₁ (H₁ g)
    --   ∙′ ↑ G.F-seq (α₀ X) (H₁ f) ▹′ G₁ (H₁ g) )
    --   ( (↑ sym (G.F-seq (F₁ (f ⋆ g)) (α₀ Z)) ∙′ ↑ G.F-seq (F₁ (f ⋆ g)) (α₀ Z))
    --   ∙′ G.F₂′ (↑ F.F-seq f g) ▹′ G₁ (α₀ Z)
    --   ∙′ ↑ G.F-seq (F₁ f) (F₁ g) ▹′ G₁ (α₀ Z)
    --   ∙′ G₁ (F₁ f) ◃′ ↑ sym (G.F-seq (F₁ g) (α₀ Z))
    --   ∙′ G₁ (F₁ f) ◃′ G.F₂′ (↑ α□ g)
    --   ∙′ G₁ (F₁ f) ◃′ ↑ G.F-seq (α₀ Y) (H₁ g)
    --   ∙′ ↑ sym (G.F-seq (F₁ f) (α₀ Y)) ▹′ G₁ (H₁ g)
    --   ∙′ G.F₂′ (↑ α□ f) ▹′ G₁ (H₁ g)
    --   ∙′ ↑ G.F-seq (α₀ X) (H₁ f) ▹′ G₁ (H₁ g) )
    --   refl
    -- reass₇ = reassoc
    --   ( refl′
    --   ∙′ G.F₂′ (↑ F.F-seq f g) ▹′ G₁ (α₀ Z)
    --   ∙′ ↑ G.F-seq (F₁ f) (F₁ g) ▹′ G₁ (α₀ Z)
    --   ∙′ G₁ (F₁ f) ◃′ ↑ sym (G.F-seq (F₁ g) (α₀ Z))
    --   ∙′ G₁ (F₁ f) ◃′ G.F₂′ (↑ α□ g)
    --   ∙′ G₁ (F₁ f) ◃′ ↑ G.F-seq (α₀ Y) (H₁ g)
    --   ∙′ ↑ sym (G.F-seq (F₁ f) (α₀ Y)) ▹′ G₁ (H₁ g)
    --   ∙′ G.F₂′ (↑ α□ f) ▹′ G₁ (H₁ g)
    --   ∙′ ↑ G.F-seq (α₀ X) (H₁ f) ▹′ G₁ (H₁ g) )
    --   ( (G.F₂′ (↑ F.F-seq f g) ∙′ ↑ G.F-seq (F₁ f) (F₁ g)) ▹′ G₁ (α₀ Z)
    --   ∙′ G₁ (F₁ f) ◃′ (↑ sym (G.F-seq (F₁ g) (α₀ Z))
    --     ∙′ G.F₂′ (↑ α□ g) ∙′ ↑ G.F-seq (α₀ Y) (H₁ g))
    --   ∙′ (↑ sym (G.F-seq (F₁ f) (α₀ Y))
    --     ∙′ G.F₂′ (↑ α□ f) ∙′ ↑ G.F-seq (α₀ X) (H₁ f)) ▹′ G₁ (H₁ g) )
    --   refl
