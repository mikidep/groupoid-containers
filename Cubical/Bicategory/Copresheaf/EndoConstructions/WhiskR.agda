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

  whiskR-pseudonat : PseudonatTrans (F ⊗₀ G) (H ⊗₀ G)
  whiskR-pseudonat .fst .N-ob x = G₁ (α₀ x)
  whiskR-pseudonat .fst .N-hom {x} {y} f = 
    sym (G-seq (F₁ f) (α₀ y)) 
    ∙ G₂ (α□ f) 
    ∙ G-seq (α₀ x) (H₁ f)
  whiskR-pseudonat .snd .N-hom-id {X} = goal
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
  whiskR-pseudonat .snd .N-hom-seq {X} {Y} {Z} f g = goal
    where
    -- open import Prelude.Reassoc
    -- sq₁ : G₂ (α□ (f » g) 
    --         ∙ α₀ X ◃ H-seq f g) 
    --       ≡ G₂ (F.F-seq f g ▹ α₀ Z 
    --         ∙ F₁ f ◃ α□ g 
    --         ∙ α□ f ▹ H₁ g)
    -- sq₁ = cong G₂ (α .snd .N-hom-seq f g)
    -- sq₂ : G₂ (α□ (f » g)) 
    --       ∙ G₂ (α₀ X ◃ H-seq f g) 
    --       ≡ G₂ (F.F-seq f g ▹ α₀ Z) 
    --       ∙ G₂ (F₁ f ◃ α□ g) 
    --       ∙ G₂ (α□ f ▹ H₁ g)
    -- sq₂ = sym (G.F₂-funct _ _)
    --   ∙ sq₁
    --   ∙ G.F₂-funct _ _
    --   ∙ ∙l (G.F₂-funct _ _)
    -- sq₃ : G₂ (α□ (f » g)) 
    --       ∙ G-seq (α₀ X) (H₁ (f » g))
    --       ∙ G₁ (α₀ X) ◃ G₂ (H-seq f g)
    --       ∙ sym (G-seq (α₀ X) (H₁ f » H₁ g))
    --       ≡ (G-seq (F₁ (f » g)) (α₀ Z)
    --         ∙ G₂ (F.F-seq f g) ▹ G₁ (α₀ Z) 
    --         ∙ sym (G-seq (F₁ f » F₁ g) (α₀ Z)))
    --       ∙ (G-seq (F₁ f) (F₁ g » α₀ Z)
    --         ∙ G₁ (F₁ f) ◃ G₂ (α□ g)
    --         ∙ sym (G-seq (F₁ f) (α₀ Y » H₁ g)))
    --       ∙ G-seq (F₁ f » α₀ Y) (H₁ g)
    --       ∙ G₂ (α□ f) ▹ G₁ (H₁ g) 
    --       ∙ sym (G-seq (α₀ X » H₁ f) (H₁ g))
    -- sq₃ = ∙l sym (G.F₂-◃ (H-seq f g))
    --   ∙ sq₂
    --   ∙ cong₂ _∙_
    --     (G.F₂-▹ (F.F-seq f g))
    --     (cong₂ _∙_
    --       (G.F₂-◃ (α□ g))
    --       (G.F₂-▹ (α□ f)))
    -- sq₄ = ∙l ∙l ∙l aux₁
    --   ∙ sq₃
    --   ∙ ∙r ∙l ∙l aux₂
    --   ∙ ∙l ∙r ∙l ∙l aux₃
    --   ∙ ∙l ∙l ∙l ∙l aux₄
    --   where
    --   aux₁ = 
    --     ∙l sym (symDistr _ _) 
    --     ∙ sym (symDistr _ _) 
    --     ∙ (cong sym $ shuffleSymRU $
    --       G.F-Assoc (α₀ X) (H₁ f) (H₁ g) ∙ sym (lUnit _))
    --   aux₂ = (cong sym $ shuffleSymRD $ 
    --       G.F-Assoc (F₁ f) (F₁ g) (α₀ Z))
    --     ∙ symDistr _ _ 
    --     ∙ ∙l symDistr _ _ 
    --     ∙ ∙l sym (rUnit _) ∙ 
    --     ∙l (symDistr _ _)
    --   aux₃ = 
    --     sym (cong sym $ shuffleSymRU $
    --       G.F-Assoc (F₁ f) (α₀ Y ) (H₁ g) ∙ sym (lUnit _))
    --     ∙ symDistr _ _ 
    --     ∙ ∙l symDistr _ _ 
    --   aux₄ = (cong sym $ shuffleSymRD $ 
    --       G.F-Assoc (α₀ X) (H₁ f) (H₁ g))
    --     ∙ symDistr _ _ 
    --     ∙ ∙l symDistr _ _ 
    --     ∙ ∙l sym (rUnit _) ∙ 
    --     ∙l (symDistr _ _)
    -- sq₅ = reassoc
    --     ( G₂ (α□ (f » g))
    --     ∷ G-seq (α₀ X) (H₁ (f » g))
    --     ∷ G₁ (α₀ X) ◃ G₂ (H-seq f g)
    --     ∷ G₁ (α₀ X) ◃ G-seq (H₁ f) (H₁ g)
    --     ∷ sym (G-seq (α₀ X) (H₁ f) ▹ G₁ (H₁ g))
    --     ∷ sym (G-seq (α₀ X » H₁ f) (H₁ g))
    --     ∷ nil )
    --     (((tm ◆ tm ◆ tm ◆ tm) ◆ tm) ◆ tm)
    --     (tm ◆ tm ◆ tm ◆ tm ◆ tm ◆ tm)
    --   ∙ sq₄
    --   ∙ reassoc
    --     ( G-seq (F₁ (f » g)) (α₀ Z)
    --     ∷ G₂ (F.F-seq f g) ▹ G₁ (α₀ Z)
    --     ∷ G-seq (F₁ f) (F₁ g) ▹ G₁ (α₀ Z)
    --     ∷ G₁ (F₁ f) ◃ sym (G-seq (F₁ g) (α₀ Z))
    --     ∷ sym (G-seq (F₁ f) (F₁ g » α₀ Z))
    --     ∷ G-seq (F₁ f) (F₁ g » α₀ Z)
    --     ∷ G₁ (F₁ f) ◃ G₂ (α□ g)
    --     ∷ G₁ (F₁ f) ◃ G-seq (α₀ Y) (H₁ g)
    --     ∷ sym (G-seq (F₁ f) (α₀ Y) ▹ G₁ (H₁ g))
    --     ∷ sym (G-seq (F₁ f » α₀ Y) (H₁ g))
    --     ∷ G-seq (F₁ f » α₀ Y) (H₁ g)
    --     ∷ G₂ (α□ f) ▹ G₁ (H₁ g) 
    --     ∷ G-seq (α₀ X) (H₁ f) ▹ G₁ (H₁ g)
    --     ∷ sym (G₁ (α₀ X) ◃ G-seq (H₁ f) (H₁ g))
    --     ∷ sym (G-seq (α₀ X) (H₁ f ⋆ H₁ g))
    --     ∷ nil )
    --     ((tm ◆ tm ◆ tm ◆ tm ◆ tm) ◆ (tm ◆ tm ◆ tm ◆ tm ◆ tm)
    --       ◆ tm ◆ tm ◆ tm ◆ tm ◆ tm)
    --     (((tm ◆ (tm ◆ tm) ◆ (tm ◆ (tm ◆ tm) ◆ tm ◆ tm) 
    --       ◆ tm ◆ (tm ◆ tm) ◆ tm ◆ tm) ◆ tm) ◆ tm)
    postulate
      -- TODO: too large to compute
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
    -- goal = ∙l ◃-∙ (G₂ (H-seq f g)) (G-seq (H₁ f) (H₁ g))
    --   ∙ rUnit _
    --   ∙ ∙l aux₁
    --   ∙ reassoc 
    --     ( sym (G-seq (F₁ (f » g)) (α₀ Z))
    --     ∷ G₂ (α□ (f » g))
    --     ∷ G-seq (α₀ X) (H₁ (f » g))
    --     ∷ G₁ (α₀ X) ◃ G₂ (H-seq f g)
    --     ∷ G₁ (α₀ X) ◃ G-seq (H₁ f) (H₁ g)
    --     ∷ sym (G-seq (α₀ X) (H₁ f) ▹ G₁ (H₁ g))
    --     ∷ sym (G-seq (α₀ X » H₁ f) (H₁ g))
    --     ∷ G-seq (α₀ X) (H₁ f ⋆ H₁ g)
    --     ∷ G₁ (α₀ X) ◃ G-seq (H₁ f) (H₁ g)
    --     ∷ nil )
    --     (((tm ◆ tm ◆ tm) ◆ tm ◆ tm) ◆ ((tm ◆ tm) ◆ tm ◆ tm))
    --     (tm ◆ ((((tm ◆ tm ◆ tm ◆ tm) ◆ tm) ◆ tm) ◆ tm) ◆ tm)
    --   ∙ (shuffleSymLU $ shuffleSymRU $ shuffleSymRU $ sq₅)
    --   ∙ aux₂
    --   where
    --   aux₁₀ =
    --     ∙l sym (rUnit _)
    --     ∙ G.F-Assoc (α₀ X) (H₁ f) (H₁ g)
    --     ∙ sym (lUnit _)
    --   aux₁ = shuffleSymLD (shuffleSymLD aux₁₀)
    --     ∙ assoc-inf
    --   aux₂ = 
    --     ∙r sym (▹-∙ {k = G₁ (α₀ Z)} 
    --       (G₂ (F.F-seq f g)) (G-seq (F₁ f) (F₁ g)))
    --     ∙ ∙l ∙r ∙l ∙r lCancel _
    --     ∙ ∙l ∙r ∙l sym (lUnit _)
    --     ∙ ∙l ∙r ∙l sym (◃-∙ (G₂ (α□ g)) (G-seq (α₀ Y) (H₁ g)))
    --     ∙ ∙l ∙r sym (◃-∙ (sym (G-seq (F₁ g) (α₀ Z))) 
    --       (G₂ (α□ g) ∙ G-seq (α₀ Y) (H₁ g)))
    --     ∙ ∙l ∙l ∙l ∙r lCancel _
    --     ∙ ∙l ∙l ∙l sym (lUnit _)
    --     ∙ ∙l ∙l ∙l sym (▹-∙ (G₂ (α□ f)) (G-seq (α₀ X) (H₁ f)))
    --     ∙ ∙l ∙l sym (▹-∙ (sym (G-seq (F₁ f) (α₀ Y))) 
    --       (G₂ (α□ f) ∙ G-seq (α₀ X) (H₁ f)))

