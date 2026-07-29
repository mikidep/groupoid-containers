{-# OPTIONS --allow-unsolved-metas #-}
open import Cubical.Foundations.Prelude

open import Cubical.Foundations.Function

open import Cubical.WildCat.Functor hiding (_$_)
open import Cubical.WildCat.Product renaming (_×_ to ProdCat)
open import Cubical.WildCat.NaturalTransformation.Base
  using () renaming (makeNatTransPath to WNatTrans≡)

open import Cubical.Bicategory.Base

module Cubical.Bicategory.Copresheaf.EndoConstructions
  (ℓ : Level) where

open import Cubical.Bicategory.Instances.Groupoids ℓ
open import Cubical.Bicategory.Copresheaf ℓ
open import Cubical.Bicategory.Instances.Copresheaf ℓ
open import Cubical.Bicategory.Copresheaf.EndoConstructions.Base ℓ public
open import Cubical.Bicategory.Copresheaf.EndoConstructions.Composite ℓ public
open import Cubical.Bicategory.Copresheaf.EndoConstructions.WhiskL ℓ
open import Cubical.Bicategory.Copresheaf.EndoConstructions.WhiskR ℓ

private _⊗₀_ = compEndo₀

module _ {F G H K : GpdEndo}
  (α : PseudonatTrans F H)
  (β : PseudonatTrans G K) where

  open import Prelude
  compEndo₁ : PseudonatTrans (F ⊗₀ G) (H ⊗₀ K)
  compEndo₁ = α▹G ⋆ᵉ H◃β
    where
    open Bicategory (CopshBicat GPD) using ()
      renaming (_⋆_ to _⋆ᵉ_)
    α▹G = whiskR-pseudonat α G
    H◃β = whiskL-pseudonat H β

open WildFunctor
open import Cubical.Functions.FunExtEquiv
open import Cubical.Foundations.Path
open import Cubical.Foundations.Function
open import Cubical.Foundations.GroupoidLaws
open import Prelude.Square
open import Prelude.ExtraGpdLaws
open import Prelude.Reassoc

open Bicategory GPD renaming (str to ⟨GPD⟩; Hom[_,_] to GPD[_,_])

open BicatReassoc ⟨GPD⟩

compEndo : WildFunctor
  (ProdCat GpdEndoWildCat GpdEndoWildCat) GpdEndoWildCat
compEndo .F-ob = uncurry compEndo₀
compEndo .F-hom = uncurry compEndo₁
compEndo .F-id {F , G} = PseudonatTrans≡ $ WNatTrans≡ 
  (funExt λ X → G.F-id) 
  goal
  where
  module F = Copresheaf F
  module G = Copresheaf G
  open F using (F₀; F₁; F₂)
  open G using ()
    renaming (
      F₀ to    G₀;
      F₁ to    G₁;
      F₂ to    G₂;
      F-id to  G-id;
      F-seq to G-seq
    )
  goal : ∀ {X Y} (f : GPD[ X , Y ]) → 
    Square
      ((sym (G-seq (F₁ f) id) ∙ refl ∙ G-seq id (F₁ f)) ∙ refl)
      refl
      (G₁ (F₁ f) ◃ G-id)
      (G-id ▹ G₁ (F₁ f))
  goal f = compPath→Square goal'
    where
    goal'' :
      G-seq (F₁ f) id
      ∙ G₁ (F₁ f) ◃ G-id
      ≡ G-seq id (F₁ f)
      ∙ G-id ▹ G₁ (F₁ f)
    goal'' = G.F-IdR (F₁ f) ∙ sym (G.F-IdL (F₁ f))
    goal' : 
      G₁ (F₁ f) ◃ G-id ∙ refl 
      ≡ ((sym (G-seq (F₁ f) id) 
          ∙ refl 
          ∙ G-seq id (F₁ f)) 
        ∙ refl)
      ∙ G-id ▹ G₁ (F₁ f)
    goal' = sym (rUnit _)
      ∙ shuffleSymLD goal''
      ∙ reassoc
        ( ↑ sym (G-seq (F₁ f) id) 
        ∙′ ↑ G-seq id (F₁ f) 
        ∙′ ↑ G-id ▹′ G₁ (F₁ f) )
        ( ((↑ sym (G-seq (F₁ f) id) 
            ∙′ refl′ ∙′ ↑ G-seq id (F₁ f)) 
          ∙′ refl′) 
        ∙′ ↑ G-id ▹′ G₁ (F₁ f) )
        refl
compEndo .F-seq {F , F'} {G , G'} {H , H'} (α , α') (β , β') = PseudonatTrans≡ $ WNatTrans≡ 
  (funExt λ X → 
    F'.F-seq (α₀ X) (β₀ X) ▹ α'₀ (H.F₀ X) ▹ β'₀ (H.F₀ X)
    ∙ F'.F₁ (α₀ X) ◃ α'□ (β₀ X) ▹ β'₀ (H.F₀ X))
  goal
  where
  open import Prelude.Utils
  module F = Copresheaf F
  module G = Copresheaf G
  module H = Copresheaf H
  module F' = Copresheaf F'
  module G' = Copresheaf G'
  module H' = Copresheaf H'
  open WildNatTrans (α .fst) renaming (N-ob to α₀; N-hom to α□)
  open WildNatTrans (β .fst) renaming (N-ob to β₀; N-hom to β□)
  open WildNatTrans (α' .fst) renaming (N-ob to α'₀; N-hom to α'□)
  open WildNatTrans (β' .fst) renaming (N-ob to β'₀; N-hom to β'□)
  goal : ∀ {X Y} (f : GPD[ X , Y ]) → 
    Square
      {! _ !}
      ((({! _ !} 
            ∙ {! _ !}) ▹ α'₀ (G.F₀ Y) 
          ∙ F'.F₁ (α₀ X) ◃ α'□ (G.F₁ f)) ▹ G'.F₁ (β₀ Y) ▹ β'₀ (H.F₀ Y)  
        ∙ (F'.F₁ (α₀ X) ◃ α'₀ (G.F₀ X) ◃ sym (G'.F-seq (G.F₁ f) (β₀ Y)) 
          ∙ {! _ !}) ▹ β'₀ (H.F₀ Y)
        ∙ F'.F₁ (α₀ X) ◃ α'₀ (G.F₀ X) ◃ G'.F₁ (β₀ X) ◃ β'□ (H.F₁ f))
      {! _ !}
      {! _ !}
  goal = ?
  -- See notepad
