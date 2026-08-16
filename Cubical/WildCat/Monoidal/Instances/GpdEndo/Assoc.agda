{-# OPTIONS --allow-unsolved-metas #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Path
open import Cubical.Functions.FunExtEquiv

open import Cubical.WildCat.Base
open import Cubical.WildCat.Functor hiding (_$_)
open import Cubical.WildCat.NaturalTransformation.Base

module Cubical.WildCat.Monoidal.Instances.GpdEndo.Assoc
  (ℓ : Level) where

open import Cubical.Bicategory.Base
open import Cubical.Bicategory.Copresheaf.EndoConstructions ℓ
open import Cubical.Bicategory.Copresheaf ℓ
open import Cubical.Bicategory.Instances.Copresheaf ℓ

open import Prelude.Reassoc
open import Prelude.ExtraGpdLaws

private
  _⊗₀_ = compEndo₀
  _⊗₁_ = compEndo₁
  GpdEndoBicat = CopshBicat GPD

module _ (F G H : GpdEndo) where
  open WildNatTrans
  open IsPseudonat

  open Bicategory GPD using (id; _◃_; _▹_)

  private 
    module F = Copresheaf F
    module G = Copresheaf G
    module H = Copresheaf H

  open F using (F₁; F₂)
  open G using () renaming (F₁ to G₁; F₂ to G₂; F₂′ to G₂′)
  open H using () renaming (F₁ to H₁; F₂ to H₂; F₂′ to H₂′)

  iMG-assoc-ob : PseudonatTrans (F ⊗₀ (G ⊗₀ H)) ((F ⊗₀ G) ⊗₀ H)
  iMG-assoc-ob .fst .N-ob X        = idfun _
  iMG-assoc-ob .fst .N-hom f       = refl
  iMG-assoc-ob .snd .N-hom-id      =
    reassoc
      ( refl′ ∙′ H₂′ (G₂′ (↑ F.F-id) ∙′ ↑ G.F-id) ∙′ ↑ H.F-id )
      ( H₂′ (G₂′ (↑ F.F-id)) ∙′ H₂′ (↑ G.F-id) ∙′ ↑ H.F-id )
      refl
  iMG-assoc-ob .snd .N-hom-seq f g = 
    reassoc
      ( refl′ 
      ∙′ (H₂′ (↑ G₂ (F.F-seq f g) 
        ∙′ ↑ G.F-seq (F₁ f) (F₁ g))) 
      ∙′ ↑ H.F-seq (G₁ (F₁ f)) (G₁ (F₁ g)) )
      ( (H₂′ (↑ G₂ (F.F-seq f g)) 
        ∙′ H₂′ (↑ G.F-seq (F₁ f) (F₁ g)) 
        ∙′ ↑ H.F-seq (G₁ (F₁ f)) (G₁ (F₁ g))) 
      ∙′ refl′ ∙′ refl′ )
      refl

module _ {F G H F′ G′ H′ : GpdEndo} 
  (α : PseudonatTrans F F′) 
  (β : PseudonatTrans G G′) 
  (γ : PseudonatTrans H H′) 
  where

  open Bicategory GpdEndoBicat using ()
    renaming (_⋆_ to _⨾_)
  open Bicategory GPD using (id; _◃_; _▹_)
    renaming (str to ⟨GPD⟩; Hom[_,_] to GPD[_,_])
  
  private
    module F = Copresheaf F
    module G = Copresheaf G
    module H = Copresheaf H
    module F′ = Copresheaf F′
    module G′ = Copresheaf G′
    module H′ = Copresheaf H′

  open F using (F₀; F₁; F₂)
  open G using () renaming (F₀ to G₀; F₁ to G₁; F₂ to G₂)
  open H using () renaming (F₀ to H₀; F₁ to H₁; F₂ to H₂)
  open F′ using () renaming (F₀ to F′₀; F₁ to F′₁; F₂ to F′₂)
  open G′ using () renaming (F₀ to G′₀; F₁ to G′₁; F₂ to G′₂)
  open H′ using () renaming (F₀ to H′₀; F₁ to H′₁; F₂ to H′₂)

  open WildNatTrans (α .fst) using ()
    renaming (N-ob to α₀; N-hom to α□)
  open WildNatTrans (β .fst) using ()
    renaming (N-ob to β₀; N-hom to β□)
  open WildNatTrans (γ .fst) using ()
    renaming (N-ob to γ₀; N-hom to γ□)

  open import Prelude

  private
    asc₀ = iMG-assoc-ob

  open 2CellLaws ⟨GPD⟩

  iMG-assoc-hom : (α ⊗₁ (β ⊗₁ γ)) ⨾ asc₀ F′ G′ H′ 
    ≡ asc₀ F G H ⨾ ((α ⊗₁ β) ⊗₁ γ)
  iMG-assoc-hom = PseudonatTrans≡ $ makeNatTransPath
    (funExt λ X → 
      cong (_» γ₀ (G′₀ (F′₀ X))) 
        (sym (H.F-seq (G₁ (α₀ X)) (β₀ (F′₀ X)))))  
    λ f → aux f
    where
    aux : 
      ∀ {X Y} (f : GPD[ X , Y ])
      → Square {! !} {!  !} {! !} {! !}
    aux f = {! !}


module _ (F G H : GpdEndo) where
  open WildNatTrans
  open IsPseudonat
  open wildIsIso

  private 
    module F = Copresheaf F
    module G = Copresheaf G
    module H = Copresheaf H
 
  iMG-assoc-isIs : wildIsIso {C = GpdEndoWildCat}
    (iMG-assoc-ob F G H)
  iMG-assoc-isIs .inv' .fst .N-ob _        = idfun _
  iMG-assoc-isIs .inv' .fst .N-hom _       = refl
  iMG-assoc-isIs .inv' .snd .N-hom-id      = {! !}
  iMG-assoc-isIs .inv' .snd .N-hom-seq f g = {! !}
  iMG-assoc-isIs .sect = PseudonatTrans≡ $ makeNatTransPath
    {! !}
    {! !}
  iMG-assoc-isIs .retr = PseudonatTrans≡ $ makeNatTransPath
    {! !}
    {! !}

open WildNatIso
open WildNatTrans
open wildIsIso

iMG-assoc : WildNatIso _ _ (assocₗ compEndo) (assocᵣ compEndo)
iMG-assoc .trans .N-ob (F , G , H) = iMG-assoc-ob F G H
iMG-assoc .trans .N-hom (α , β , γ) = iMG-assoc-hom α β γ
iMG-assoc .isIs (F , G , H) = iMG-assoc-isIs F G H
