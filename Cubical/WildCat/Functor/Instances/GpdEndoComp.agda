open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.WildCat.Product
open import Cubical.WildCat.Functor
open import Cubical.WildCat.Instances.GpdEndo renaming (GpdEndo to GpdEndoC)

open import Cubical.LU2C.GpdEndo.Constructions.Comp0 {ℓ-zero}
open import Cubical.LU2C.GpdEndo.Constructions.Comp1
open import Cubical.LU2C.GpdEndo.Base
open import Cubical.LU2C.GpdEndo.NatTrans.Base

module Cubical.WildCat.Functor.Instances.GpdEndoComp where

open import Cubical.LU2C.Base
open import Cubical.LU2C.Instances.Groupoids ℓ-zero

open WildFunctor

open LU2C HGpd using () renaming (str to ⟨HGpd⟩)
open import Cubical.Foundations.Path
open import Cubical.Foundations.GroupoidLaws
open import Prelude.ExtraGpdLaws
open import Reflection.Reassoc
open import Cubical.WildCat.AsLU2C.Instances
open NotHGpd

import Cubical.WildCat.Functor.Instances.GpdEndoComp.Coherence as Coherence

-- BEGIN VIBE
-- TODO: check vibe
compWild : WildFunctor (GpdEndoC × GpdEndoC) GpdEndoC
compWild .F-ob = uncurry _⨾₀_
compWild .F-hom {F , G} {F′ , G′} = uncurry (_⨾₁_ {F = F} {F′} {G} {G′})
compWild .F-id {F , G} = GpdEndoTrans≡ {F = F ⨾₀ G} {G = F ⨾₀ G}
  (funExt λ x → G.F-id)
  λ f → compPath→Square (goal f)
  where
  module F = GpdEndo F
  module G = GpdEndo G
  open F using (F₀; F₁; F₂)
  open G using () renaming
    ( F₀ to G₀
    ; F₁ to G₁
    ; F₂ to G₂
    )
  -- TODO: check vibe
  goal : ∀ {x y} (f : HGpd [ x , y ]) → _
  goal f =
    G₁ (F₁ f) ◃ G.F-id ∙ refl
      ≡⟨ ∙r G.F-IdR (F₁ f) ⟩
    sym (G.F-seq (F₁ f) id) ∙ refl
      ≡⟨ ∙l sym (rCancel (G.F-seq id (F₁ f))) ⟩
    sym (G.F-seq (F₁ f) id)
    ∙ G.F-seq id (F₁ f)
    ∙ sym (G.F-seq id (F₁ f))
      ≡⟨ ∙l ∙l sym (G.F-IdL (F₁ f)) ⟩
    sym (G.F-seq (F₁ f) id)
    ∙ G.F-seq id (F₁ f)
    ∙ G.F-id ▹ G₁ (F₁ f)
      ≡⟨ reassoc! ⟩
    ((sym (G.F-seq (F₁ f) id)
      ∙ refl ∙ G.F-seq id (F₁ f)) ∙ refl)
    ∙ G.F-id ▹ G₁ (F₁ f)
      ∎
compWild .F-seq {F , G} {F′ , G′} {F″ , G″} (α , β) (α′ , β′) =
  GpdEndoTrans≡ {F = F ⨾₀ G} {G = F″ ⨾₀ G″}
    (funExt Comp.component) λ f → compPath→Square (sym (Comp.goal f))
  where
  module Comp = Coherence.CompSeq {F} {F′} {F″} {G} {G′} {G″} α β α′ β′
  -- See notepad
-- END VIBE
