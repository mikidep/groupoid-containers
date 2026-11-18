open import Cubical.Foundations.Prelude

open import Cubical.LU2C.GpdEndo.Base
open import Cubical.LU2C.GpdEndo.NatTrans.Base

module Cubical.WildCat.Functor.Instances.GpdEndoComp.Coherence where

open import Cubical.LU2C.Base
open import Cubical.LU2C.Instances.Groupoids ℓ-zero

open import Cubical.Foundations.GroupoidLaws
open import Prelude.ExtraGpdLaws
open import Prelude.Reassoc
open import Cubical.WildCat.AsLU2C.Instances
open NotHGpd

-- BEGIN VIBE
open import Cubical.WildCat.Functor.Instances.GpdEndoComp.Coherence.Pasting
  using (paste-naturality) public
-- END VIBE

module CompSeq {F F′ F″ G G′ G″ : GpdEndo}
  (α : GpdEndoTrans F F′) (β : GpdEndoTrans G G′)
  (α′ : GpdEndoTrans F′ F″) (β′ : GpdEndoTrans G′ G″) where
  module F = GpdEndo F
  module F′ = GpdEndo F′
  module F″ = GpdEndo F″
  module G = GpdEndo G
  module G′ = GpdEndo G′
  module G″ = GpdEndo G″
  module α = GpdEndoTrans {F = F} {F′} α
  module α′ = GpdEndoTrans {F = F′} {F″} α′
  module β = GpdEndoTrans {F = G} {G′} β
  module β′ = GpdEndoTrans {F = G′} {G″} β′

  open F using (F₀; F₁)
  open F′ using () renaming (F₀ to F′₀; F₁ to F′₁)
  open F″ using () renaming (F₀ to F″₀; F₁ to F″₁)
  open G using () renaming (F₁ to G₁; F₂ to G₂)
  open G′ using () renaming (F₁ to G′₁; F₂ to G′₂)
  open G″ using () renaming (F₁ to G″₁)
  open α using () renaming (N-ob to α₀; N-hom to α□)
  open α′ using () renaming (N-ob to α′₀; N-hom to α′□)
  open β using () renaming (N-ob to β₀; N-hom to β□)
  open β′ using () renaming (N-ob to β′₀; N-hom to β′□)

  component : ∀ x → _
  component x =
    G.F-seq (α₀ x) (α′₀ x) ▹ β₀ (F″₀ x) ▹ β′₀ (F″₀ x)
    ∙ G₁ (α₀ x) ◃ β□ (α′₀ x) ▹ β′₀ (F″₀ x)

  -- BEGIN VIBE
  -- TODO: check vibe
  goal-β : ∀ {x y} (f : HGpd [ x , y ])
    → (sym (G.F-seq (F₁ f) (α₀ y ⋆ α′₀ y)) ▹ β₀ (F″₀ y)
        ∙ G₂ (α□ f ▹ α′₀ y ∙ α₀ x ◃ α′□ f) ▹ β₀ (F″₀ y)
        ∙ G.F-seq (α₀ x ⋆ α′₀ x) (F″₁ f) ▹ β₀ (F″₀ y)
        ∙ G₁ (α₀ x ⋆ α′₀ x) ◃ β□ (F″₁ f))
      ∙ (G.F-seq (α₀ x) (α′₀ x) ▹ β₀ (F″₀ x) ∙ G₁ (α₀ x) ◃ β□ (α′₀ x)) ▹ G′₁ (F″₁ f)
    ≡ G₁ (F₁ f) ◃ (G.F-seq (α₀ y) (α′₀ y) ▹ β₀ (F″₀ y) ∙ G₁ (α₀ y) ◃ β□ (α′₀ y))
      ∙ ((sym (G.F-seq (F₁ f) (α₀ y)) ∙ G₂ (α□ f) ∙ G.F-seq (α₀ x) (F′₁ f)) ▹ β₀ (F′₀ y)
          ∙ G₁ (α₀ x) ◃ β□ (F′₁ f)) ▹ G′₁ (α′₀ y)
      ∙ G₁ (α₀ x) ◃ β₀ (F′₀ x) ◃ (sym (G′.F-seq (F′₁ f) (α′₀ y)) ∙ G′₂ (α′□ f) ∙ G′.F-seq (α′₀ x) (F″₁ f))
  goal-β {x} {y} f = paste-naturality {G} {G′} β
    {a₀ = F₀ x} {b₀ = F′₀ x} {c₀ = F″₀ x}
    {a₁ = F₀ y} {b₁ = F′₀ y} {c₁ = F″₀ y}
    (F₁ f) (F′₁ f) (F″₁ f)
    (α₀ x) (α′₀ x) (α₀ y) (α′₀ y) (α□ f) (α′□ f)
  -- END VIBE

  -- BEGIN VIBE
  -- TODO: check vibe
  goal : ∀ {x y} (f : HGpd [ x , y ])
    → (G.F□ {f = F₁ f} {g = α₀ y ⋆ α′₀ y}
          {h = α₀ x ⋆ α′₀ x} {k = F″₁ f} (α□ f ▹ α′₀ y ∙ α₀ x ◃ α′□ f) ▹ β₀ (F″₀ y) ▹ β′₀ (F″₀ y)
        ∙ G₁ (α₀ x ⋆ α′₀ x) ◃ (β□ (F″₁ f) ▹ β′₀ (F″₀ y) ∙ β₀ (F″₀ x) ◃ β′□ (F″₁ f)))
      ∙ component x ▹ G″₁ (F″₁ f)
    ≡ G₁ (F₁ f) ◃ component y
      ∙ (G.F□ {f = F₁ f} {g = α₀ y} {h = α₀ x} {k = F′₁ f} (α□ f) ▹ β₀ (F′₀ y)
          ∙ G₁ (α₀ x) ◃ β□ (F′₁ f)) ▹ (G′₁ (α′₀ y) ⋆ β′₀ (F″₀ y))
      ∙ (G₁ (α₀ x) ⋆ β₀ (F′₀ x)) ◃ (G′.F□ {f = F′₁ f} {g = α′₀ y} {h = α′₀ x} {k = F″₁ f} (α′□ f) ▹ β′₀ (F″₀ y)
            ∙ G′₁ (α′₀ x) ◃ β′□ (F″₁ f))
  goal {x} {y} f =
    (G.F□ {f = F₁ f} {g = α₀ y ⋆ α′₀ y}
          {h = α₀ x ⋆ α′₀ x} {k = F″₁ f} (α□ f ▹ α′₀ y ∙ α₀ x ◃ α′□ f) ▹ β₀ (F″₀ y) ▹ β′₀ (F″₀ y)
      ∙ G₁ (α₀ x ⋆ α′₀ x) ◃ (β□ (F″₁ f) ▹ β′₀ (F″₀ y) ∙ β₀ (F″₀ x) ◃ β′□ (F″₁ f)))
    ∙ component x ▹ G″₁ (F″₁ f)
      ≡⟨ reass₁ ⟩
    (sym (G.F-seq (F₁ f) (α₀ y ⋆ α′₀ y)) ▹ β₀ (F″₀ y)
      ∙ G₂ (α□ f ▹ α′₀ y ∙ α₀ x ◃ α′□ f) ▹ β₀ (F″₀ y)
      ∙ G.F-seq (α₀ x ⋆ α′₀ x) (F″₁ f) ▹ β₀ (F″₀ y)
      ∙ G₁ (α₀ x ⋆ α′₀ x) ◃ β□ (F″₁ f)) ▹ β′₀ (F″₀ y)
    ∙ G₁ (α₀ x ⋆ α′₀ x) ◃ β₀ (F″₀ x) ◃ β′□ (F″₁ f)
    ∙ (G.F-seq (α₀ x) (α′₀ x) ▹ β₀ (F″₀ x) ∙ G₁ (α₀ x) ◃ β□ (α′₀ x)) ▹ β′₀ (F″₀ x) ▹ G″₁ (F″₁ f)
      ≡⟨ ∙l whisk-interchange ((G.F-seq (α₀ x) (α′₀ x)) ▹ β₀ (F″₀ x) ∙ G₁ (α₀ x) ◃ (β□ (α′₀ x))) (β′□ (F″₁ f)) ⟩
    (sym (G.F-seq (F₁ f) (α₀ y ⋆ α′₀ y)) ▹ β₀ (F″₀ y)
      ∙ G₂ (α□ f ▹ α′₀ y ∙ α₀ x ◃ α′□ f) ▹ β₀ (F″₀ y)
      ∙ G.F-seq (α₀ x ⋆ α′₀ x) (F″₁ f) ▹ β₀ (F″₀ y)
      ∙ G₁ (α₀ x ⋆ α′₀ x) ◃ β□ (F″₁ f)) ▹ β′₀ (F″₀ y)
    ∙ (G.F-seq (α₀ x) (α′₀ x) ▹ β₀ (F″₀ x) ∙ G₁ (α₀ x) ◃ β□ (α′₀ x)) ▹ G′₁ (F″₁ f) ▹ β′₀ (F″₀ y)
    ∙ G₁ (α₀ x) ◃ β₀ (F′₀ x) ◃ G′₁ (α′₀ x) ◃ β′□ (F″₁ f)
      ≡⟨ reass₂ ⟩
    ((sym (G.F-seq (F₁ f) (α₀ y ⋆ α′₀ y)) ▹ β₀ (F″₀ y)
        ∙ G₂ (α□ f ▹ α′₀ y ∙ α₀ x ◃ α′□ f) ▹ β₀ (F″₀ y)
        ∙ G.F-seq (α₀ x ⋆ α′₀ x) (F″₁ f) ▹ β₀ (F″₀ y)
        ∙ G₁ (α₀ x ⋆ α′₀ x) ◃ β□ (F″₁ f))
      ∙ (G.F-seq (α₀ x) (α′₀ x) ▹ β₀ (F″₀ x) ∙ G₁ (α₀ x) ◃ β□ (α′₀ x)) ▹ G′₁ (F″₁ f)) ▹ β′₀ (F″₀ y)
    ∙ G₁ (α₀ x) ◃ β₀ (F′₀ x) ◃ G′₁ (α′₀ x) ◃ β′□ (F″₁ f)
      ≡⟨ ∙r cong (_▹ β′₀ (F″₀ y)) (goal-β f) ⟩
    (G₁ (F₁ f) ◃ (G.F-seq (α₀ y) (α′₀ y) ▹ β₀ (F″₀ y) ∙ G₁ (α₀ y) ◃ β□ (α′₀ y))
      ∙ ((sym (G.F-seq (F₁ f) (α₀ y)) ∙ G₂ (α□ f) ∙ G.F-seq (α₀ x) (F′₁ f)) ▹ β₀ (F′₀ y)
          ∙ G₁ (α₀ x) ◃ β□ (F′₁ f)) ▹ G′₁ (α′₀ y)
      ∙ G₁ (α₀ x) ◃ β₀ (F′₀ x) ◃ (sym (G′.F-seq (F′₁ f) (α′₀ y)) ∙ G′₂ (α′□ f) ∙ G′.F-seq (α′₀ x) (F″₁ f))) ▹ β′₀ (F″₀ y)
    ∙ G₁ (α₀ x) ◃ β₀ (F′₀ x) ◃ G′₁ (α′₀ x) ◃ β′□ (F″₁ f)
      ≡⟨ reass₃ ⟩
    G₁ (F₁ f) ◃ component y
    ∙ (G.F□ {f = F₁ f} {g = α₀ y} {h = α₀ x} {k = F′₁ f} (α□ f) ▹ β₀ (F′₀ y)
        ∙ G₁ (α₀ x) ◃ β□ (F′₁ f)) ▹ (G′₁ (α′₀ y) ⋆ β′₀ (F″₀ y))
    ∙ (G₁ (α₀ x) ⋆ β₀ (F′₀ x)) ◃ (G′.F□ {f = F′₁ f} {g = α′₀ y} {h = α′₀ x} {k = F″₁ f} (α′□ f) ▹ β′₀ (F″₀ y)
          ∙ G′₁ (α′₀ x) ◃ β′□ (F″₁ f))
      ∎
    where
    -- TODO: check vibe
    reass₁ = reassoc source target refl
      where
      source =
        ((↑ (sym (G.F-seq (F₁ f) (α₀ y ⋆ α′₀ y)))
            ∙′ ↑ (G₂ (α□ f ▹ α′₀ y ∙ α₀ x ◃ α′□ f))
            ∙′ ↑ (G.F-seq (α₀ x ⋆ α′₀ x) (F″₁ f))) ▹′ β₀ (F″₀ y) ▹′ β′₀ (F″₀ y)
          ∙′ G₁ (α₀ x ⋆ α′₀ x) ◃′ (↑ (β□ (F″₁ f) ▹ β′₀ (F″₀ y)) ∙′ ↑ (β₀ (F″₀ x) ◃ β′□ (F″₁ f))))
        ∙′ (↑ (G.F-seq (α₀ x) (α′₀ x) ▹ β₀ (F″₀ x) ▹ β′₀ (F″₀ x))
            ∙′ ↑ (G₁ (α₀ x) ◃ β□ (α′₀ x) ▹ β′₀ (F″₀ x))) ▹′ G″₁ (F″₁ f)
      target =
        (↑ (sym (G.F-seq (F₁ f) (α₀ y ⋆ α′₀ y)) ▹ β₀ (F″₀ y))
          ∙′ ↑ (G₂ (α□ f ▹ α′₀ y ∙ α₀ x ◃ α′□ f)) ▹′ β₀ (F″₀ y)
          ∙′ ↑ (G.F-seq (α₀ x ⋆ α′₀ x) (F″₁ f) ▹ β₀ (F″₀ y))
          ∙′ ↑ (G₁ (α₀ x ⋆ α′₀ x) ◃ β□ (F″₁ f))) ▹′ β′₀ (F″₀ y)
        ∙′ ↑ (G₁ (α₀ x ⋆ α′₀ x) ◃ β₀ (F″₀ x) ◃ β′□ (F″₁ f))
        ∙′ (↑ (G.F-seq (α₀ x) (α′₀ x) ▹ β₀ (F″₀ x)) ∙′ ↑ (G₁ (α₀ x) ◃ β□ (α′₀ x))) ▹′ β′₀ (F″₀ x) ▹′ G″₁ (F″₁ f)
    -- TODO: check vibe
    reass₂ = reassoc source target refl
      where
      source =
        (↑ (sym (G.F-seq (F₁ f) (α₀ y ⋆ α′₀ y)) ▹ β₀ (F″₀ y))
          ∙′ ↑ (G₂ (α□ f ▹ α′₀ y ∙ α₀ x ◃ α′□ f)) ▹′ β₀ (F″₀ y)
          ∙′ ↑ (G.F-seq (α₀ x ⋆ α′₀ x) (F″₁ f) ▹ β₀ (F″₀ y))
          ∙′ ↑ (G₁ (α₀ x ⋆ α′₀ x) ◃ β□ (F″₁ f))) ▹′ β′₀ (F″₀ y)
        ∙′ (↑ (G.F-seq (α₀ x) (α′₀ x) ▹ β₀ (F″₀ x)) ∙′ ↑ (G₁ (α₀ x) ◃ β□ (α′₀ x))) ▹′ G′₁ (F″₁ f) ▹′ β′₀ (F″₀ y)
        ∙′ ↑ (G₁ (α₀ x) ◃ β₀ (F′₀ x) ◃ G′₁ (α′₀ x) ◃ β′□ (F″₁ f))
      target =
        ((↑ (sym (G.F-seq (F₁ f) (α₀ y ⋆ α′₀ y)) ▹ β₀ (F″₀ y))
            ∙′ ↑ (G₂ (α□ f ▹ α′₀ y ∙ α₀ x ◃ α′□ f)) ▹′ β₀ (F″₀ y)
            ∙′ ↑ (G.F-seq (α₀ x ⋆ α′₀ x) (F″₁ f) ▹ β₀ (F″₀ y))
            ∙′ ↑ (G₁ (α₀ x ⋆ α′₀ x) ◃ β□ (F″₁ f)))
          ∙′ (↑ (G.F-seq (α₀ x) (α′₀ x) ▹ β₀ (F″₀ x)) ∙′ ↑ (G₁ (α₀ x) ◃ β□ (α′₀ x))) ▹′ G′₁ (F″₁ f)) ▹′ β′₀ (F″₀ y)
        ∙′ ↑ (G₁ (α₀ x) ◃ β₀ (F′₀ x) ◃ G′₁ (α′₀ x) ◃ β′□ (F″₁ f))
    -- TODO: check vibe
    reass₃ = reassoc source target refl
      where
      source =
        (G₁ (F₁ f) ◃′ (↑ (G.F-seq (α₀ y) (α′₀ y) ▹ β₀ (F″₀ y)) ∙′ ↑ (G₁ (α₀ y) ◃ β□ (α′₀ y)))
          ∙′ ((↑ (sym (G.F-seq (F₁ f) (α₀ y))) ∙′ ↑ (G₂ (α□ f)) ∙′ ↑ (G.F-seq (α₀ x) (F′₁ f))) ▹′ β₀ (F′₀ y)
              ∙′ ↑ (G₁ (α₀ x) ◃ β□ (F′₁ f))) ▹′ G′₁ (α′₀ y)
          ∙′ G₁ (α₀ x) ◃′ β₀ (F′₀ x) ◃′ (↑ (sym (G′.F-seq (F′₁ f) (α′₀ y))) ∙′ ↑ (G′₂ (α′□ f)) ∙′ ↑ (G′.F-seq (α′₀ x) (F″₁ f)))) ▹′ β′₀ (F″₀ y)
        ∙′ ↑ (G₁ (α₀ x) ◃ β₀ (F′₀ x) ◃ G′₁ (α′₀ x) ◃ β′□ (F″₁ f))
      target =
        G₁ (F₁ f) ◃′ (↑ (G.F-seq (α₀ y) (α′₀ y) ▹ β₀ (F″₀ y) ▹ β′₀ (F″₀ y))
            ∙′ ↑ (G₁ (α₀ y) ◃ β□ (α′₀ y) ▹ β′₀ (F″₀ y)))
        ∙′ ((↑ (sym (G.F-seq (F₁ f) (α₀ y)))
              ∙′ ↑ (G₂ (α□ f))
              ∙′ ↑ (G.F-seq (α₀ x) (F′₁ f))) ▹′ β₀ (F′₀ y)
            ∙′ ↑ (G₁ (α₀ x) ◃ β□ (F′₁ f))) ▹′ (G′₁ (α′₀ y) ⋆ β′₀ (F″₀ y))
        ∙′ (G₁ (α₀ x) ⋆ β₀ (F′₀ x)) ◃′ ((↑ (sym (G′.F-seq (F′₁ f) (α′₀ y)))
                ∙′ ↑ (G′₂ (α′□ f))
                ∙′ ↑ (G′.F-seq (α′₀ x) (F″₁ f))) ▹′ β′₀ (F″₀ y)
              ∙′ ↑ (G′₁ (α′₀ x) ◃ β′□ (F″₁ f)))
  -- END VIBE
