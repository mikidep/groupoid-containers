-- BEGIN VIBE
open import Cubical.Foundations.Prelude

open import Cubical.LU2C.GpdEndo.Base
open import Cubical.LU2C.GpdEndo.NatTrans.Base

module Cubical.WildCat.Functor.Instances.GpdEndoComp.Coherence.Pasting where

open import Cubical.LU2C.Base
open import Cubical.LU2C.Instances.Groupoids ℓ-zero

open import Cubical.Foundations.GroupoidLaws
open import Prelude.ExtraGpdLaws
open import Prelude.Reassoc
open import Cubical.WildCat.AsLU2C.Instances
open NotHGpd

-- Paste the two naturality squares, then compare their images under G.
--
-- a₀ ───── top ─────→ a₁
-- │ upper₀           │ upper₁
-- b₀ ──── middle ───→ b₁
-- │ lower₀           │ lower₁
-- c₀ ───── bottom ──→ c₁

private
  module Interchange {G G′ : GpdEndo {ℓ = ℓ-zero}}
    (β : GpdEndoTrans G G′)
    {a₀ b₀ c₀ a₁ b₁ c₁ : LU2C.ob HGpd}
    (top : HGpd [ a₀ , a₁ ]) (middle : HGpd [ b₀ , b₁ ])
    (bottom : HGpd [ c₀ , c₁ ])
    (upper₀ : HGpd [ a₀ , b₀ ]) (lower₀ : HGpd [ b₀ , c₀ ])
    (upper₁ : HGpd [ a₁ , b₁ ]) (lower₁ : HGpd [ b₁ , c₁ ])
    (upper-square : top ⋆ upper₁ ≡ upper₀ ⋆ middle)
    (lower-square : middle ⋆ lower₁ ≡ lower₀ ⋆ bottom) where

    module G = GpdEndo G
    module G′ = GpdEndo G′
    module β = GpdEndoTrans {F = G} {G′} β
    open G using () renaming (F₁ to G₁; F₂ to G₂)
    open G′ using () renaming (F₁ to G′₁; F₂ to G′₂)
    open β using () renaming (N-ob to β₀; N-hom to β□)
    open import Cubical.WildCat.AsLU2C.NaturalTransformation.Properties
      {F = G.str} {G = G′.str} using (N-hom-nat)

    -- Move G's comparison past β's naturality square.
    interchange₁ :
        (sym (G.F-seq top (upper₁ ⋆ lower₁)) ▹ β₀ c₁
          ∙ G₂ (upper-square ▹ lower₁ ∙ upper₀ ◃ lower-square) ▹ β₀ c₁
          ∙ G.F-seq (upper₀ ⋆ lower₀) bottom ▹ β₀ c₁
          ∙ G₁ (upper₀ ⋆ lower₀) ◃ β□ bottom)
        ∙ (G.F-seq upper₀ lower₀ ▹ β₀ c₀ ∙ G₁ upper₀ ◃ β□ lower₀) ▹ G′₁ bottom
      ≡ sym (G.F-seq top (upper₁ ⋆ lower₁)) ▹ β₀ c₁
        ∙ G₂ (upper-square ▹ lower₁) ▹ β₀ c₁
        ∙ (G.F-seq upper₀ (middle ⋆ lower₁) ∙ G₁ upper₀ ◃ G₂ lower-square) ▹ β₀ c₁
        ∙ G₁ upper₀ ◃ β□ (lower₀ ⋆ bottom)
        ∙ G₁ upper₀ ◃ β₀ b₀ ◃ G′.F-seq lower₀ bottom
    interchange₁ =
      (sym (G.F-seq top (upper₁ ⋆ lower₁)) ▹ β₀ c₁
        ∙ G₂ (upper-square ▹ lower₁ ∙ upper₀ ◃ lower-square) ▹ β₀ c₁
        ∙ G.F-seq (upper₀ ⋆ lower₀) bottom ▹ β₀ c₁
        ∙ G₁ (upper₀ ⋆ lower₀) ◃ β□ bottom)
      ∙ (G.F-seq upper₀ lower₀ ▹ β₀ c₀ ∙ G₁ upper₀ ◃ β□ lower₀) ▹ G′₁ bottom
        ≡⟨ reass₁ ⟩
      sym (G.F-seq top (upper₁ ⋆ lower₁)) ▹ β₀ c₁
      ∙ G₂ (upper-square ▹ lower₁) ▹ β₀ c₁
      ∙ G₂ (upper₀ ◃ lower-square) ▹ β₀ c₁
      ∙ G.F-seq (upper₀ ⋆ lower₀) bottom ▹ β₀ c₁
      ∙ (G₁ (upper₀ ⋆ lower₀) ◃ β□ bottom ∙ G.F-seq upper₀ lower₀ ▹ β₀ c₀ ▹ G′₁ bottom)
      ∙ G₁ upper₀ ◃ β□ lower₀ ▹ G′₁ bottom
        ≡⟨ ∙l ∙l ∙l ∙l ∙r whisk-interchange (G.F-seq upper₀ lower₀) (β□ bottom) ⟩
      sym (G.F-seq top (upper₁ ⋆ lower₁)) ▹ β₀ c₁
      ∙ G₂ (upper-square ▹ lower₁) ▹ β₀ c₁
      ∙ G₂ (upper₀ ◃ lower-square) ▹ β₀ c₁
      ∙ G.F-seq (upper₀ ⋆ lower₀) bottom ▹ β₀ c₁
      ∙ (G.F-seq upper₀ lower₀ ▹ G₁ bottom ▹ β₀ c₁ ∙ G₁ upper₀ ◃ G₁ lower₀ ◃ β□ bottom)
      ∙ G₁ upper₀ ◃ β□ lower₀ ▹ G′₁ bottom
        ≡⟨ ∙l ∙l ∙l reass₂ ⟩
      sym (G.F-seq top (upper₁ ⋆ lower₁)) ▹ β₀ c₁
      ∙ G₂ (upper-square ▹ lower₁) ▹ β₀ c₁
      ∙ G₂ (upper₀ ◃ lower-square) ▹ β₀ c₁
      ∙ (G.F-seq (upper₀ ⋆ lower₀) bottom ∙ G.F-seq upper₀ lower₀ ▹ G₁ bottom) ▹ β₀ c₁
      ∙ G₁ upper₀ ◃ (G₁ lower₀ ◃ β□ bottom ∙ β□ lower₀ ▹ G′₁ bottom)
        ≡⟨ ∙l ∙l ∙l ∙r cong (_▹ β₀ c₁) (G.F-Assoc-comp {x = a₀} {b₀} {c₀} {c₁} upper₀ lower₀ bottom) ⟩
      sym (G.F-seq top (upper₁ ⋆ lower₁)) ▹ β₀ c₁
      ∙ G₂ (upper-square ▹ lower₁) ▹ β₀ c₁
      ∙ G₂ (upper₀ ◃ lower-square) ▹ β₀ c₁
      ∙ (G.F-seq upper₀ (lower₀ ⋆ bottom) ∙ G₁ upper₀ ◃ G.F-seq lower₀ bottom) ▹ β₀ c₁
      ∙ G₁ upper₀ ◃ (G₁ lower₀ ◃ β□ bottom ∙ β□ lower₀ ▹ G′₁ bottom)
        ≡⟨ ∙l ∙l ∙l reass₃ ⟩
      sym (G.F-seq top (upper₁ ⋆ lower₁)) ▹ β₀ c₁
      ∙ G₂ (upper-square ▹ lower₁) ▹ β₀ c₁
      ∙ G₂ (upper₀ ◃ lower-square) ▹ β₀ c₁
      ∙ G.F-seq upper₀ (lower₀ ⋆ bottom) ▹ β₀ c₁
      ∙ G₁ upper₀ ◃ (G.F-seq lower₀ bottom ▹ β₀ c₁ ∙ G₁ lower₀ ◃ β□ bottom ∙ β□ lower₀ ▹ G′₁ bottom)
        ≡⟨ ∙l ∙l ∙l ∙l cong (G₁ upper₀ ◃_) (sym (β.N-hom-seq {x = b₀} {c₀} {c₁} lower₀ bottom)) ⟩
      sym (G.F-seq top (upper₁ ⋆ lower₁)) ▹ β₀ c₁
      ∙ G₂ (upper-square ▹ lower₁) ▹ β₀ c₁
      ∙ G₂ (upper₀ ◃ lower-square) ▹ β₀ c₁
      ∙ G.F-seq upper₀ (lower₀ ⋆ bottom) ▹ β₀ c₁
      ∙ G₁ upper₀ ◃ (β□ (lower₀ ⋆ bottom) ∙ β₀ b₀ ◃ G′.F-seq lower₀ bottom)
        ≡⟨ ∙l ∙l reass₄ ⟩
      sym (G.F-seq top (upper₁ ⋆ lower₁)) ▹ β₀ c₁
      ∙ G₂ (upper-square ▹ lower₁) ▹ β₀ c₁
      ∙ (G₂ (upper₀ ◃ lower-square) ∙ G.F-seq upper₀ (lower₀ ⋆ bottom)) ▹ β₀ c₁
      ∙ G₁ upper₀ ◃ β□ (lower₀ ⋆ bottom)
      ∙ G₁ upper₀ ◃ β₀ b₀ ◃ G′.F-seq lower₀ bottom
        ≡⟨ ∙l ∙l ∙r cong (_▹ β₀ c₁) (sym (G.F-seq-nat {x = a₀} {b₀} {c₁} refl lower-square)) ⟩
      sym (G.F-seq top (upper₁ ⋆ lower₁)) ▹ β₀ c₁
      ∙ G₂ (upper-square ▹ lower₁) ▹ β₀ c₁
      ∙ (G.F-seq upper₀ (middle ⋆ lower₁) ∙ G₁ upper₀ ◃ G₂ lower-square) ▹ β₀ c₁
      ∙ G₁ upper₀ ◃ β□ (lower₀ ⋆ bottom)
      ∙ G₁ upper₀ ◃ β₀ b₀ ◃ G′.F-seq lower₀ bottom
        ∎
      where
      -- Elaborate the quoted terms separately before comparing their normal forms.
      reass₁ = reassoc source target refl
        where
        source =
          (↑ (sym (G.F-seq top (upper₁ ⋆ lower₁)) ▹ β₀ c₁)
            ∙′ cong′ G₁ (↑ (upper-square ▹ lower₁) ∙′ ↑ (upper₀ ◃ lower-square)) ▹′ β₀ c₁
            ∙′ ↑ (G.F-seq (upper₀ ⋆ lower₀) bottom ▹ β₀ c₁)
            ∙′ ↑ (G₁ (upper₀ ⋆ lower₀) ◃ β□ bottom))
          ∙′ (↑ (G.F-seq upper₀ lower₀ ▹ β₀ c₀) ∙′ ↑ (G₁ upper₀ ◃ β□ lower₀)) ▹′ G′₁ bottom
        target =
          ↑ (sym (G.F-seq top (upper₁ ⋆ lower₁)) ▹ β₀ c₁)
          ∙′ ↑ (G₂ (upper-square ▹ lower₁) ▹ β₀ c₁)
          ∙′ ↑ (G₂ (upper₀ ◃ lower-square) ▹ β₀ c₁)
          ∙′ ↑ (G.F-seq (upper₀ ⋆ lower₀) bottom ▹ β₀ c₁)
          ∙′ (↑ (G₁ (upper₀ ⋆ lower₀) ◃ β□ bottom) ∙′ ↑ (G.F-seq upper₀ lower₀ ▹ β₀ c₀ ▹ G′₁ bottom))
          ∙′ ↑ (G₁ upper₀ ◃ β□ lower₀ ▹ G′₁ bottom)
      reass₂ = reassoc source target refl
        where
        source =
          ↑ (G.F-seq (upper₀ ⋆ lower₀) bottom ▹ β₀ c₁)
          ∙′ (↑ (G.F-seq upper₀ lower₀ ▹ G₁ bottom ▹ β₀ c₁)
              ∙′ ↑ (G₁ upper₀ ◃ G₁ lower₀ ◃ β□ bottom))
          ∙′ ↑ (G₁ upper₀ ◃ β□ lower₀ ▹ G′₁ bottom)
        target =
          (↑ (G.F-seq (upper₀ ⋆ lower₀) bottom) ∙′ ↑ (G.F-seq upper₀ lower₀ ▹ G₁ bottom)) ▹′ β₀ c₁
          ∙′ G₁ upper₀ ◃′ (↑ (G₁ lower₀ ◃ β□ bottom) ∙′ ↑ (β□ lower₀ ▹ G′₁ bottom))
      reass₃ = reassoc source target refl
        where
        source =
          (↑ (G.F-seq upper₀ (lower₀ ⋆ bottom)) ∙′ ↑ (G₁ upper₀ ◃ G.F-seq lower₀ bottom)) ▹′ β₀ c₁
          ∙′ G₁ upper₀ ◃′ (↑ (G₁ lower₀ ◃ β□ bottom) ∙′ ↑ (β□ lower₀ ▹ G′₁ bottom))
        target =
          ↑ (G.F-seq upper₀ (lower₀ ⋆ bottom) ▹ β₀ c₁)
          ∙′ G₁ upper₀ ◃′ (↑ (G.F-seq lower₀ bottom ▹ β₀ c₁)
                ∙′ ↑ (G₁ lower₀ ◃ β□ bottom)
                ∙′ ↑ (β□ lower₀ ▹ G′₁ bottom))
      reass₄ = reassoc source target refl
        where
        source =
          ↑ (G₂ (upper₀ ◃ lower-square) ▹ β₀ c₁)
          ∙′ ↑ (G.F-seq upper₀ (lower₀ ⋆ bottom) ▹ β₀ c₁)
          ∙′ G₁ upper₀ ◃′ (↑ (β□ (lower₀ ⋆ bottom)) ∙′ ↑ (β₀ b₀ ◃ G′.F-seq lower₀ bottom))
        target =
          (↑ (G₂ (upper₀ ◃ lower-square)) ∙′ ↑ (G.F-seq upper₀ (lower₀ ⋆ bottom))) ▹′ β₀ c₁
          ∙′ ↑ (G₁ upper₀ ◃ β□ (lower₀ ⋆ bottom))
          ∙′ ↑ (G₁ upper₀ ◃ β₀ b₀ ◃ G′.F-seq lower₀ bottom)

    -- Apply naturality in the lower square and split β's composite square.
    interchange₂ :
        sym (G.F-seq top (upper₁ ⋆ lower₁)) ▹ β₀ c₁
        ∙ G₂ (upper-square ▹ lower₁) ▹ β₀ c₁
        ∙ (G.F-seq upper₀ (middle ⋆ lower₁) ∙ G₁ upper₀ ◃ G₂ lower-square) ▹ β₀ c₁
        ∙ G₁ upper₀ ◃ β□ (lower₀ ⋆ bottom)
        ∙ G₁ upper₀ ◃ β₀ b₀ ◃ G′.F-seq lower₀ bottom
      ≡ sym (G.F-seq top (upper₁ ⋆ lower₁)) ▹ β₀ c₁
        ∙ G₂ (upper-square ▹ lower₁) ▹ β₀ c₁
        ∙ (G.F-seq (upper₀ ⋆ middle) lower₁ ∙ G.F-seq upper₀ middle ▹ G₁ lower₁) ▹ β₀ c₁
        ∙ G₁ upper₀ ◃ G₁ middle ◃ β□ lower₁
        ∙ G₁ upper₀ ◃ β□ middle ▹ G′₁ lower₁
        ∙ G₁ upper₀ ◃ β₀ b₀ ◃ sym (G′.F-seq middle lower₁)
        ∙ G₁ upper₀ ◃ β₀ b₀ ◃ G′₂ lower-square
        ∙ G₁ upper₀ ◃ β₀ b₀ ◃ G′.F-seq lower₀ bottom
    interchange₂ =
      sym (G.F-seq top (upper₁ ⋆ lower₁)) ▹ β₀ c₁
      ∙ G₂ (upper-square ▹ lower₁) ▹ β₀ c₁
      ∙ (G.F-seq upper₀ (middle ⋆ lower₁) ∙ G₁ upper₀ ◃ G₂ lower-square) ▹ β₀ c₁
      ∙ G₁ upper₀ ◃ β□ (lower₀ ⋆ bottom)
      ∙ G₁ upper₀ ◃ β₀ b₀ ◃ G′.F-seq lower₀ bottom
        ≡⟨ ∙l ∙l reass₁ ⟩
      sym (G.F-seq top (upper₁ ⋆ lower₁)) ▹ β₀ c₁
      ∙ G₂ (upper-square ▹ lower₁) ▹ β₀ c₁
      ∙ G.F-seq upper₀ (middle ⋆ lower₁) ▹ β₀ c₁
      ∙ G₁ upper₀ ◃ (G₂ lower-square ▹ β₀ c₁ ∙ β□ (lower₀ ⋆ bottom))
      ∙ G₁ upper₀ ◃ β₀ b₀ ◃ G′.F-seq lower₀ bottom
        ≡⟨ ∙l ∙l ∙l ∙r cong (G₁ upper₀ ◃_) (sym (N-hom-nat β.str {X = b₀} {c₁} lower-square)) ⟩
      sym (G.F-seq top (upper₁ ⋆ lower₁)) ▹ β₀ c₁
      ∙ G₂ (upper-square ▹ lower₁) ▹ β₀ c₁
      ∙ G.F-seq upper₀ (middle ⋆ lower₁) ▹ β₀ c₁
      ∙ G₁ upper₀ ◃ (β□ (middle ⋆ lower₁) ∙ β₀ b₀ ◃ G′₂ lower-square)
      ∙ G₁ upper₀ ◃ β₀ b₀ ◃ G′.F-seq lower₀ bottom
        ≡⟨ ∙l ∙l ∙l reass₂ ⟩
      sym (G.F-seq top (upper₁ ⋆ lower₁)) ▹ β₀ c₁
      ∙ G₂ (upper-square ▹ lower₁) ▹ β₀ c₁
      ∙ G.F-seq upper₀ (middle ⋆ lower₁) ▹ β₀ c₁
      ∙ G₁ upper₀ ◃ β□ (middle ⋆ lower₁)
      ∙ G₁ upper₀ ◃ β₀ b₀ ◃ G′₂ lower-square
      ∙ G₁ upper₀ ◃ β₀ b₀ ◃ G′.F-seq lower₀ bottom
        ≡⟨ ∙l ∙l ∙l ∙r cong (G₁ upper₀ ◃_) (shuffleSymR (β.N-hom-seq {x = b₀} {b₁} {c₁} middle lower₁)) ⟩
      sym (G.F-seq top (upper₁ ⋆ lower₁)) ▹ β₀ c₁
      ∙ G₂ (upper-square ▹ lower₁) ▹ β₀ c₁
      ∙ G.F-seq upper₀ (middle ⋆ lower₁) ▹ β₀ c₁
      ∙ G₁ upper₀ ◃ ((G.F-seq middle lower₁ ▹ β₀ c₁ ∙ G₁ middle ◃ β□ lower₁ ∙ β□ middle ▹ G′₁ lower₁)
            ∙ sym (β₀ b₀ ◃ (G′.F-seq middle lower₁)))
      ∙ G₁ upper₀ ◃ β₀ b₀ ◃ G′₂ lower-square
      ∙ G₁ upper₀ ◃ β₀ b₀ ◃ G′.F-seq lower₀ bottom
        ≡⟨ ∙l ∙l reass₃ ⟩
      sym (G.F-seq top (upper₁ ⋆ lower₁)) ▹ β₀ c₁
      ∙ G₂ (upper-square ▹ lower₁) ▹ β₀ c₁
      ∙ (G.F-seq upper₀ (middle ⋆ lower₁) ∙ G₁ upper₀ ◃ G.F-seq middle lower₁) ▹ β₀ c₁
      ∙ G₁ upper₀ ◃ G₁ middle ◃ β□ lower₁
      ∙ G₁ upper₀ ◃ β□ middle ▹ G′₁ lower₁
      ∙ G₁ upper₀ ◃ β₀ b₀ ◃ sym (G′.F-seq middle lower₁)
      ∙ G₁ upper₀ ◃ β₀ b₀ ◃ G′₂ lower-square
      ∙ G₁ upper₀ ◃ β₀ b₀ ◃ G′.F-seq lower₀ bottom
        ≡⟨ ∙l ∙l ∙r cong (_▹ β₀ c₁) (sym (G.F-Assoc-comp {x = a₀} {b₀} {b₁} {c₁} upper₀ middle lower₁)) ⟩
      sym (G.F-seq top (upper₁ ⋆ lower₁)) ▹ β₀ c₁
      ∙ G₂ (upper-square ▹ lower₁) ▹ β₀ c₁
      ∙ (G.F-seq (upper₀ ⋆ middle) lower₁ ∙ G.F-seq upper₀ middle ▹ G₁ lower₁) ▹ β₀ c₁
      ∙ G₁ upper₀ ◃ G₁ middle ◃ β□ lower₁
      ∙ G₁ upper₀ ◃ β□ middle ▹ G′₁ lower₁
      ∙ G₁ upper₀ ◃ β₀ b₀ ◃ sym (G′.F-seq middle lower₁)
      ∙ G₁ upper₀ ◃ β₀ b₀ ◃ G′₂ lower-square
      ∙ G₁ upper₀ ◃ β₀ b₀ ◃ G′.F-seq lower₀ bottom
        ∎
      where
      reass₁ = reassoc source target refl
        where
        source =
          (↑ (G.F-seq upper₀ (middle ⋆ lower₁)) ∙′ ↑ (G₁ upper₀ ◃ G₂ lower-square)) ▹′ β₀ c₁
          ∙′ ↑ (G₁ upper₀ ◃ β□ (lower₀ ⋆ bottom))
          ∙′ ↑ (G₁ upper₀ ◃ β₀ b₀ ◃ G′.F-seq lower₀ bottom)
        target =
          ↑ (G.F-seq upper₀ (middle ⋆ lower₁) ▹ β₀ c₁)
          ∙′ G₁ upper₀ ◃′ (↑ (G₂ lower-square ▹ β₀ c₁) ∙′ ↑ (β□ (lower₀ ⋆ bottom)))
          ∙′ ↑ (G₁ upper₀ ◃ β₀ b₀ ◃ G′.F-seq lower₀ bottom)
      reass₂ = reassoc source target refl
        where
        source =
          G₁ upper₀ ◃′ (↑ (β□ (middle ⋆ lower₁)) ∙′ ↑ (β₀ b₀ ◃ G′₂ lower-square))
          ∙′ ↑ (G₁ upper₀ ◃ β₀ b₀ ◃ G′.F-seq lower₀ bottom)
        target =
          ↑ (G₁ upper₀ ◃ β□ (middle ⋆ lower₁))
          ∙′ ↑ (G₁ upper₀ ◃ β₀ b₀ ◃ G′₂ lower-square)
          ∙′ ↑ (G₁ upper₀ ◃ β₀ b₀ ◃ G′.F-seq lower₀ bottom)
      reass₃ = reassoc source target refl
        where
        source =
          ↑ (G.F-seq upper₀ (middle ⋆ lower₁) ▹ β₀ c₁)
          ∙′ G₁ upper₀ ◃′ ((↑ (G.F-seq middle lower₁ ▹ β₀ c₁)
                  ∙′ ↑ (G₁ middle ◃ β□ lower₁)
                  ∙′ ↑ (β□ middle ▹ G′₁ lower₁))
                ∙′ ↑ (sym (β₀ b₀ ◃ (G′.F-seq middle lower₁))))
          ∙′ ↑ (G₁ upper₀ ◃ β₀ b₀ ◃ G′₂ lower-square)
          ∙′ ↑ (G₁ upper₀ ◃ β₀ b₀ ◃ G′.F-seq lower₀ bottom)
        target =
          (↑ (G.F-seq upper₀ (middle ⋆ lower₁)) ∙′ ↑ (G₁ upper₀ ◃ G.F-seq middle lower₁)) ▹′ β₀ c₁
          ∙′ ↑ (G₁ upper₀ ◃ G₁ middle ◃ β□ lower₁)
          ∙′ ↑ (G₁ upper₀ ◃ β□ middle ▹ G′₁ lower₁)
          ∙′ ↑ (G₁ upper₀ ◃ β₀ b₀ ◃ sym (G′.F-seq middle lower₁))
          ∙′ ↑ (G₁ upper₀ ◃ β₀ b₀ ◃ G′₂ lower-square)
          ∙′ ↑ (G₁ upper₀ ◃ β₀ b₀ ◃ G′.F-seq lower₀ bottom)

    -- Use G's associativity and interchange with the upper square.
    interchange₃ :
        sym (G.F-seq top (upper₁ ⋆ lower₁)) ▹ β₀ c₁
        ∙ G₂ (upper-square ▹ lower₁) ▹ β₀ c₁
        ∙ (G.F-seq (upper₀ ⋆ middle) lower₁ ∙ G.F-seq upper₀ middle ▹ G₁ lower₁) ▹ β₀ c₁
        ∙ G₁ upper₀ ◃ G₁ middle ◃ β□ lower₁
        ∙ G₁ upper₀ ◃ β□ middle ▹ G′₁ lower₁
        ∙ G₁ upper₀ ◃ β₀ b₀ ◃ sym (G′.F-seq middle lower₁)
        ∙ G₁ upper₀ ◃ β₀ b₀ ◃ G′₂ lower-square
        ∙ G₁ upper₀ ◃ β₀ b₀ ◃ G′.F-seq lower₀ bottom
      ≡ G₁ top ◃ (G.F-seq upper₁ lower₁ ▹ β₀ c₁ ∙ G₁ upper₁ ◃ β□ lower₁)
        ∙ ((sym (G.F-seq top upper₁) ∙ G₂ upper-square ∙ G.F-seq upper₀ middle) ▹ β₀ b₁
            ∙ G₁ upper₀ ◃ β□ middle) ▹ G′₁ lower₁
        ∙ G₁ upper₀ ◃ β₀ b₀ ◃ (sym (G′.F-seq middle lower₁) ∙ G′₂ lower-square ∙ G′.F-seq lower₀ bottom)
    interchange₃ =
      sym (G.F-seq top (upper₁ ⋆ lower₁)) ▹ β₀ c₁
      ∙ G₂ (upper-square ▹ lower₁) ▹ β₀ c₁
      ∙ (G.F-seq (upper₀ ⋆ middle) lower₁ ∙ G.F-seq upper₀ middle ▹ G₁ lower₁) ▹ β₀ c₁
      ∙ G₁ upper₀ ◃ G₁ middle ◃ β□ lower₁
      ∙ G₁ upper₀ ◃ β□ middle ▹ G′₁ lower₁
      ∙ G₁ upper₀ ◃ β₀ b₀ ◃ sym (G′.F-seq middle lower₁)
      ∙ G₁ upper₀ ◃ β₀ b₀ ◃ G′₂ lower-square
      ∙ G₁ upper₀ ◃ β₀ b₀ ◃ G′.F-seq lower₀ bottom
        ≡⟨ ∙l reass₁ ⟩
      sym (G.F-seq top (upper₁ ⋆ lower₁)) ▹ β₀ c₁
      ∙ (G₂ (upper-square ▹ lower₁) ∙ G.F-seq (upper₀ ⋆ middle) lower₁) ▹ β₀ c₁
      ∙ G.F-seq upper₀ middle ▹ G₁ lower₁ ▹ β₀ c₁
      ∙ G₁ upper₀ ◃ G₁ middle ◃ β□ lower₁
      ∙ G₁ upper₀ ◃ β□ middle ▹ G′₁ lower₁
      ∙ G₁ upper₀ ◃ β₀ b₀ ◃ sym (G′.F-seq middle lower₁)
      ∙ G₁ upper₀ ◃ β₀ b₀ ◃ G′₂ lower-square
      ∙ G₁ upper₀ ◃ β₀ b₀ ◃ G′.F-seq lower₀ bottom
        ≡⟨ ∙l ∙r cong (_▹ β₀ c₁) (sym (G.F-seq-nat {x = a₀} {b₁} {c₁} upper-square refl)) ⟩
      sym (G.F-seq top (upper₁ ⋆ lower₁)) ▹ β₀ c₁
      ∙ (G.F-seq (top ⋆ upper₁) lower₁ ∙ G₂ upper-square ▹ G₁ lower₁) ▹ β₀ c₁
      ∙ G.F-seq upper₀ middle ▹ G₁ lower₁ ▹ β₀ c₁
      ∙ G₁ upper₀ ◃ G₁ middle ◃ β□ lower₁
      ∙ G₁ upper₀ ◃ β□ middle ▹ G′₁ lower₁
      ∙ G₁ upper₀ ◃ β₀ b₀ ◃ sym (G′.F-seq middle lower₁)
      ∙ G₁ upper₀ ◃ β₀ b₀ ◃ G′₂ lower-square
      ∙ G₁ upper₀ ◃ β₀ b₀ ◃ G′.F-seq lower₀ bottom
        ≡⟨ reass₂ ⟩
      (sym (G.F-seq top (upper₁ ⋆ lower₁)) ∙ G.F-seq (top ⋆ upper₁) lower₁) ▹ β₀ c₁
      ∙ G₂ upper-square ▹ G₁ lower₁ ▹ β₀ c₁
      ∙ G.F-seq upper₀ middle ▹ G₁ lower₁ ▹ β₀ c₁
      ∙ G₁ upper₀ ◃ G₁ middle ◃ β□ lower₁
      ∙ G₁ upper₀ ◃ β□ middle ▹ G′₁ lower₁
      ∙ G₁ upper₀ ◃ β₀ b₀ ◃ sym (G′.F-seq middle lower₁)
      ∙ G₁ upper₀ ◃ β₀ b₀ ◃ G′₂ lower-square
      ∙ G₁ upper₀ ◃ β₀ b₀ ◃ G′.F-seq lower₀ bottom
        ≡⟨ ∙r cong (_▹ β₀ c₁)
          (shuffleSymL (shuffleSymR (G.F-Assoc-comp {x = a₀} {a₁} {b₁} {c₁} top upper₁ lower₁)
            ∙ sym (assoc (G.F-seq top (upper₁ ⋆ lower₁))
                (G₁ top ◃ G.F-seq upper₁ lower₁)
                (sym (G.F-seq top upper₁ ▹ G₁ lower₁))))) ⟩
      (G₁ top ◃ G.F-seq upper₁ lower₁ ∙ sym ((G.F-seq top upper₁) ▹ G₁ lower₁)) ▹ β₀ c₁
      ∙ G₂ upper-square ▹ G₁ lower₁ ▹ β₀ c₁
      ∙ G.F-seq upper₀ middle ▹ G₁ lower₁ ▹ β₀ c₁
      ∙ G₁ upper₀ ◃ G₁ middle ◃ β□ lower₁
      ∙ G₁ upper₀ ◃ β□ middle ▹ G′₁ lower₁
      ∙ G₁ upper₀ ◃ β₀ b₀ ◃ sym (G′.F-seq middle lower₁)
      ∙ G₁ upper₀ ◃ β₀ b₀ ◃ G′₂ lower-square
      ∙ G₁ upper₀ ◃ β₀ b₀ ◃ G′.F-seq lower₀ bottom
        ≡⟨ reass₃ ⟩
      G₁ top ◃ G.F-seq upper₁ lower₁ ▹ β₀ c₁
      ∙ ((sym (G.F-seq top upper₁) ∙ G₂ upper-square ∙ G.F-seq upper₀ middle) ▹ G₁ lower₁ ▹ β₀ c₁
          ∙ G₁ upper₀ ◃ G₁ middle ◃ β□ lower₁)
      ∙ G₁ upper₀ ◃ β□ middle ▹ G′₁ lower₁
      ∙ G₁ upper₀ ◃ β₀ b₀ ◃ sym (G′.F-seq middle lower₁)
      ∙ G₁ upper₀ ◃ β₀ b₀ ◃ G′₂ lower-square
      ∙ G₁ upper₀ ◃ β₀ b₀ ◃ G′.F-seq lower₀ bottom
        ≡⟨ ∙l ∙r sym (whisk-interchange (sym (G.F-seq top upper₁) ∙ G₂ upper-square ∙ G.F-seq upper₀ middle) (β□ lower₁)) ⟩
      G₁ top ◃ G.F-seq upper₁ lower₁ ▹ β₀ c₁
      ∙ (G₁ top ◃ G₁ upper₁ ◃ β□ lower₁
          ∙ (sym (G.F-seq top upper₁) ∙ G₂ upper-square ∙ G.F-seq upper₀ middle) ▹ β₀ b₁ ▹ G′₁ lower₁)
      ∙ G₁ upper₀ ◃ β□ middle ▹ G′₁ lower₁
      ∙ G₁ upper₀ ◃ β₀ b₀ ◃ sym (G′.F-seq middle lower₁)
      ∙ G₁ upper₀ ◃ β₀ b₀ ◃ G′₂ lower-square
      ∙ G₁ upper₀ ◃ β₀ b₀ ◃ G′.F-seq lower₀ bottom
        ≡⟨ reass₄ ⟩
      G₁ top ◃ (G.F-seq upper₁ lower₁ ▹ β₀ c₁ ∙ G₁ upper₁ ◃ β□ lower₁)
      ∙ ((sym (G.F-seq top upper₁) ∙ G₂ upper-square ∙ G.F-seq upper₀ middle) ▹ β₀ b₁
          ∙ G₁ upper₀ ◃ β□ middle) ▹ G′₁ lower₁
      ∙ G₁ upper₀ ◃ β₀ b₀ ◃ (sym (G′.F-seq middle lower₁) ∙ G′₂ lower-square ∙ G′.F-seq lower₀ bottom)
        ∎
      where
      reass₁ = reassoc source target refl
        where
        source =
          ↑ (G₂ (upper-square ▹ lower₁) ▹ β₀ c₁)
          ∙′ (↑ (G.F-seq (upper₀ ⋆ middle) lower₁) ∙′ ↑ (G.F-seq upper₀ middle ▹ G₁ lower₁)) ▹′ β₀ c₁
          ∙′ ↑ (G₁ upper₀ ◃ G₁ middle ◃ β□ lower₁)
          ∙′ ↑ (G₁ upper₀ ◃ β□ middle ▹ G′₁ lower₁)
          ∙′ ↑ (G₁ upper₀ ◃ β₀ b₀ ◃ sym (G′.F-seq middle lower₁))
          ∙′ ↑ (G₁ upper₀ ◃ β₀ b₀ ◃ G′₂ lower-square)
          ∙′ ↑ (G₁ upper₀ ◃ β₀ b₀ ◃ G′.F-seq lower₀ bottom)
        target =
          (↑ (G₂ (upper-square ▹ lower₁)) ∙′ ↑ (G.F-seq (upper₀ ⋆ middle) lower₁)) ▹′ β₀ c₁
          ∙′ ↑ (G.F-seq upper₀ middle ▹ G₁ lower₁ ▹ β₀ c₁)
          ∙′ ↑ (G₁ upper₀ ◃ G₁ middle ◃ β□ lower₁)
          ∙′ ↑ (G₁ upper₀ ◃ β□ middle ▹ G′₁ lower₁)
          ∙′ ↑ (G₁ upper₀ ◃ β₀ b₀ ◃ sym (G′.F-seq middle lower₁))
          ∙′ ↑ (G₁ upper₀ ◃ β₀ b₀ ◃ G′₂ lower-square)
          ∙′ ↑ (G₁ upper₀ ◃ β₀ b₀ ◃ G′.F-seq lower₀ bottom)
      reass₂ = reassoc source target refl
        where
        source =
          ↑ (sym (G.F-seq top (upper₁ ⋆ lower₁)) ▹ β₀ c₁)
          ∙′ (↑ (G.F-seq (top ⋆ upper₁) lower₁) ∙′ ↑ (G₂ upper-square ▹ G₁ lower₁)) ▹′ β₀ c₁
          ∙′ ↑ (G.F-seq upper₀ middle ▹ G₁ lower₁ ▹ β₀ c₁)
          ∙′ ↑ (G₁ upper₀ ◃ G₁ middle ◃ β□ lower₁)
          ∙′ ↑ (G₁ upper₀ ◃ β□ middle ▹ G′₁ lower₁)
          ∙′ ↑ (G₁ upper₀ ◃ β₀ b₀ ◃ sym (G′.F-seq middle lower₁))
          ∙′ ↑ (G₁ upper₀ ◃ β₀ b₀ ◃ G′₂ lower-square)
          ∙′ ↑ (G₁ upper₀ ◃ β₀ b₀ ◃ G′.F-seq lower₀ bottom)
        target =
          (↑ (sym (G.F-seq top (upper₁ ⋆ lower₁))) ∙′ ↑ (G.F-seq (top ⋆ upper₁) lower₁)) ▹′ β₀ c₁
          ∙′ ↑ (G₂ upper-square ▹ G₁ lower₁ ▹ β₀ c₁)
          ∙′ ↑ (G.F-seq upper₀ middle ▹ G₁ lower₁ ▹ β₀ c₁)
          ∙′ ↑ (G₁ upper₀ ◃ G₁ middle ◃ β□ lower₁)
          ∙′ ↑ (G₁ upper₀ ◃ β□ middle ▹ G′₁ lower₁)
          ∙′ ↑ (G₁ upper₀ ◃ β₀ b₀ ◃ sym (G′.F-seq middle lower₁))
          ∙′ ↑ (G₁ upper₀ ◃ β₀ b₀ ◃ G′₂ lower-square)
          ∙′ ↑ (G₁ upper₀ ◃ β₀ b₀ ◃ G′.F-seq lower₀ bottom)
      reass₃ = reassoc source target refl
        where
        source =
          (↑ (G₁ top ◃ G.F-seq upper₁ lower₁) ∙′ ↑ (sym ((G.F-seq top upper₁) ▹ G₁ lower₁))) ▹′ β₀ c₁
          ∙′ ↑ (G₂ upper-square ▹ G₁ lower₁ ▹ β₀ c₁)
          ∙′ ↑ (G.F-seq upper₀ middle ▹ G₁ lower₁ ▹ β₀ c₁)
          ∙′ ↑ (G₁ upper₀ ◃ G₁ middle ◃ β□ lower₁)
          ∙′ ↑ (G₁ upper₀ ◃ β□ middle ▹ G′₁ lower₁)
          ∙′ ↑ (G₁ upper₀ ◃ β₀ b₀ ◃ sym (G′.F-seq middle lower₁))
          ∙′ ↑ (G₁ upper₀ ◃ β₀ b₀ ◃ G′₂ lower-square)
          ∙′ ↑ (G₁ upper₀ ◃ β₀ b₀ ◃ G′.F-seq lower₀ bottom)
        target =
          ↑ (G₁ top ◃ G.F-seq upper₁ lower₁ ▹ β₀ c₁)
          ∙′ ((↑ (sym (G.F-seq top upper₁)) ∙′ ↑ (G₂ upper-square) ∙′ ↑ (G.F-seq upper₀ middle)) ▹′ G₁ lower₁ ▹′ β₀ c₁
              ∙′ ↑ (G₁ upper₀ ◃ G₁ middle ◃ β□ lower₁))
          ∙′ ↑ (G₁ upper₀ ◃ β□ middle ▹ G′₁ lower₁)
          ∙′ ↑ (G₁ upper₀ ◃ β₀ b₀ ◃ sym (G′.F-seq middle lower₁))
          ∙′ ↑ (G₁ upper₀ ◃ β₀ b₀ ◃ G′₂ lower-square)
          ∙′ ↑ (G₁ upper₀ ◃ β₀ b₀ ◃ G′.F-seq lower₀ bottom)
      reass₄ = reassoc source target refl
        where
        source =
          ↑ (G₁ top ◃ G.F-seq upper₁ lower₁ ▹ β₀ c₁)
          ∙′ (↑ (G₁ top ◃ G₁ upper₁ ◃ β□ lower₁)
              ∙′ (↑ (sym (G.F-seq top upper₁)) ∙′ ↑ (G₂ upper-square) ∙′ ↑ (G.F-seq upper₀ middle)) ▹′ β₀ b₁ ▹′ G′₁ lower₁)
          ∙′ ↑ (G₁ upper₀ ◃ β□ middle ▹ G′₁ lower₁)
          ∙′ ↑ (G₁ upper₀ ◃ β₀ b₀ ◃ sym (G′.F-seq middle lower₁))
          ∙′ ↑ (G₁ upper₀ ◃ β₀ b₀ ◃ G′₂ lower-square)
          ∙′ ↑ (G₁ upper₀ ◃ β₀ b₀ ◃ G′.F-seq lower₀ bottom)
        target =
          G₁ top ◃′ (↑ (G.F-seq upper₁ lower₁ ▹ β₀ c₁) ∙′ ↑ (G₁ upper₁ ◃ β□ lower₁))
          ∙′ ((↑ (sym (G.F-seq top upper₁)) ∙′ ↑ (G₂ upper-square) ∙′ ↑ (G.F-seq upper₀ middle)) ▹′ β₀ b₁
              ∙′ ↑ (G₁ upper₀ ◃ β□ middle)) ▹′ G′₁ lower₁
          ∙′ G₁ upper₀ ◃′ β₀ b₀ ◃′ (↑ (sym (G′.F-seq middle lower₁)) ∙′ ↑ (G′₂ lower-square) ∙′ ↑ (G′.F-seq lower₀ bottom))

    interchange :
        (sym (G.F-seq top (upper₁ ⋆ lower₁)) ▹ β₀ c₁
          ∙ G₂ (upper-square ▹ lower₁ ∙ upper₀ ◃ lower-square) ▹ β₀ c₁
          ∙ G.F-seq (upper₀ ⋆ lower₀) bottom ▹ β₀ c₁
          ∙ G₁ (upper₀ ⋆ lower₀) ◃ β□ bottom)
        ∙ (G.F-seq upper₀ lower₀ ▹ β₀ c₀ ∙ G₁ upper₀ ◃ β□ lower₀) ▹ G′₁ bottom
      ≡ G₁ top ◃ (G.F-seq upper₁ lower₁ ▹ β₀ c₁ ∙ G₁ upper₁ ◃ β□ lower₁)
        ∙ ((sym (G.F-seq top upper₁) ∙ G₂ upper-square ∙ G.F-seq upper₀ middle) ▹ β₀ b₁
            ∙ G₁ upper₀ ◃ β□ middle) ▹ G′₁ lower₁
        ∙ G₁ upper₀ ◃ β₀ b₀ ◃ (sym (G′.F-seq middle lower₁) ∙ G′₂ lower-square ∙ G′.F-seq lower₀ bottom)
    interchange = interchange₁ ∙ interchange₂ ∙ interchange₃

-- Also used for the associator's naturality square.
paste-naturality = Interchange.interchange

-- END VIBE
