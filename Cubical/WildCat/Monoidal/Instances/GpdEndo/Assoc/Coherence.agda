open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Path

module Cubical.WildCat.Monoidal.Instances.GpdEndo.Assoc.Coherence where

open import Cubical.LU2C.Base
open import Cubical.LU2C.Instances.Groupoids ℓ-zero
open import Cubical.LU2C.GpdEndo.Base {ℓ-zero}
open import Cubical.LU2C.GpdEndo.Constructions {ℓ-zero}
open import Cubical.LU2C.GpdEndo.NatTrans.Base {ℓ-zero}
open import Cubical.LU2C.GpdEndo.NatTrans.Constructions {ℓ-zero}
open import Cubical.WildCat.AsLU2C.Instances
open import Prelude.ExtraGpdLaws
open import Prelude.Reassoc
import Cubical.WildCat.Functor.Instances.GpdEndoComp.Coherence as Comp

open NotHGpd

-- Mapping two vertically pasted squares commutes with the comparison maps.
--
--   a0 -------- top --------> a1
--    |                        |
--    | upper0                 | upper1
--    v                        v
--   b0 ------- middle ------> b1
--    |                        |
--    | lower0                 | lower1
--    v                        v
--   c0 ------- bottom ------> c1
--
-- Compare mapping the outer rectangle with pasting the two mapped squares.
-- H.F-seq compares H(upper ; lower) with H(upper) ; H(lower).
-- The square below uses its inverse, from the pasted images to the image
-- of the pasted rectangle.

module Pasting (H : GpdEndo)
  {a₀ b₀ c₀ a₁ b₁ c₁ : LU2C.ob HGpd}
  (top : HGpd [ a₀ , a₁ ]) (middle : HGpd [ b₀ , b₁ ])
  (bottom : HGpd [ c₀ , c₁ ])
  (upper₀ : HGpd [ a₀ , b₀ ]) (lower₀ : HGpd [ b₀ , c₀ ])
  (upper₁ : HGpd [ a₁ , b₁ ]) (lower₁ : HGpd [ b₁ , c₁ ])
  (upper-square : top ⋆ upper₁ ≡ upper₀ ⋆ middle)
  (lower-square : middle ⋆ lower₁ ≡ lower₀ ⋆ bottom) where

  private module H = GpdEndo H
  open H using () renaming (F₁ to H₁; F₂ to H₂)

  upper-image = H.F□ {x = a₀} {a₁} {b₁} {b₀}
    {f = top} {upper₁} {upper₀} {middle} upper-square
  lower-image = H.F□ {x = b₀} {b₁} {c₁} {c₀}
    {f = middle} {lower₁} {lower₀} {bottom} lower-square
  pasted-image = H.F□ {x = a₀} {a₁} {c₁} {c₀}
    {f = top} {upper₁ ⋆ lower₁} {upper₀ ⋆ lower₀} {bottom}
    (upper-square ▹ lower₁ ∙ upper₀ ◃ lower-square)

  -- paste-image equates the following two paths of morphisms H(a0) -> H(c1).
  -- Here H(f) means H₁ f, and ";" is left-to-right composition
  -- (whiskering when one of its arguments is a path).
  --
  --   S0 : H(upper0 ; lower0) -> H(upper0) ; H(lower0)
  --   S1 : H(upper1 ; lower1) -> H(upper1) ; H(lower1)
  --
  -- These are H.F-seq upper₀ lower₀ and H.F-seq upper₁ lower₁.
  --
  --   Map the rectangle, then split:              Split first, then paste the images:
  --
  --   H(top) ; H(upper1 ; lower1)                 H(top) ; H(upper1 ; lower1)
  --                 |                                           |
  --                 | pasted-image                              | H(top) ; S1
  --                 v                                           v
  --   H(upper0 ; lower0) ; H(bottom)              H(top) ; H(upper1) ; H(lower1)
  --                 |                                           |
  --                 | S0 ; H(bottom)                            | upper-image ; H(lower1)
  --                 |                                           v
  --                 |                             H(upper0) ; H(middle) ; H(lower1)
  --                 |                                           | H(upper0) ; lower-image
  --                 v                                           v
  --   H(upper0) ; H(lower0) ; H(bottom)           H(upper0) ; H(lower0) ; H(bottom)
  --
  -- Both routes have exactly the same start and end. The comparison maps
  -- S0 and S1 are essential: the two mapped diagrams alone have different
  -- vertical boundaries.

  paste-image :
      pasted-image ∙ H.F-seq upper₀ lower₀ ▹ H₁ bottom
    ≡ H₁ top ◃ H.F-seq upper₁ lower₁
      ∙ upper-image ▹ H₁ lower₁ ∙ H₁ upper₀ ◃ lower-image
  paste-image =
    pasted-image ∙ H.F-seq upper₀ lower₀ ▹ H₁ bottom
        ≡⟨ reass₁ ⟩
    (sym (H.F-seq top (upper₁ ⋆ lower₁))
      ∙ H₂ (upper-square ▹ lower₁ ∙ upper₀ ◃ lower-square)
      ∙ H.F-seq (upper₀ ⋆ lower₀) bottom ∙ refl)
    ∙ (H.F-seq upper₀ lower₀ ∙ refl) ▹ H₁ bottom
        ≡⟨ Comp.paste-naturality {H} {H} (idPseudonatTrans H)
          {a₀ = a₀} {b₀} {c₀} {a₁} {b₁} {c₁}
          top middle bottom upper₀ lower₀ upper₁ lower₁ upper-square lower-square ⟩
    H₁ top ◃ (H.F-seq upper₁ lower₁ ∙ refl)
    ∙ (upper-image ∙ refl) ▹ H₁ lower₁
    ∙ H₁ upper₀ ◃ lower-image
        ≡⟨ reass₂ ⟩
    H₁ top ◃ H.F-seq upper₁ lower₁
    ∙ upper-image ▹ H₁ lower₁ ∙ H₁ upper₀ ◃ lower-image
        ∎
    where
    reass₁ = reassoc source target refl
      where
      source =
        (↑ sym (H.F-seq top (upper₁ ⋆ lower₁))
          ∙′ ↑ H₂ (upper-square ▹ lower₁ ∙ upper₀ ◃ lower-square)
          ∙′ ↑ H.F-seq (upper₀ ⋆ lower₀) bottom)
        ∙′ ↑ H.F-seq upper₀ lower₀ ▹′ H₁ bottom
      target =
        (↑ sym (H.F-seq top (upper₁ ⋆ lower₁))
          ∙′ ↑ H₂ (upper-square ▹ lower₁ ∙ upper₀ ◃ lower-square)
          ∙′ ↑ H.F-seq (upper₀ ⋆ lower₀) bottom ∙′ refl′)
        ∙′ (↑ H.F-seq upper₀ lower₀ ∙′ refl′) ▹′ H₁ bottom
    reass₂ = reassoc source target refl
      where
      source =
        H₁ top ◃′ (↑ H.F-seq upper₁ lower₁ ∙′ refl′)
        ∙′ (↑ upper-image ∙′ refl′) ▹′ H₁ lower₁
        ∙′ H₁ upper₀ ◃′ ↑ lower-image
      target =
        H₁ top ◃′ ↑ H.F-seq upper₁ lower₁
        ∙′ ↑ upper-image ▹′ H₁ lower₁
        ∙′ H₁ upper₀ ◃′ ↑ lower-image

  square : Square
    (upper-image ▹ H₁ lower₁ ∙ H₁ upper₀ ◃ lower-image)
    pasted-image
    (H₁ top ◃ sym (H.F-seq upper₁ lower₁))
    (sym (H.F-seq upper₀ lower₀) ▹ H₁ bottom)
  square = symP (compPath→Square (sym paste-image))

module Naturality {F G H F′ G′ H′ : GpdEndo}
  (α : GpdEndoTrans F F′)
  (β : GpdEndoTrans G G′)
  (γ : GpdEndoTrans H H′) where

  private
    module F = GpdEndo F
    module G = GpdEndo G
    module H = GpdEndo H
    module F′ = GpdEndo F′
    module G′ = GpdEndo G′
    module H′ = GpdEndo H′

  open F using (F₀; F₁)
  open G using () renaming (F₀ to G₀; F₁ to G₁; F₂ to G₂)
  open H using () renaming (F₁ to H₁; F₂ to H₂)
  open F′ using () renaming (F₀ to F′₀; F₁ to F′₁)
  open G′ using () renaming (F₀ to G′₀; F₁ to G′₁)
  open H′ using () renaming (F₁ to H′₁)
  open GpdEndoTrans {F = F} {F′} α using ()
    renaming (N-ob to α₀; N-hom to α□)
  open GpdEndoTrans {F = G} {G′} β using ()
    renaming (N-ob to β₀; N-hom to β□)
  open GpdEndoTrans {F = H} {H′} γ using ()
    renaming (N-ob to γ₀; N-hom to γ□)

  private
    source = _⨾₁_ {F = F} {F′} {G ⨾₀ H} {G′ ⨾₀ H′}
      α (_⨾₁_ {F = G} {G′} {H} {H′} β γ)
    target = _⨾₁_ {F = F ⨾₀ G} {F′ ⨾₀ G′} {H} {H′}
      (_⨾₁_ {F = F} {F′} {G} {G′} α β) γ
    module source = GpdEndoTrans {F = F ⨾₀ (G ⨾₀ H)} {F′ ⨾₀ (G′ ⨾₀ H′)} source
    module target = GpdEndoTrans {F = (F ⨾₀ G) ⨾₀ H} {(F′ ⨾₀ G′) ⨾₀ H′} target

  component : ∀ x → _
  component x = sym (H.F-seq (G₁ (α₀ x)) (β₀ (F′₀ x))) ▹ γ₀ (G′₀ (F′₀ x))

  module _ {x y : LU2C.ob HGpd} (f : HGpd [ x , y ]) where
    private
      module Paste = Pasting H
        {a₀ = G₀ (F₀ x)} {b₀ = G₀ (F′₀ x)} {c₀ = G′₀ (F′₀ x)}
        {a₁ = G₀ (F₀ y)} {b₁ = G₀ (F′₀ y)} {c₁ = G′₀ (F′₀ y)}
        (G₁ (F₁ f)) (G₁ (F′₁ f)) (G′₁ (F′₁ f))
        (G₁ (α₀ x)) (β₀ (F′₀ x)) (G₁ (α₀ y)) (β₀ (F′₀ y))
        (G.F□ {x = F₀ x} {F₀ y} {F′₀ y} {F′₀ x}
          {f = F₁ f} {α₀ y} {α₀ x} {F′₁ f} (α□ f))
        (β□ (F′₁ f))

      source-normal =
        (Paste.upper-image ▹ H₁ (β₀ (F′₀ y))
          ∙ H₁ (G₁ (α₀ x)) ◃ Paste.lower-image) ▹ γ₀ (G′₀ (F′₀ y))
        ∙ (H₁ (G₁ (α₀ x)) ⋆ H₁ (β₀ (F′₀ x))) ◃ γ□ (G′₁ (F′₁ f))
      target-normal =
        Paste.pasted-image ▹ γ₀ (G′₀ (F′₀ y))
        ∙ H₁ (G₁ (α₀ x) ⋆ β₀ (F′₀ x)) ◃ γ□ (G′₁ (F′₁ f))

      source-normalize : source.N-hom f ∙ refl ≡ source-normal
      source-normalize =
        ∙r ∙r cong (_▹ (H₁ (β₀ (F′₀ y)) ⋆ γ₀ (G′₀ (F′₀ y))))
          (symDistr (H₂ (G.F-seq (F₁ f) (α₀ y)))
            (H.F-seq (G₁ (F₁ f)) (G₁ (α₀ y))))
        ∙ reass
        where
        reass = reassoc before after refl
          where
          before =
            ((↑ sym (H.F-seq (G₁ (F₁ f)) (G₁ (α₀ y)))
                ∙′ cong′ H₁ (↑ sym (G.F-seq (F₁ f) (α₀ y))))
                ▹′ H₁ (β₀ (F′₀ y)) ▹′ γ₀ (G′₀ (F′₀ y))
              ∙′ cong′ H₁ (↑ G₂ (α□ f)) ▹′ H₁ (β₀ (F′₀ y)) ▹′ γ₀ (G′₀ (F′₀ y))
              ∙′ (cong′ H₁ (↑ G.F-seq (α₀ x) (F′₁ f))
                  ∙′ ↑ H.F-seq (G₁ (α₀ x)) (G₁ (F′₁ f)))
                ▹′ H₁ (β₀ (F′₀ y)) ▹′ γ₀ (G′₀ (F′₀ y))
              ∙′ H₁ (G₁ (α₀ x)) ◃′
                (↑ sym (H.F-seq (G₁ (F′₁ f)) (β₀ (F′₀ y))) ▹′ γ₀ (G′₀ (F′₀ y))
                  ∙′ cong′ H₁ (↑ β□ (F′₁ f)) ▹′ γ₀ (G′₀ (F′₀ y))
                  ∙′ ↑ H.F-seq (β₀ (F′₀ x)) (G′₁ (F′₁ f)) ▹′ γ₀ (G′₀ (F′₀ y))
                  ∙′ H₁ (β₀ (F′₀ x)) ◃′ ↑ γ□ (G′₁ (F′₁ f))))
            ∙′ refl′
          after =
            ((↑ sym (H.F-seq (G₁ (F₁ f)) (G₁ (α₀ y)))
                ∙′ cong′ H₁
                  (↑ sym (G.F-seq (F₁ f) (α₀ y))
                    ∙′ ↑ G₂ (α□ f) ∙′ ↑ G.F-seq (α₀ x) (F′₁ f))
                ∙′ ↑ H.F-seq (G₁ (α₀ x)) (G₁ (F′₁ f)))
                ▹′ H₁ (β₀ (F′₀ y))
              ∙′ H₁ (G₁ (α₀ x)) ◃′
                (↑ sym (H.F-seq (G₁ (F′₁ f)) (β₀ (F′₀ y)))
                  ∙′ cong′ H₁ (↑ β□ (F′₁ f))
                  ∙′ ↑ H.F-seq (β₀ (F′₀ x)) (G′₁ (F′₁ f))))
              ▹′ γ₀ (G′₀ (F′₀ y))
            ∙′ (H₁ (G₁ (α₀ x)) ⋆ H₁ (β₀ (F′₀ x))) ◃′ ↑ γ□ (G′₁ (F′₁ f))

      target-normalize : refl ∙ target.N-hom f ≡ target-normal
      target-normalize = reassoc before after refl
        where
        before =
          refl′ ∙′
          (↑ sym (H.F-seq (G₁ (F₁ f)) (G₁ (α₀ y) ⋆ β₀ (F′₀ y)))
              ▹′ γ₀ (G′₀ (F′₀ y))
            ∙′ cong′ H₁
              (↑ sym (G.F-seq (F₁ f) (α₀ y)) ▹′ β₀ (F′₀ y)
                ∙′ ↑ G₂ (α□ f) ▹′ β₀ (F′₀ y)
                ∙′ ↑ G.F-seq (α₀ x) (F′₁ f) ▹′ β₀ (F′₀ y)
                ∙′ G₁ (α₀ x) ◃′ ↑ β□ (F′₁ f))
              ▹′ γ₀ (G′₀ (F′₀ y))
            ∙′ ↑ H.F-seq (G₁ (α₀ x) ⋆ β₀ (F′₀ x)) (G′₁ (F′₁ f))
              ▹′ γ₀ (G′₀ (F′₀ y))
            ∙′ H₁ (G₁ (α₀ x) ⋆ β₀ (F′₀ x)) ◃′ ↑ γ□ (G′₁ (F′₁ f)))
        after =
          (↑ sym (H.F-seq (G₁ (F₁ f)) (G₁ (α₀ y) ⋆ β₀ (F′₀ y)))
            ∙′ cong′ H₁
              ((↑ sym (G.F-seq (F₁ f) (α₀ y))
                  ∙′ ↑ G₂ (α□ f) ∙′ ↑ G.F-seq (α₀ x) (F′₁ f))
                  ▹′ β₀ (F′₀ y)
                ∙′ G₁ (α₀ x) ◃′ ↑ β□ (F′₁ f))
            ∙′ ↑ H.F-seq (G₁ (α₀ x) ⋆ β₀ (F′₀ x)) (G′₁ (F′₁ f)))
            ▹′ γ₀ (G′₀ (F′₀ y))
          ∙′ H₁ (G₁ (α₀ x) ⋆ β₀ (F′₀ x)) ◃′ ↑ γ□ (G′₁ (F′₁ f))

      normalized-square : Square source-normal target-normal
        (H₁ (G₁ (F₁ f)) ◃ component y)
        (component x ▹ H′₁ (G′₁ (F′₁ f)))
      normalized-square i =
        Paste.square i ▹ γ₀ (G′₀ (F′₀ y))
        ∙ sym (H.F-seq (G₁ (α₀ x)) (β₀ (F′₀ x))) i ◃ γ□ (G′₁ (F′₁ f))

    square : Square
      (source.N-hom f ∙ refl)
      (refl ∙ target.N-hom f)
      (H₁ (G₁ (F₁ f)) ◃ component y)
      (component x ▹ H′₁ (G′₁ (F′₁ f)))
    square = compPath→Square
      ( ∙l target-normalize
      ∙ Square→compPath normalized-square
      ∙ ∙r sym source-normalize
      )
