open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Path
open import Cubical.Functions.FunExtEquiv

open import Cubical.WildCat.Base hiding (_[_,_])
open import Cubical.WildCat.Functor hiding (_$_)
open import Cubical.WildCat.NaturalTransformation.Base
open import Cubical.WildCat.Functor.Instances.GpdEndoComp using (compWild)
import Cubical.WildCat.Monoidal.Instances.GpdEndo.Assoc.Coherence as Coherence

module Cubical.WildCat.Monoidal.Instances.GpdEndo.Assoc
  (ℓ : Level) where

open import Cubical.LU2C.Base
open import Cubical.LU2C.Pseudofunctor.NatTrans.Base
open import Cubical.LU2C.Instances.Groupoids ℓ-zero
open import Cubical.WildCat.Instances.GpdEndo
  renaming (GpdEndo to GpdEndoWC)
open import Cubical.LU2C.GpdEndo.Base {ℓ-zero}
open import Cubical.LU2C.GpdEndo.Constructions {ℓ-zero}
open import Cubical.LU2C.GpdEndo.NatTrans.Base {ℓ-zero}
open import Cubical.LU2C.GpdEndo.NatTrans.Constructions {ℓ-zero}

open import Cubical.WildCat.AsLU2C.Instances
open import Prelude.Reassoc
open import Reflection.Reassoc
open import Prelude.ExtraGpdLaws

open NotHGpd
open NotWC GpdEndoWC

module _ (F G H : GpdEndo) where
  open WildNatTrans
  open IsGpdEndoTrans
  open GpdEndoTransConv

  iMG-assoc-ob : GpdEndoTrans (F ⨾₀ (G ⨾₀ H)) ((F ⨾₀ G) ⨾₀ H)
  iMG-assoc-ob .fst .N-ob X = idfun _
  iMG-assoc-ob .fst .N-hom f = refl
  iMG-assoc-ob .snd =
    fromStrict {F = F ⨾₀ (G ⨾₀ H)} {(F ⨾₀ G) ⨾₀ H} strictGoal
    where
    strictGoal : _
    strictGoal .N-hom-id {x} = reassoc!
    strictGoal .N-hom-seq f g = reassoc!

module _ {F G H F′ G′ H′ : GpdEndo}
  (α : GpdEndoTrans F F′)
  (β : GpdEndoTrans G G′)
  (γ : GpdEndoTrans H H′) where

  private asc₀ = iMG-assoc-ob

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

  -- Naturality in all three arguments; ";" means left-to-right composition.
  --
  --   F ; (G ; H) ---- alpha ; (beta ; gamma) ----> F' ; (G' ; H')
  --       |                                               |
  --       | assoc(F,G,H)                                  | assoc(F',G',H')
  --       v                                               v
  --   (F ; G) ; H ---- (alpha ; beta) ; gamma ----> (F' ; G') ; H'
  --
  -- Both vertical arrows have identity components. At x, the two routes
  -- are compared by the inverse of H's composition comparison:
  --
  --   H(G(alpha_x)) ; H(beta_F'x) ; gamma_G'F'x
  --                         |
  --                         | H.F-seq^{-1}, whiskered by gamma_G'F'x
  --                         v
  --   H(G(alpha_x) ; beta_F'x) ; gamma_G'F'x

  iMG-assoc-hom :
    _⋆_ {x = F ⨾₀ (G ⨾₀ H)} {F′ ⨾₀ (G′ ⨾₀ H′)} {(F′ ⨾₀ G′) ⨾₀ H′}
      (_⨾₁_ {F = F} {F′} {G ⨾₀ H} {G′ ⨾₀ H′}
        α (_⨾₁_ {F = G} {G′} {H} {H′} β γ))
      (asc₀ F′ G′ H′)
    ≡ _⋆_ {x = F ⨾₀ (G ⨾₀ H)} {(F ⨾₀ G) ⨾₀ H} {(F′ ⨾₀ G′) ⨾₀ H′}
      (asc₀ F G H)
      (_⨾₁_ {F = F ⨾₀ G} {F′ ⨾₀ G′} {H} {H′}
        (_⨾₁_ {F = F} {F′} {G} {G′} α β) γ)
  iMG-assoc-hom =
    GpdEndoTrans≡ {F = F ⨾₀ (G ⨾₀ H)} {G = (F′ ⨾₀ G′) ⨾₀ H′}
      (funExt λ x → sym (H.F-seq (G₁ (α₀ x)) (β₀ (F′₀ x))) ▹ γ₀ (G′₀ (F′₀ x))) 
      λ f → compPath→Square (goal f)
    where
    -- module Nat = Coherence.Naturality {F} {G} {H} {F′} {G′} {H′} α β γ
    source = _⨾₁_ {F = F} {F′} {G ⨾₀ H} {G′ ⨾₀ H′}
      α (_⨾₁_ {F = G} {G′} {H} {H′} β γ)
    target = _⨾₁_ {F = F ⨾₀ G} {F′ ⨾₀ G′} {H} {H′}
      (_⨾₁_ {F = F} {F′} {G} {G′} α β) γ
    module source = GpdEndoTrans {F = F ⨾₀ (G ⨾₀ H)} {F′ ⨾₀ (G′ ⨾₀ H′)} source
    module target = GpdEndoTrans {F = (F ⨾₀ G) ⨾₀ H} {(F′ ⨾₀ G′) ⨾₀ H′} target

    goal : ∀ {x y} f → _
    goal {x} {y} f =
      H₁ (G₁ (F₁ f)) ◃ sym (H.F-seq (G₁ (α₀ y)) (β₀ (F′₀ y))) ▹ γ₀ (G′₀ (F′₀ y))
      ∙ refl
      ∙ (sym (H.F-seq (G₁ (F₁ f)) (G₁ (α₀ y) ⋆ β₀ (F′₀ y))) ▹ γ₀ (G′₀ (F′₀ y))
        ∙ H₂ (sym (G.F-seq (F₁ f) (α₀ y)) ▹ β₀ (F′₀ y)
          ∙ G₂ (α□ f) ▹ β₀ (F′₀ y)
          ∙ G.F-seq (α₀ x) (F′₁ f) ▹ β₀ (F′₀ y)
          ∙ G₁ (α₀ x) ◃ β□ (F′₁ f)) ▹ γ₀ (G′₀ (F′₀ y))
        ∙ H.F-seq (G₁ (α₀ x) ⋆ β₀ (F′₀ x)) (G′₁ (F′₁ f))
          ▹ γ₀ (G′₀ (F′₀ y))
        ∙ H₁ (G₁ (α₀ x) ⋆ β₀ (F′₀ x)) ◃ γ□ (G′₁ (F′₁ f)))
          ≡⟨ {! !} ⟩
      ((sym (H₂ (G.F-seq (F₁ f) (α₀ y))
          ∙ H.F-seq (G₁ (F₁ f)) (G₁ (α₀ y)))
          ▹ (H₁ (β₀ (F′₀ y)) ⋆ γ₀ (G′₀ (F′₀ y)))
        ∙ H₂ (G₂ (α□ f)) ▹ (H₁ (β₀ (F′₀ y)) ⋆ γ₀ (G′₀ (F′₀ y)))
        ∙ (H₂ (G.F-seq (α₀ x) (F′₁ f))
          ∙ H.F-seq (G₁ (α₀ x)) (G₁ (F′₁ f)))
          ▹ (H₁ (β₀ (F′₀ y)) ⋆ γ₀ (G′₀ (F′₀ y)))
        ∙ H₁ (G₁ (α₀ x)) ◃
          (sym (H.F-seq (G₁ (F′₁ f)) (β₀ (F′₀ y))) ▹ γ₀ (G′₀ (F′₀ y))
            ∙ H₂ (β□ (F′₁ f)) ▹ γ₀ (G′₀ (F′₀ y))
            ∙ H.F-seq (β₀ (F′₀ x)) (G′₁ (F′₁ f)) ▹ γ₀ (G′₀ (F′₀ y))
            ∙ H₁ (β₀ (F′₀ x)) ◃ γ□ (G′₁ (F′₁ f))))
        ∙ refl)
      ∙ sym (H.F-seq (G₁ (α₀ x)) (β₀ (F′₀ x))) ▹ γ₀ (G′₀ (F′₀ x)) ▹ H′₁ (G′₁ (F′₁ f))
          ∎
      -- TODO: look at G;H F-seq-nat?

module _ (F G H : GpdEndo) where
  open WildNatTrans
  open IsGpdEndoTrans
  open GpdEndoTransConv
  open wildIsIso

  iMG-assoc-isIs : wildIsIso {C = GpdEndoWC}
    {x = F ⨾₀ (G ⨾₀ H)} {y = (F ⨾₀ G) ⨾₀ H} (iMG-assoc-ob F G H)
  iMG-assoc-isIs .inv' .fst .N-ob _ = idfun _
  iMG-assoc-isIs .inv' .fst .N-hom _ = refl
  iMG-assoc-isIs .inv' .snd =
    fromStrict {F = (F ⨾₀ G) ⨾₀ H} {F ⨾₀ (G ⨾₀ H)} strictGoal
    where
    strictGoal : _
    strictGoal .N-hom-id {x} = reassoc!
    strictGoal .N-hom-seq f g = reassoc!
  iMG-assoc-isIs .sect =
    GpdEndoTrans≡ {F = (F ⨾₀ G) ⨾₀ H} {G = (F ⨾₀ G) ⨾₀ H}
      refl λ f → reassoc!
  iMG-assoc-isIs .retr =
    GpdEndoTrans≡ {F = F ⨾₀ (G ⨾₀ H)} {G = F ⨾₀ (G ⨾₀ H)}
      refl λ f → reassoc!

iMG-assoc : WildNatIso _ GpdEndoWC (assocₗ compWild) (assocᵣ compWild)
iMG-assoc = record where
  trans = record where
    N-ob (F , G , H) = iMG-assoc-ob F G H
    N-hom {F , G , H} {F′ , G′ , H′} (α , β , γ) =
      iMG-assoc-hom {F} {G} {H} {F′} {G′} {H′} α β γ
  isIs (F , G , H) = iMG-assoc-isIs F G H
