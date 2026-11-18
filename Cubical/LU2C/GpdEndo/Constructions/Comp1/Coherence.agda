open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws
open import Prelude.ExtraGpdLaws
open import Prelude.Reassoc

module Cubical.LU2C.GpdEndo.Constructions.Comp1.Coherence {ℓ : Level} where

open import Cubical.LU2C.Base
open import Cubical.LU2C.GpdEndo.Base {ℓ}
open import Cubical.LU2C.GpdEndo.NatTrans.Base {ℓ}
open import Cubical.LU2C.Instances.Groupoids ℓ
open import Cubical.WildCat.AsLU2C.Instances
  renaming (_⋆_ to infixr 15 _⋆_)

open NotHGpd

-- Post-whiskering preserves the identity and composition coherence of α.
module _ {F F′ : GpdEndo} (α : GpdEndoTrans F F′) (G : GpdEndo) where
  private module F = GpdEndo F
  private module F′ = GpdEndo F′
  private module G = GpdEndo G
  private module α = GpdEndoTrans {F = F} {F′} α

  open F using (F₁)
  open F′ using () renaming (F₁ to F′₁)
  open G using () renaming (F₁ to G₁; F₂ to G₂)
  open α using () renaming (N-ob to α₀; N-hom to α□)

  map-id : ∀ {x}
    → G.F□ (α□ (id {x = x .fst}))
      ∙ G₁ (α₀ x) ◃ (G₂ F′.F-id ∙ G.F-id)
      ≡ (G₂ F.F-id ∙ G.F-id) ▹ G₁ (α₀ x)
  map-id {x} =
      G.F□ (α□ id)
      ∙ G₁ (α₀ x) ◃ (G₂ F′.F-id ∙ G.F-id)
    ≡⟨ reass₁ ⟩
      sym (G.F-seq (F₁ id) (α₀ x))
      ∙ G₂ (α□ id)
      ∙ (G.F-seq (α₀ x) (F′₁ id) ∙ G₁ (α₀ x) ◃ G₂ F′.F-id)
      ∙ G₁ (α₀ x) ◃ G.F-id
    ≡⟨ ∙l ∙l ∙r G.F-seq-nat refl F′.F-id ⟩
      sym (G.F-seq (F₁ id) (α₀ x))
      ∙ G₂ (α□ id)
      ∙ (G₂ (α₀ x ◃ F′.F-id) ∙ G.F-seq (α₀ x) id)
      ∙ G₁ (α₀ x) ◃ G.F-id
    ≡⟨ reass₂ ⟩
      sym (G.F-seq (F₁ id) (α₀ x))
      ∙ G₂ (α□ id ∙ α₀ x ◃ F′.F-id)
      ∙ G.F-seq (α₀ x) id ∙ G₁ (α₀ x) ◃ G.F-id
    ≡⟨ ∙l ∙r cong G₂ α.N-hom-id ⟩
      sym (G.F-seq (F₁ id) (α₀ x))
      ∙ G₂ (F.F-id ▹ α₀ x)
      ∙ G.F-seq (α₀ x) id ∙ G₁ (α₀ x) ◃ G.F-id
    ≡⟨ ∙l ∙l (∙l G.F-IdR (α₀ x) ∙ rCancel _) ⟩
      sym (G.F-seq (F₁ id) (α₀ x)) ∙ G₂ (F.F-id ▹ α₀ x) ∙ refl
    ≡⟨ ∙l sym (rUnit _) ∙ sym (G.F-seq-nat-sym F.F-id refl) ⟩
      G₂ F.F-id ▹ G₁ (α₀ x) ∙ sym (G.F-seq id (α₀ x))
    ≡⟨ ∙l sym (G.F-IdL (α₀ x)) ⟩
      G₂ F.F-id ▹ G₁ (α₀ x) ∙ G.F-id ▹ G₁ (α₀ x)
    ≡⟨ sym (▹-∙ (G₂ F.F-id) G.F-id) ⟩
      (G₂ F.F-id ∙ G.F-id) ▹ G₁ (α₀ x)
    ∎
    where
    reass₁ = reassoc source target refl
      where
      source target : Term _ _
      source =
        (↑ sym (G.F-seq (F₁ id) (α₀ x))
          ∙′ cong′ G₁ (↑ α□ id)
          ∙′ ↑ G.F-seq (α₀ x) (F′₁ id))
        ∙′ G₁ (α₀ x) ◃′ (cong′ G₁ (↑ F′.F-id)
          ∙′ ↑ G.F-id)
      target =
        ↑ sym (G.F-seq (F₁ id) (α₀ x))
        ∙′ cong′ G₁ (↑ α□ id)
        ∙′ (↑ G.F-seq (α₀ x) (F′₁ id)
          ∙′ G₁ (α₀ x) ◃′ cong′ G₁ (↑ F′.F-id))
        ∙′ G₁ (α₀ x) ◃′ ↑ G.F-id

    reass₂ = reassoc source target refl
      where
      source target : Term _ _
      source =
        ↑ sym (G.F-seq (F₁ id) (α₀ x))
        ∙′ cong′ G₁ (↑ α□ id)
        ∙′ (cong′ G₁ (α₀ x ◃′ ↑ F′.F-id)
          ∙′ ↑ G.F-seq (α₀ x) id)
        ∙′ G₁ (α₀ x) ◃′ ↑ G.F-id
      target =
        ↑ sym (G.F-seq (F₁ id) (α₀ x))
        ∙′ cong′ G₁ (↑ α□ id
          ∙′ α₀ x ◃′ ↑ F′.F-id)
        ∙′ ↑ G.F-seq (α₀ x) id
        ∙′ G₁ (α₀ x) ◃′ ↑ G.F-id

  map-seq : ∀ {x y z} (f : HGpd [ x , y ]) (g : HGpd [ y , z ])
    → G.F□ (α□ (f ⋆ g))
      ∙ G₁ (α₀ x) ◃ (G₂ (F′.F-seq f g) ∙ G.F-seq (F′₁ f) (F′₁ g))
      ≡ (G₂ (F.F-seq f g) ∙ G.F-seq (F₁ f) (F₁ g)) ▹ G₁ (α₀ z)
      ∙ G₁ (F₁ f) ◃ G.F□ (α□ g)
      ∙ G.F□ (α□ f) ▹ G₁ (F′₁ g)
  map-seq {x} {y} {z} f g =
      G.F□ (α□ (f ⋆ g))
      ∙ G₁ (α₀ x) ◃ (G₂ (F′.F-seq f g) ∙ G.F-seq (F′₁ f) (F′₁ g))
    ≡⟨ reass₁ ⟩
      sym (G.F-seq (F₁ (f ⋆ g)) (α₀ z))
      ∙ G₂ (α□ (f ⋆ g))
      ∙ (G.F-seq (α₀ x) (F′₁ (f ⋆ g)) ∙ G₁ (α₀ x) ◃ G₂ (F′.F-seq f g))
      ∙ G₁ (α₀ x) ◃ G.F-seq (F′₁ f) (F′₁ g)
    ≡⟨ ∙l ∙l ∙r G.F-seq-nat refl (F′.F-seq f g) ⟩
      sym (G.F-seq (F₁ (f ⋆ g)) (α₀ z))
      ∙ G₂ (α□ (f ⋆ g))
      ∙ (G₂ (α₀ x ◃ F′.F-seq f g) ∙ G.F-seq (α₀ x) (F′₁ f ⋆ F′₁ g))
      ∙ G₁ (α₀ x) ◃ G.F-seq (F′₁ f) (F′₁ g)
    ≡⟨ reass₂ ⟩
      sym (G.F-seq (F₁ (f ⋆ g)) (α₀ z))
      ∙ G₂ (α□ (f ⋆ g) ∙ α₀ x ◃ F′.F-seq f g)
      ∙ G.F-seq (α₀ x) (F′₁ f ⋆ F′₁ g)
      ∙ G₁ (α₀ x) ◃ G.F-seq (F′₁ f) (F′₁ g)
    ≡⟨ ∙l ∙r cong G₂ (α.N-hom-seq f g) ⟩
      sym (G.F-seq (F₁ (f ⋆ g)) (α₀ z))
      ∙ G₂ (F.F-seq f g ▹ α₀ z ∙ F₁ f ◃ α□ g ∙ α□ f ▹ F′₁ g)
      ∙ G.F-seq (α₀ x) (F′₁ f ⋆ F′₁ g)
      ∙ G₁ (α₀ x) ◃ G.F-seq (F′₁ f) (F′₁ g)
    ≡⟨ ∙l ∙l sym (G.F-Assoc-comp (α₀ x) (F′₁ f) (F′₁ g)) ⟩
      sym (G.F-seq (F₁ (f ⋆ g)) (α₀ z))
      ∙ G₂ (F.F-seq f g ▹ α₀ z ∙ F₁ f ◃ α□ g ∙ α□ f ▹ F′₁ g)
      ∙ G.F-seq (α₀ x ⋆ F′₁ f) (F′₁ g)
      ∙ G.F-seq (α₀ x) (F′₁ f) ▹ G₁ (F′₁ g)
    ≡⟨ reass₃ ⟩
      sym (G.F-seq (F₁ (f ⋆ g)) (α₀ z))
      ∙ G₂ (F.F-seq f g ▹ α₀ z)
      ∙ G₂ (F₁ f ◃ α□ g)
      ∙ (G₂ (α□ f ▹ F′₁ g) ∙ G.F-seq (α₀ x ⋆ F′₁ f) (F′₁ g))
      ∙ G.F-seq (α₀ x) (F′₁ f) ▹ G₁ (F′₁ g)
    ≡⟨ ∙l ∙l ∙l ∙r sym (G.F-seq-nat (α□ f) refl) ⟩
      sym (G.F-seq (F₁ (f ⋆ g)) (α₀ z))
      ∙ G₂ (F.F-seq f g ▹ α₀ z)
      ∙ G₂ (F₁ f ◃ α□ g)
      ∙ (G.F-seq (F₁ f ⋆ α₀ y) (F′₁ g) ∙ G₂ (α□ f) ▹ G₁ (F′₁ g))
      ∙ G.F-seq (α₀ x) (F′₁ f) ▹ G₁ (F′₁ g)
    ≡⟨ ∙l ∙l ∙l ∙r ∙r shuffleSymR (G.F-Assoc-comp (F₁ f) (α₀ y) (F′₁ g)) ⟩
      sym (G.F-seq (F₁ (f ⋆ g)) (α₀ z))
      ∙ G₂ (F.F-seq f g ▹ α₀ z)
      ∙ G₂ (F₁ f ◃ α□ g)
      ∙ (((G.F-seq (F₁ f) (α₀ y ⋆ F′₁ g)
          ∙ G₁ (F₁ f) ◃ G.F-seq (α₀ y) (F′₁ g))
          ∙ sym (G.F-seq (F₁ f) (α₀ y) ▹ G₁ (F′₁ g)))
          ∙ G₂ (α□ f) ▹ G₁ (F′₁ g))
      ∙ G.F-seq (α₀ x) (F′₁ f) ▹ G₁ (F′₁ g)
    ≡⟨ reass₄ ⟩
      sym (G.F-seq (F₁ (f ⋆ g)) (α₀ z))
      ∙ G₂ (F.F-seq f g ▹ α₀ z)
      ∙ (G₂ (F₁ f ◃ α□ g) ∙ G.F-seq (F₁ f) (α₀ y ⋆ F′₁ g))
      ∙ G₁ (F₁ f) ◃ G.F-seq (α₀ y) (F′₁ g)
      ∙ G.F□ (α□ f) ▹ G₁ (F′₁ g)
    ≡⟨ ∙l ∙l ∙r sym (G.F-seq-nat refl (α□ g)) ⟩
      sym (G.F-seq (F₁ (f ⋆ g)) (α₀ z))
      ∙ G₂ (F.F-seq f g ▹ α₀ z)
      ∙ (G.F-seq (F₁ f) (F₁ g ⋆ α₀ z) ∙ G₁ (F₁ f) ◃ G₂ (α□ g))
      ∙ G₁ (F₁ f) ◃ G.F-seq (α₀ y) (F′₁ g)
      ∙ G.F□ (α□ f) ▹ G₁ (F′₁ g)
    ≡⟨ ∙l ∙l ∙r ∙r shuffleSymR (sym (G.F-Assoc-comp (F₁ f) (F₁ g) (α₀ z))) ⟩
      sym (G.F-seq (F₁ (f ⋆ g)) (α₀ z))
      ∙ G₂ (F.F-seq f g ▹ α₀ z)
      ∙ (((G.F-seq (F₁ f ⋆ F₁ g) (α₀ z)
          ∙ G.F-seq (F₁ f) (F₁ g) ▹ G₁ (α₀ z))
          ∙ sym (G₁ (F₁ f) ◃ G.F-seq (F₁ g) (α₀ z)))
          ∙ G₁ (F₁ f) ◃ G₂ (α□ g))
      ∙ G₁ (F₁ f) ◃ G.F-seq (α₀ y) (F′₁ g)
      ∙ G.F□ (α□ f) ▹ G₁ (F′₁ g)
    ≡⟨ reass₅ ⟩
      sym (G.F-seq (F₁ (f ⋆ g)) (α₀ z))
      ∙ (G₂ (F.F-seq f g ▹ α₀ z) ∙ G.F-seq (F₁ f ⋆ F₁ g) (α₀ z))
      ∙ G.F-seq (F₁ f) (F₁ g) ▹ G₁ (α₀ z)
      ∙ G₁ (F₁ f) ◃ G.F□ (α□ g)
      ∙ G.F□ (α□ f) ▹ G₁ (F′₁ g)
    ≡⟨ ∙l ∙r sym (G.F-seq-nat (F.F-seq f g) refl) ⟩
      sym (G.F-seq (F₁ (f ⋆ g)) (α₀ z))
      ∙ (G.F-seq (F₁ (f ⋆ g)) (α₀ z) ∙ G₂ (F.F-seq f g) ▹ G₁ (α₀ z))
      ∙ G.F-seq (F₁ f) (F₁ g) ▹ G₁ (α₀ z)
      ∙ G₁ (F₁ f) ◃ G.F□ (α□ g)
      ∙ G.F□ (α□ f) ▹ G₁ (F′₁ g)
    ≡⟨ reass₆ ⟩
      (sym (G.F-seq (F₁ (f ⋆ g)) (α₀ z)) ∙ G.F-seq (F₁ (f ⋆ g)) (α₀ z))
      ∙ (G₂ (F.F-seq f g) ∙ G.F-seq (F₁ f) (F₁ g)) ▹ G₁ (α₀ z)
      ∙ G₁ (F₁ f) ◃ G.F□ (α□ g)
      ∙ G.F□ (α□ f) ▹ G₁ (F′₁ g)
    ≡⟨ ∙r lCancel _ ∙ sym (lUnit _) ⟩
      (G₂ (F.F-seq f g) ∙ G.F-seq (F₁ f) (F₁ g)) ▹ G₁ (α₀ z)
      ∙ G₁ (F₁ f) ◃ G.F□ (α□ g)
      ∙ G.F□ (α□ f) ▹ G₁ (F′₁ g)
    ∎
    where
    reass₁ = reassoc source target refl
      where
      source target : Term _ _
      source =
        (↑ sym (G.F-seq (F₁ (f ⋆ g)) (α₀ z))
          ∙′ cong′ G₁ (↑ α□ (f ⋆ g))
          ∙′ ↑ G.F-seq (α₀ x) (F′₁ (f ⋆ g)))
        ∙′ G₁ (α₀ x) ◃′ (cong′ G₁ (↑ F′.F-seq f g)
          ∙′ ↑ G.F-seq (F′₁ f) (F′₁ g))
      target =
        ↑ sym (G.F-seq (F₁ (f ⋆ g)) (α₀ z))
        ∙′ cong′ G₁ (↑ α□ (f ⋆ g))
        ∙′ (↑ G.F-seq (α₀ x) (F′₁ (f ⋆ g))
          ∙′ G₁ (α₀ x) ◃′ cong′ G₁ (↑ F′.F-seq f g))
        ∙′ G₁ (α₀ x) ◃′ ↑ G.F-seq (F′₁ f) (F′₁ g)

    reass₂ = reassoc source target refl
      where
      source target : Term _ _
      source =
        ↑ sym (G.F-seq (F₁ (f ⋆ g)) (α₀ z))
        ∙′ cong′ G₁ (↑ α□ (f ⋆ g))
        ∙′ (cong′ G₁ (α₀ x ◃′ ↑ F′.F-seq f g)
          ∙′ ↑ G.F-seq (α₀ x) (F′₁ f ⋆ F′₁ g))
        ∙′ G₁ (α₀ x) ◃′ ↑ G.F-seq (F′₁ f) (F′₁ g)
      target =
        ↑ sym (G.F-seq (F₁ (f ⋆ g)) (α₀ z))
        ∙′ cong′ G₁ (↑ α□ (f ⋆ g)
          ∙′ α₀ x ◃′ ↑ F′.F-seq f g)
        ∙′ ↑ G.F-seq (α₀ x) (F′₁ f ⋆ F′₁ g)
        ∙′ G₁ (α₀ x) ◃′ ↑ G.F-seq (F′₁ f) (F′₁ g)

    reass₃ = reassoc source target refl
      where
      source target : Term _ _
      source =
        ↑ sym (G.F-seq (F₁ (f ⋆ g)) (α₀ z))
        ∙′ cong′ G₁ (↑ F.F-seq f g ▹′ α₀ z
          ∙′ F₁ f ◃′ ↑ α□ g
          ∙′ ↑ α□ f ▹′ F′₁ g)
        ∙′ ↑ G.F-seq (α₀ x ⋆ F′₁ f) (F′₁ g)
        ∙′ ↑ G.F-seq (α₀ x) (F′₁ f) ▹′ G₁ (F′₁ g)
      target =
        ↑ sym (G.F-seq (F₁ (f ⋆ g)) (α₀ z))
        ∙′ cong′ G₁ (↑ F.F-seq f g ▹′ α₀ z)
        ∙′ cong′ G₁ (F₁ f ◃′ ↑ α□ g)
        ∙′ (cong′ G₁ (↑ α□ f ▹′ F′₁ g)
          ∙′ ↑ G.F-seq (α₀ x ⋆ F′₁ f) (F′₁ g))
        ∙′ ↑ G.F-seq (α₀ x) (F′₁ f) ▹′ G₁ (F′₁ g)

    reass₄ = reassoc source target refl
      where
      source target : Term _ _
      source =
        ↑ sym (G.F-seq (F₁ (f ⋆ g)) (α₀ z))
        ∙′ cong′ G₁ (↑ F.F-seq f g ▹′ α₀ z)
        ∙′ cong′ G₁ (F₁ f ◃′ ↑ α□ g)
        ∙′ (((↑ G.F-seq (F₁ f) (α₀ y ⋆ F′₁ g)
              ∙′ G₁ (F₁ f) ◃′ ↑ G.F-seq (α₀ y) (F′₁ g))
            ∙′ ↑ sym (G.F-seq (F₁ f) (α₀ y) ▹ G₁ (F′₁ g)))
          ∙′ cong′ G₁ (↑ α□ f) ▹′ G₁ (F′₁ g))
        ∙′ ↑ G.F-seq (α₀ x) (F′₁ f) ▹′ G₁ (F′₁ g)
      target =
        ↑ sym (G.F-seq (F₁ (f ⋆ g)) (α₀ z))
        ∙′ cong′ G₁ (↑ F.F-seq f g ▹′ α₀ z)
        ∙′ (cong′ G₁ (F₁ f ◃′ ↑ α□ g)
          ∙′ ↑ G.F-seq (F₁ f) (α₀ y ⋆ F′₁ g))
        ∙′ G₁ (F₁ f) ◃′ ↑ G.F-seq (α₀ y) (F′₁ g)
        ∙′ (↑ sym (G.F-seq (F₁ f) (α₀ y))
          ∙′ cong′ G₁ (↑ α□ f)
          ∙′ ↑ G.F-seq (α₀ x) (F′₁ f)) ▹′ G₁ (F′₁ g)

    reass₅ = reassoc source target refl
      where
      source target : Term _ _
      source =
        ↑ sym (G.F-seq (F₁ (f ⋆ g)) (α₀ z))
        ∙′ cong′ G₁ (↑ F.F-seq f g ▹′ α₀ z)
        ∙′ (((↑ G.F-seq (F₁ f ⋆ F₁ g) (α₀ z)
              ∙′ ↑ G.F-seq (F₁ f) (F₁ g) ▹′ G₁ (α₀ z))
            ∙′ ↑ sym (G₁ (F₁ f) ◃ G.F-seq (F₁ g) (α₀ z)))
          ∙′ G₁ (F₁ f) ◃′ cong′ G₁ (↑ α□ g))
        ∙′ G₁ (F₁ f) ◃′ ↑ G.F-seq (α₀ y) (F′₁ g)
        ∙′ (↑ sym (G.F-seq (F₁ f) (α₀ y))
          ∙′ cong′ G₁ (↑ α□ f)
          ∙′ ↑ G.F-seq (α₀ x) (F′₁ f)) ▹′ G₁ (F′₁ g)
      target =
        ↑ sym (G.F-seq (F₁ (f ⋆ g)) (α₀ z))
        ∙′ (cong′ G₁ (↑ F.F-seq f g ▹′ α₀ z)
          ∙′ ↑ G.F-seq (F₁ f ⋆ F₁ g) (α₀ z))
        ∙′ ↑ G.F-seq (F₁ f) (F₁ g) ▹′ G₁ (α₀ z)
        ∙′ G₁ (F₁ f) ◃′ (↑ sym (G.F-seq (F₁ g) (α₀ z))
          ∙′ cong′ G₁ (↑ α□ g)
          ∙′ ↑ G.F-seq (α₀ y) (F′₁ g))
        ∙′ (↑ sym (G.F-seq (F₁ f) (α₀ y))
          ∙′ cong′ G₁ (↑ α□ f)
          ∙′ ↑ G.F-seq (α₀ x) (F′₁ f)) ▹′ G₁ (F′₁ g)

    reass₆ = reassoc source target refl
      where
      source target : Term _ _
      source =
        ↑ sym (G.F-seq (F₁ (f ⋆ g)) (α₀ z))
        ∙′ (↑ G.F-seq (F₁ (f ⋆ g)) (α₀ z)
          ∙′ cong′ G₁ (↑ F.F-seq f g) ▹′ G₁ (α₀ z))
        ∙′ ↑ G.F-seq (F₁ f) (F₁ g) ▹′ G₁ (α₀ z)
        ∙′ G₁ (F₁ f) ◃′ (↑ sym (G.F-seq (F₁ g) (α₀ z))
          ∙′ cong′ G₁ (↑ α□ g)
          ∙′ ↑ G.F-seq (α₀ y) (F′₁ g))
        ∙′ (↑ sym (G.F-seq (F₁ f) (α₀ y))
          ∙′ cong′ G₁ (↑ α□ f)
          ∙′ ↑ G.F-seq (α₀ x) (F′₁ f)) ▹′ G₁ (F′₁ g)
      target =
        (↑ sym (G.F-seq (F₁ (f ⋆ g)) (α₀ z))
          ∙′ ↑ G.F-seq (F₁ (f ⋆ g)) (α₀ z))
        ∙′ (cong′ G₁ (↑ F.F-seq f g)
          ∙′ ↑ G.F-seq (F₁ f) (F₁ g)) ▹′ G₁ (α₀ z)
        ∙′ G₁ (F₁ f) ◃′ (↑ sym (G.F-seq (F₁ g) (α₀ z))
          ∙′ cong′ G₁ (↑ α□ g)
          ∙′ ↑ G.F-seq (α₀ y) (F′₁ g))
        ∙′ (↑ sym (G.F-seq (F₁ f) (α₀ y))
          ∙′ cong′ G₁ (↑ α□ f)
          ∙′ ↑ G.F-seq (α₀ x) (F′₁ f)) ▹′ G₁ (F′₁ g)
