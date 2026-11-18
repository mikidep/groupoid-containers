open import Cubical.Foundations.Prelude

open import Cubical.WildCat.Functor
open import Cubical.LU2C.Pseudofunctor 

module Cubical.LU2C.GpdEndo.Constructions.Comp1 {ℓ : Level} where

open import Prelude.Shapes using (Triangle; Hex)
open import Cubical.WildCat.AsLU2C.Instances
  renaming (_⋆_ to infixr 15 _⋆_)

open import Cubical.LU2C.Base 
open import Cubical.LU2C.GpdEndo.Base {ℓ = ℓ}
open import Cubical.LU2C.GpdEndo.Constructions.Comp0 {ℓ = ℓ}
open import Cubical.LU2C.GpdEndo.NatTrans.Base {ℓ = ℓ}
open import Cubical.LU2C.Instances.Groupoids ℓ

open GpdEndo using () renaming (str to ⟨_⟩)

open NotHGpd

module _ {F F′ G G′ : GpdEndo}
  (α : GpdEndoTrans F F′)
  (β : GpdEndoTrans G G′)
  where

  private module F = GpdEndo F
  private module F′ = GpdEndo F′
  private module G = GpdEndo G
  private module G′ = GpdEndo G′
  private module FG = GpdEndo (F ⨾₀ G)
  private module F′G′ = GpdEndo (F′ ⨾₀ G′)

  open F using (F₀; F₁; F₂)
  open F′ using () renaming 
    ( F₀ to F′₀
    ; F₁ to F′₁
    ; F₂ to F′₂
    )
  open G using () renaming 
    ( F₀ to G₀
    ; F₁ to G₁
    ; F₂ to G₂
    )
  open G′ using () renaming 
    ( F₀ to G′₀
    ; F₁ to G′₁
    ; F₂ to G′₂
    )

  private module α = GpdEndoTrans {F = F} {F′} α
  private module β = GpdEndoTrans {F = G} {G′} β

  open α using () renaming (N-ob to α₀; N-hom to α□)
  open β using () renaming (N-ob to β₀; N-hom to β□)

  private module Goal where
    open import Prelude.ExtraGpdLaws
    open import Prelude.Reassoc
    open import Cubical.LU2C.GpdEndo.Constructions.Comp1.Coherence {ℓ}
    open import Cubical.WildCat.AsLU2C.NaturalTransformation.Properties
      {F = G.str} {G = G′.str} using (N-hom-nat)

    N-ob : ∀ x → HGpd [ G₀ (F₀ x) , G′₀ (F′₀ x) ]
    N-ob x = G₁ (α₀ x) ⋆ β₀ (F′₀ x)

    αβ₀ = N-ob

    N-hom
      : ∀ {x y} (f : HGpd [ x , y ])
      → G₁ (F₁ f) ⋆ G₁ (α₀ y) ⋆ β₀ (F′₀ y)
        ≡ G₁ (α₀ x) ⋆ β₀ (F′₀ x) ⋆ G′₁ (F′₁ f)
    N-hom {x} {y} f =
      -- sym (G.F-seq (F₁ f) (α₀ y)) ▹ β₀ (F′₀ y)
      -- ∙ G₂ (α□ f) ▹ β₀ (F′₀ y)
      -- ∙ G.F-seq (α₀ x) (F′₁ f) ▹ β₀ (F′₀ y)
      G.F□ (α□ f) ▹ β₀ (F′₀ y)
      ∙ G₁ (α₀ x) ◃ β□ (F′₁ f)

    αβ□ = N-hom

      -- G₁ (F₁ f) ⋆ G₁ (α₀ y) ⋆ β₀ (F′₀ y)
      --     ≡⟨ sym (G.F-seq (F₁ f) (α₀ y)) ▹ β₀ (F′₀ y) ⟩
      -- G₁ (F₁ f ⋆ α₀ y) ⋆ β₀ (F′₀ y)
      --     ≡⟨ G₂ (α□ f) ▹ β₀ (F′₀ y) ⟩
      -- G₁ (α₀ x ⋆ F′₁ f) ⋆ β₀ (F′₀ y)
      --     ≡⟨ G.F-seq (α₀ x) (F′₁ f) ▹ β₀ (F′₀ y) ⟩
      -- G₁ (α₀ x) ⋆ G₁ (F′₁ f) ⋆ β₀ (F′₀ y)
      --     ≡⟨ G₁ (α₀ x) ◃ β□ (F′₁ f) ⟩
      -- G₁ (α₀ x) ⋆ β₀ (F′₀ x) ⋆ G′₁ (F′₁ f)
      --     ∎

    str : WildNatTrans _ _ ⟨ F ⨾₀ G ⟩ ⟨ F′ ⨾₀ G′ ⟩
    str = record where
      N-ob = N-ob
      N-hom = N-hom

    isPseudo-id : ∀ {x}
      → αβ□ (id {x = x .fst}) ∙ αβ₀ x ◃ F′G′.F-id
        ≡ FG.F-id ▹ αβ₀ x
    isPseudo-id {x} =
      αβ□ (id {x = x .fst})
      ∙ αβ₀ x ◃ F′G′.F-id
          ≡⟨ reass₁ ⟩
      G.F□ (α□ id) ▹ β₀ (F′₀ x)
      ∙ G₁ (α₀ x) ◃ ((β□ (F′₁ id) ∙ β₀ (F′₀ x) ◃ G′₂ F′.F-id)
        ∙ β₀ (F′₀ x) ◃ G′.F-id)
          ≡⟨ ∙l cong (G₁ (α₀ x) ◃_) (∙r N-hom-nat β.str F′.F-id) ⟩
      G.F□ (α□ id) ▹ β₀ (F′₀ x)
      ∙ G₁ (α₀ x) ◃ ((G₂ F′.F-id ▹ β₀ (F′₀ x) ∙ β□ id)
        ∙ β₀ (F′₀ x) ◃ G′.F-id)
          ≡⟨ ∙l cong (G₁ (α₀ x) ◃_) (sym assoc-inf) ⟩
      G.F□ (α□ id) ▹ β₀ (F′₀ x)
      ∙ G₁ (α₀ x) ◃ (G₂ F′.F-id ▹ β₀ (F′₀ x)
        ∙ β□ id ∙ β₀ (F′₀ x) ◃ G′.F-id)
          ≡⟨ ∙l cong (G₁ (α₀ x) ◃_) (∙l β.N-hom-id) ⟩
      G.F□ (α□ id) ▹ β₀ (F′₀ x)
      ∙ G₁ (α₀ x) ◃ (G₂ F′.F-id ▹ β₀ (F′₀ x)
        ∙ G.F-id ▹ β₀ (F′₀ x))
          ≡⟨ reass₂ ⟩
      (G.F□ (α□ id) ∙ G₁ (α₀ x) ◃ (G₂ F′.F-id ∙ G.F-id))
      ▹ β₀ (F′₀ x)
          ≡⟨ cong (_▹ β₀ (F′₀ x)) (map-id {F = F} {F′} α G {x}) ⟩
      FG.F-id ▹ αβ₀ x
          ∎
      where
      reass₁ = reassoc source target refl
        where
        source target : Term _ _
        source =
          (↑ G.F□ (α□ id) ▹′ β₀ (F′₀ x)
            ∙′ G₁ (α₀ x) ◃′ ↑ β□ (F′₁ id))
          ∙′ G₁ (α₀ x) ◃′ β₀ (F′₀ x) ◃′ (↑ G′₂ F′.F-id
            ∙′ ↑ G′.F-id)
        target =
          ↑ G.F□ (α□ id) ▹′ β₀ (F′₀ x)
          ∙′ G₁ (α₀ x) ◃′ ((↑ β□ (F′₁ id)
              ∙′ β₀ (F′₀ x) ◃′ ↑ G′₂ F′.F-id)
            ∙′ β₀ (F′₀ x) ◃′ ↑ G′.F-id)

      reass₂ = reassoc source target refl
        where
        source target : Term _ _
        source =
          ↑ G.F□ (α□ id) ▹′ β₀ (F′₀ x)
          ∙′ G₁ (α₀ x) ◃′ (↑ G₂ F′.F-id ▹′ β₀ (F′₀ x)
            ∙′ ↑ G.F-id ▹′ β₀ (F′₀ x))
        target =
          (↑ G.F□ (α□ id)
            ∙′ G₁ (α₀ x) ◃′ (↑ G₂ F′.F-id
              ∙′ ↑ G.F-id)) ▹′ β₀ (F′₀ x)

    isPseudo-seq : ∀ {x y z}
      (f : HGpd [ x , y ])
      (g : HGpd [ y , z ])
      → αβ□ (f ⋆ g) ∙ αβ₀ x ◃ F′G′.F-seq f g
        ≡ FG.F-seq f g ▹ αβ₀ z
        ∙ FG.F₁ f ◃ αβ□ g
        ∙ αβ□ f ▹ F′G′.F₁ g
    isPseudo-seq {x} {y} {z} f g =
      αβ□ (f ⋆ g) ∙ αβ₀ x ◃ F′G′.F-seq f g
          ≡⟨ reass₁ ⟩
      G.F□ (α□ (f ⋆ g)) ▹ β₀ (F′₀ z)
      ∙ G₁ (α₀ x) ◃ ((β□ (F′₁ (f ⋆ g)) ∙ β₀ (F′₀ x) ◃ G′₂ (F′.F-seq f g))
        ∙ β₀ (F′₀ x) ◃ G′.F-seq (F′₁ f) (F′₁ g))
          ≡⟨ ∙l cong (G₁ (α₀ x) ◃_) (∙r N-hom-nat β.str (F′.F-seq f g)) ⟩
      G.F□ (α□ (f ⋆ g)) ▹ β₀ (F′₀ z)
      ∙ G₁ (α₀ x) ◃ ((G₂ (F′.F-seq f g) ▹ β₀ (F′₀ z) ∙ β□ (F′₁ f ⋆ F′₁ g))
        ∙ β₀ (F′₀ x) ◃ G′.F-seq (F′₁ f) (F′₁ g))
          ≡⟨ ∙l cong (G₁ (α₀ x) ◃_) (sym assoc-inf) ⟩
      G.F□ (α□ (f ⋆ g)) ▹ β₀ (F′₀ z)
      ∙ G₁ (α₀ x) ◃ (G₂ (F′.F-seq f g) ▹ β₀ (F′₀ z)
        ∙ β□ (F′₁ f ⋆ F′₁ g) ∙ β₀ (F′₀ x) ◃ G′.F-seq (F′₁ f) (F′₁ g))
          ≡⟨ ∙l cong (G₁ (α₀ x) ◃_) (∙l β.N-hom-seq (F′₁ f) (F′₁ g)) ⟩
      G.F□ (α□ (f ⋆ g)) ▹ β₀ (F′₀ z)
      ∙ G₁ (α₀ x) ◃ (G₂ (F′.F-seq f g) ▹ β₀ (F′₀ z)
        ∙ G.F-seq (F′₁ f) (F′₁ g) ▹ β₀ (F′₀ z)
        ∙ G₁ (F′₁ f) ◃ β□ (F′₁ g) ∙ β□ (F′₁ f) ▹ G′₁ (F′₁ g))
          ≡⟨ reass₂ ⟩
      (G.F□ (α□ (f ⋆ g))
        ∙ G₁ (α₀ x) ◃ (G₂ (F′.F-seq f g) ∙ G.F-seq (F′₁ f) (F′₁ g))) ▹ β₀ (F′₀ z)
      ∙ G₁ (α₀ x) ◃ G₁ (F′₁ f) ◃ β□ (F′₁ g)
      ∙ G₁ (α₀ x) ◃ β□ (F′₁ f) ▹ G′₁ (F′₁ g)
          ≡⟨ ∙r cong (_▹ β₀ (F′₀ z)) (map-seq {F = F} {F′} α G f g) ⟩
      (FG.F-seq f g ▹ G₁ (α₀ z)
        ∙ G₁ (F₁ f) ◃ G.F□ (α□ g) ∙ G.F□ (α□ f) ▹ G₁ (F′₁ g)) ▹ β₀ (F′₀ z)
      ∙ G₁ (α₀ x) ◃ G₁ (F′₁ f) ◃ β□ (F′₁ g)
      ∙ G₁ (α₀ x) ◃ β□ (F′₁ f) ▹ G′₁ (F′₁ g)
          ≡⟨ reass₃ ⟩
      FG.F-seq f g ▹ G₁ (α₀ z) ▹ β₀ (F′₀ z)
      ∙ G₁ (F₁ f) ◃ G.F□ (α□ g) ▹ β₀ (F′₀ z)
      ∙ (G.F□ (α□ f) ▹ G₁ (F′₁ g) ▹ β₀ (F′₀ z)
        ∙ G₁ (α₀ x) ◃ G₁ (F′₁ f) ◃ β□ (F′₁ g))
      ∙ G₁ (α₀ x) ◃ β□ (F′₁ f) ▹ G′₁ (F′₁ g)
          ≡⟨ ∙l ∙l ∙r sym (whisk-interchange (G.F□ (α□ f)) (β□ (F′₁ g))) ⟩
      FG.F-seq f g ▹ G₁ (α₀ z) ▹ β₀ (F′₀ z)
      ∙ G₁ (F₁ f) ◃ G.F□ (α□ g) ▹ β₀ (F′₀ z)
      ∙ (G₁ (F₁ f) ◃ G₁ (α₀ y) ◃ β□ (F′₁ g)
        ∙ G.F□ (α□ f) ▹ β₀ (F′₀ y) ▹ G′₁ (F′₁ g))
      ∙ G₁ (α₀ x) ◃ β□ (F′₁ f) ▹ G′₁ (F′₁ g)
          ≡⟨ reass₄ ⟩
      FG.F-seq f g ▹ αβ₀ z
      ∙ FG.F₁ f ◃ αβ□ g
      ∙ αβ□ f ▹ F′G′.F₁ g
          ∎
      where
      reass₁ = reassoc source target refl
        where
        source target : Term _ _
        source =
          (↑ G.F□ (α□ (f ⋆ g)) ▹′ β₀ (F′₀ z)
            ∙′ G₁ (α₀ x) ◃′ ↑ β□ (F′₁ (f ⋆ g)))
          ∙′ G₁ (α₀ x) ◃′ β₀ (F′₀ x) ◃′ (↑ G′₂ (F′.F-seq f g)
            ∙′ ↑ G′.F-seq (F′₁ f) (F′₁ g))
        target =
          ↑ G.F□ (α□ (f ⋆ g)) ▹′ β₀ (F′₀ z)
          ∙′ G₁ (α₀ x) ◃′ ((↑ β□ (F′₁ (f ⋆ g))
              ∙′ β₀ (F′₀ x) ◃′ ↑ G′₂ (F′.F-seq f g))
            ∙′ β₀ (F′₀ x) ◃′ ↑ G′.F-seq (F′₁ f) (F′₁ g))

      reass₂ = reassoc source target refl
        where
        source target : Term _ _
        source =
          ↑ G.F□ (α□ (f ⋆ g)) ▹′ β₀ (F′₀ z)
          ∙′ G₁ (α₀ x) ◃′ (↑ G₂ (F′.F-seq f g) ▹′ β₀ (F′₀ z)
            ∙′ ↑ G.F-seq (F′₁ f) (F′₁ g) ▹′ β₀ (F′₀ z)
            ∙′ G₁ (F′₁ f) ◃′ ↑ β□ (F′₁ g)
            ∙′ ↑ β□ (F′₁ f) ▹′ G′₁ (F′₁ g))
        target =
          (↑ G.F□ (α□ (f ⋆ g))
            ∙′ G₁ (α₀ x) ◃′ (↑ G₂ (F′.F-seq f g)
              ∙′ ↑ G.F-seq (F′₁ f) (F′₁ g))) ▹′ β₀ (F′₀ z)
          ∙′ G₁ (α₀ x) ◃′ G₁ (F′₁ f) ◃′ ↑ β□ (F′₁ g)
          ∙′ G₁ (α₀ x) ◃′ ↑ β□ (F′₁ f) ▹′ G′₁ (F′₁ g)

      reass₃ = reassoc source target refl
        where
        source target : Term _ _
        source =
          (↑ FG.F-seq f g ▹′ G₁ (α₀ z)
            ∙′ G₁ (F₁ f) ◃′ ↑ G.F□ (α□ g)
            ∙′ ↑ G.F□ (α□ f) ▹′ G₁ (F′₁ g)) ▹′ β₀ (F′₀ z)
          ∙′ G₁ (α₀ x) ◃′ G₁ (F′₁ f) ◃′ ↑ β□ (F′₁ g)
          ∙′ G₁ (α₀ x) ◃′ ↑ β□ (F′₁ f) ▹′ G′₁ (F′₁ g)
        target =
          ↑ FG.F-seq f g ▹′ G₁ (α₀ z) ▹′ β₀ (F′₀ z)
          ∙′ G₁ (F₁ f) ◃′ ↑ G.F□ (α□ g) ▹′ β₀ (F′₀ z)
          ∙′ (↑ G.F□ (α□ f) ▹′ G₁ (F′₁ g) ▹′ β₀ (F′₀ z)
            ∙′ G₁ (α₀ x) ◃′ G₁ (F′₁ f) ◃′ ↑ β□ (F′₁ g))
          ∙′ G₁ (α₀ x) ◃′ ↑ β□ (F′₁ f) ▹′ G′₁ (F′₁ g)

      reass₄ = reassoc source target refl
        where
        source target : Term _ _
        source =
          ↑ FG.F-seq f g ▹′ G₁ (α₀ z) ▹′ β₀ (F′₀ z)
          ∙′ G₁ (F₁ f) ◃′ ↑ G.F□ (α□ g) ▹′ β₀ (F′₀ z)
          ∙′ (G₁ (F₁ f) ◃′ G₁ (α₀ y) ◃′ ↑ β□ (F′₁ g)
            ∙′ ↑ G.F□ (α□ f) ▹′ β₀ (F′₀ y) ▹′ G′₁ (F′₁ g))
          ∙′ G₁ (α₀ x) ◃′ ↑ β□ (F′₁ f) ▹′ G′₁ (F′₁ g)
        target =
          ↑ FG.F-seq f g ▹′ G₁ (α₀ z) ▹′ β₀ (F′₀ z)
          ∙′ G₁ (F₁ f) ◃′ (↑ G.F□ (α□ g) ▹′ β₀ (F′₀ z)
            ∙′ G₁ (α₀ y) ◃′ ↑ β□ (F′₁ g))
          ∙′ (↑ G.F□ (α□ f) ▹′ β₀ (F′₀ y)
            ∙′ G₁ (α₀ x) ◃′ ↑ β□ (F′₁ f)) ▹′ G′₁ (F′₁ g)

  open GpdEndoTransConv {F = F ⨾₀ G} {F′ ⨾₀ G′}

  _⨾₁_ : GpdEndoTrans (F ⨾₀ G) (F′ ⨾₀ G′)
  _⨾₁_ .fst = Goal.str
  _⨾₁_ .snd = fromStrict record where
    N-hom-id {x} = Goal.isPseudo-id {x}
    N-hom-seq f g = Goal.isPseudo-seq f g
