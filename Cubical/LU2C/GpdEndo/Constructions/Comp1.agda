{-# OPTIONS --allow-unsolved-metas #-}

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
    open WildNatTrans
    open import Prelude.ExtraGpdLaws
    open import Reflection.Reassoc

    str : WildNatTrans _ _ ⟨ F ⨾₀ G ⟩ ⟨ F′ ⨾₀ G′ ⟩
    str .N-ob x = G₁ (α₀ x) ⋆ β₀ (F′₀ x)
    str .N-hom {x} {y} f = 
          sym (G.F-seq (F₁ f) (α₀ y)) ▹ β₀ (F′₀ y)
          ∙ G₂ (α□ f) ▹ β₀ (F′₀ y)
          ∙ G.F-seq (α₀ x) (F′₁ f) ▹ β₀ (F′₀ y)
          ∙ G₁ (α₀ x) ◃ β□ (F′₁ f)
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

    isPseudo-id : ∀ {x} → _
    isPseudo-id {x} = 
      (sym (G.F-seq (F₁ id) (α₀ x)) ▹ β₀ (F′₀ x)
        ∙ G₂ (α□ id) ▹ β₀ (F′₀ x)
        ∙ G.F-seq (α₀ x) (F′₁ id) ▹ β₀ (F′₀ x)
        ∙ G₁ (α₀ x) ◃ β□ (F′₁ id))
      ∙ G₁ (α₀ x) ◃ β₀ (F′₀ x) ◃ (G′₂ F′.F-id ∙ G′.F-id)
      ∙ refl
          -- ≡⟨ reassoc! ⟩
          ≡⟨ {! !} ⟩
      sym (G.F-seq (F₁ id) (α₀ x)) ▹ β₀ (F′₀ x)
      ∙ G₂ (α□ id) ▹ β₀ (F′₀ x)
      ∙ G.F-seq (α₀ x) (F′₁ id) ▹ β₀ (F′₀ x)
      ∙ G₁ (α₀ x) ◃ β□ (F′₁ id)
      ∙ G₁ (α₀ x) ◃ β₀ (F′₀ x) ◃ G′₂ F′.F-id
      ∙ G₁ (α₀ x) ◃ β₀ (F′₀ x) ◃ G′.F-id
          ≡⟨ {! !} ⟩ -- β nat
      sym (G.F-seq (F₁ id) (α₀ x)) ▹ β₀ (F′₀ x)
      ∙ G₂ (α□ id) ▹ β₀ (F′₀ x)
      ∙ G.F-seq (α₀ x) (F′₁ id) ▹ β₀ (F′₀ x)
      ∙ G₁ (α₀ x) ◃ G₂ F′.F-id ▹ β₀ (F′₀ x) 
      ∙ G₁ (α₀ x) ◃ β□ id
      ∙ G₁ (α₀ x) ◃ β₀ (F′₀ x) ◃ G′.F-id
          ≡⟨ {! !} ⟩ -- β.N-hom-id
      sym (G.F-seq (F₁ id) (α₀ x)) ▹ β₀ (F′₀ x)
      ∙ G₂ (α□ id) ▹ β₀ (F′₀ x)
      ∙ G.F-seq (α₀ x) (F′₁ id) ▹ β₀ (F′₀ x)
      ∙ G₁ (α₀ x) ◃ G₂ F′.F-id ▹ β₀ (F′₀ x) 
      ∙ G₁ (α₀ x) ◃ G.F-id ▹ β₀ (F′₀ x)
          ≡⟨ {! !} ⟩ -- G seq nat
      sym (G.F-seq (F₁ id) (α₀ x)) ▹ β₀ (F′₀ x)
      ∙ G₂ (α□ id) ▹ β₀ (F′₀ x)
      ∙ G₂ (α₀ x ◃ F′.F-id) ▹ β₀ (F′₀ x) 
      ∙ G.F-seq (α₀ x) id ▹ β₀ (F′₀ x)
      ∙ G₁ (α₀ x) ◃ G.F-id ▹ β₀ (F′₀ x)
          ≡⟨ {! !} ⟩ -- G IdL
      sym (G.F-seq (F₁ id) (α₀ x)) ▹ β₀ (F′₀ x)
      ∙ G₂ (α□ id) ▹ β₀ (F′₀ x)
      ∙ G₂ (α₀ x ◃ F′.F-id) ▹ β₀ (F′₀ x) 
      ∙ refl
          ≡⟨ {! !} ⟩
          -- ≡⟨ reassoc! ⟩
      sym (G.F-seq (F₁ id) (α₀ x)) ▹ β₀ (F′₀ x)
      ∙ G₂ (α□ id
        ∙ α₀ x ◃ F′.F-id) ▹ β₀ (F′₀ x) 
          ≡⟨ {! !} ⟩ -- α id
      sym (G.F-seq (F₁ id) (α₀ x)) ▹ β₀ (F′₀ x)
      ∙ G₂ (F.F-id ▹ α₀ x) ▹ β₀ (F′₀ x) 
          ≡⟨ {! !} ⟩ -- some G₂ nat
      G₂ F.F-id ▹ G₁ (α₀ x) ▹ β₀ (F′₀ x) 
      ∙ sym (G.F-seq id (α₀ x)) ▹ β₀ (F′₀ x)
          ≡⟨ {! !} ⟩ -- G IdL
      G₂ F.F-id ▹ G₁ (α₀ x) ▹ β₀ (F′₀ x) 
      ∙ G.F-id ▹ G₁ (α₀ x) ▹ β₀ (F′₀ x) 
          -- ≡⟨ reassoc! ⟩
          ≡⟨ {! !} ⟩
      ((G₂ F.F-id ∙ G.F-id) ▹ G₁ (α₀ x) ▹ β₀ (F′₀ x)) 
      ∙ refl
          ∎

    isPseudo-seq : ∀ {x y z} 
      (f : HGpd [ x , y ])
      (g : HGpd [ y , z ])
      → _
    isPseudo-seq {x} {y} {z} f g = 
      (sym (G.F-seq (F₁ (f ⋆ g)) (α₀ z)) ▹ β₀ (F′₀ z)
        ∙ G₂ (α□ (f ⋆ g)) ▹ β₀ (F′₀ z)
        ∙ G.F-seq (α₀ x) (F′₁ (f ⋆ g)) ▹ β₀ (F′₀ z)
        ∙ G₁ (α₀ x) ◃ β□ (F′₁ (f ⋆ g)))
      ∙ G₁ (α₀ x) ◃ β₀ (F′₀ x) ◃ (
        G′₂ (F′.F-seq f g) 
        ∙ G′.F-seq (F′₁ f) (F′₁ g))
          ≡⟨ ? ⟩
      (G₂ (F.F-seq f g) 
        ∙ G.F-seq (F₁ f) (F₁ g)
      ) ▹ G₁ (α₀ z) ▹ β₀ (F′₀ z)
      ∙ refl
      ∙ G₁ (F₁ f) ◃ (
        sym (G.F-seq (F₁ g) (α₀ z)) ▹ β₀ (F′₀ z)
        ∙ G₂ (α□ g) ▹ β₀ (F′₀ z)
        ∙ G.F-seq (α₀ y) (F′₁ g) ▹ β₀ (F′₀ z)
        ∙ G₁ (α₀ y) ◃ β□ (F′₁ g)
      )
      ∙ refl
      ∙ (sym (G.F-seq (F₁ f) (α₀ y)) ▹ β₀ (F′₀ y)
        ∙ G₂ (α□ f) ▹ β₀ (F′₀ y)
        ∙ G.F-seq (α₀ x) (F′₁ f) ▹ β₀ (F′₀ y)
        ∙ G₁ (α₀ x) ◃ β□ (F′₁ f)
      ) ▹ G′₁ (F′₁ g)
      ∙ refl
          ∎

  _⨾₁_ : GpdEndoTrans (F ⨾₀ G) (F′ ⨾₀ G′)
  _⨾₁_ .fst = Goal.str
  _⨾₁_ .snd = record where
    N-hom-id {x} = Goal.isPseudo-id {x}
    N-hom-seq f g = Goal.isPseudo-seq f g
