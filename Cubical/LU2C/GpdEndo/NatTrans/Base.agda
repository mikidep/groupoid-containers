{-# OPTIONS --allow-unsolved-metas #-}

open import Cubical.Foundations.Prelude

open import Cubical.WildCat.Functor using (WildNatTrans)

module Cubical.LU2C.GpdEndo.NatTrans.Base {ℓ : Level} where

open import Prelude.Shapes using (Triangle; Hex)
open import Cubical.WildCat.AsLU2C.Instances

open import Cubical.LU2C.Base 
open import Cubical.LU2C.Pseudofunctor.NatTrans.Base
open import Cubical.LU2C.Pseudofunctor.NatTrans.Path
open import Cubical.LU2C.GpdEndo.Base {ℓ = ℓ}
open import Cubical.LU2C.Instances.Groupoids ℓ

open NotHGpd

module _ {F G : GpdEndo} where
  private module F = GpdEndo F
  private module G = GpdEndo G

  open F using (F₀; F₁; F₂)
  open G using () renaming 
    ( F₀ to G₀
    ; F₁ to G₁
    ; F₂ to G₂
    )

  record IsGpdEndoTrans (α : WildNatTrans _ _ F.str G.str) 
    : Type (ℓ-suc ℓ) where
    open WildNatTrans α using ()
      renaming (N-ob to α₀; N-hom to α□)
    field
      N-hom-id : ∀ {x} 
        → α□ (id {x = x .fst}) 
          ∙ α₀ x ◃ G.F-id 
          ≡ F.F-id ▹ α₀ x 
      N-hom-seq : ∀ {x y z} 
        (f : HGpd [ x , y ])
        (g : HGpd [ y , z ])
        → α□ (f ⋆ g)
          ∙ α₀ x ◃ G.F-seq f g
          ≡ F.F-seq f g ▹ α₀ z
          ∙ F₁ f ◃ α□ g
          ∙ α□ f ▹ G₁ g

  record IsGpdEndoTransSquare (α : WildNatTrans _ _ F.str G.str) 
    : Type (ℓ-suc ℓ) where
    open WildNatTrans α using ()
      renaming (N-ob to α₀; N-hom to α□)
    field
      N-hom-id : ∀ {x} 
        → Square 
          (α□ (id {x = x .fst})) 
          refl 
          (F.F-id ▹ α₀ x) 
          (α₀ x ◃ G.F-id) 
      N-hom-seq : ∀ {x y z} 
        (f : HGpd [ x , y ])
        (g : HGpd [ y , z ])
        → Hex
          (α□ (f ⋆ g))
          (α₀ x ◃ G.F-seq f g)
          refl
          (F.F-seq f g ▹ α₀ z)
          (F₁ f ◃ α□ g)
          (α□ f ▹ G₁ g)
    
  module GpdEndoTransConv {α : WildNatTrans _ _ F.str G.str} where
    open WildNatTrans α using ()
      renaming (N-ob to α₀; N-hom to α□)
    open import Prelude.Square

    Square→N-hom-id : ∀ {x} 
      → Square 
        (α□ (id {x = x .fst}))  
        (F.F-id ▹ α₀ x)
        refl 
        (α₀ x ◃ G.F-id) 
      → α□ (id {x = x .fst}) 
        ∙ α₀ x ◃ G.F-id 
        ≡ F.F-id ▹ α₀ x 
    Square→N-hom-id {x} = PathP→compPathL∙∙

    fromStrict : IsGpdEndoTrans α → IsPseudonat {F = F.str} {G = G.str} α
    fromStrict = ?

    toStrict : IsPseudonat {F = F.str} {G = G.str} α → IsGpdEndoTrans α
    toStrict = ?

  module GpdEndoTrans (α : PseudonatTrans {C = HGpd} {HGpd} F G) where
    open Σ α using () renaming (fst to str) public
    open WildNatTrans str public
    open GpdEndoTransConv {α = α .fst}
    open IsGpdEndoTrans (toStrict (α .snd)) public

  GpdEndoTrans≡ = PseudonatTrans≡ {C = HGpd} {HGpd} {F = F} {G}
  GpdEndoTrans□ = PseudonatTrans□ {C = HGpd} {HGpd} {F = F} {G}
  isGroupoidGpdEndoTrans = isGroupoidPseudonatTrans {C = HGpd} {HGpd} {F = F} {G}

module _ (F G : GpdEndo) where
  GpdEndoTrans = PseudonatTrans {C = HGpd} {HGpd} F G


