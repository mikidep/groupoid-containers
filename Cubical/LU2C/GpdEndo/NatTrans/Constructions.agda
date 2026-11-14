
open import Cubical.Foundations.Prelude

open import Cubical.LU2C.Base
open import Cubical.WildCat.AsLU2C.Instances

module Cubical.LU2C.GpdEndo.NatTrans.Constructions where

open import Cubical.WildCat.Functor hiding (compWildNatTrans)

open import Cubical.LU2C.Pseudofunctor.NatTrans.Base

open import Cubical.LU2C.Instances.Groupoids ℓ-zero
open import Cubical.LU2C.GpdEndo.Base {ℓ = ℓ-zero}
open import Cubical.LU2C.GpdEndo.NatTrans.Base



open import Cubical.Foundations.Function
open import Cubical.Foundations.GroupoidLaws
open import Prelude.ExtraGpdLaws

-- open import Prelude.Reassoc
open import Reflection.Reassoc

open NotHGpd

private ⟨_⟩ = fst

open GpdEndoTransConv

module _ (F : GpdEndo) where

  -- this and the other are here because they are stricter
  -- than the general counterpart
  idWildNatTrans : WildNatTrans _ _ ⟨ F ⟩ ⟨ F ⟩
  idWildNatTrans = record where
    N-ob X = idfun _
    N-hom _ = refl
  {-# INLINE idWildNatTrans #-}

  idPseudonatTrans : GpdEndoTrans F F
  idPseudonatTrans .fst = idWildNatTrans
  idPseudonatTrans .snd = fromStrict {F = F} {F} record where
    N-hom-id {x} = sym (lUnit _)
    N-hom-seq f g = reassoc!

module _ {F G H : GpdEndo}
  (α : GpdEndoTrans F G)
  (β : GpdEndoTrans G H) where

  private module F = GpdEndo F
  private module G = GpdEndo G
  private module H = GpdEndo H
  private module α = GpdEndoTrans {F = F} {G} α
  private module β = GpdEndoTrans {F = G} {H} β

  open F using (F₀; F₁; F₂)
  open G using () renaming 
    ( F₀ to G₀
    ; F₁ to G₁
    ; F₂ to G₂
    )
  open H using () renaming
    ( F₀ to H₀
    ; F₁ to H₁
    ; F₂ to H₂
    )
  open α using () renaming (N-ob to α₀; N-hom to α□)
  open β using () renaming (N-ob to β₀; N-hom to β□)

  compWildNatTrans : WildNatTrans _ _ ⟨ F ⟩ ⟨ H ⟩
  compWildNatTrans = record where
    N-ob x = α₀ x ⋆ β₀ x
    N-hom {x} {y} f = α□ f ▹ β₀ y ∙ α₀ x ◃ β□ f
  {-# INLINE compWildNatTrans #-}

  compPseudonatTrans : GpdEndoTrans F H
  compPseudonatTrans .fst = compWildNatTrans
  compPseudonatTrans .snd = fromStrict {F = F} {H} record where
    N-hom-id {x} =
        (α□ id ▹ β₀ x ∙ α₀ x ◃ β□ id) ∙ α₀ x ◃ β₀ x ◃ H.F-id
      ≡⟨ reassoc! ⟩
        α□ id ▹ β₀ x ∙ α₀ x ◃ (β□ id ∙ β₀ x ◃ H.F-id)
      ≡⟨ ∙l cong (α₀ x ◃_) (β.N-hom-id) ⟩
        α□ id ▹ β₀ x ∙ α₀ x ◃ G.F-id ▹ β₀ x
      ≡⟨ reassoc! ⟩
        (α□ id ∙ α₀ x ◃ G.F-id) ▹ β₀ x
      ≡⟨ cong (_▹ β₀ x) (α.N-hom-id) ⟩
        F.F-id ▹ α₀ x ▹ β₀ x
      ∎
    N-hom-seq {x} {y} {z} f g =
        (α□ (f ⋆ g) ▹ β₀ z ∙ α₀ x ◃ β□ (f ⋆ g))
        ∙ α₀ x ◃ β₀ x ◃ H.F-seq f g
      ≡⟨ reassoc! ⟩
        α□ (f ⋆ g) ▹ β₀ z
        ∙ α₀ x ◃ (β□ (f ⋆ g) ∙ β₀ x ◃ H.F-seq f g)
      ≡⟨ ∙l cong (α₀ x ◃_) (β.N-hom-seq f g) ⟩
        α□ (f ⋆ g) ▹ β₀ z
        ∙ α₀ x ◃ (G.F-seq f g ▹ β₀ z
          ∙ G₁ f ◃ β□ g ∙ β□ f ▹ H₁ g)
      ≡⟨ reassoc! ⟩
        (α□ (f ⋆ g) ∙ α₀ x ◃ G.F-seq f g) ▹ β₀ z
        ∙ α₀ x ◃ G₁ f ◃ β□ g
        ∙ α₀ x ◃ β□ f ▹ H₁ g
      ≡⟨ ∙r cong (_▹ β₀ z) (α.N-hom-seq f g) ⟩
        (F.F-seq f g ▹ α₀ z 
          ∙ F₁ f ◃ α□ g ∙ α□ f ▹ G₁ g) ▹ β₀ z
        ∙ α₀ x ◃ G₁ f ◃ β□ g
        ∙ α₀ x ◃ β□ f ▹ H₁ g
      ≡⟨ reassoc! ⟩
        F.F-seq f g ▹ α₀ z ▹ β₀ z
        ∙ F₁ f ◃ α□ g ▹ β₀ z
        ∙ (α□ f ▹ G₁ g ▹ β₀ z ∙ α₀ x ◃ G₁ f ◃ β□ g)
        ∙ α₀ x ◃ β□ f ▹ H₁ g
      ≡⟨ ∙l ∙l ∙r sym (whisk-interchange (α□ f) (β□ g)) ⟩
        F.F-seq f g ▹ α₀ z ▹ β₀ z
        ∙ F₁ f ◃ α□ g ▹ β₀ z
        ∙ (F₁ f ◃ α₀ y ◃ β□ g
          ∙ α□ f ▹ β₀ y ▹ H₁ g)
        ∙ α₀ x ◃ β□ f ▹ H₁ g
      ≡⟨ reassoc! ⟩
        F.F-seq f g ▹ α₀ z ▹ β₀ z
        ∙ F₁ f ◃ (α□ g ▹ β₀ z ∙ α₀ y ◃ β□ g)
        ∙ (α□ f ▹ β₀ y ∙ α₀ x ◃ β□ f) ▹ H₁ g
      ∎
