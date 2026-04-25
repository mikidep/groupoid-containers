{-# OPTIONS --no-lossy-unification #-}
open import Cubical.Foundations.Prelude

module Cubical.Prebicategory.Instances.Copresheaf.IsPrebicategory (ℓ : Level) where

open import Cubical.Prebicategory.Base
open import Cubical.Prebicategory.Copresheaf ℓ
open import Cubical.Foundations.GroupoidLaws

open import Cubical.Prebicategory.Instances.Copresheaf ℓ

private
  variable
    ℓC ℓC′ : Level

module _ (C : Prebicategory ℓC ℓC′) where
  open import Cubical.WildCat.Base
  open import Cubical.WildCat.Functor
  open import Cubical.WildCat.NaturalTransformation.Base
    using () renaming (makeNatTransPath to WNatTrans≡ ; makeNatTransSquare' to WNatTransSquare)

  open IsPrebicategory
  private 
    CopshC = CopshWildCat C

  open WildCat CopshC
  open Whiskering CopshC

  isPrebicatCopsh' : IsPrebicategory' CopshC
  isPrebicatCopsh' .IsPrebicategory'.triangle  {a = F} {b = G} {c = H} α@(⟨α⟩ , aa) β@(⟨β⟩ , _) = goal where
    open WildNatTrans
    open import Prelude
    goal : Square (⋆Assoc {u = F} {v = G} {w = G} {x = H} α id β) (⋆IdR α ▹ β) refl (α ◃ ⋆IdL β)
    goal = 2NatTrans□ refl
      -- (idfun (Square {! !} {! !} {! !} {! !}) 
      -- {! ((⟨α⟩ , aa) ⋆ id)!})
  isPrebicatCopsh' .IsPrebicategory'.pentagon-α α β γ δ = 2NatTrans≡ {! !}
  isPrebicatCopsh' .IsPrebicategory'.pentagon₁ α β γ δ = 2NatTrans□ {! !}
  isPrebicatCopsh' .IsPrebicategory'.pentagon₂ α β γ δ = 2NatTrans□ {! !}
  isPrebicatCopsh' .IsPrebicategory'.isGpdHom = {! !}
