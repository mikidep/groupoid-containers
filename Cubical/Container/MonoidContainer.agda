open import Cubical.Foundations.Prelude

open import Cubical.Container.Base
open import Cubical.WildCat.Base using (WildCat)
import Cubical.Container.Constructions as CC
import Cubical.WildCat.Instances.Container as WC
import Cubical.Bicategory.Base as BB

module Cubical.Container.MonoidContainer (T : Container) where

open CC.Morphisms
open CC.Monoidal hiding (lUnit; rUnit; assoc)
open BB.Whiskering WC.ContainerWildCat
module MC = CC.Monoidal

LUnit = λ {x} → MC.lUnit x
LUnit⁻ = λ {x} → MC.lUnit⁻ x
RUnit = λ {x} → MC.rUnit x
RUnit⁻ = λ {x} → MC.rUnit⁻ x
Assoc = λ {x y z} → MC.assoc x y z
Assoc⁻ = λ {x y z} → MC.assoc⁻ x y z

infixr 50 _⊗₂_
_⊗₂_ : ∀ {F G H K : Container}
  {α α′ : F ⇒ H}
  {β β′ : G ⇒ K}
  (p : α ≡ α′)
  (q : β ≡ β′)
  → α ⊗₁ β ≡ α′ ⊗₁ β′
p ⊗₂ q = cong₂ _⊗₁_ p q

open Container T

record Pseudomonoid : Type where
  field
    η : 𝟙 ⇒ T 
    μ : T ⊗₀ T ⇒ T

    -- 2-cells
    lUnit : η ⊗₁ id ⋆ μ ≡ LUnit
    rUnit : id ⊗₁ η ⋆ μ ≡ RUnit
    assoc : Assoc ⋆ μ ⊗₁ id ⋆ μ ≡ id ⊗₁ μ ⋆ μ

    -- Equations on 2-cells
    -- Adapted from: Day & Street
    -- Monoidal Bicategories and Hopf Algebroids
    -- DOI: 10.1006/aima.1997.1649
    -- Sect. 3, though those equations are for a
    -- Gray monoid, where ̰̰_⊗_ is strictly associative.

    assoc-coh : 
      id ⊗₁ Assoc ◃ Assoc ◃ assoc ⊗₂ refl {x = id} ▹ μ
      ∙ id ⊗₁ Assoc ◃ id ⊗₁ μ ⊗₁ id ◃ assoc
      ∙ refl {x = id} ⊗₂ assoc ▹ μ
      ≡ Assoc ◃ μ ⊗₁ id ⊗₁ id ◃ assoc
      ∙ id ⊗₁ id ⊗₁ μ ◃ assoc

    lrUnit-coh : 
      id ⊗₁ η ⊗₁ id ◃ assoc
      ∙ refl {x = id} ⊗₂ lUnit ▹ μ
      ≡ Assoc ◃ rUnit ⊗₂ refl {x = id} ▹ μ

record PsMndCont : Type where
  field
    e : S
    m : (s : S) → (P s → S) → S
    ↖ : {s : S} {v : P s → S} (p : P (m s v))
      → P s
    ↗ : {s : S} {v : P s → S} (p : P (m s v))
      → P (v (↖ p))

module _ (pmc : PsMndCont) where
  open PsMndCont pmc
  open Pseudomonoid
  open _⇒_
  open import Cubical.Foundations.Function

  PsMndCont→Pseudomonoid : Pseudomonoid
  PsMndCont→Pseudomonoid .η .σ _ = e
  PsMndCont→Pseudomonoid .η .π _ = _
  PsMndCont→Pseudomonoid .μ .σ = uncurry m
  PsMndCont→Pseudomonoid .μ .π (s , v) pq = ↖ pq , ↗ pq
  PsMndCont→Pseudomonoid .lUnit = {! !}
  PsMndCont→Pseudomonoid .rUnit = {! !}
  PsMndCont→Pseudomonoid .assoc = {! !}
  PsMndCont→Pseudomonoid .assoc-coh = {! !}
  PsMndCont→Pseudomonoid .lrUnit-coh = {! !}

