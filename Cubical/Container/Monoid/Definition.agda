open import Cubical.Foundations.Prelude

open import Cubical.Container.Base
import Cubical.Container.Constructions as CC
import Cubical.WildCat.Instances.Container as WC
import Cubical.Bicategory.Base as BB

module Cubical.Container.Monoid.Definition (T : Container) where

open CC.Morphisms
open CC.Monoidal
open BB.Whiskering WC.ContainerWildCat

infixr 50 _⨾₂_
_⨾₂_ : ∀ {F G H K : Container}
  {α α′ : F ⇒ H}
  {β β′ : G ⇒ K}
  (p : α ≡ α′)
  (q : β ≡ β′)
  → α ⨾₁ β ≡ α′ ⨾₁ β′
p ⨾₂ q = cong₂ _⨾₁_ p q

_◃⨾_ : ∀ {F G H K : Container}
  (α  : F ⇒ H)
  {β β′ : G ⇒ K}
  (q : β ≡ β′)
  → α ⨾₁ β ≡ α ⨾₁ β′
α ◃⨾ q = refl {x = α} ⨾₂ q

_⨾▹_ : ∀ {F G H K : Container}
  {α α′ : F ⇒ H}
  (p : α ≡ α′)
  (β : G ⇒ K)
  → α ⨾₁ β ≡ α′ ⨾₁ β
p ⨾▹ β = p ⨾₂ refl {x = β}

open import Prelude.Shapes

record Pseudomonoid : Type where
  field
    η : 𝕀 ⇒ T 
    μ : T ⨾₀ T ⇒ T

    -- 2-cells
    lUnit : η ⨾₁ id ⋆ μ ≡ ⨾lUnit
    rUnit : id ⨾₁ η ⋆ μ ≡ ⨾rUnit
    assoc : ⨾assoc ⋆ μ ⨾₁ id ⋆ μ ≡ id ⨾₁ μ ⋆ μ

    -- Equations on 2-cells
    -- Adapted from: Day & Street
    -- Monoidal Bicategories and Hopf Algebroids
    -- DOI: 10.1006/aima.1997.1649
    -- Sect. 3, though those equations are for a
    -- Gray-monoid, where ̰̰_⨾_ is strictly associative.

    -- assoc-coh : 
    --   id ⨾₁ ⨾assoc ◃ ⨾assoc ◃ (assoc ⨾▹ id) ▹ μ
    --   ∙ id ⨾₁ ⨾assoc ◃ id ⨾₁ μ ⨾₁ id ◃ assoc
    --   ∙ (id ◃⨾ assoc) ▹ μ
    --   ≡ ⨾assoc ◃ μ ⨾₁ id ⨾₁ id ◃ assoc
    --   ∙ id ⨾₁ id ⨾₁ μ ◃ assoc

    assoc-coh : 
      Hex
        (id ⨾₁ ⨾assoc ◃ ⨾assoc ◃ (assoc ⨾▹ id) ▹ μ)
        (id ⨾₁ ⨾assoc ◃ id ⨾₁ μ ⨾₁ id ◃ assoc)
        ((id ◃⨾ assoc) ▹ μ)
        refl
        (⨾assoc ◃ μ ⨾₁ id ⨾₁ id ◃ assoc)
        (id ⨾₁ id ⨾₁ μ ◃ assoc)

    -- lrUnit-coh : 
    --   id ⨾₁ η ⨾₁ id ◃ assoc
    --   ∙ (id ◃⨾ lUnit) ▹ μ
    --   ≡ ⨾assoc ◃ (rUnit ⨾▹ id) ▹ μ

    lrUnit-coh : 
      Square 
        (id ⨾₁ η ⨾₁ id ◃ assoc)
        (⨾assoc ◃ (rUnit ⨾▹ id) ▹ μ)
        refl
        ((id ◃⨾ lUnit) ▹ μ)
