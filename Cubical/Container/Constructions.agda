open import Cubical.Foundations.Prelude
open import Cubical.Data.Unit
open import Cubical.Container.Base
open import Prelude.Utils

module Cubical.Container.Constructions where

module Morphisms where
  module _ {F : Container} where
    id : F ⇒ F
    id = CMor (idfun _) (λ s → idfun _)

  module _ {F G H : Container} where
    infixr 20 _⋆_
    _⋆_ : F ⇒ G → G ⇒ H → F ⇒ H
    CMor σ π ⋆ CMor σ′ π′ = CMor (σ » σ′) (λ s → π′ (σ s) » π s)

module Extent where
  ⟦_⟧₀ : (F : Container) → Type → Type
  ⟦ F ⟧₀ X = Σ S (λ s → P s → X)
    where open Container F

  module _ {X Y : Type} where
    ⟦_⟧₁ : (F : Container) → (X → Y) → ⟦ F ⟧₀ X → ⟦ F ⟧₀ Y
    ⟦ F ⟧₁ f (s , px) = s , px » f 
      where open Container F

  module _ {F G : Container} (α : F ⇒ G) where
    open _⇒_ α

    Ext₁ : ∀ X → ⟦ F ⟧₀ X → ⟦ G ⟧₀ X
    Ext₁ X (s , px) = σ s , π s » px

    -- what′s going on here?
    -- (S ⊲ P) ⇒ G ≃ Π(s : S) . ⟦G⟧ (P s)
    _ : Ext₁ ≡ λ where
      X (s , px) → ⟦ G ⟧₁ px (σ s , π s)
    _ = refl

module Monoidal where
  module _ where
    open Container

    𝟙 : Container
    𝟙 .S = Unit
    𝟙 .P _ = Unit

  module _ (F G : Container) where
    open Container F
    open Container G using ()
      renaming (S to S′; P to P′)
    open Extent

    _⊗₀_ : Container
    _⊗₀_ .Container.S = ⟦ G ⟧₀ S
    _⊗₀_ .Container.P (s′ , v′) = Σ[ p′ ∈ P′ s′ ] P (v′ p′)

  module _ {F G H K : Container} (α : F ⇒ H) (β : G ⇒ K) where
    open Extent

    open Container F renaming (S to Sꟳ; P to Pꟳ)
    open Container G renaming (S to Sᴳ; P to Pᴳ)
    open Container H renaming (S to Sᴴ; P to Pᴴ)

    open _⇒_ α
    open _⇒_ β renaming (σ to σ′; π to π′)

    open import Prelude

    infixr 50 _⊗₁_
    _⊗₁_ : F ⊗₀ G ⇒ H ⊗₀ K
    _⊗₁_ ._⇒_.σ = ⟦ G ⟧₁ σ » Ext₁ β Sᴴ
      -- σ′ sᴳ , (π′ sᴳ » Pᴳ→Sꟳ » σ)
    _⊗₁_ ._⇒_.π (sᴳ , Pᴳ→Sꟳ) (pᴷ , pᴴ) = goal
      where
      pᴳ = π′ sᴳ pᴷ
      goal = pᴳ , π (Pᴳ→Sꟳ pᴳ) pᴴ

  module _ (F : Container) where
    lUnit : 𝟙 ⊗₀ F ⇒ F
    lUnit = CMor fst λ _ p → p , _

    lUnit⁻ : F ⇒ 𝟙 ⊗₀ F
    lUnit⁻ = CMor (λ s → s , _) λ _ → fst

    rUnit : F ⊗₀ 𝟙 ⇒ F
    rUnit = CMor (λ x → snd x _) λ _ p → _ , p

    rUnit⁻ : F ⇒ F ⊗₀ 𝟙
    rUnit⁻ = CMor (λ s → _ , (λ _ → s)) λ s p → p .snd

  module _ (F G H : Container) where
    assoc : F ⊗₀ (G ⊗₀ H) ⇒ (F ⊗₀ G) ⊗₀ H
    assoc = CMor σ π
      where
      σ : _
      σ ((s″ , op″) , op′) = s″ , λ p″ → op″ p″ , λ p′ → op′ (p″ , p′)
      π : _
      π ((s″ , op″) , op′) ((p″ , (p′ , p))) = (p″ , p′) , p

    assoc⁻ : (F ⊗₀ G) ⊗₀ H ⇒ F ⊗₀ (G ⊗₀ H)
    assoc⁻ = CMor σ π
      where
      σ : _
      σ (s″ , op) .fst = (s″ , op » fst)
      σ (s″ , op) .snd (p″ , p′) = op p″ .snd p′
      π : _
      π (s″ , op) ((p″ , p′) , p) = p″ , (p′ , p)

module Fibration where

  -- Reindexing
  _* : ∀ {S S′ : Type} 
    (σ : S′ → S) (P : S → Type)
    → S′ → Type
  (σ *) P s′ = P (σ s′)

  -- Cartesian lift
  _^ : ∀ {S S′ : Type} 
    (σ : S′ → S) (P : S → Type)
    → S′ ⊲ (σ *) P ⇒ S ⊲ P
  (σ ^) P = CMor σ λ _ → idfun _

  module _ where
    open _⇒_

    -- Vertical fraction
    _ᵥ : ∀ {S S′ : Type} 
      {P : S → Type}
      {P′ : S′ → Type}
      → (α : S′ ⊲ P′ ⇒ S ⊲ P)
      → S′ ⊲ P′ ⇒ S′ ⊲ (α .σ *) P
    α ᵥ = CMor (idfun _) (α .π)
