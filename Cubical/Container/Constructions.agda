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

module _ (S : Type) (P : S → Type) where
  -- Paths between vertical maps over
  -- related base maps
  module Path {s₁ s₂ : S} 
    {ps₁ : P s₁ → S} 
    {ps₂ : P s₂ → S}
    where
    _≡[_,_]ᴾ_ : 
      (π₁ : (p : P s₁) → P (ps₁ p)) 
      (s≡ : s₁ ≡ s₂) (ps≡ : PathP (λ i → P (s≡ i) → S) ps₁ ps₂) 
      (π₂ : (p : P s₂) → P (ps₂ p)) → Type
    π₁ ≡[ s≡ , ps≡ ]ᴾ π₂ = PathP (λ i → (p : P (s≡ i)) → P (ps≡ i p)) π₁ π₂

  -- How complicated can this get?
  module Square {s₀₀ s₀₁ s₁₀ s₁₁ : S}
    {s≡₀₋ : s₀₀ ≡ s₀₁}
    {s≡₁₋ : s₁₀ ≡ s₁₁}
    {s≡₋₀ : s₀₀ ≡ s₁₀}
    {s≡₋₁ : s₀₁ ≡ s₁₁}
    (s□ : Square s≡₀₋ s≡₁₋ s≡₋₀ s≡₋₁)
    {ps₀₀ : P s₀₀ → S}
    {ps₀₁ : P s₀₁ → S}
    {ps₁₀ : P s₁₀ → S}
    {ps₁₁ : P s₁₁ → S}
    {ps≡₀₋ : PathP (λ i → P (s≡₀₋ i) → S) ps₀₀ ps₀₁}
    {ps≡₁₋ : PathP (λ i → P (s≡₁₋ i) → S) ps₁₀ ps₁₁}
    {ps≡₋₀ : PathP (λ i → P (s≡₋₀ i) → S) ps₀₀ ps₁₀}
    {ps≡₋₁ : PathP (λ i → P (s≡₋₁ i) → S) ps₀₁ ps₁₁}
    (ps□ : SquareP (λ i j → P (s□ i j) → S) ps≡₀₋ ps≡₁₋ ps≡₋₀ ps≡₋₁)
    {π₀₀ : (p : P s₀₀) → P (ps₀₀ p)}
    {π₀₁ : (p : P s₀₁) → P (ps₀₁ p)}
    {π₁₀ : (p : P s₁₀) → P (ps₁₀ p)}
    {π₁₁ : (p : P s₁₁) → P (ps₁₁ p)}
    where

    open Path

    Squareᴾ : 
      (π≡₀₋ : π₀₀ ≡[ s≡₀₋ , ps≡₀₋ ]ᴾ π₀₁)
      (π≡₁₋ : π₁₀ ≡[ s≡₁₋ , ps≡₁₋ ]ᴾ π₁₁)
      (π≡₋₀ : π₀₀ ≡[ s≡₋₀ , ps≡₋₀ ]ᴾ π₁₀)
      (π≡₋₁ : π₀₁ ≡[ s≡₋₁ , ps≡₋₁ ]ᴾ π₁₁)
      → Type
    Squareᴾ π≡₀₋ π≡₁₋ π≡₋₀ π≡₋₁ = SquareP
      (λ i j → (p : P (s□ i j)) → P (ps□ i j p))
      π≡₀₋ π≡₁₋ π≡₋₀ π≡₋₁

