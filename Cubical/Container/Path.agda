-- {-# OPTIONS --allow-unsolved-metas #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Path
open import Cubical.Container.Base
open import Prelude.Shapes

module Cubical.Container.Path where

module _ {F G : Container} {α β : F ⇒ G} where
  open Container F
  open Container G renaming
    (
      S to S′
    ; P to P′
    )
  open _⇒_ α
  open _⇒_ β renaming
    (
      σ to σ′
    ; π to π′
    )

  open import Cubical.Foundations.Equiv
  open import Cubical.Foundations.Equiv.Properties

  CMor≡′ : (∀ (s : S) → _,_ {B = λ s′ → P′ s′ → P s} (σ s) (π s) ≡ (σ′ s , π′ s))
    → α ≡ β
  CMor≡′ htpy = equivFun (congEquiv CMor′≃CMor) (funExt htpy)

module _ {F G : Container} {α β γ δ : F ⇒ G} where
  private module F = Container F

  CMor□′ :
    ∀ {p : α ≡ β}
    → {q : γ ≡ δ}
    → {r : α ≡ γ}
    → {s : β ≡ δ}
    → ((s' : F.S) 
      → let f = λ (x : F ⇒ G) → CMor′⁻ x s'
      in Square (cong f p) (cong f q) (cong f r) (cong f s))
    → Square p q r s
  CMor□′ sq i j ._⇒_.σ s = sq s i j .fst
  CMor□′ sq i j ._⇒_.π s = sq s i j .snd

module _ {F G : Container} {α β γ δ ζ : F ⇒ G} where
  open Container F

  CMorPentagon′ :
    ∀ {p : α ≡ β}
      {q : β ≡ γ}
      {r : γ ≡ δ}
      {u : α ≡ ζ}
      {v : ζ ≡ δ}
    → (∀ (s : S) → let f = λ (x : F ⇒ G) → CMor′⁻ x s
      in Pentagon (cong f p) (cong f q) (cong f r) (cong f u) (cong f v))
    → Pentagon p q r u v
  CMorPentagon′ {p} {q} {r} {u} {v} pnts = goal
    where
    goal : Σ _ (λ _ → Σ _ _)
    goal .fst = CMor≡′ λ s → pnts s .fst
    goal .snd .fst = CMor□′ λ s → pnts s .snd .fst
    goal .snd .snd = CMor□′ λ s → pnts s .snd .snd

module Displayed (S : Type) (P : S → Type) where
  -- Paths between vertical maps over
  -- related base maps
  module _ {s₁ s₂ : S} 
    {ps₁ : P s₁ → S} 
    {ps₂ : P s₂ → S}
    where
    _≡[_,_]ᴾ_ : 
      (π₁ : (p : P s₁) → P (ps₁ p)) 
      (s≡ : s₁ ≡ s₂) (ps≡ : PathP (λ i → P (s≡ i) → S) ps₁ ps₂) 
      (π₂ : (p : P s₂) → P (ps₂ p)) → Type
    π₁ ≡[ s≡ , ps≡ ]ᴾ π₂ = PathP (λ i → (p : P (s≡ i)) → P (ps≡ i p)) π₁ π₂

  -- How complicated can this get?
  module _ {s₀₀ s₀₁ s₁₀ s₁₁ : S}
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

    Squareᴾ : 
      (π≡₀₋ : π₀₀ ≡[ s≡₀₋ , ps≡₀₋ ]ᴾ π₀₁)
      (π≡₁₋ : π₁₀ ≡[ s≡₁₋ , ps≡₁₋ ]ᴾ π₁₁)
      (π≡₋₀ : π₀₀ ≡[ s≡₋₀ , ps≡₋₀ ]ᴾ π₁₀)
      (π≡₋₁ : π₀₁ ≡[ s≡₋₁ , ps≡₋₁ ]ᴾ π₁₁)
      → Type
    Squareᴾ π≡₀₋ π≡₁₋ π≡₋₀ π≡₋₁ = SquareP
      (λ i j → (p : P (s□ i j)) → P (ps□ i j p))
      π≡₀₋ π≡₁₋ π≡₋₀ π≡₋₁

