open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Unit
open import Cubical.Container.Base
import Cubical.Container.Constructions as CC
import Cubical.Container.Path

module Cubical.Container.Monoid.PsMndCont (T : Container) where

open import Prelude.Utils
open import Prelude.Shapes

open Container T

open Cubical.Container.Path.Displayed S P

record PsMndCont : Type where
  field
    e : S
    m : (s : S) → (P s → S) → S
    ↖ : {s : S} {s′ : P s → S} 
      (p : P (m s s′)) → P s
    ↗ : {s : S} {s′ : P s → S} 
      (p : P (m s s′)) → P (s′ (↖ p))

  -- Helpers

  -- Multiply inner trees
  m′ : ∀ {s : S} 
    (s′ : P s → S) 
    (s″ : (p : P s) → P (s′ p) → S)
    → P s → S
  m′ s′ s″ p = m (s′ p) (s″ p)

  m″ : ∀ {s : S} {s′ : P s → S} 
    (s″ : (p : P s) → P (s′ p) → S) 
    (s‴ : (p : P s) → (p′ : P (s′ p)) → P (s″ p p′) → S) 
    → (p : P s) → P (s′ p) → S
  m″ s″ s‴ p = m′ (s″ p) (s‴ p)

  -- Collapse positions after multiplying
  -- outer tree
  m↖↗ : ∀ {s : S} 
    {s′ : P s → S} 
    (s″ : (p : P s) → P (s′ p) → S)
    → P (m s s′) → S
  m↖↗ s″ p = s″ (↖ p) (↗ p)

  field
    lUnit-σ : ∀ (s : S) → m s (const e) ≡ s

    lUnit-π : ∀ {s : S}
      → ↖ {s} {const e} ≡[ lUnit-σ s , (λ _ _ → s) ]ᴾ idfun (P s)

    rUnit-σ : ∀ (s : S) 
      → m e (const s) ≡ s

    rUnit-π : ∀ {s : S}
      → ↗ {e} {const s} ≡[ rUnit-σ s , (λ _ _ → s) ]ᴾ idfun (P s)

    -- This can probably be rewritten in terms of ⟦T⟧₁, but is it worth it?
    assoc-σ : 
      ∀ (s : S) (s′ : P s → S) 
      (s″ : (p : P s) → P (s′ p) → S)
      → m s (m′ s′ s″)
        ≡ m (m s s′) (m↖↗ s″)

    assoc-π₁ :
      ∀ (s : S) (s′ : P s → S) 
      (s″ : (p : P s) → P (s′ p) → S)
      → ↖ {s′ = m′ s′ s″} 
          ≡[ assoc-σ _ _ _ , (λ _ _ → s) ]ᴾ 
        (↖ {s′ = m↖↗ s″} » ↖)

    assoc-π₂ :
      ∀ (s : S) (s′ : P s → S) 
      (s″ : (p : P s) → P (s′ p) → S)
      → (λ p → ↖ {s′ = s″ (↖ p)} (↗ {s′ = m′ s′ s″} p)) 
          ≡[ assoc-σ _ _ _ , (λ i p → s′ (assoc-π₁ s s′ s″ i p)) ]ᴾ
        (↖ {s′ = m↖↗ s″} » ↗)

    assoc-π₃ :
      ∀ (s : S) (s′ : P s → S) 
      (s″ : (p : P s) → P (s′ p) → S)
      → (λ p → ↗ {s′ = s″ (↖ p)} (↗ {s′ = m′ s′ s″} p)) 
          ≡[ assoc-σ _ _ s″ , (λ i p → s″ (assoc-π₁ s s′ s″ i p) (assoc-π₂ s s′ s″ i p)) ]ᴾ
        ↗ {s′ = m↖↗ s″}

    lrUnit-coh-σ : 
      ∀ {s : S} {s′ : P s → S} 
      → Square
        (assoc-σ s (const e) (λ p _ → s′ p)) 
        (cong (m s) (funExt λ p → rUnit-σ (s′ p)))
        (refl {x = m s (λ p → m e (const (s′ p)))})
        (cong₂ (λ s pp → m s (pp » s′)) (lUnit-σ s) lUnit-π)

    lrUnit-coh-π₁ : 
      ∀ {s : S} {s′ : P s → S} 
      → Squareᴾ (lrUnit-coh-σ {s} {s′}) (λ _ _ _ → s)
        (assoc-π₁ s (const e) (λ p _ → s′ p))
        (cong (λ x → ↖ {s′ = x}) (funExt (λ p → rUnit-σ (s′ p))))
        refl 
        (congP (λ i → ↖ {s′ = λ p → s′ (lUnit-π i p)} »_) lUnit-π)
        -- (λ i p → lUnit-π i (↖ {s′ = λ x → s′ (lUnit-π i x)} p))

    lrUnit-coh-π₂ :
      ∀ {s : S} {s′ : P s → S} 
      → Squareᴾ (lrUnit-coh-σ {s′ = s′})
        (λ i j p → s′ (lrUnit-coh-π₁ i j p))
        (assoc-π₃ s (const e) (λ p _ → s′ p))
        (λ i p → rUnit-π i (↗ {s′ = λ q → rUnit-σ (s′ q) i} p))
        refl
        (congP (λ j f → ↗ {s′ = λ p → s′ (f p)}) lUnit-π)

    assoc-coh-σ :
      ∀ {s : S} {s′ : P s → S} 
        {s″ : (p : P s) → P (s′ p) → S} 
        {s‴ : (p : P s) → (p′ : P (s′ p)) → P (s″ p p′) → S} 
      → Pentagon 
        (λ i → m s (λ p → assoc-σ (s′ p) (s″ p) (s‴ p) i))
        (assoc-σ s (m′ s′ s″) (λ p → m↖↗ (s‴ p)))
        (λ i → m (assoc-σ s s′ s″ i) (λ (p : P (assoc-σ s s′ s″ i)) 
          → s‴ (assoc-π₁ s s′ s″ i p) (assoc-π₂ s s′ s″ i p) (assoc-π₃ s s′ s″ i p)))
        (assoc-σ s s′ (m″ s″ s‴))
        (assoc-σ (m s s′) (m↖↗ s″) (λ p → s‴ (↖ p) (↗ p)))

    -- assoc-coh-π₁ :
    --   ∀ {s : S} {s′ : P s → S} 
    --     {s″ : (p : P s) → P (s′ p) → S} 
    --     {s‴ : (p : P s) → (p′ : P (s′ p)) → P (s″ p p′) → S} 
    --   → PentagonP {B = λ cohs → P cohs → P s}
    --       (assoc-coh-σ {s} {s′} {s″} {s‴})
    --       (λ i p → ↖ p)
    --       (assoc-π₁ s (m′ s′ s″) (λ p → m↖↗ (s‴ p)))
    --       (λ i p → assoc-π₁ s s′ s″ i (↖ p))
    --       (assoc-π₁ s s′ (λ p′ → m′ (s″ p′) (s‴ p′)))
    --       (λ i p → ↖ (assoc-π₁ (m s s′) (m↖↗ s″) (λ p → s‴ (↖ p) (↗ p)) i p))

    -- assoc-coh-π₂ :
    --   ∀ {s : S} {s′ : P s → S} 
    --     {s″ : (p : P s) → P (s′ p) → S} 
    --     {s‴ : (p : P s) → (p′ : P (s′ p)) → P (s″ p p′) → S} 
    --   → PentagonP' {B = λ cohs cohp → (p : P cohs) → P (s′ cohp)}
    --       (assoc-coh-σ {s} {s′} {s″} {s‴})
    --       (λ i p → ?)
    --       (λ i p → ?)
    --       (λ i p → ?)
    --       (λ i p → ?)
    --       (λ i p → ?)

open import Cubical.Foundations.Equiv

record IsCartesian (pmc : PsMndCont) : Type where
  open PsMndCont pmc
  field
    cart-e : P e ≃ Unit
    cart-m : {s : S} {s′ : P s → S} 
      → isEquiv (λ (p : P (m s s′)) → idfun (Σ (P s) (λ ↖p → P (s′ ↖p))) 
        (↖ p , ↗ p))
