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

    lUnit-π : ∀ (s : S)
      → ↖ {s} {const e} ≡[ lUnit-σ s , (λ _ _ → s) ]ᴾ idfun (P s)

    rUnit-σ : ∀ (s : S) 
      → m e (const s) ≡ s

    rUnit-π : ∀ (s : S)
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
        (λ p → ↗ (↖ {s′ = m↖↗ s″} p))

    assoc-π₃ :
      ∀ (s : S) (s′ : P s → S) 
      (s″ : (p : P s) → P (s′ p) → S)
      → (λ p → ↗ {s′ = s″ (↖ p)} (↗ {s′ = m′ s′ s″} p)) 
          ≡[ assoc-σ _ _ s″ , (λ i p → s″ (assoc-π₁ s s′ s″ i p) (assoc-π₂ s s′ s″ i p)) ]ᴾ
        ↗ {s′ = m↖↗ s″}

    lrUnit-coh-σ : 
      ∀ {s : S} {s′ : P s → S} 
      → Square
            {a₀₀ = m s (λ p → m e (const (s′ p)))} 
            {a₀₁ = m (m s (const e)) (λ p → s′ (↖ {s′ = const e} p))}
        (assoc-σ s (const e) (λ p _ → s′ p)) 
            {a₁₀ = m s (λ p → m e (const (s′ p)))} 
            {a₁₁ = m s s′}
        (λ i → m s (λ p → rUnit-σ (s′ p) i))
        (refl {x = m s (λ p → m e (const (s′ p)))})
        (λ i → m (lUnit-σ s i) (λ p → s′ (lUnit-π s i p)))

    lrUnit-coh-π₁ : 
      ∀ {s : S} {s′ : P s → S} 
      → Squareᴾ (lrUnit-coh-σ {s} {s′}) (λ _ _ _ → s)
            {π₀₀ = ↖ {s′ = λ p → m e (λ _ → s′ p)}}
            {π₀₁ = λ p → ↖ {s′ = const e} (↖ p)}
            {π₁₀ = ↖ {s′ = λ p → m e (λ _ → s′ p)}}
            {π₁₁ = ↖ {s′ = s′}}
        (assoc-π₁ s (const e) (λ p _ → s′ p))
        (λ i → ↖ {s′ = λ p → rUnit-σ (s′ p) i})
        (refl {x = ↖ {s′ = λ p → m e (λ _ → s′ p)}})
        (λ i p → lUnit-π s i (↖ {s′ = λ p′ → s′ (lUnit-π s i p′)} p))

    lrUnit-coh-π₂ :
      ∀ {s : S} {s′ : P s → S} 
      → Squareᴾ (lrUnit-coh-σ {s′ = s′})
        (λ i j p → s′ (lrUnit-coh-π₁ i j p))
            {π₀₀ = λ p → ↗ {s′ = const (s′ (↖ p))} (↗ p)}
            {π₀₁ = ↗ {s′ = λ p → s′ (↖ p)}}
            {π₁₀ = λ p → ↗ {s′ = const (s′ (↖ p))} (↗ p)}
            {π₁₁ = ↗ {s′ = λ p → s′ p}}
        (assoc-π₃ s (const e) (λ p _ → s′ p))
        (λ i p → rUnit-π (s′ (↖ p)) i (↗ {s′ = λ q → rUnit-σ (s′ q) i} p))
        (refl {x = λ p → ↗ {s′ = const (s′ (↖ p))} (↗ p)})
        (λ i → ↗ {s′ = λ p → s′ (lUnit-π s i p)})

    assoc-coh-σ :
      ∀ {s : S} {s′ : P s → S} 
        {s″ : (p : P s) → P (s′ p) → S} 
        {s‴ : (p : P s) → (p′ : P (s′ p)) → P (s″ p p′) → S} 
      → Hex 
            {a = m s (m′ s′ (λ p → m′ (s″ p) (s‴ p)))}
            {b = m s (m′ (m′ s′ s″) (λ p → m↖↗ (s‴ p)))}
            {c = m (m s (m′ s′ s″)) (m↖↗ (λ p → m↖↗ (s‴ p)))}
            {d = m (m (m s s′) (m↖↗ s″)) (m↖↗ (λ p → s‴ (↖ p) (↗ p)))}
            {e = m s (m′ s′ (λ p → m′ (s″ p) (s‴ p)))}
            {f = m (m s s′) (m↖↗ (m″ s″ s‴))}
        (λ i → m s (λ p → assoc-σ (s′ p) (s″ p) (s‴ p) i))
        (assoc-σ s (m′ s′ s″) (λ p → m↖↗ (s‴ p)))
        (λ i → m (assoc-σ s s′ s″ i) (λ (p : P (assoc-σ s s′ s″ i)) 
          → s‴ (assoc-π₁ s s′ s″ i p) (assoc-π₂ s s′ s″ i p) (assoc-π₃ s s′ s″ i p)))
        refl
        (assoc-σ s s′ (m″ s″ s‴))
        (assoc-σ (m s s′) (m↖↗ s″) (λ p → s‴ (↖ p) (↗ p)))

  private
    acσ-fill : 
      ∀ (s : S) (s′ : P s → S) 
        (s″ : (p : P s) → P (s′ p) → S) 
        (s‴ : (p : P s) → (p′ : P (s′ p)) → P (s″ p p′) → S) 
        (i j k : I) → S
    acσ-fill s s′ s″ s‴ = Hex-filler (assoc-coh-σ {s} {s′} {s″} {s‴}) 

  field
    assoc-coh-π₁ :
      ∀ {s : S} {s′ : P s → S} 
        {s″ : (p : P s) → P (s′ p) → S} 
        {s‴ : (p : P s) → (p′ : P (s′ p)) → P (s″ p p′) → S} 
      → HexP' (λ t → P t → P s)
              (assoc-coh-σ {s} {s′} {s″} {s‴})
              {a = ↖ {s′ = m′ s′ (λ p → m′ (s″ p) (s‴ p))}}
              {b = ↖ {s′ = m′ (m′ s′ s″) (λ p → m↖↗ (s‴ p))}}
              {c = ↖ {s′ = m↖↗ (λ p → m↖↗ (s‴ p))} » ↖}
              {d = ↖ » ↖ {s′ = m↖↗ s″} » ↖}
              {e = ↖ {s′ = m′ s′ (λ p → m′ (s″ p) (s‴ p))}}
              {f = ↖ {s′ = m↖↗ (m″ s″ s‴)} » ↖}
          (λ i p → ↖ {s′ = λ p → assoc-σ (s′ p) (s″ p) (s‴ p) i} p)
          (assoc-π₁ s (m′ s′ s″) (λ p → m↖↗ (s‴ p)))
          (λ i p → assoc-π₁ s s′ s″ i (↖ p))
          refl
          (assoc-π₁ s s′ (m″ s″ s‴))
          (λ i p → ↖ (assoc-π₁ (m s s′) (m↖↗ s″) (λ p → s‴ (↖ p) (↗ p)) i p))

  private
    acπ₁-fill : 
      ∀ (s : S) (s′ : P s → S) 
        (s″ : (p : P s) → P (s′ p) → S) 
        (s‴ : (p : P s) → (p′ : P (s′ p)) → P (s″ p p′) → S) 
        (i j k : I) → P (acσ-fill s s′ s″ s‴ i j k) → P s
    acπ₁-fill s s′ s″ s‴ = 
      HexP-filler 
        (λ i j k → P (acσ-fill s s′ s″ s‴ i j k) → P s) 
        (assoc-coh-π₁ {s} {s′} {s″} {s‴})

  field
    assoc-coh-π₂ :
      ∀ {s : S} {s′ : P s → S} 
        {s″ : (p : P s) → P (s′ p) → S} 
        {s‴ : (p : P s) → (p′ : P (s′ p)) → P (s″ p p′) → S} 
      → HexP (λ i j k 
            → (p : P (acσ-fill s s′ s″ s‴ i j k)) 
            → P (s′ (acπ₁-fill s s′ s″ s‴ i j k p)))
              {a = λ p → ↖ {s′ = λ p′ → m (s″ (↖ p) p′) (s‴ (↖ p) p′)} (↗ p)}
              {b = λ p → ↖ {s′ = s″ (↖ p)} (↖ (↗ p))}
              {c = λ p → ↖ {s′ = s″ (↖ (↖ p))} (↗ (↖ p))}
              {d = λ p → ↗ {s′ = s′} (↖ (↖ p))}
              {e = λ p → ↖ {s′ = m″ s″ s‴ (↖ p)} (↗ p)}
              {f = λ p → ↗ {s′ = s′} (↖ p)}
          (λ i p → assoc-π₁ (s′ (↖ p)) (s″ (↖ p)) (s‴ (↖ p)) i (↗ p))
          (λ i p → ↖ (assoc-π₂ s (m′ s′ s″) (λ p′ → m↖↗ (s‴ p′)) i p))
          (λ i p → assoc-π₂ s s′ s″ i (↖ p))
          refl
          (assoc-π₂ s s′ (m″ s″ s‴))
          (λ i p → ↗ (assoc-π₁ (m s s′) (m↖↗ s″) (λ p′ → s‴ (↖ p′) (↗ p′)) i p))

  private
    acπ₂-fill : 
      ∀ (s : S) (s′ : P s → S) 
        (s″ : (p : P s) → P (s′ p) → S) 
        (s‴ : (p : P s) → (p′ : P (s′ p)) → P (s″ p p′) → S) 
        (i j k : I) 
          → (p : P (acσ-fill s s′ s″ s‴ i j k)) 
          → P (s′ (acπ₁-fill s s′ s″ s‴ i j k p))
    acπ₂-fill s s′ s″ s‴ = 
      HexP-filler 
        (λ i j k 
            → (p : P (acσ-fill s s′ s″ s‴ i j k)) 
            → P (s′ (acπ₁-fill s s′ s″ s‴ i j k p)))
        (assoc-coh-π₂ {s} {s′} {s″} {s‴})

  field
    assoc-coh-π₃ :
      ∀ {s : S} {s′ : P s → S} 
        {s″ : (p : P s) → P (s′ p) → S} 
        {s‴ : (p : P s) → (p′ : P (s′ p)) → P (s″ p p′) → S} 
      → HexP (λ i j k 
            → (p : P (acσ-fill s s′ s″ s‴ i j k)) 
            → P (s″ (acπ₁-fill s s′ s″ s‴ i j k p) 
                (acπ₂-fill s s′ s″ s‴ i j k p)))
              {a = λ p → ↖ {s′ = s‴ (↖ p) (↖ (↗ p))} (↗ (↗ p))}
              {b = λ p → ↗ {s′ = s″ (↖ p)} (↖ (↗ p))}
              {c = λ p → ↗ {s′ = s″ (↖ (↖ p))} (↗ (↖ p))}
              {d = λ p → ↗ {s′ = m↖↗ s″} (↖ p)}
              {e = λ p → ↖ {s′ = s‴ (↖ p) (↖ (↗ p))} (↗ (↗ p))}
              {f = λ p → ↖ {s′ = s‴ (↖ (↖ p)) (↗ (↖ p))} (↗ p)}
          (λ i p → assoc-π₂ (s′ (↖ p)) (s″ (↖ p)) (s‴ (↖ p)) i (↗ p))
          (λ i p → ↗ (assoc-π₂ s (m′ s′ s″) (λ p′ → m↖↗ (s‴ p′)) i p))
          (λ i p → assoc-π₃ s s′ s″ i (↖ p))
          refl
          (λ i p → ↖ (assoc-π₃ s s′ (m″ s″ s‴) i p))
          (assoc-π₂ (m s s′) (m↖↗ s″) (λ p → s‴ (↖ p) (↗ p)))

  private
    acπ₃-fill : 
      ∀ (s : S) (s′ : P s → S) 
        (s″ : (p : P s) → P (s′ p) → S) 
        (s‴ : (p : P s) → (p′ : P (s′ p)) → P (s″ p p′) → S) 
        (i j k : I) 
        → (p : P (acσ-fill s s′ s″ s‴ i j k)) 
        → P (s″ (acπ₁-fill s s′ s″ s‴ i j k p) 
            (acπ₂-fill s s′ s″ s‴ i j k p))
    acπ₃-fill s s′ s″ s‴ = 
      HexP-filler 
        (λ i j k 
            → (p : P (acσ-fill s s′ s″ s‴ i j k)) 
            → P (s″ (acπ₁-fill s s′ s″ s‴ i j k p) 
                (acπ₂-fill s s′ s″ s‴ i j k p)))
        (assoc-coh-π₃ {s} {s′} {s″} {s‴})

  field
    assoc-coh-π₄ :
      ∀ {s : S} {s′ : P s → S} 
        {s″ : (p : P s) → P (s′ p) → S} 
        {s‴ : (p : P s) → (p′ : P (s′ p)) → P (s″ p p′) → S} 
      → HexP (λ i j k 
            → (p : P (acσ-fill s s′ s″ s‴ i j k)) 
            → P (s‴ (acπ₁-fill s s′ s″ s‴ i j k p) 
                (acπ₂-fill s s′ s″ s‴ i j k p)
                (acπ₃-fill s s′ s″ s‴ i j k p)))
              {a = λ p → ↗ {s′ = s‴ (↖ p) (↖ (↗ p))} (↗ (↗ p))}
              {b = λ p → ↗ {s′ = λ q → s‴ (↖ p) (↖ q) (↗ q)} (↗ p)}
              {c = λ p → ↗ {s′ = λ p → s‴ (↖ p) (↖ (↗ p)) (↗ (↗ p))} p}
              {d = λ p → ↗ {s′ = λ p → s‴ (↖ (↖ p)) (↗ (↖ p)) (↗ p)} p}
              {e = λ p → ↗ {s′ = s‴ (↖ p) (↖ (↗ p))} (↗ (↗ p))}
              {f = λ p → ↗ {s′ = s‴ (↖ (↖ p)) (↗ (↖ p))} (↗ p)}
          (λ i p → assoc-π₃ (s′ (↖ p)) (s″ (↖ p)) (s‴ (↖ p)) i (↗ p))
          (λ i p → assoc-π₃ s (m′ s′ s″) (λ p → m↖↗ (s‴ p)) i p)
          (λ i → ↗ {s′ = λ p → s‴ (assoc-π₁ s s′ s″ i p) (assoc-π₂ s s′ s″ i p) (assoc-π₃ s s′ s″ i p)})
          refl
          (λ i p → ↗ (assoc-π₃ s s′ (m″ s″ s‴) i p))
          (assoc-π₃ (m s s′) (m↖↗ s″) (λ p → s‴ (↖ p) (↗ p)))

-- private
--   acπ₄-fill : 
--     ∀ (s : S) (s′ : P s → S) 
--       (s″ : (p : P s) → P (s′ p) → S) 
--       (s‴ : (p : P s) → (p′ : P (s′ p)) → P (s″ p p′) → S) 
--       (i j k : I) 
--       → (p : P (acσ-fill s s′ s″ s‴ i j k)) 
--       → P (s‴ (acπ₁-fill s s′ s″ s‴ i j k p) 
--           (acπ₂-fill s s′ s″ s‴ i j k p)
--           (acπ₃-fill s s′ s″ s‴ i j k p))
--   acπ₄-fill s s′ s″ s‴ = 
--     HexP-filler 
--       (λ i j k 
--           → (p : P (acσ-fill s s′ s″ s‴ i j k)) 
--           → P (s‴ (acπ₁-fill s s′ s″ s‴ i j k p) 
--               (acπ₂-fill s s′ s″ s‴ i j k p)
--               (acπ₃-fill s s′ s″ s‴ i j k p)))
--       (assoc-coh-π₃ {s} {s′} {s″} {s‴})

open import Cubical.Foundations.Equiv

record IsCartesian (pmc : PsMndCont) : Type where
  open PsMndCont pmc
  field
    cart-e : P e ≃ Unit
    cart-m : {s : S} {s′ : P s → S} 
      → isEquiv (λ (p : P (m s s′)) → idfun (Σ (P s) (λ ↖p → P (s′ ↖p))) 
        (↖ p , ↗ p))
