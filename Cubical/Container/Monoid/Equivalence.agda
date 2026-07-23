open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Container.Base
import Cubical.Container.Constructions as CC
open import Cubical.Container.Path
open import Cubical.Container.Monoid.Definition
open import Cubical.Container.Monoid.PsMndCont

open import Prelude.Shapes

module Cubical.Container.Monoid.Equivalence 
  (T : Container) (pmc : PsMndCont T) where

open CC.Morphisms using (_⋆_; id)
open CC.Monoidal using (𝟙; _⊗₀_; _⊗₁_)
private module MC = CC.Monoidal

open PsMndCont pmc
open Pseudomonoid
open _⇒_

open Container T

private
  pm-η : 𝟙 ⇒ T
  pm-η .σ _ = e
  pm-η .π _ = _

  pm-μ : T ⊗₀ T ⇒ T
  pm-μ .σ = uncurry m
  pm-μ .π _ pq = ↖ pq , ↗ pq

  pm-lUnit : pm-η ⊗₁ id ⋆ pm-μ ≡ MC.lUnit _
  pm-lUnit = cong₂ CMor
    (funExt λ ks → lUnit-σ (ks .fst))
    (funExt λ ks → λ i p → lUnit-π (ks .fst) i p , _)

  pm-rUnit : id ⊗₁ pm-η ⋆ pm-μ ≡ MC.rUnit _
  pm-rUnit = cong₂ CMor 
    (funExt λ ks → rUnit-σ (ks .snd tt)) 
    (funExt λ ks → λ i p → _ , rUnit-π (ks .snd tt) i p)

  pm-assoc : MC.assoc _ _ _ ⋆ pm-μ ⊗₁ id ⋆ pm-μ ≡ id ⊗₁ pm-μ ⋆ pm-μ
  pm-assoc = cong₂ CMor
    (funExt λ { ((s , s′), s″) → assoc-σ s s′ (curry s″) }) 
    (funExt λ { ((s , s′), s″) 
      → λ i p → 
        ( assoc-π₁ s s′ (curry s″) i p 
        , assoc-π₂ s s′ (curry s″) i p) 
        , assoc-π₃ s s′ (curry s″) i p })

PsMndCont→Pseudomonoid : Pseudomonoid T
PsMndCont→Pseudomonoid .η = pm-η
PsMndCont→Pseudomonoid .μ = pm-μ
PsMndCont→Pseudomonoid .lUnit = pm-lUnit
PsMndCont→Pseudomonoid .rUnit = pm-rUnit
PsMndCont→Pseudomonoid .assoc = pm-assoc
PsMndCont→Pseudomonoid .assoc-coh = 
  Hex→compPath cmorhex 
  ∙ sym (doubleCompPath≡compPath _ _ _)
  where
  open import Prelude.Square
  open import Prelude.Shapes
  aux : ∀ ss → _
  aux ss = ΣHex (auxσ , auxπ)
    where
    s = ss .fst .fst .fst
    s′ = ss .fst .fst .snd
    s″ = curry (ss .fst .snd)
    s‴ = curry (curry (ss .snd))
    B : S → Type
    B cohs = P cohs →
      Σ (Σ (Σ (P s) (λ p′ → P (s′ p′)))
       (λ p″ → P (uncurry s″ p″)))
      (λ p‴ → P (uncurry (uncurry s‴) p‴))
    auxσ = assoc-coh-σ {s} {s′} {s″} {s‴}
    auxπ : HexP (λ i j k → B (Hex-filler (assoc-coh-σ {s} {s′} {s″} {s‴}) i j k))
      (λ i p → 
          ( (↖ p 
            , assoc-π₁ (s′ (↖ p)) (s″ (↖ p)) (s‴ (↖ p)) i (↗ p)) 
          , assoc-π₂ (s′ (↖ p)) (s″ (↖ p)) (s‴ (↖ p)) i (↗ p)) 
        , assoc-π₃ (s′ (↖ p)) (s″ (↖ p)) (s‴ (↖ p)) i (↗ p))
      (λ i p → 
          ( ( assoc-π₁ s (m′ s′ s″) (λ p′ → m↖↗ (s‴ p′)) i p 
            , ↖ (assoc-π₂ s (m′ s′ s″) (λ p′ → m↖↗ (s‴ p′)) i p)) 
          , ↗ (assoc-π₂ s (m′ s′ s″) (λ p′ → m↖↗ (s‴ p′)) i p)) 
        , assoc-π₃ s (m′ s′ s″) (λ p′ → m↖↗ (s‴ p′)) i p)
      (λ i p → 
          ( ( assoc-π₁ s s′ s″ i (↖ p) 
            , assoc-π₂ s s′ s″ i (↖ p)) 
          , assoc-π₃ s s′ s″ i (↖ p)) 
        , ↗ p)
      refl
      (λ i p → 
          ( ( assoc-π₁ s s′ (λ p′ → m′ (s″ p′) (s‴ p′)) i p 
            , assoc-π₂ s s′ (λ p′ → m′ (s″ p′) (s‴ p′)) i p) 
          , ↖ (assoc-π₃ s s′ (λ p′ → m′ (s″ p′) (s‴ p′)) i p)) 
        , ↗ (assoc-π₃ s s′ (λ p′ → m′ (s″ p′) (s‴ p′)) i p))
      (λ i p → 
          ( ( ↖ (assoc-π₁ (m s s′) (m↖↗ s″) (λ p′ → s‴ (↖ p′) (↗ p′)) i p) 
            , ↗ (assoc-π₁ (m s s′) (m↖↗ s″) (λ p′ → s‴ (↖ p′) (↗ p′)) i p)) 
          , assoc-π₂ (m s s′) (m↖↗ s″) (λ p′ → s‴ (↖ p′) (↗ p′)) i p) 
        , assoc-π₃ (m s s′) (m↖↗ s″) (λ p′ → s‴ (↖ p′) (↗ p′)) i p)
    auxπ .fst      i p .fst .fst .fst = assoc-coh-π₁ .fst i p
    auxπ .fst      i p .fst .fst .snd = assoc-coh-π₂ .fst i p
    auxπ .fst      i p .fst .snd      = assoc-coh-π₃ .fst i p
    auxπ .fst      i p .snd           = assoc-coh-π₄ .fst i p
    auxπ .snd .fst i j p .fst .fst .fst = assoc-coh-π₁ .snd .fst i j p
    auxπ .snd .fst i j p .fst .fst .snd = assoc-coh-π₂ .snd .fst i j p
    auxπ .snd .fst i j p .fst .snd      = assoc-coh-π₃ .snd .fst i j p
    auxπ .snd .fst i j p .snd           = assoc-coh-π₄ .snd .fst i j p
    auxπ .snd .snd i j p .fst .fst .fst = assoc-coh-π₁ .snd .snd i j p
    auxπ .snd .snd i j p .fst .fst .snd = assoc-coh-π₂ .snd .snd i j p
    auxπ .snd .snd i j p .fst .snd      = assoc-coh-π₃ .snd .snd i j p
    auxπ .snd .snd i j p .snd           = assoc-coh-π₄ .snd .snd i j p
  cmorhex = CMorHex′ aux

PsMndCont→Pseudomonoid .lrUnit-coh =
  PathP→compPathL∙∙
    (CMor□′ λ s → ΣSquare (
      lrUnit-coh-σ
      , λ i j p → (lrUnit-coh-π₁ i j p , _) 
        , lrUnit-coh-π₂ i j p
      ))
  where
  open import Cubical.Foundations.Path
  open import Prelude.Square
