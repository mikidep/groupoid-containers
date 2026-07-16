open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Container.Base
import Cubical.Container.Constructions as CC
open import Cubical.Container.Path
open import Cubical.Container.Monoid.Definition
open import Cubical.Container.Monoid.PsMndCont

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
    (funExt λ _ → λ i p → lUnit-π i p , _)

  pm-rUnit : id ⊗₁ pm-η ⋆ pm-μ ≡ MC.rUnit _
  pm-rUnit = cong₂ CMor 
    (funExt λ ks → rUnit-σ (ks .snd tt)) 
    (funExt λ _ → λ i p → _ , rUnit-π i p)

  pm-assoc : MC.assoc _ _ _ ⋆ pm-μ ⊗₁ id ⋆ pm-μ ≡ id ⊗₁ pm-μ ⋆ pm-μ
  pm-assoc = cong₂ CMor
    (funExt λ { ((s , s′), s″) → assoc-σ _ _ _ }) 
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
PsMndCont→Pseudomonoid .assoc-coh = CMorPentagon′ aux
  where
  open import Prelude.Square
  open import Prelude.Utils
  aux : ∀ ss → _
  aux ss = ΣPentagon (auxσ , auxπ)
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
    auxσ : Pentagon 
      (λ i → m s (λ p → assoc-σ (s′ p) (s″ p) (s‴ p) i))
      (assoc-σ s (m′ s′ s″) (λ p → m↖↗ (s‴ p)))
      (λ i → m (assoc-σ s s′ s″ i) (λ (p : P (assoc-σ s s′ s″ i)) → s‴ 
        (assoc-π₁ s s′ s″ i p) (assoc-π₂ s s′ s″ i p) (assoc-π₃ s s′ s″ i p)))
      (assoc-σ s s′ λ p → m′ (s″ p) (s‴ p))
      (assoc-σ (m s s′) (m↖↗ s″) (λ p → s‴ (↖ p) (↗ p)))
    auxσ = assoc-coh-σ {s} {s′} {s″} {s‴}
    auxπ : PentagonP' {B = B} auxσ 
      (λ i x → 
          ( (↖ x 
            , assoc-π₁ (s′ (↖ x)) (s″ (↖ x)) (s‴ (↖ x)) i (↗ x)) 
          , assoc-π₂ (s′ (↖ x)) (s″ (↖ x)) (s‴ (↖ x)) i (↗ x)) 
        , assoc-π₃ (s′ (↖ x)) (s″ (↖ x)) (s‴ (↖ x)) i (↗ x))
      (λ i x → 
          ( ( assoc-π₁ s (m′ s′ s″) (λ p → m↖↗ (s‴ p)) i x 
            , ↖ (assoc-π₂ s (m′ s′ s″) (λ p → m↖↗ (s‴ p)) i x)) 
          , ↗ (assoc-π₂ s (m′ s′ s″) (λ p → m↖↗ (s‴ p)) i x)) 
        , assoc-π₃ s (m′ s′ s″) (λ p → m↖↗ (s‴ p)) i x)
      (λ i x → 
          ( ( assoc-π₁ s s′ s″ i (↖ x) 
            , assoc-π₂ s s′ s″ i (↖ x)) 
          , assoc-π₃ s s′ s″ i (↖ x)) 
        , ↗ x)
      (λ i x → 
          ( ( assoc-π₁ s s′ (λ p′ → m′ (s″ p′) (s‴ p′)) i x 
            , assoc-π₂ s s′ (λ p′ → m′ (s″ p′) (s‴ p′)) i x) 
          , ↖ (assoc-π₃ s s′ (λ p′ → m′ (s″ p′) (s‴ p′)) i x)) 
        , ↗ (assoc-π₃ s s′ (λ p′ → m′ (s″ p′) (s‴ p′)) i x))
      (λ i x → 
          ( ( ↖ (assoc-π₁ (m s s′) (m↖↗ s″) (λ p → s‴ (↖ p) (↗ p)) i x) 
            , ↗ (assoc-π₁ (m s s′) (m↖↗ s″) (λ p → s‴ (↖ p) (↗ p)) i x)) 
          , assoc-π₂ (m s s′) (m↖↗ s″) (λ p → s‴ (↖ p) (↗ p)) i x) 
        , assoc-π₃ (m s s′) (m↖↗ s″) (λ p → s‴ (↖ p) (↗ p)) i x)
    auxπ = {! !}

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
