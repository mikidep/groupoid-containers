open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Sigma
open import Cubical.Data.Unit


open import Cubical.Container.Base
open import Cubical.Container.Path
open import Cubical.Container.Monoid.Definition
open import Cubical.Container.Monoid.PsMndCont

open import Prelude.Shapes

module Cubical.Container.Monoid.Equivalence.From
  (T : Container) (pm : Pseudomonoid T) where
 
open _⇒_

open Container T

open PsMndCont 
open Pseudomonoid pm

lrUnit-coh′ = CMor□′⁻ lrUnit-coh

Pseudomonoid→PsMndCont : PsMndCont T
Pseudomonoid→PsMndCont .e = η .σ tt
Pseudomonoid→PsMndCont .m = curry (μ .σ)
Pseudomonoid→PsMndCont .↖ p = μ .π _ p .fst
Pseudomonoid→PsMndCont .↗ p = μ .π _ p .snd
Pseudomonoid→PsMndCont .lUnit-σ s i = lUnit i .σ (s , const tt)
Pseudomonoid→PsMndCont .lUnit-π s i p = lUnit i .π (s , const tt) p .fst
Pseudomonoid→PsMndCont .rUnit-σ s i = rUnit i .σ (tt , const s)
Pseudomonoid→PsMndCont .rUnit-π s i p = rUnit i .π (tt , const s) p .snd
Pseudomonoid→PsMndCont .assoc-σ s s′ s″ i = 
  assoc i .σ ((s , s′) , uncurry s″)
Pseudomonoid→PsMndCont .assoc-π₁ s s′ s″ i p = 
  assoc i .π ((s , s′) , uncurry s″) p .fst .fst
Pseudomonoid→PsMndCont .assoc-π₂ s s′ s″ i p = 
  assoc i .π ((s , s′) , uncurry s″) p .fst .snd
Pseudomonoid→PsMndCont .assoc-π₃ s s′ s″ i p = 
  assoc i .π ((s , s′) , uncurry s″) p .snd
Pseudomonoid→PsMndCont .lrUnit-coh-σ {s} {s′} i j = 
  lrUnit-coh i j .σ ((s , const tt) , λ ptt → s′ (ptt .fst))
Pseudomonoid→PsMndCont .lrUnit-coh-π₁ {s} {s′} i j p = 
  lrUnit-coh i j .π ((s , const tt) , λ ptt → s′ (ptt .fst)) p .fst .fst
Pseudomonoid→PsMndCont .lrUnit-coh-π₂ {s} {s′} i j p = 
  lrUnit-coh i j .π ((s , const tt) , λ ptt → s′ (ptt .fst)) p .snd
Pseudomonoid→PsMndCont .assoc-coh-σ {s} {s′} {s″} {s‴} .fst i = 
  assoc-coh .fst i .σ (((s , s′) , uncurry s″) , uncurry (uncurry s‴))
Pseudomonoid→PsMndCont .assoc-coh-σ {s} {s′} {s″} {s‴} .snd .fst i j = 
  assoc-coh .snd .fst i j .σ 
    (((s , s′) , uncurry s″) , uncurry (uncurry s‴))
Pseudomonoid→PsMndCont .assoc-coh-σ {s} {s′} {s″} {s‴} .snd .snd i j = 
  assoc-coh .snd .snd i j .σ 
    (((s , s′) , uncurry s″) , uncurry (uncurry s‴))
Pseudomonoid→PsMndCont .assoc-coh-π₁ {s} {s′} {s″} {s‴} .fst i p = 
  assoc-coh .fst i .π 
    (((s , s′) , uncurry s″) , uncurry (uncurry s‴)) p
    .fst .fst .fst
Pseudomonoid→PsMndCont .assoc-coh-π₁ {s} {s′} {s″} {s‴} .snd .fst i j p = 
  assoc-coh .snd .fst i j .π 
    (((s , s′) , uncurry s″) , uncurry (uncurry s‴)) p
    .fst .fst .fst
Pseudomonoid→PsMndCont .assoc-coh-π₁ {s} {s′} {s″} {s‴} .snd .snd i j p = 
  assoc-coh .snd .snd i j .π 
    (((s , s′) , uncurry s″) , uncurry (uncurry s‴)) p
    .fst .fst .fst
Pseudomonoid→PsMndCont .assoc-coh-π₂ {s} {s′} {s″} {s‴} .fst i p = 
  assoc-coh .fst i .π 
    (((s , s′) , uncurry s″) , uncurry (uncurry s‴)) p
    .fst .fst .snd
Pseudomonoid→PsMndCont .assoc-coh-π₂ {s} {s′} {s″} {s‴} .snd .fst i j p = 
  assoc-coh .snd .fst i j .π 
    (((s , s′) , uncurry s″) , uncurry (uncurry s‴)) p
    .fst .fst .snd
Pseudomonoid→PsMndCont .assoc-coh-π₂ {s} {s′} {s″} {s‴} .snd .snd i j p = 
  assoc-coh .snd .snd i j .π 
    (((s , s′) , uncurry s″) , uncurry (uncurry s‴)) p
    .fst .fst .snd
Pseudomonoid→PsMndCont .assoc-coh-π₃ {s} {s′} {s″} {s‴} .fst i p = 
  assoc-coh .fst i .π 
    (((s , s′) , uncurry s″) , uncurry (uncurry s‴)) p
    .fst .snd
Pseudomonoid→PsMndCont .assoc-coh-π₃ {s} {s′} {s″} {s‴} .snd .fst i j p = 
  assoc-coh .snd .fst i j .π 
    (((s , s′) , uncurry s″) , uncurry (uncurry s‴)) p
    .fst .snd
Pseudomonoid→PsMndCont .assoc-coh-π₃ {s} {s′} {s″} {s‴} .snd .snd i j p = 
  assoc-coh .snd .snd i j .π 
    (((s , s′) , uncurry s″) , uncurry (uncurry s‴)) p
    .fst .snd
Pseudomonoid→PsMndCont .assoc-coh-π₄ {s} {s′} {s″} {s‴} .fst i p = 
  assoc-coh .fst i .π 
    (((s , s′) , uncurry s″) , uncurry (uncurry s‴)) p
    .snd
Pseudomonoid→PsMndCont .assoc-coh-π₄ {s} {s′} {s″} {s‴} .snd .fst i j p = 
  assoc-coh .snd .fst i j .π 
    (((s , s′) , uncurry s″) , uncurry (uncurry s‴)) p
    .snd
Pseudomonoid→PsMndCont .assoc-coh-π₄ {s} {s′} {s″} {s‴} .snd .snd i j p = 
  assoc-coh .snd .snd i j .π 
    (((s , s′) , uncurry s″) , uncurry (uncurry s‴)) p
    .snd
