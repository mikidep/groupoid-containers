{-# OPTIONS --allow-unsolved-metas #-}
open import Cubical.Foundations.Prelude

open import Cubical.Foundations.Function
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

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

open CC.Path S P
open CC.Square S P

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

open import Prelude.Utils

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
      ∀ {s : S} {s′ : P s → S} 
      {s″ : (p : P s) → P (s′ p) → S}
      → m s (m′ s′ s″)
        ≡ m (m s s′) (m↖↗ s″)

    assoc-π₁ :
      ∀ {s : S} {s′ : P s → S} 
      {s″ : (p : P s) → P (s′ p) → S}
      → ↖ {s′ = m′ s′ s″} 
          ≡[ assoc-σ , (λ _ _ → s) ]ᴾ 
        (↖ {s′ = m↖↗ s″} » ↖)

    assoc-π₂ :
      ∀ {s : S} {s′ : P s → S} 
      {s″ : (p : P s) → P (s′ p) → S}
      → (λ p → ↖ {s′ = s″ (↖ p)} (↗ {s′ = m′ s′ s″} p)) 
          ≡[ assoc-σ , (λ i p → s′ (assoc-π₁ i p)) ]ᴾ
        (↖ {s′ = m↖↗ s″} » ↗)

    assoc-π₃ :
      ∀ {s : S} {s′ : P s → S} 
      {s″ : (p : P s) → P (s′ p) → S}
      → (λ p → ↗ {s′ = s″ (↖ p)} (↗ {s′ = m′ s′ s″} p)) 
          ≡[ assoc-σ {s″ = s″} , (λ i p → s″ (assoc-π₁ i p) (assoc-π₂ i p)) ]ᴾ
        ↗ {s′ = m↖↗ s″}

    lrUnit-coh-σ : 
      ∀ {s : S} {s′ : P s → S} 
      → Square
        assoc-σ 
        (cong (m s) (funExt λ p → rUnit-σ (s′ p)))
        (refl {x = m s (λ p → m e (const (s′ p)))})
        (cong₂ (λ s pp → m s (pp » s′)) (lUnit-σ s) lUnit-π)

    lrUnit-coh-π₁ : 
      ∀ {s : S} {s′ : P s → S} 
      → Squareᴾ (lrUnit-coh-σ {s} {s′}) (λ _ _ _ → s)
        assoc-π₁
        (cong (λ x → ↖ {s′ = x}) (funExt (λ p → rUnit-σ (s′ p))))
        refl 
        (congP (λ i → ↖ {s′ = λ p → s′ (lUnit-π i p)} »_) lUnit-π)
        -- (λ i p → lUnit-π i (↖ {s′ = λ x → s′ (lUnit-π i x)} p))

    lrUnit-coh-π₂ :
      ∀ {s : S} {s′ : P s → S} 
      → Squareᴾ (lrUnit-coh-σ {s′ = s′})
        (λ i j p → s′ (lrUnit-coh-π₁ i j p))
        assoc-π₃
        (λ i p → rUnit-π i (↗ {s′ = λ q → rUnit-σ (s′ q) i} p))
        refl
        (congP (λ j f → ↗ {s′ = λ p → s′ (f p)}) lUnit-π)

    -- assoc-coh-σ :
    --   ∀ {s : S} {s′ : P s → S} 
    --     {s″ : (p : P s) → P (s′ p) → S} 
    --     {s‴ : (p : P s) → (p′ : P (s′ p)) → P (s″ p p′) → S} 
    --   → Square
    --     (assoc-σ {s = s} {s′ = s′} {s″ = λ p → m′ (s″ p) (s‴ p)})
    --     {! !}
    --     (λ i → m s (λ p → assoc-σ {s = s′ p} {s′ = s″ p} {s″ = s‴ p} i))
    --     (assoc-σ {s = m s s′} {s′ = (m↖↗ s″)} {s″ = λ p → s‴ (↖ p) (↗ p)})

-- module _ (pmc : PsMndCont) where
--   open PsMndCont pmc
--   open Pseudomonoid
--   open _⇒_
--
--   private
--     pm-η : 𝟙 ⇒ T
--     pm-η .σ _ = e
--     pm-η .π _ = _
--
--     pm-μ : T ⊗₀ T ⇒ T
--     pm-μ .σ = uncurry m
--     pm-μ .π _ pq = ↖ pq , ↗ pq
--
--   PsMndCont→Pseudomonoid : Pseudomonoid
--   PsMndCont→Pseudomonoid .η = pm-η
--   PsMndCont→Pseudomonoid .μ = pm-μ
--   PsMndCont→Pseudomonoid .lUnit = cong₂ CMor
--     (funExt λ ks → lUnit-σ (ks .fst))
--     (funExt λ _ → λ i p → lUnit-π i p , _)
--   PsMndCont→Pseudomonoid .rUnit = cong₂ CMor 
--     (funExt λ ks → rUnit-σ (ks .snd tt)) 
--     (funExt λ _ → λ i p → _ , rUnit-π i p)
--   PsMndCont→Pseudomonoid .assoc = cong₂ CMor
--     (funExt λ { ((s , s′), s″) → assoc-σ }) 
--     (funExt λ { ((s , s′), s″) 
--       → λ i p → (assoc-π₁ i p , assoc-π₂ i p) , assoc-π₃ i p }) 
--   PsMndCont→Pseudomonoid .assoc-coh = 
--     Square→compPath 
--       (CMor□′ λ s → ΣSquare (
--         goalσ s
--         , {! !}
--         ))
--     where
--     open import Cubical.Foundations.Path
--     open import Prelude.Square
--     goalσ : ∀ s → _
--     goalσ (((s , s′) , s″') , s‴') = goal
--       where
--       s″ = curry s″'
--       s‴ = curry (curry s‴')
--       a = assoc-σ
--       b = λ i → m (assoc-σ i) (λ p → s‴ (assoc-π₁ i p) (assoc-π₂ i p) (assoc-π₃ i p))
--       goal : Square
--         (assoc-σ {s = s} {s′ = s′} {s″ = λ p q → m (s″ p q) (s‴ p q)})
--         {! _ !}
--         (λ i → m s (λ p → assoc-σ {s = s′ p} {s′ = s″ p} {s″ = s‴ p} i))
--         (assoc-σ {s = m s s′} {s′ = m↖↗ s″} {s″ = λ p → s‴ (↖ p) (↗ p)})
--       goal = {! !}
--   PsMndCont→Pseudomonoid .lrUnit-coh = 
--     PathP→compPathL∙∙
--       (CMor□′ λ s → ΣSquare (
--         lrUnit-coh-σ
--         , goal s
--         ))
--     where
--     open import Cubical.Foundations.Path
--     open import Prelude.Square
--     goal : (s : Σ (Σ S (λ s₁ → P s₁ → Unit)) 
--         (λ s₁ → Σ (P (s₁ .fst)) (λ p′ → Unit) → S)) 
--       → SquareP (λ i j → P (lrUnit-coh-σ {s′ = λ p → s .snd (p , _)} i j) 
--           → Σ (Σ (P (s .fst .fst)) (λ p′ → Unit)) (λ p′ → P (s .snd p′)))
--         (λ i x → (assoc-π₁ i x , tt) , assoc-π₃ i x)
--         (λ i x → (↖ x , tt) , rUnit-π i (↗ x))
--         (λ _ x → (↖ x , tt) , ↗ (↗ x)) 
--         (λ i x → (lUnit-π i (↖ x) , tt) , ↗ x)
--     goal ((s , _) , ss) i j p .fst = lrUnit-coh-π₁ i j p , _
--     goal ((s , _) , ss) i j p .snd = lrUnit-coh-π₂ i j p
--
