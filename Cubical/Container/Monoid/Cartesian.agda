open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Container.Base
open import Cubical.Container.Monoid.PsMndCont

module Cubical.Container.Monoid.Cartesian
  {T : Container} where

open Container T

record PsMndCont₀ : Type where
  field
    e : S
    m : (s : S) → (P s → S) → S
    ↖ : {s : S} {s′ : P s → S} 
      (p : P (m s s′)) → P s
    ↗ : {s : S} {s′ : P s → S} 
      (p : P (m s s′)) → P (s′ (↖ p))

  -- Helpers

  -- Currying through m
  -- Kind of like currying in a T-induced subuniverse?
  T-uncurry :
    {s : S}         -- A 
    {s′ : P s → S}  -- B 
    {C : (p : P s) → P (s′ p) → Type}
    → (f : (p : P s) (p′ : P (s′ p)) → C p p′)
    → (p : P (m s s′)) → C (↖ p) (↗ p)
  T-uncurry f p = f (↖ p) (↗ p)

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
  m↖↗ s″ = T-uncurry s″
  -- m↖↗ s″ p = s″ (↖ p) (↗ p)

  m↖↗′ : ∀ {s : S} {s′ : P s → S} 
    {s″ : (p : P s) → P (s′ p) → S} 
    (s‴ : (p : P s) → (p′ : P (s′ p)) → P (s″ p p′) → S) 
    → (p : P (m s s′)) → P (m↖↗ s″ p) → S
  m↖↗′ s‴ = T-uncurry s‴
  -- m↖↗′ s‴ p = s‴ (↖ p) (↗ p)

module _ (pmc₀ : PsMndCont₀) where
  open PsMndCont₀ pmc₀

  record PsMndCont₁-cart : Type where
    field
      cart-e : isEquiv {A = P e} {B = Unit}
        (const tt)

      cart-m : {s : S} {s′ : P s → S} 
        → isEquiv {A = P (m s s′)} {B = Σ (P s) (λ p → P (s′ p))}
          (T-uncurry _,_)
      -- is cart-m equivalent to asking that
      -- T-uncurry is an equiv. for all B?
      

  record PsMndCont₁-σ : Type where
    field
      lUnit-σ : ∀ (s : S) → m s (const e) ≡ s

      rUnit-σ : ∀ (s : S) → m e (const s) ≡ s

      -- This can probably be rewritten in terms of ⟦T⟧₁, 
      -- but is it worth it?
      assoc-σ : 
        ∀ (s : S) (s′ : P s → S) 
          (s″ : (p : P s) → P (s′ p) → S)
        → m s (m′ s′ s″) ≡ m (m s s′) (m↖↗ s″)

module _ 
  (pmc₀ : PsMndCont₀) 
  (pmc₁σ : PsMndCont₁-σ pmc₀)
  (pmc₁c : PsMndCont₁-cart pmc₀) where
  open PsMndCont₀ pmc₀
  open PsMndCont₁-σ pmc₁σ
  open PsMndCont₁-cart pmc₁c
  open import Cubical.Foundations.Isomorphism
  open Iso

  cart-e-iso = equivToIso (_ , cart-e)
  cart-m-iso = λ {s : S} {s′ : P s → S} 
    → equivToIso (_ , cart-m {s} {s′})

  tt′ : P e
  tt′ = invEq (_ , cart-e) tt

  pmc : PsMndCont T
  pmc .PsMndCont.e = e
  pmc .PsMndCont.m = m
  pmc .PsMndCont.↖ = ↖
  pmc .PsMndCont.↗ = ↗
  pmc .PsMndCont.lUnit-σ = lUnit-σ
  pmc .PsMndCont.lUnit-π s i p = 
    {! cart-m-iso {s} {const e} .fun ? .fst  !}
    -- {! cart-m-iso {s} {const e} .rightInv (? , ?) i .fst  !}
  pmc .PsMndCont.rUnit-σ = rUnit-σ
  -- Reason on the pullback
  pmc .PsMndCont.rUnit-π s i p = 
    {! transp (λ j → P ()) !}
  pmc .PsMndCont.assoc-σ = assoc-σ
  pmc .PsMndCont.assoc-π₁ = {! !}
  pmc .PsMndCont.assoc-π₂ = {! !}
  pmc .PsMndCont.assoc-π₃ = {! !}
  pmc .PsMndCont.lrUnit-coh-σ = {! !}
  pmc .PsMndCont.lrUnit-coh-π₁ = {! !}
  pmc .PsMndCont.lrUnit-coh-π₂ = {! !}
  pmc .PsMndCont.assoc-coh-σ = {! !}
  pmc .PsMndCont.assoc-coh-π₁ = {! !}
  pmc .PsMndCont.assoc-coh-π₂ = {! !}
  pmc .PsMndCont.assoc-coh-π₃ = {! !}
  pmc .PsMndCont.assoc-coh-π₄ = {! !}

  -- module _ (isCart : IsCartesian) where
  --   open IsCartesian isCart
  --   open import Cubical.Foundations.Isomorphism
  --   open Iso
  --
    -- cart-e-iso = equivToIso (_ , cart-e)
    --
    -- tt′ : P e
    -- tt′ = invEq (_ , cart-e) tt
    --
    -- lUnit-↗-cart :
    --   ∀ (s : S)
    --   → ↗ {s} {const e} ≡ const tt′
    -- lUnit-↗-cart s = funExt λ p → sym (cart-e-iso .leftInv (↗ p))

    -- lUnit-π-cart :
    --   ∀ (s : S)
    --   → PathP (λ i →
    --       PathP (λ j →
    --         (p : P {! !}) → P {! !}) 
    --       {! !}
    --       {! !})
    --     (lUnit-π s)
    --     {! !}


    -- lUnit-π-unique : 
    --     PathP {! !}
    --       lUnit-π
    --       {! !}
