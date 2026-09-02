open import Cubical.Foundations.Prelude

open import Cubical.Foundations.Function
open import Cubical.Data.Unit

open import Cubical.Container.Base
open import Cubical.Container.Monoid.PsMndCont

module Cubical.Container.Monoid.Free (T : Container) where

open Container T

data S* : Type where
  unit : S*
  sup : (s : S) → (ps* : P s → S*) → S*

module _ 
  (B : S* → Type)
  (unit′ : B unit)
  (sup′ : {s : S} {ps* : P s → S*} 
    (ps*′ : (p : P s) → B (ps* p)) → B (sup s ps*))
  where

  S*-elim : ∀ s* → B s*
  S*-elim unit = unit′
  S*-elim (sup s ps*) = sup′ λ p → S*-elim (ps* p)

P* : S* → Type
P* unit = Unit
P* (sup s ps*) = Σ (P s) (λ p → P* (ps* p))

T* = S* ⊲ P*

private module T*Mnd where
  m : (s : S*) → (P* s → S*) → S*
  m unit s′ = s′ tt
  m (sup s ps*) s′ = sup s λ p → m (ps* p) (curry s′ p)

  ↖ : ∀ {s s′} → P* (m s s′) → P* s
  ↖ {(unit)} = _
  ↖ {sup s ps*} {s′} (p , p*) = p , ↖ {ps* p} {curry s′ p} p*

  ↗ : ∀ {s s′} → (p : P* (m s s′)) → P* (s′ (↖ p))
  ↗ {(unit)} p = p
  ↗ {sup s ps*} {s′} (p , p*) = ↗ {ps* p} {curry s′ p} p*

  -- Currying through m
  -- Kind of like currying in a T-induced subuniverse?
  T-uncurry :
    {s : S*}         -- A 
    {s′ : P* s → S*}  -- B 
    {C : (p : P* s) → P* (s′ p) → Type}
    → (f : (p : P* s) (p′ : P* (s′ p)) → C p p′)
    → (p : P* (m s s′)) → C (↖ p) (↗ p)
  T-uncurry f p = f (↖ p) (↗ p)

  -- Multiply inner trees
  m′ : ∀ {s : S*} 
    (s′ : P* s → S*) 
    (s″ : (p : P* s) → P* (s′ p) → S*)
    → P* s → S*
  m′ s′ s″ p = m (s′ p) (s″ p)

  m″ : ∀ {s : S*} {s′ : P* s → S*} 
    (s″ : (p : P* s) → P* (s′ p) → S*) 
    (s‴ : (p : P* s) → (p′ : P* (s′ p)) → P* (s″ p p′) → S*) 
    → (p : P* s) → P* (s′ p) → S*
  m″ s″ s‴ p = m′ (s″ p) (s‴ p)

  -- Collapse positions after multiplying
  -- outer tree

  m↖↗ : ∀ {s : S*} 
    {s′ : P* s → S*} 
    (s″ : (p : P* s) → P* (s′ p) → S*)
    → P* (m s s′) → S*
  m↖↗ s″ = T-uncurry s″

  m↖↗′ : ∀ {s : S*} {s′ : P* s → S*} 
    {s″ : (p : P* s) → P* (s′ p) → S*} 
    (s‴ : (p : P* s) → (p′ : P* (s′ p)) → P* (s″ p p′) → S*) 
    → (p : P* (m s s′)) → P* (m↖↗ s″ p) → S*
  m↖↗′ s‴ = T-uncurry s‴

  lUnit-σ : (s : S*) → m s (λ _ → unit) ≡ s
  lUnit-σ unit = refl
  lUnit-σ (sup s ps*) = cong (sup s) (funExt λ p → lUnit-σ (ps* p))

  lUnit-π : (s : S*) 
    → PathP (λ i → (p : P* (lUnit-σ s i)) → P* s) 
      (λ p → ↖ p) 
      (λ x → x)
  lUnit-π unit = refl
  lUnit-π (sup s ps*) i (p , p*) = p , lUnit-π (ps* p) i p*

  assoc-σ : (s : S*) (s′ : P* s → S*) (s″ : (p : P* s) → P* (s′ p) → S*) 
    → m s (λ p → m (s′ p) (s″ p)) 
      ≡ m (m s s′) (λ p → s″ (↖ p) (↗ p))
  assoc-σ unit s′ s″ = refl
  assoc-σ (sup s ps*) s′ s″ = cong (sup s) (funExt λ p → assoc-σ (ps* p) (curry s′ p) (curry s″ p))

  assoc-π₁ : (s : S*) (s′ : P* s → S*) (s″ : (p : P* s) → P* (s′ p) → S*) 
    → PathP (λ i → (p : P* (assoc-σ s s′ s″ i)) → P* s)
      (λ p → ↖ {s′ = λ p₁ → m (s′ p₁) (s″ p₁)} p)
      (λ x → ↖ {s′ = s′} (↖ {m s s′} {m↖↗ s″} x))
  assoc-π₁ unit s′ s″ i p = _
  assoc-π₁ (sup s ps*) s′ s″ i (p , p*) = p , assoc-π₁ (ps* p) _ _ i p*

  assoc-π₂ : (s : S*) (s′ : P* s → S*) (s″ : (p : P* s) → P* (s′ p) → S*) 
    → PathP
      (λ i → (p : P* (assoc-σ s s′ s″ i)) → P* (s′ (assoc-π₁ s s′ s″ i p)))
      (λ p → ↖ {s′ (↖ {s′ = m′ s′ s″} p)} {s″ (↖ {s′ = m′ s′ s″} p)}
         (↗ {s′ = m′ s′ s″} p))
      (λ p → ↗ (↖ {m s s′} {m↖↗ s″} p))
  assoc-π₂ unit s′ s″ i p = ↖ {s′ tt} {s″ tt} p
  assoc-π₂ (sup s ps*) s′ s″ i (p , p*) = assoc-π₂ (ps* p) _ _ i p*

  assoc-π₃ : (s : S*) (s′ : P* s → S*) (s″ : (p : P* s) → P* (s′ p) → S*) 
    → PathP
      (λ i →
         (p : P* (assoc-σ s s′ s″ i)) →
         P* (s″ (assoc-π₁ s s′ s″ i p) (assoc-π₂ s s′ s″ i p)))
      (λ p → ↗ {s′ (↖ {s′ = m′ s′ s″} p)} {s″ (↖ {s′ = m′ s′ s″} p)}
         (↗ {s′ = m′ s′ s″} p))
      (λ p → ↗ {m s s′} {m↖↗ s″} p)
  assoc-π₃ unit s′ s″ i p = ↗ {s′ tt} {s″ tt} p
  assoc-π₃ (sup s ps*) s′ s″ i (p , p*) = assoc-π₃ (ps* p) _ _ i p*

  open import Prelude.Shapes
  assoc-coh-σ :
    ∀ {s : S*} {s′ : P* s → S*} 
      {s″ : (p : P* s) → P* (s′ p) → S*} 
      {s‴ : (p : P* s) → (p′ : P* (s′ p)) → P* (s″ p p′) → S*} 
    → Hex 
          {a = m s (m′ s′ (m″ s″ s‴))}
          {b = m s (m′ (m′ s′ s″) (λ p → m↖↗ (s‴ p)))}
          {c = m (m s (m′ s′ s″)) (m↖↗ (λ p → m↖↗ (s‴ p)))}
          {d = m (m (m s s′) (m↖↗ s″)) (m↖↗ (m↖↗′ s‴))}
          {e = m s (m′ s′ (m″ s″ s‴))}
          {f = m (m s s′) (m↖↗ (m″ s″ s‴))}
      (λ i → m s (λ p → assoc-σ (s′ p) (s″ p) (s‴ p) i))
      (assoc-σ s (m′ s′ s″) (λ p → m↖↗ (s‴ p)))
      (λ i → m (assoc-σ s s′ s″ i) (λ (p : P* (assoc-σ s s′ s″ i)) 
        → s‴ (assoc-π₁ s s′ s″ i p) (assoc-π₂ s s′ s″ i p) (assoc-π₃ s s′ s″ i p)))
      refl
      (assoc-σ s s′ (m″ s″ s‴))
      (assoc-σ (m s s′) (m↖↗ s″) (m↖↗′ s‴))
  assoc-coh-σ {(unit)} {s′} {s″} {s‴} = 
    goal {s′ = s′ tt} {s″ = s″ tt} {s‴ = s‴ tt}
    where
    goal : 
      ∀ {s′ : S*} 
        {s″ : P* s′ → S*} 
        {s‴ : (p′ : P* s′) → P* (s″ p′) → S*} 
      → Hex 
            {a = m s′ (m′ s″ s‴)}
            {b = m (m s′ s″) (m↖↗ s‴)}
            {c = m (m s′ s″) (m↖↗ s‴)}
            {d = m (m s′ s″) (m↖↗ s‴)}
            {e = m s′ (m′ s″ s‴)}
            {f = m s′ (m′ s″ s‴)}
        (assoc-σ s′ s″ s‴)
        refl
        (λ i → m (m s′ s″) (λ p → s‴ 
          (assoc-π₂ unit (const s′) (const s″) i p) 
          (assoc-π₃ unit (const s′) (const s″) i p)))
        refl
        refl
        (assoc-σ s′ s″ s‴)
    goal {(unit)}    = refl , refl , refl
    -- sup s λ p → HexP-filler something?
    goal {sup s ps*} {s″} {s‴} .fst i = sup s λ p → goal {ps* p} {curry s″ p} {curry s‴ p} .fst i
    goal {sup s ps*} {s″} {s‴} .snd .fst i j = sup s λ p → goal {ps* p} {curry s″ p} {curry s‴ p} .snd .fst i j
    goal {sup s ps*} {s″} {s‴} .snd .snd i j = sup s λ p → goal {ps* p} {curry s″ p} {curry s‴ p} .snd .snd i j
  assoc-coh-σ {sup s ps*} {s′} {s″} {s‴} .fst i = sup s λ p → assoc-coh-σ {ps* p} {curry s′ p} {curry s″ p} {curry s‴ p} .fst i
  assoc-coh-σ {sup s ps*} {s′} {s″} {s‴} .snd .fst i j = sup s λ p → assoc-coh-σ {ps* p} {curry s′ p} {curry s″ p} {curry s‴ p} .snd .fst i j
  assoc-coh-σ {sup s ps*} {s′} {s″} {s‴} .snd .snd i j = sup s λ p → assoc-coh-σ {ps* p} {curry s′ p} {curry s″ p} {curry s‴ p} .snd .snd i j

open PsMndCont

T*Mnd : PsMndCont T*
T*Mnd .e = unit
T*Mnd .m = T*Mnd.m
T*Mnd .↖ = T*Mnd.↖
T*Mnd .↗ = T*Mnd.↗
T*Mnd .lUnit-σ = T*Mnd.lUnit-σ
T*Mnd .lUnit-π = T*Mnd.lUnit-π
T*Mnd .rUnit-σ _ = refl
T*Mnd .rUnit-π _ = refl
T*Mnd .assoc-σ = T*Mnd.assoc-σ
T*Mnd .assoc-π₁ = T*Mnd.assoc-π₁
T*Mnd .assoc-π₂ = T*Mnd.assoc-π₂
T*Mnd .assoc-π₃ = T*Mnd.assoc-π₃

T*Mnd .lrUnit-coh-σ {(unit)} = refl
T*Mnd .lrUnit-coh-σ {sup s ps*} {s′} i j = 
  sup s 
    λ p → T*Mnd .lrUnit-coh-σ {ps* p} {s′ = curry s′ p} i j
T*Mnd .lrUnit-coh-π₁ {(unit)} = refl
T*Mnd .lrUnit-coh-π₁ {sup s ps*} i j (p , p*) = 
  p , T*Mnd .lrUnit-coh-π₁ {s = ps* p} i j p*
T*Mnd .lrUnit-coh-π₂ {(unit)} = refl
T*Mnd .lrUnit-coh-π₂ {sup s ps*} i j (p , p*) = 
  T*Mnd .lrUnit-coh-π₂ {s = ps* p} i j p*

T*Mnd .assoc-coh-σ = T*Mnd.assoc-coh-σ
T*Mnd .assoc-coh-π₁  = {! !}
T*Mnd .assoc-coh-π₂  = {! !}
T*Mnd .assoc-coh-π₃  = {! !}
T*Mnd .assoc-coh-π₄  = {! !}
