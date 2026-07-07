open import Cubical.Foundations.Prelude

open import Cubical.Foundations.Function
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Container.Base
open import Cubical.Container.MonoidContainer

module Cubical.Container.FreeMonoid (T : Container) where

open Container T

data S* : Type where
  unit : S*
  sup : (s : S) → (ps* : P s → S*) → S*

P* : S* → Type
P* unit = Unit
P* (sup s ps*) = Σ (P s) (λ p → P* (ps* p))

T* = S* ⊲ P*

open PsMndCont

T*Mnd-m : (s : S*) → (P* s → S*) → S*
T*Mnd-m unit s′ = s′ _
T*Mnd-m (sup s ps*) s′ = sup s λ p → T*Mnd-m (ps* p) λ p* → s′ (p , p*)

T*Mnd-↖ : ∀ s s′ → P* (T*Mnd-m s s′) → P* s
T*Mnd-↖ unit s′ p = _
T*Mnd-↖ (sup s ps*) s′ (p , p*) = p , T*Mnd-↖ (ps* p) (λ p*₁ → s′ (p , p*₁)) p*

T*Mnd-↗ : ∀ s s′ → (p : P* (T*Mnd-m s s′)) → P* (s′ (T*Mnd-↖ s s′ p))
T*Mnd-↗ unit s′ p = p
T*Mnd-↗ (sup s ps*) s′ (p , p*) = T*Mnd-↗ (ps* p) (λ p*₁ → s′ (p , p*₁)) p*

T*Mnd-lUnit-σ : (s : S*) → T*Mnd-m s (λ _ → unit) ≡ s
T*Mnd-lUnit-σ unit = refl
T*Mnd-lUnit-σ (sup s ps*) = cong (sup s) (funExt λ p → T*Mnd-lUnit-σ (ps* p))

T*Mnd-lUnit-π : (s : S*) 
  → PathP (λ i → (p : P* (T*Mnd-lUnit-σ s i)) → P* s) 
    (λ p → T*Mnd-↖ s (λ _ → unit) p) 
    (λ x → x)
T*Mnd-lUnit-π unit = refl
T*Mnd-lUnit-π (sup s ps*) i (p , p*) = p , T*Mnd-lUnit-π (ps* p) i p*

T*Mnd-assoc-σ : (s : S*) (s′ : P* s → S*) (s″ : (p : P* s) → P* (s′ p) → S*) 
  → T*Mnd-m s (λ p → T*Mnd-m (s′ p) (s″ p)) 
    ≡ T*Mnd-m (T*Mnd-m s s′) (λ p → s″ (T*Mnd-↖ s s′ p) (T*Mnd-↗ s s′ p))
T*Mnd-assoc-σ unit s′ s″ = refl
T*Mnd-assoc-σ (sup s ps*) s′ s″ = cong (sup s) (funExt λ p → T*Mnd-assoc-σ (ps* p) (λ z → s′ (p , z)) λ p₁ → s″ (p , p₁))

T*Mnd-assoc-π₁ : (s : S*) (s′ : P* s → S*) (s″ : (p : P* s) → P* (s′ p) → S*) 
  → PathP (λ i → (p : P* (T*Mnd-assoc-σ s s′ s″ i)) → P* s)
    (λ p → T*Mnd-↖ s (λ p₁ → T*Mnd-m (s′ p₁) (s″ p₁)) p)
    (λ x →
       T*Mnd-↖ s s′
       (T*Mnd-↖ (T*Mnd-m s s′)
        (λ p → s″ (T*Mnd-↖ s s′ p) (T*Mnd-↗ s s′ p)) x))
T*Mnd-assoc-π₁ unit s′ s″ i p = _
T*Mnd-assoc-π₁ (sup s ps*) s′ s″ i (p , p*) = p , T*Mnd-assoc-π₁ (ps* p) _ _ i p*

T*Mnd-assoc-π₂ : (s : S*) (s′ : P* s → S*) (s″ : (p : P* s) → P* (s′ p) → S*) 
  → PathP
    (λ i →
       (p : P* (T*Mnd-assoc-σ s s′ s″ i)) →
       P* (s′ (T*Mnd-assoc-π₁ s s′ s″ i p)))
    (λ p →
       T*Mnd-↖ (s′ (T*Mnd-↖ s (λ v → T*Mnd-m (s′ v) (s″ v)) p))
       (s″ (T*Mnd-↖ s (λ v → T*Mnd-m (s′ v) (s″ v)) p))
       (T*Mnd-↗ s (λ p₁ → T*Mnd-m (s′ p₁) (s″ p₁)) p))
    (λ x →
       T*Mnd-↗ s s′
       (T*Mnd-↖ (T*Mnd-m s s′)
        (λ p → s″ (T*Mnd-↖ s s′ p) (T*Mnd-↗ s s′ p)) x))
T*Mnd-assoc-π₂ unit s′ s″ i p = T*Mnd-↖ (s′ tt) (s″ tt) p
T*Mnd-assoc-π₂ (sup s ps*) s′ s″ i (p , p*) = T*Mnd-assoc-π₂ (ps* p) _ _ i p*

T*Mnd-assoc-π₃ : (s : S*) (s′ : P* s → S*) (s″ : (p : P* s) → P* (s′ p) → S*) 
  → PathP
    (λ i →
       (p : P* (T*Mnd-assoc-σ s s′ s″ i)) →
       P* (s″ (T*Mnd-assoc-π₁ s s′ s″ i p) (T*Mnd-assoc-π₂ s s′ s″ i p)))
    (λ p →
       T*Mnd-↗ (s′ (T*Mnd-↖ s (λ v → T*Mnd-m (s′ v) (s″ v)) p))
       (s″ (T*Mnd-↖ s (λ v → T*Mnd-m (s′ v) (s″ v)) p))
       (T*Mnd-↗ s (λ p₁ → T*Mnd-m (s′ p₁) (s″ p₁)) p))
    (λ p →
       T*Mnd-↗ (T*Mnd-m s s′)
       (λ p₁ → s″ (T*Mnd-↖ s s′ p₁) (T*Mnd-↗ s s′ p₁)) p)
T*Mnd-assoc-π₃ unit s′ s″ i p = T*Mnd-↗ (s′ tt) (s″ tt) p
T*Mnd-assoc-π₃ (sup s ps*) s′ s″ i (p , p*) = T*Mnd-assoc-π₃ (ps* p) _ _ i p*

-- TODO: how about a container with shapes (s : S) and positions
-- lists of P whose shapes multiply to s?

T*Mnd : PsMndCont T*
T*Mnd .e = unit
T*Mnd .m = T*Mnd-m
T*Mnd .↖ p = T*Mnd-↖ _ _ p
T*Mnd .↗ p = T*Mnd-↗ _ _ p
T*Mnd .lUnit-σ = T*Mnd-lUnit-σ
T*Mnd .lUnit-π {s} = T*Mnd-lUnit-π s
T*Mnd .rUnit-σ s = refl
T*Mnd .rUnit-π = refl
T*Mnd .assoc-σ = T*Mnd-assoc-σ
T*Mnd .assoc-π₁ {s} {s′} {s″} = T*Mnd-assoc-π₁ s s′ s″
T*Mnd .assoc-π₂ {s} {s′} {s″} = T*Mnd-assoc-π₂ s s′ s″
T*Mnd .assoc-π₃ {s} {s′} {s″} = T*Mnd-assoc-π₃ s s′ s″
