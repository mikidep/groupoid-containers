module Prelude.ExtraGpdLaws where

open import Cubical.Foundations.Prelude

cong₂Funct' : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {x y : A} {B : Type ℓ'} {C : Type ℓ''}(f : A → B → C) →
        (p : x ≡ y) →
        {u v : B} (q : u ≡ v) →
        cong₂ f p q ≡ cong (λ x → f x u) p ∙ cong (f y) q
cong₂Funct' {x = x} {y = y} f p {u = u} {v = v} q j i =
  hcomp (λ k → λ { (i = i0) → f x u
                  ; (i = i1) → f y (q k)
                  ; (j = i0) → f (p i) (q (i ∧ k))})
       (f (p i) u)
