module Prelude.ExtraGpdLaws where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws

cong₂Funct' : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {x y : A} {B : Type ℓ'} {C : Type ℓ''}(f : A → B → C) →
        (p : x ≡ y) →
        {u v : B} (q : u ≡ v) →
        cong₂ f p q ≡ cong (λ x → f x u) p ∙ cong (f y) q
cong₂Funct' {x = x} {y = y} f p {u = u} {v = v} q j i =
  hcomp (λ k → λ { (i = i0) → f x u
                  ; (i = i1) → f y (q k)
                  ; (j = i0) → f (p i) (q (i ∧ k))})
       (f (p i) u)

module _ where
  private
    variable
      ℓ : Level
      A : Type ℓ
      x y z w v : A

  assoc-inf : {p : x ≡ y} {q : y ≡ z} {r : z ≡ w} →
    p ∙ q ∙ r ≡ (p ∙ q) ∙ r
  assoc-inf {p} {q} {r} = assoc p q r

  shuffleSym : {p : x ≡ y} {q : y ≡ z} {r : x ≡ z}
    → p ∙ q ≡ r
    → q ≡ sym p ∙ r
  shuffleSym {p} {q} {r} ξ =
    lUnit _ 
    ∙ cong (_∙ q) (sym (lCancel _)) 
    ∙ sym assoc-inf 
    ∙ cong (sym p ∙_) ξ 
