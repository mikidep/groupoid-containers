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

  shuffleSymL : {p : x ≡ z} {q : x ≡ y} {r : y ≡ z}
    → p ≡ q ∙ r
    → sym q ∙ p ≡ r
  shuffleSymL {p} {q} {r} ξ =
   cong (sym q ∙_) ξ
   ∙ assoc (sym q) q r
   ∙ cong (_∙ r) (lCancel q)
   ∙ sym (lUnit r)

  shuffleSymR : {p : x ≡ y} {q : x ≡ z} {r : y ≡ z}
    → p ∙ r ≡ q
    → p ≡ q ∙ sym r
  shuffleSymR {p} {q} {r} ξ =
    rUnit p
    ∙ cong (p ∙_) (sym (rCancel r))
    ∙ assoc p r (sym r)
    ∙ cong (_∙ sym r) ξ

  invUniq : {p : x ≡ y} {q : y ≡ x}
    → p ∙ q ≡ refl
    → sym p ≡ q
  invUniq {p} {q} ξ = 
    rUnit (sym p)
    ∙ cong (sym p ∙_) (sym ξ)
    ∙ assoc (sym p) p q
    ∙ cong (_∙ q) (lCancel p)
    ∙ sym (lUnit q)
