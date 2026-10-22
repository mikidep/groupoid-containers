module CubicalCompat.Reflection.ReassocTests where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Data.Sigma using (_×_)
open import Prelude.ExtraGpdLaws
open import CubicalCompat.Reflection.Reassoc
open import Cubical.Data.Bool using (true; false)
open import Cubical.Data.List.Base using ([]; [_])
open import Cubical.Data.Unit.Base using (Unit; tt)
open import CubicalCompat.Reflection.Base
import Agda.Builtin.Reflection as R

private
  macro
    rejects-reassoc : R.Term → R.Term → R.TC Unit
    rejects-reassoc ty hole =
      R.runSpeculative
        (R.catchTC
          (newMeta ty >>= λ goal →
            R.noConstraints (reassocMacro (R.def (quote refl) []) goal) >>
            R.returnTC (true , false))
          (R.returnTC (false , false))) >>= λ where
        true → R.typeError [ R.strErr "reassoc unexpectedly solved a negative test" ]
        false → R.unify hole (R.con (quote tt) [])

private variable
  ℓ ℓ′ : Level
  A : Type ℓ
  B : Type ℓ′
  x y z w : A

associativity : (p : x ≡ y) (q : y ≡ z) (r : z ≡ w)
  → (p ∙ q) ∙ r ≡ p ∙ q ∙ r
associativity p q r = reassoc!

units : (p : x ≡ y) → refl ∙ (p ∙ refl) ≡ p
units p = reassoc!

congruence : (f : A → B) (p : x ≡ y) (q : y ≡ z)
  → cong f (p ∙ q) ≡ cong f p ∙ cong f q
congruence f p q = reassoc!

residual : (p : x ≡ y) (q : y ≡ z)
  → sym p ∙ (p ∙ q) ≡ q
residual p q = reassoc-with (shuffleSymL {q = p} refl)

explicit-endpoints : (p : x ≡ y) (q : y ≡ z) (r : z ≡ w)
  → (p ∙ q) ∙ r ≡ p ∙ q ∙ r
explicit-endpoints p q r = proof
  where
  proof = reassoc-on ((p ∙ q) ∙ r) (p ∙ q ∙ r) refl

no-commutativity : (p q : x ≡ x) → Unit
no-commutativity p q = rejects-reassoc (p ∙ q ≡ q ∙ p)

no-automatic-cancellation : (p : x ≡ y) → Unit
no-automatic-cancellation p = rejects-reassoc (sym p ∙ p ≡ refl)

module _ (prefix₁ prefix₂ p tail : x ≡ x) where
  prefixed-residual : prefix₁ ∙ prefix₂ ∙ tail
    ≡ prefix₁ ∙ prefix₂ ∙ sym p ∙ p ∙ tail
  prefixed-residual = reassoc-with (∙l ∙l (sym (shuffleSymL {q = p} refl)))

  explicit-prefixed-residual : prefix₁ ∙ prefix₂ ∙ tail
    ≡ prefix₁ ∙ prefix₂ ∙ sym p ∙ p ∙ tail
  explicit-prefixed-residual = proof
    where
    proof = reassoc-on
      (prefix₁ ∙ prefix₂ ∙ tail)
      (prefix₁ ∙ prefix₂ ∙ sym p ∙ p ∙ tail)
      (∙l ∙l (sym (shuffleSymL {q = p} refl)))

module _ {ℓ₁ ℓ₂ ℓ₃ : Level} {A : Type ℓ₁} {B : Type ℓ₂} {C : Type ℓ₃}
  (f : A → B) (g : B → C) {x y z : A} (p : x ≡ y) (q : y ≡ z) where

  nested-congruence : cong g (cong f (refl ∙ p ∙ q))
    ≡ (cong (λ x → g (f x)) p ∙ refl) ∙ cong g (cong f q)
  nested-congruence = reassoc!

  F₂ : ∀ {x y} → x ≡ y → f x ≡ f y
  F₂ = cong f

  transparent-wrapper : F₂ (p ∙ q) ≡ F₂ p ∙ F₂ q
  transparent-wrapper = reassoc!

  inverse-atoms : cong g (cong f (sym p ∙ p ∙ q))
    ≡ sym (cong g (cong f p)) ∙ cong g (cong f p) ∙ cong g (cong f q)
  inverse-atoms = reassoc!

module _ {A B C : Type} (compose : A → B → C)
  {x y z : A} {u v w : B} (p : x ≡ y) (q : y ≡ z)
  (r : u ≡ v) (s : v ≡ w) where

  whisker-right : cong₂ compose (p ∙ q) refl
    ≡ cong₂ compose p (refl {x = u}) ∙ cong₂ compose q refl
  whisker-right = reassoc!

  whisker-left : cong₂ compose (refl {x = x}) (r ∙ s)
    ≡ cong₂ compose refl r ∙ cong₂ compose refl s
  whisker-left = reassoc!

module _ {A B C : Type} {f g h : A → B}
  (p : f ≡ g) (q : g ≡ h) (k : B → C) where

  function-paths : congS {B = A → C} (λ f x → k (f x)) (p ∙ q)
    ≡ congS (λ f x → k (f x)) p ∙ congS (λ f x → k (f x)) q
  function-paths = reassoc!

  implicit-functions : cong (λ f {x} → k (f x)) (p ∙ q)
    ≡ cong (λ f {x} → k (f x)) p ∙ cong (λ f {x} → k (f x)) q
  implicit-functions = reassoc!

  repeated-path : congS {B = A → B × B} (λ f x → f x , f x) (p ∙ q)
    ≡ congS (λ f x → f x , f x) p ∙ congS (λ f x → f x , f x) q
  repeated-path = reassoc!

-- All 54 original call sites, as ordinary path equalities.
import CubicalCompat.Reflection.ReassocTests.CurrentCases

-- Also check the actual container coherence goals: their reflexive factors
-- are hidden behind inferred natural transformations, unlike the copied chains.
import Cubical.WildCat.Monoidal.Instances.Container
