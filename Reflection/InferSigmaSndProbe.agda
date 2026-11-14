module Reflection.InferSigmaSndProbe where

open import Cubical.Foundations.Prelude
open import Cubical.Data.List.Base using ([])
open import Cubical.Data.Bool using (false)
open import Cubical.Data.Unit.Base using (Unit)
open import Reflection.Base
open import Reflection.InferSigma using (inferΣ)
import Agda.Builtin.Reflection as R

-- Recover the witness by applying inferΣ to the typed pair (x , ?isx).
-- If x is X .fst, Σ-eta lets it reuse X and fills ?isx with X .snd.
-- Use {@(tactic inferΣ-snd P x) isx : P x} on the witness binder.
-- This recovers existing evidence, not a proof of an arbitrary predicate:
-- it needs a first projection that has not already reduced away.
inferΣ-snd : ∀ {ℓ ℓ'} {A : Type ℓ} (P : A → Type ℓ')
  (x : A) → R.Term → R.TC Unit
inferΣ-snd {A = A} P x hole = R.withNormalisation false (
  R.quoteTC x >>= λ x′ →
  inferΣ (Σ A P) (R.con (quote _,_) (x′ v∷ hole v∷ [])))
