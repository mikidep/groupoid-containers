-- Recover implicit Σ arguments from their inferred first projections.
module CubicalCompat.Reflection.InferSigma where

open import Cubical.Foundations.Prelude

private
  open import Cubical.Data.List.Base using (List; []; _∷_; [_])
  open import Cubical.Data.Unit.Base using (Unit; tt)
  open import Cubical.Data.Bool using (true; false)
  open import CubicalCompat.Reflection.Base
  import Agda.Builtin.Reflection as R

  typed : ∀ {ℓ} (A : Type ℓ) → A → A
  typed _ x = x

  lastVisible : List (R.Arg R.Term) → R.TC R.Term
  lastVisible (varg t ∷ []) = R.returnTC t
  lastVisible (_ ∷ args) = lastVisible args
  lastVisible [] = R.typeError [ R.strErr "inferΣ: expected a projection argument" ]

  -- Instance-based notation may still be choosing the category, so a type
  -- headed by ob is not necessarily a genuinely abstract, non-Σ type yet.
  mutual
    waitForMetas : R.Term → R.TC Unit
    waitForMetas (R.meta m _) = R.blockTC (R.blockerMeta m)
    waitForMetas (R.var _ args) = waitForArgs args
    waitForMetas (R.def _ args) = waitForArgs args
    waitForMetas (R.con _ args) = waitForArgs args
    waitForMetas (R.lam _ (R.abs _ t)) = waitForMetas t
    waitForMetas (R.pi (R.arg _ a) (R.abs _ b)) = waitForMetas a >> waitForMetas b
    waitForMetas (R.agda-sort (R.set t)) = waitForMetas t
    waitForMetas (R.agda-sort (R.prop t)) = waitForMetas t
    waitForMetas _ = R.returnTC tt

    waitForArgs : List (R.Arg R.Term) → R.TC Unit
    waitForArgs [] = R.returnTC tt
    waitForArgs (R.arg _ t ∷ ts) = waitForMetas t >> waitForArgs ts

  recover : R.Term → R.Term → R.TC Unit
  recover hole (R.meta m _) = R.blockTC (R.blockerMeta m)
  recover hole (R.def n args) with R.primQNameEquality n (quote fst)
  ... | true = lastVisible args >>= λ candidate →
    R.reduce candidate >>= λ where
      (R.meta m _) → R.blockTC (R.blockerMeta m)
      _ → R.noConstraints (R.unify candidate hole) <|> R.returnTC tt
  ... | false = R.returnTC tt
  recover _ _ = R.returnTC tt

  solve : R.Term → R.Type → R.TC Unit
  solve hole (R.meta m _) = R.blockTC (R.blockerMeta m)
  solve hole ty@(R.def n _) with R.primQNameEquality n (quote Σ)
  ... | true = R.reduce (R.def (quote fst) (hole v∷ [])) >>= recover hole
  ... | false = waitForMetas ty
  solve _ _ = R.returnTC tt

-- For an implicit Σ argument whose first component has been inferred as
-- fst x, reuse x and its second component.
-- Attach it to the operation's argument: {@(tactic inferΣ Ob) a : Ob}.
-- This recovers existing evidence; it does not attempt to prove a predicate.
-- Keep the expected type: inferring it again from an eta-expanded pair would
-- introduce a fresh, underdetermined predicate family.
inferΣ : ∀ {ℓ} (Ob : Type ℓ) → R.Term → R.TC Unit
inferΣ Ob hole = R.withNormalisation false (
  R.quoteTC Ob >>= λ ty →
  R.reduce ty >>= solve (R.def (quote typed) (ty v∷ hole v∷ [])))
