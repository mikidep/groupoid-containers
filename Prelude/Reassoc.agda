{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

open import Cubical.Foundations.Prelude

module Prelude.Reassoc {ℓ} {A : Type ℓ} where

open import Cubical.Data.Nat
open import Prelude.Utils
open import Cubical.Data.Sigma using (_×_)
open import Cubical.Foundations.GroupoidLaws

infixr 20 _◆_

data Term : ℕ → Type where
  refl′ : Term 0
  tm : Term 1
  _◆_ : {m n : ℕ} → Term m → Term n → Term (m + n)

infixr 20 _∷_

data Ev : ℕ → (x y : A) → Type ℓ where
  nil : ∀ {x} → Ev 0 x x
  _∷_ : ∀ {n} {x y z} (p : x ≡ y) (l : Ev n y z)
    → Ev (suc n) x z

split : ∀ {x y} m {n} → Ev (m + n) x y 
  → Σ[ z ∈ A ] Ev m x z × Ev n z y
split zero ev = _ , nil , ev
split (suc m) (p ∷ ev) =
  let z , ev₁ , ev₂ = split m ev
  in z , p ∷ ev₁ , ev₂

embed : ∀ {n} {x y} → Term n → Ev n x y → x ≡ y
embed refl′ nil = refl
embed tm (p ∷ nil) = p
embed (_◆_ {m} {n} t t') ev =
  let z , ev₁ , ev₂ = split m ev
  in embed t ev₁ ∙ embed t' ev₂

nf : ∀ {n} {x y} → Ev n x y → x ≡ y
nf nil = refl
nf (p ∷ ev) = p ∙ nf ev

nf-split-∙ : ∀ {x y} m {n} (ev : Ev (m + n) x y)
  → let z , ev₁ , ev₂ = split m ev
    in nf ev₁ ∙ nf ev₂ ≡ nf ev
nf-split-∙ zero ev = sym (lUnit _)
nf-split-∙ (suc m) (p ∷ ev) =
  let _ , ev₁ , ev₂ = split m ev
  in sym (assoc p (nf ev₁) (nf ev₂))
  ∙ cong (p ∙_) (nf-split-∙ m ev)

nf-sound : ∀ {n} {x y} (t : Term n) (ev : Ev n x y)
  → embed t ev ≡ nf ev
nf-sound refl′ nil = refl
nf-sound tm (p ∷ nil) = rUnit _
nf-sound (_◆_ {m} {n} t t') ev =
  let z , ev₁ , ev₂ = split m ev
  in cong₂ _∙_ (nf-sound t ev₁) (nf-sound t' ev₂)
    ∙ nf-split-∙ m ev

reassoc : ∀ {n} {x y} (ev : Ev n x y) (t t' : Term n)
  → embed t ev ≡ embed t' ev
reassoc ev t t' = nf-sound t ev ∙ sym (nf-sound t' ev)
