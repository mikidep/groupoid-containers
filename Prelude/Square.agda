{-# OPTIONS --hidden-argument-puns #-}

module Prelude.Square where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Path
open import Cubical.Foundations.HLevels using (isSet→SquareP)
open import Cubical.Foundations.Equiv

private
  variable
    ℓ ℓ' : Level

module _
  {ℓA ℓB} {A : Type ℓA} {B : A → (i j : I) → Type ℓB}
  {f₀₀ : ∀ a → B a i0 i0}
  {f₀₁ : ∀ a → B a i0 i1}
  {f₀₋ : PathP (λ j → ∀ a → B a i0 j) f₀₀ f₀₁}
  {f₁₀ : ∀ a → B a i1 i0}
  {f₁₁ : ∀ a → B a i1 i1}
  {f₁₋ : PathP (λ j → ∀ a → B a i1 j) f₁₀ f₁₁}
  {f₋₀ : PathP (λ i → ∀ a → B a i i0) f₀₀ f₁₀}
  {f₋₁ : PathP (λ i → ∀ a → B a i i1) f₀₁ f₁₁} where

  open import Cubical.Foundations.Equiv
  open import Cubical.Reflection.StrictEquiv

  funExtSquare :
      (f : (a : A) → SquareP (B a) (λ j → f₀₋ j a) (λ j → f₁₋ j a) (λ i → f₋₀ i a) (λ i → f₋₁ i a))
    → SquareP (λ i j → (a : A) → B a i j) f₀₋ f₁₋ f₋₀ f₋₁
  funExtSquare f i j a = f a i j

  funExtSquare⁻ :
      (sq : SquareP (λ i j → (a : A) → B a i j) f₀₋ f₁₋ f₋₀ f₋₁)
    → ((a : A) → SquareP (B a) (λ j → f₀₋ j a) (λ j → f₁₋ j a) (λ i → f₋₀ i a) (λ i → f₋₁ i a))
  funExtSquare⁻ sq a i j = sq i j a

  funExtSquareEquiv :
    ((a : A) → SquareP (B a) (λ j → f₀₋ j a) (λ j → f₁₋ j a) (λ i → f₋₀ i a) (λ i → f₋₁ i a))
      ≃
    (SquareP (λ i j → (a : A) → B a i j) f₀₋ f₁₋ f₋₀ f₋₁)
  unquoteDef funExtSquareEquiv = defStrictEquiv funExtSquareEquiv funExtSquare funExtSquare⁻

module _
  {A : I → I → Type ℓ}
  {B : (i j : I) → A i j → Type ℓ'}
  {x₀₀ : Σ (A i0 i0) (B i0 i0)}
  {x₀₁ : Σ (A i0 i1) (B i0 i1)}
  {x₀₋ : PathP (λ j → Σ (A i0 j) (B i0 j)) x₀₀ x₀₁}
  {x₁₀ : Σ (A i1 i0) (B i1 i0)}
  {x₁₁ : Σ (A i1 i1) (B i1 i1)}
  {x₁₋ : PathP (λ j → Σ (A i1 j) (B i1 j)) x₁₀ x₁₁}
  {x₋₀ : PathP (λ i → Σ (A i i0) (B i i0)) x₀₀ x₁₀}
  {x₋₁ : PathP (λ i → Σ (A i i1) (B i i1)) x₀₁ x₁₁}
  where

  fstP : ∀ {ℓ ℓ'} {A : I → Type ℓ} {B : (i : I) → A i → Type ℓ'}
    → {x₀ : Σ (A i0) (B i0)}
    → {x₁ : Σ (A i1) (B i1)}
    → PathP (λ i → Σ (A i) (B i)) x₀ x₁
    → PathP A (fst x₀) (fst x₁)
  fstP p = λ i → fst (p i)
  {-# INLINE fstP #-}

  sndP : ∀ {ℓ ℓ'} {A : I → Type ℓ} {B : (i : I) → A i → Type ℓ'}
    → {x₀ : Σ (A i0) (B i0)}
    → {x₁ : Σ (A i1) (B i1)}
    → (p : PathP (λ i → Σ (A i) (B i)) x₀ x₁)
    → PathP (λ i → B i (fstP p i)) (snd x₀) (snd x₁)
  sndP p = λ i → snd (p i)
  {-# INLINE sndP #-}

  ΣSquareP :
    Σ[ sq ∈ SquareP A (fstP x₀₋) (fstP x₁₋) (fstP x₋₀) (fstP x₋₁) ]
      SquareP (λ i j → B i j (sq i j)) (sndP x₀₋) (sndP x₁₋) (sndP x₋₀) (sndP x₋₁)
    → SquareP (λ i j → Σ (A i j) (B i j)) x₀₋ x₁₋ x₋₀ x₋₁
  ΣSquareP sq = λ i j → (sq .fst i j) , (sq .snd i j)

  ΣSquarePProp : ((a : A i1 i1) → isProp (B i1 i1 a))
    → SquareP A (fstP x₀₋) (fstP x₁₋) (fstP x₋₀) (fstP x₋₁)
    → SquareP (λ i j → Σ (A i j) (B i j)) x₀₋ x₁₋ x₋₀ x₋₁
  fst (ΣSquarePProp propB₁₁ sqA i j) = sqA i j
  snd (ΣSquarePProp propB₁₁ sqA i j) = sqB i j where
    propB : (i j : I) → isProp (B i j (sqA i j))
    propB i j = transport (λ k → isProp (B (~ k ∨ i) (~ k ∨ j) (sqA (~ k ∨ i) (~ k ∨ j)))) (propB₁₁ (sqA i1 i1))

    sqB : SquareP (λ i j → B i j (sqA i j)) (sndP x₀₋) (sndP x₁₋) (sndP x₋₀) (sndP x₋₁)
    sqB = isProp→SquareP (λ i j → propB i j) _ _ _ _

  ΣSquarePSet : ((a : A i1 i1) → isSet (B i1 i1 a))
    → SquareP A (fstP x₀₋) (fstP x₁₋) (fstP x₋₀) (fstP x₋₁)
    → SquareP (λ i j → Σ (A i j) (B i j)) x₀₋ x₁₋ x₋₀ x₋₁
  ΣSquarePSet is-set-B₁₁ sqA i j .fst = sqA i j
  ΣSquarePSet is-set-B₁₁ sqA i j .snd = sqB i j where
    is-set-B : (i j : I) → isSet (B i j (sqA i j))
    is-set-B i j = transport (λ k → isSet (B (~ k ∨ i) (~ k ∨ j) (sqA (~ k ∨ i) (~ k ∨ j)))) (is-set-B₁₁ (sqA i1 i1))

    sqB : SquareP (λ i j → B i j (sqA i j)) (sndP x₀₋) (sndP x₁₋) (sndP x₋₀) (sndP x₋₁)
    sqB = isSet→SquareP (λ i j → is-set-B i j) _ _ _ _

ΣSquare : {A : Type ℓ} {B : A → Type ℓ'}
  {x₀₀ x₀₁ : Σ A B}
  {x₀₋ : x₀₀ ≡ x₀₁}
  {x₁₀ x₁₁ : Σ A B}
  {x₁₋ : x₁₀ ≡ x₁₁}
  {x₋₀ : x₀₀ ≡ x₁₀}
  {x₋₁ : x₀₁ ≡ x₁₁}
  → Σ[ sq ∈ Square (cong fst x₀₋) (cong fst x₁₋) (cong fst x₋₀) (cong fst x₋₁) ]
      SquareP (λ i j → B (sq i j)) (cong snd x₀₋) (cong snd x₁₋) (cong snd x₋₀) (cong snd x₋₁)
  → Square x₀₋ x₁₋ x₋₀ x₋₁
ΣSquare {A = A} {B = B} = ΣSquareP {A = λ _ _ → A} {B = λ _ _ → B}

ΣSquareProp : {A : Type ℓ} {B : A → Type ℓ'}
  → (∀ a → isProp (B a))
  → {x₀₀ x₀₁ : Σ A B}
  → {x₀₋ : x₀₀ ≡ x₀₁}
  → {x₁₀ x₁₁ : Σ A B}
  → {x₁₋ : x₁₀ ≡ x₁₁}
  → {x₋₀ : x₀₀ ≡ x₁₀}
  → {x₋₁ : x₀₁ ≡ x₁₁}
  → Square (cong fst x₀₋) (cong fst x₁₋) (cong fst x₋₀) (cong fst x₋₁)
  → Square x₀₋ x₁₋ x₋₀ x₋₁
ΣSquareProp {A = A} {B = B} propB = ΣSquarePProp {A = λ _ _ → A} {B = λ _ _ → B} propB


module _ {A : Type ℓ} {a b c d : A} 
  {p : a ≡ c} {q : b ≡ d} 
  {r : a ≡ b} {s : c ≡ d}
  where

  PathP→compPathL∙∙ : PathP (λ i → p i ≡ q i) r s
    → sym p ∙∙ r ∙∙ q ≡ s
  PathP→compPathL∙∙ = Square≃doubleComp r s p q .fst 

  compPathL∙∙→PathP : sym p ∙∙ r ∙∙ q ≡ s
    → PathP (λ i → p i ≡ q i) r s
  compPathL∙∙→PathP = invEq (Square≃doubleComp r s p q)
    where
    open import Cubical.Foundations.Equiv
