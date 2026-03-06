module Prelude where

open import Cubical.Foundations.Prelude public

open import Cubical.Foundations.Function using (_$_; idfun; const) public

module _
  {ℓ ℓ' ℓ'' : Level}
  {A : Type ℓ}
  {B : A → Type ℓ'}
  {C : (a : A) → B a → Type ℓ''} where

  infixl 9 _»_
  _»_ : (f : (a : A) → B a) → (g : {a : A} → (b : B a) → C a b) → (a : A) → C a (f a)
  _»_ f g x = g (f x) 
  {-# INLINE _»_ #-}


_€_ : ∀ {ℓ ℓ'} {A : Type ℓ} {B : A → Type ℓ'} → (a : A) → ((a : A) → B a) → B a
a € f = f a
{-# INLINE _€_ #-}
infixl -1 _€_

funExtNonDepHet : {ℓ ℓ′ : Level}
  {A : I → Type ℓ} {B : (i : I) → Type ℓ′}
  {f : A i0 → B i0} {g : A i1 → B i1}
  → ((x : A i0) → PathP B (f x) (g (transport (λ ι → A ι) x)))
  → PathP (λ i → A i → B i) f g
funExtNonDepHet {A = A} {B} {f} {g} = invEq (heteroHomotopy≃Homotopy {g = g}) » funExtDep
  where
  open import Cubical.Foundations.Equiv using (invEq)
  open import Cubical.Functions.FunExtEquiv using (funExtDep; heteroHomotopy≃Homotopy)

funExtConstCod : {ℓ ℓ′ : Level} {A : I → Type ℓ} {B : Type ℓ′}
  {f : A i0 → B} {g : A i1 → B}
  → ({x₀ : A i0} {x₁ : A i1} → PathP A x₀ x₁ → f x₀ ≡ g x₁)
  → PathP (λ i → A i → B) f g
funExtConstCod {A = A} h i x = h (λ j → coei→j A i j x) i
  where
  open import Cubical.Foundations.CartesianKanOps

funExtNonDepHet⁻ : {ℓ ℓ′ : Level}
  {A : I → Type ℓ} {B : (i : I) → Type ℓ′}
  {f : A i0 → B i0} {g : A i1 → B i1}
  → PathP (λ i → A i → B i) f g
  → ((x : A i0) → PathP B (f x) (g (transport (λ ι → A ι) x)))
funExtNonDepHet⁻ {A = A} {B} {f} {g} = funExtDep⁻ » fst (heteroHomotopy≃Homotopy {g = g})
  where
  open import Cubical.Functions.FunExtEquiv using (funExtDep⁻; heteroHomotopy≃Homotopy)

module _ where
  private
    variable
      ℓ ℓ′ ℓ″ : Level
      A : Type ℓ
      A′ : Type ℓ′

  module _ {x : A} {z : A′}
    (P : (y : A) → x ≡ y → (w : A′) → z ≡ w → Type ℓ″)
    (d : P x refl z refl)
    where

    private
      ΠP : (y : A) → x ≡ y → _
      ΠP y p = ∀ z q → P y p z q

    J₂ : {y : A} (p : x ≡ y) {w : A′} (q : z ≡ w)
      → P y p w q
    J₂ p = J ΠP (λ _ → J (P x refl) d) p _  

module _ (A : Type) (P : A → Type) (x : A) where
  open import Cubical.Foundations.Isomorphism
  open Iso

  JIso : Iso (∀ y → x ≡ y → P y) (P x)
  JIso .fun f = f x refl
  JIso .inv px _ p = subst P p px
  JIso .rightInv b = substRefl {B = P} b
  JIso .leftInv a ι y p = transp (λ i → P (p (i ∨ ι))) ι (a (p ι) λ i → p (i ∧ ι))
  
  JEquiv = isoToEquiv JIso

module _ {ℓ} {A : Type ℓ} {B : A → Type ℓ} where
  open import Cubical.Foundations.HLevels 
  open import Cubical.Foundations.Equiv
  open import Cubical.Functions.Implicit

  isGroupoidImplicitΠ : ((x : A) → isGroupoid (B x)) → isGroupoid ({x : A} → B x)
  isGroupoidImplicitΠ H = isOfHLevelRespectEquiv 3 (invEquiv implicit≃Explicit) (isGroupoidΠ H)

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

open import Prelude.Square public
