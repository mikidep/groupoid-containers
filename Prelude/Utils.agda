open import Cubical.Foundations.Prelude

module Prelude.Utils where

open import Cubical.Foundations.Function using (_$_; idfun; const) public

private
  variable
    ℓ ℓ' ℓ'' : Level
    A : Type ℓ
    B : A → Type ℓ'
    C : (a : A) → B a → Type ℓ''

infixl 9 _»_
_»_ : (f : (a : A) → B a) → (g : {a : A} → (b : B a) → C a b) → (a : A) → C a (f a)
_»_ f g x = g (f x)
{-# INLINE _»_ #-}

_€_ : (a : A) → ((a : A) → B a) → B a
a € f = f a
{-# INLINE _€_ #-}
infixl -1 _€_

module _ where
  open import Cubical.Foundations.HLevels
  open import Cubical.Foundations.Equiv
  open import Cubical.Functions.Implicit

  isGroupoidImplicitΠ : ((x : A) → isGroupoid (B x)) → isGroupoid ({x : A} → B x)
  isGroupoidImplicitΠ H = isOfHLevelRespectEquiv 3 (invEquiv implicit≃Explicit) (isGroupoidΠ H)
