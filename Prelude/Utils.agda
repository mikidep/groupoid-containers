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

      
module _ {A : Type ℓ} {B : A → Type ℓ'}
  {a b c : Σ A B} 
  (pp : a ≡ b)
  (qq : b ≡ c) where

  private
    p =  cong fst pp  
    q =  cong fst qq  
    p' =  cong snd pp  
    q' =  cong snd qq  

  open import Prelude.Square
  open import Cubical.Data.Sigma.Properties

  ΣcompPath : 
    ΣPathP (p ∙ q , compPathP' {B = B} p' q') ≡ pp ∙ qq
  ΣcompPath = J D d qq 
    where
    open import Cubical.Foundations.GroupoidLaws
    D : _
    D y tt = ΣPathP (p ∙ t , compPathP' {B = B} p' t') ≡ pp ∙ tt
      where
      t = cong fst tt
      t' = cong snd tt
    d = 
      ΣSquare (sym (rUnit p) , symP (rUnitP' B p')) 
      ∙ rUnit pp

