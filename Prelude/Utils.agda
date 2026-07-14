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


module _ {A : Type ℓ} {a b c d e : A} where
  module _
    (p : a ≡ b)
    (q : b ≡ c)
    (r : c ≡ d)
    (s : a ≡ e)
    (t : e ≡ d)
    where

    Pentagon : Type ℓ
    Pentagon = p ∙ q ∙ r ≡ s ∙ t

  module _
    {B : A → Type ℓ'}
    {p : a ≡ b}
    {q : b ≡ c}
    {r : c ≡ d}
    {s : a ≡ e}
    {t : e ≡ d}
    {a' : B a}
    {b' : B b}
    {c' : B c}
    {d' : B d}
    {e' : B e}
    (pnt : Pentagon p q r s t)
    (p' : PathP (λ i → B (p i)) a' b')
    (q' : PathP (λ i → B (q i)) b' c')
    (r' : PathP (λ i → B (r i)) c' d')
    (s' : PathP (λ i → B (s i)) a' e')
    (t' : PathP (λ i → B (t i)) e' d')
    where

    p'q'r' : PathP (λ i → B ((p ∙ q ∙ r) i)) a' d'
    p'q'r' = compPathP' {B = B} p' (compPathP' {B = B} q' r')

    s't' : PathP (λ i → B ((s ∙ t) i)) a' d' 
    s't' = compPathP' {B = B} s' t' 

    PentagonP : Type ℓ'
    PentagonP = PathP 
      (λ i → PathP (λ j → B (pnt i j)) a' d') 
      p'q'r' 
      s't' 
      
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

module _ {A : Type ℓ} {B : A → Type ℓ'}
  {a b c d e : Σ A B} 
  {pp : a ≡ b}
  {qq : b ≡ c}
  {rr : c ≡ d}
  {ss : a ≡ e}
  {tt : e ≡ d}
  where

  private
    p =  cong fst pp  
    q =  cong fst qq  
    r =  cong fst rr  
    s =  cong fst ss  
    t =  cong fst tt  
    
    p' =  cong snd pp  
    q' =  cong snd qq  
    r' =  cong snd rr  
    s' =  cong snd ss  
    t' =  cong snd tt  

  open import Prelude.Square
  open import Cubical.Data.Sigma.Properties

  ΣPentagon : 
    Σ[ pnt ∈ Pentagon p q r s t ] 
      (PentagonP {B = B} pnt p' q' r' s' t')
    → Pentagon pp qq rr ss tt
  ΣPentagon (pnt , pntP) = 
    sym (cong (pp ∙_) (ΣcompPath qq rr))
    ∙ sym (ΣcompPath pp (ΣPathP (q ∙ r , compPathP' {B = B} q' r')))
    ∙ ΣSquare (pnt , pntP)
    ∙ ΣcompPath ss tt
