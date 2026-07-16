open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Path
open import Cubical.Foundations.Equiv

module Prelude.Shapes where

private
  variable
    ℓ ℓ' ℓ'' : Level
    A : Type ℓ
    B : A → Type ℓ'
    C : (a : A) → B a → Type ℓ''

module _ (A : I → I → Type ℓ)
  {a : A i0 i0}
  {b : A i0 i1}
  {c : A i1 i1}
  (ab : PathP (λ i → A i0 i ) a b)
  (bc : PathP (λ i → A i  i1) b c)
  (ac : PathP (λ i → A i  i ) a c)
  where
  
  -- b ∙──────∙ c
  --   │    🯐🯑 
  --   │  🯐🯑   
  --   │🯐🯑     
  -- a ∙

  TriangleP : Type ℓ
  TriangleP = PathP
    (λ i → PathP (λ j → A (i ∧ j) j) a (bc i))
    ab
    ac

  TriangleP≡SquareP : 
    TriangleP 
    ≡ SquareP
      (λ i j → A (i ∧ j) j)
      ab ac refl bc
  TriangleP≡SquareP = refl

module _ {A : Type ℓ}
  {a b c : A}
  (ab : a ≡ b)
  (bc : b ≡ c)
  (ac : a ≡ c)
  where
  
  Triangle : Type ℓ
  Triangle = TriangleP (λ _ _ → A) ab bc ac

module _ (A : I → I → I → Type ℓ)
  {a : A i0 i0 i0}
  {b : A i0 i0 i1}
  {c : A i1 i0 i1}
  {d : A i1 i1 i1}
  {e : A i1 i0 i0}
  (ab : PathP (λ i → A i0 i0 i) a b)
  (bc : PathP (λ i → A i i0 i1) b c)
  (cd : PathP (λ i → A i1 i i1) c d)
  (ae : PathP (λ i → A i i0 i0) a e)
  (ed : PathP (λ i → A i1 i i)  e d)
  where

  open import Cubical.Foundations.HLevels

  PentagonP : Type ℓ
  PentagonP = Σ (PathP (λ i → A i1 i0 i) e c)
    (λ ec → Σ (SquareP (λ i j → A i i0 j) ab ec ae bc)
      (λ _ → TriangleP (A i1) ec cd ed))

module _ {A : Type ℓ} {a b c d e : A} where
  module _
    (ab : a ≡ b)
    (bc : b ≡ c)
    (cd : c ≡ d)
    (ae : a ≡ e)
    (ed : e ≡ d)
    where

    Pentagon : Type ℓ
    Pentagon = PentagonP (λ _ _ _ → A)
      ab bc cd ae ed

    Pentagon→compPath' :
      Pentagon → sym ae ∙ ab ∙ bc ≡ ed ∙ sym cd
    Pentagon→compPath' (ec , sq , tr) = 
      PathP→compPathL sq
      ∙ shuffleSymRD
        (Square≃doubleComp ec ed refl cd .fst tr)
      where
      open import Prelude.ExtraGpdLaws

    compPath'→Pentagon :
      sym ae ∙ ab ∙ bc ≡ ed ∙ sym cd → Pentagon
    compPath'→Pentagon cmpp = goal
      where
      diag = sym ae ∙∙ ab ∙∙ bc
      aux : diag ≡ ed ∙ sym cd
      aux = doubleCompPath≡compPath (sym ae) ab bc ∙ cmpp
      aux' : Square ed diag refl (sym cd)
      aux' = invEq (Square≃doubleComp ed diag refl (sym cd)) (sym aux)
      goal : Pentagon
      goal .fst = diag
      goal .snd .fst = doubleCompPath-filler (sym ae) ab bc
      goal .snd .snd = symP aux'

  -- module _
  --   {B : A → Type ℓ'}
  --   {p : a ≡ b}
  --   {q : b ≡ c}
  --   {r : c ≡ d}
  --   {s : a ≡ e}
  --   {t : e ≡ d}
  --   {a' : B a}
  --   {b' : B b}
  --   {c' : B c}
  --   {d' : B d}
  --   {e' : B e}
  --   (pnt : Pentagon p q r s t)
  --   (p' : PathP (λ i → B (p i)) a' b')
  --   (q' : PathP (λ i → B (q i)) b' c')
  --   (r' : PathP (λ i → B (r i)) c' d')
  --   (s' : PathP (λ i → B (s i)) a' e')
  --   (t' : PathP (λ i → B (t i)) e' d')
  --   where
  --
  --   p'q'r' : PathP (λ i → B ((p ∙ q ∙ r) i)) a' d'
  --   p'q'r' = compPathP' {B = B} p' (compPathP' {B = B} q' r')
  --
  --   s't' : PathP (λ i → B ((s ∙ t) i)) a' d' 
  --   s't' = compPathP' {B = B} s' t' 
  --
  --   PentagonP' : Type ℓ'
  --   PentagonP' = PathP 
  --     (λ i → PathP (λ j → B (pnt i j)) a' d') 
  --     p'q'r' 
  --     s't' 
--
-- module _ {A : Type ℓ} {B : A → Type ℓ'}
--   {a b c d e : Σ A B} 
--   {pp : a ≡ b}
--   {qq : b ≡ c}
--   {rr : c ≡ d}
--   {ss : a ≡ e}
--   {tt : e ≡ d}
--   where
--
--   private
--     p =  cong fst pp  
--     q =  cong fst qq  
--     r =  cong fst rr  
--     s =  cong fst ss  
--     t =  cong fst tt  
--
--     p' =  cong snd pp  
--     q' =  cong snd qq  
--     r' =  cong snd rr  
--     s' =  cong snd ss  
--     t' =  cong snd tt  
--
--   open import Prelude.Square
--   open import Cubical.Data.Sigma.Properties
--
--   ΣPentagon : 
--     Σ[ pnt ∈ Pentagon p q r s t ] 
--       (PentagonP' {B = B} pnt p' q' r' s' t')
--     → Pentagon pp qq rr ss tt
--   ΣPentagon (pnt , pntP) = 
--     sym (cong (pp ∙_) (ΣcompPath qq rr))
--     ∙ sym (ΣcompPath pp (ΣPathP (q ∙ r , compPathP' {B = B} q' r')))
--     ∙ ΣSquare (pnt , pntP)
--     ∙ ΣcompPath ss tt
