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
  {x : A i0 i1} {y : A i0 i0} 
  {z : A i1 i0} {w : A i1 i1} 
  (p : PathP (λ i → A i0 (~ i)) x y)
  (q : PathP (λ i → A i i0)     y z)
  (r : PathP (λ i → A i1 i)     z w)
  where

  doubleCompP-faces : (i j : I) → Partial (i ∨ ~ i) (A i j)
  doubleCompP-faces i j (i = i0) = p (~ j)
  doubleCompP-faces i j (i = i1) = r j

  doubleCompP : PathP (λ i → A i i1) x w
  doubleCompP i =
    comp (λ j → A i j) (doubleCompP-faces i) (q i)

  doubleCompP-filler : 
    SquareP A (symP p) r q doubleCompP
  doubleCompP-filler i j =
    fill (λ j → A i j) (doubleCompP-faces i) (inS (q i)) j

-- module _ (A : I → I → Type ℓ)
--   {a : A i0 i0}
--   {b : A i0 i1}
--   {c : A i1 i1}
--   (ab : PathP (λ i → A i0 i ) a b)
--   (bc : PathP (λ i → A i  i1) b c)
--   (ac : PathP (λ i → A i  i ) a c)
--   where
--
--   -- b ∙──────∙ c
--   --   │    🯐🯑 
--   --   │  🯐🯑   
--   --   │🯐🯑     
--   -- a ∙
--
--   TriangleP : Type ℓ
--   TriangleP = PathP
--     (λ i → PathP (λ j → A (i ∧ j) j) a (bc i))
--     ab
--     ac
--
--   TriangleP≡SquareP : 
--     TriangleP 
--     ≡ SquareP
--       (λ i j → A (i ∧ j) j)
--       ab ac refl bc
--   TriangleP≡SquareP = refl
--
-- module _ {A : Type ℓ}
--   {a b c : A}
--   (ab : a ≡ b)
--   (bc : b ≡ c)
--   (ac : a ≡ c)
--   where
--
--   Triangle : Type ℓ
--   Triangle = TriangleP (λ _ _ → A) ab bc ac

  --                d ∙
  --                🯐🯑│
  --            c 🯐🯑  │
  --   b ∙───────∙    │
  --     │       ¦    ∙ f
  --     │       ¦  🯐🯑  
  --     │       ¦🯐🯑      
  --   a ∙───────∙ e     
  --
module _ (A : I → I → I → Type ℓ)
  {a : A i0 i0 i0}
  {b : A i0 i0 i1}
  {c : A i1 i0 i1}
  {d : A i1 i1 i1}
  {e : A i1 i0 i0}
  {f : A i1 i1 i0}
  where

  module _
    (ab : PathP (λ i → A i0 i0 i) a b)
    (bc : PathP (λ i → A i i0 i1) b c)
    (cd : PathP (λ i → A i1 i i1) c d)
    (ae : PathP (λ i → A i i0 i0) a e)
    (ef : PathP (λ i → A i1 i i0) e f)
    (fd : PathP (λ i → A i1 i1 i) f d)
    where
    
    open import Cubical.Foundations.HLevels

    HexP : Type ℓ
    HexP = Σ (PathP (λ i → A i1 i0 i) e c)
      (λ ec → Σ (SquareP (λ i j → A i i0 j) ab ec ae bc)
        (λ _ → SquareP (A i1) ec fd ef cd))

    module _ (hexp : HexP) where
      
      open Σ hexp using ()
        renaming (fst to ec)
      open Σ (hexp .snd) using ()
        renaming (fst to sq₁; snd to sq₂)

      HexP-faces : (i j k : I) → Partial i (A i j k)
      HexP-faces i j k (i = i1) = sq₂ j k

      HexP-comp : (i k : I) → A i i1 k
      HexP-comp i k = 
        comp (λ j → A i j k) (λ j → HexP-faces i j k) (sq₁ i k)

      HexP-filler : (i j k : I) → A i j k
      HexP-filler i j k =
        fill (λ j → A i j k) (λ j → HexP-faces i j k) 
          (inS (sq₁ i k)) j

-- module _ (A : I → I → I → Type ℓ)
--   {a : A i0 i0 i0}
--   {b : A i0 i0 i1}
--   {c : A i1 i0 i1}
--   {d : A i1 i1 i1}
--   {e : A i1 i0 i0}
--   where
--
--   module _
--     (ab : PathP (λ i → A i0 i0 i) a b)
--     (bc : PathP (λ i → A i i0 i1) b c)
--     (cd : PathP (λ i → A i1 i i1) c d)
--     (ae : PathP (λ i → A i i0 i0) a e)
--     (ed : PathP (λ i → A i1 i i)  e d)
--     where
--
--     PentagonP : Type ℓ
--     PentagonP = Σ (PathP (λ i → A i1 i0 i) e c)
--       (λ ec → Σ (SquareP (λ i j → A i i0 j) ab ec ae bc)
--         (λ _ → TriangleP (A i1) ec cd ed))
--
--   module _
--     {ab : PathP (λ i → A i0 i0 i) a b}
--     {bc : PathP (λ i → A i i0 i1) b c}
--     {cd : PathP (λ i → A i1 i i1) c d}
--     {ae : PathP (λ i → A i i0 i0) a e}
--     {ed : PathP (λ i → A i1 i i)  e d}
--     (pnt : PentagonP ab bc cd ae ed) 
--     where
--
--     private
--       dg = pnt .fst
--       sq = pnt .snd .fst
--       tr = pnt .snd .snd
--
--     pntP-comp : (j k : I)
--       → A i0 (j ∧ k) k
--     pntP-comp j k = goal
--       module PntP-comp where
--       private
--         part : ∀ i → Partial (~ j) (A (~ i) (j ∧ k) k)
--         part i (j = i0) = sq (~ i) k
--         goal = comp
--           (λ i → A (~ i) (j ∧ k) k)
--           part
--           (tr j k)
--       filler' : (i : I) → A (~ i) (j ∧ k) k
--       filler' = fill 
--           (λ i → A (~ i) (j ∧ k) k)
--           part
--           (inS (tr j k))
--
--     open PntP-comp 
--
--     pntP-filler : (i j k : I) → A i (j ∧ k) k
--     pntP-filler i j k = filler' (j ∧ k) k (~ i)

    -- _ = λ (i j : I) → {! filler i i0 j !}

-- module _ {A : Type ℓ} {a b c d e : A} where
--   module _
--     (ab : a ≡ b)
--     (bc : b ≡ c)
--     (cd : c ≡ d)
--     (ae : a ≡ e)
--     (ed : e ≡ d)
--     where
--
--     Pentagon : Type ℓ
--     Pentagon = PentagonP (λ _ _ _ → A)
--       ab bc cd ae ed
--
--   module _
--     {ab : a ≡ b}
--     {bc : b ≡ c}
--     {cd : c ≡ d}
--     {ae : a ≡ e}
--     {ed : e ≡ d}
--     where
--
--     open import Prelude.ExtraGpdLaws
--
--     Pnt = Pentagon ab bc cd ae ed
--
--     -- Pnt-part : Pnt
--     --   → (i j k : I) 
--     --   → Partial (~ j ∨ i) A 
--     -- Pnt-part = PntP-part (λ _ _ _ → A) 
--
--     Pentagon→compPath' :
--       Pnt → sym ae ∙ ab ∙ bc ≡ ed ∙ sym cd
--     Pentagon→compPath' (ec , sq , tr) = 
--       PathP→compPathL sq
--       ∙ shuffleSymRD
--         (Square≃doubleComp ec ed refl cd .fst tr)
--
--     compPath'→Pentagon :
--       sym ae ∙ ab ∙ bc ≡ ed ∙ sym cd → Pnt
--     compPath'→Pentagon cmpp = goal
--       where
--       diag = sym ae ∙∙ ab ∙∙ bc
--       aux : diag ≡ ed ∙ sym cd
--       aux = doubleCompPath≡compPath (sym ae) ab bc ∙ cmpp
--       aux' : Square ed diag refl (sym cd)
--       aux' = invEq (Square≃doubleComp ed diag refl (sym cd)) (sym aux)
--       goal : Pnt
--       goal .fst = diag
--       goal .snd .fst = doubleCompPath-filler (sym ae) ab bc
--       goal .snd .snd = symP aux'
--
--     compPath'→compPath :
--       sym ae ∙ ab ∙ bc ≡ ed ∙ sym cd
--       → ab ∙ bc ∙ cd ≡ ae ∙ ed
--     compPath'→compPath cmpp' = 
--       assoc-inf ∙ shuffleSymRU 
--         (shuffleSymLD cmpp' ∙ assoc-inf)
--
--     compPath→compPath' :
--       ab ∙ bc ∙ cd ≡ ae ∙ ed
--       → sym ae ∙ ab ∙ bc ≡ ed ∙ sym cd
--     compPath→compPath' cmpp = 
--       shuffleSymLU 
--         (shuffleSymRD (sym assoc-inf ∙ cmpp) 
--           ∙ sym assoc-inf)
--
--   module _
--     {B : A → Type ℓ'}
--     {ab : a ≡ b}
--     {bc : b ≡ c}
--     {cd : c ≡ d}
--     {ae : a ≡ e}
--     {ed : e ≡ d}
--     {a' : B a}
--     {b' : B b}
--     {c' : B c}
--     {d' : B d}
--     {e' : B e}
--     (pnt : Pentagon ab bc cd ae ed)
--     (ab' : PathP (λ i → B (ab i)) a' b')
--     (bc' : PathP (λ i → B (bc i)) b' c')
--     (cd' : PathP (λ i → B (cd i)) c' d')
--     (ae' : PathP (λ i → B (ae i)) a' e')
--     (ed' : PathP (λ i → B (ed i)) e' d')
--     where
--
--     -- fam : I → I → I → Type ℓ'
--     -- fam i j k = B (Pnt-part pnt i j k {! !})
--
--     -- PentagonP' : Type ℓ'
--     -- PentagonP' = PentagonP (λ i j k → B (pnt i j k)) 
--     --   p' q' r' s' t' 
--
-- module _ {A : (i j k : I) → Type ℓ}
--   {B : (i j k : I) → A i j k → Type ℓ'}
--   {a : Σ (A i0 i0 i0) (B i0 i0 i0)}
--   {b : Σ (A i0 i0 i1) (B i0 i0 i1)}
--   {c : Σ (A i1 i0 i1) (B i1 i0 i1)}
--   {d : Σ (A i1 i1 i1) (B i1 i1 i1)}
--   {e : Σ (A i1 i0 i0) (B i1 i0 i0)}
--   {ab : PathP (λ i → Σ (A i0 i0 i) (B i0 i0 i)) a b}
--   {bc : PathP (λ i → Σ (A i i0 i1) (B i i0 i1)) b c}
--   {cd : PathP (λ i → Σ (A i1 i i1) (B i1 i i1)) c d}
--   {ae : PathP (λ i → Σ (A i i0 i0) (B i i0 i0)) a e}
--   {ed : PathP (λ i → Σ (A i1 i i ) (B i1 i i )) e d}
--   where
--
--   -- ΣPentagonP :
--   --   (pntA : PentagonP A
--   --     (λ i → fst (ab i))
--   --     (λ i → fst (bc i))
--   --     (λ i → fst (cd i))
--   --     (λ i → fst (ae i))
--   --     (λ i → fst (ed i)))
--   --   → PentagonP (λ i j k → B i j k {! pntP-filler A pntA i j k  !}) {! !} {! !} {! !} {! !} {! !} 
--   --   → PentagonP (λ i j k → Σ (A i j k) (B i j k))
--   --     ab bc cd ae ed
--   -- ΣPentagonP = {!  !}
--
-- -- module _ {A : Type ℓ} {B : A → Type ℓ'}
-- --   {a b c d e : Σ A B} 
-- --   {pp : a ≡ b}
-- --   {qq : b ≡ c}
-- --   {rr : c ≡ d}
-- --   {ss : a ≡ e}
-- --   {tt : e ≡ d}
-- --   where
-- --
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
