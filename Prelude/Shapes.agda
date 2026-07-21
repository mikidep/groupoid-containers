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

module HexP (A : I → I → I → Type ℓ)
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
    
    HexP : Type ℓ
    HexP = Σ (PathP (λ i → A i1 i0 i) e c)
      (λ ec → Σ (SquareP (λ i j → A i i0 j) ab ec ae bc)
        (λ _ → SquareP (A i1) ec fd ef cd))

  module _
    {ab : PathP (λ i → A i0 i0 i) a b}
    {bc : PathP (λ i → A i i0 i1) b c}
    {cd : PathP (λ i → A i1 i i1) c d}
    {ae : PathP (λ i → A i i0 i0) a e}
    {ef : PathP (λ i → A i1 i i0) e f}
    {fd : PathP (λ i → A i1 i1 i) f d}
    (hexp : HexP ab bc cd ae ef fd)
    where
    
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

open HexP public

module ΣHexP 
  {A : (i j k : I) → Type ℓ}
  {B : (i j k : I) → A i j k → Type ℓ'}
  where

  ΣAB : (i j k : I) → Type (ℓ-max ℓ ℓ')
  ΣAB i j k = Σ (A i j k) (B i j k)

  module _
    {a : ΣAB i0 i0 i0}
    {b : ΣAB i0 i0 i1}
    {c : ΣAB i1 i0 i1}
    {d : ΣAB i1 i1 i1}
    {e : ΣAB i1 i0 i0}
    {f : ΣAB i1 i1 i0}
    {ab : PathP (λ i → ΣAB i0 i0 i) a b}
    {bc : PathP (λ i → ΣAB i i0 i1) b c}
    {cd : PathP (λ i → ΣAB i1 i i1) c d}
    {ae : PathP (λ i → ΣAB i i0 i0) a e}
    {ef : PathP (λ i → ΣAB i1 i i0) e f}
    {fd : PathP (λ i → ΣAB i1 i1 i) f d}
    where

    ΣHexP :
      Σ (HexP A 
          (λ i → fst (ab i))
          (λ i → fst (bc i))
          (λ i → fst (cd i))
          (λ i → fst (ae i))
          (λ i → fst (ef i))
          (λ i → fst (fd i)))
        (λ hexA → HexP (λ i j k → B i j k (HexP-filler A hexA i j k)) 
          (λ i → snd (ab i))
          (λ i → snd (bc i))
          (λ i → snd (cd i))
          (λ i → snd (ae i))
          (λ i → snd (ef i))
          (λ i → snd (fd i)))
      → HexP ΣAB
        ab bc cd ae ef fd
    ΣHexP (hexA , hexB) .fst i = hexA .fst i , hexB .fst i
    ΣHexP (hexA , hexB) .snd .fst i j = 
      hexA .snd .fst i j , hexB .snd .fst i j
    ΣHexP (hexA , hexB) .snd .snd i j =
      hexA .snd .snd i j , hexB .snd .snd i j
      
open ΣHexP public
  
module _ {A : Type ℓ} where
  open HexP (λ _ _ _ → A)
    using ()
    renaming 
      ( HexP to Hex
      ; HexP-comp to Hex-comp
      ; HexP-filler to Hex-filler
        )
    public

  module _
    {a b c d e f : A}
    {ab : a ≡ b}
    {bc : b ≡ c}
    {cd : c ≡ d}
    {ae : a ≡ e}
    {ef : e ≡ f}
    {fd : f ≡ d}
    where

    Hex→compPath :
      Hex ab bc cd ae ef fd
      → ab ∙ bc ∙ cd ≡ ae ∙ ef ∙ fd 
    Hex→compPath (ec , sq₁ , sq₂) = goal
      where
      open import Prelude.ExtraGpdLaws
      intrm : sym ae ∙ ab ∙ bc ≡ ef ∙ fd ∙ sym cd
      intrm = PathP→compPathL sq₁ ∙ PathP→compPathR sq₂
      intrm' = shuffleSymLD intrm ∙ ∙l assoc-inf ∙ assoc-inf
      goal = assoc-inf ∙ shuffleSymRU intrm'

module _ 
  {A : Type ℓ}
  {B : A → Type ℓ'}
  where
  
  open ΣHexP
    {A = λ _ _ _ → A}
    {B = λ _ _ _ → B}
    using ()
    renaming (ΣHexP to ΣHex)
    public
