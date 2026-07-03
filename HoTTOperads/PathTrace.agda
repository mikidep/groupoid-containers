{-# OPTIONS --cubical --no-import-sorts #-}
-- Path-tracing lemmas: how a function-valued PathP built by `_◁_` or by a
-- `subst` along a path of index families evaluates along a moving argument.
-- Pure cubical infrastructure (no universe); used by the universe-level
-- dependent-pentagon proof (HoTTOperads.Universe.PentagonDepProof).
--
--   ◁≡∙        : on ordinary paths, `_◁_` is path composition.
--   ◁-line     : tracing `p ◁ q` along a line is the pointwise prefix of
--                `p` composed with the traced base (the pointwise hcomp
--                computation is judgmental).
--   subst-line : tracing a carrier transported by `subst` along a path Q
--                of index families is tracing the original carrier along
--                the Q-start filler, then a cong-f₁ bridge (J on Q).

module HoTTOperads.PathTrace where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.GroupoidLaws using
  (lUnit ; rUnit ; symRefl ; hcomp-unique ; congFunct) renaming (assoc to ∙assoc)
open import Cubical.Foundations.Transport using (substComposite)
open import Cubical.Foundations.HLevels using (isOfHLevelPathP')
open import Cubical.Functions.FunExtEquiv using (funExtDep ; funExtDepEquiv)
open import Cubical.Data.Sigma using (Σ ; _,_ ; fst ; snd)

private variable ℓ ℓ' ℓ'' : Level

-- ◁ for ordinary paths is path composition.
◁≡∙ : {T : Type ℓ} {x y z : T} (p : x ≡ y) (q : y ≡ z)
    → p ◁ q ≡ p ∙ q
◁≡∙ {T = T} {x = x} p q =
  J (λ y' p' → {z' : T} (q' : y' ≡ z') → p' ◁ q' ≡ p' ∙ q')
    (λ q' → lem q' ∙ lUnit q')
    p q
  where
    lem : {z' : T} (q' : x ≡ z') → refl ◁ q' ≡ q'
    lem q' j i = hfill (λ k → λ { (i = i0) → x
                                 ; (i = i1) → q' i1 })
                       (inS (q' i)) (~ j)

-- Tracing a ◁-prepended function-PathP along a line.
◁-line : {X : I → Type ℓ} {T : Type ℓ'}
         {f₀ f₀' : X i0 → T} {f₁ : X i1 → T}
         (p : f₀ ≡ f₀') (q : PathP (λ i → X i → T) f₀' f₁)
         {a₀ : X i0} {a₁ : X i1} (a : PathP X a₀ a₁)
       → (λ i → (p ◁ q) i (a i)) ≡ funExt⁻ p a₀ ∙ (λ i → q i (a i))
◁-line {f₀ = f₀} {f₀' = f₀'} {f₁ = f₁} p q {a₀ = a₀} a =
    ptwise
  ∙ ◁≡∙ (funExt⁻ p a₀) (λ i → q i (a i))
  where
    -- the function-level ◁ traced along `a` is the value-level ◁ of the
    -- pointwise prefix over the traced base (hcomp computes pointwise).
    ptwise : (λ i → (p ◁ q) i (a i))
           ≡ (funExt⁻ p a₀ ◁ (λ i → q i (a i)))
    ptwise = refl

-- Tracing a subst-transported carrier (J on the family-of-families path Q).
subst-line : {X₀ X₁ : Type ℓ} {T : Type ℓ'}
             {f₀ : X₀ → T} {f₁ : X₁ → T}
             (P₀ : X₀ ≡ X₁)
             (pf : PathP (λ i → P₀ i → T) f₀ f₁)
             (P₁ : X₀ ≡ X₁) (Q : P₀ ≡ P₁)
             (x' : X₀)
           → (λ i → subst (λ p → PathP (λ i' → p i' → T) f₀ f₁) Q pf i
                          (transport-filler P₁ x' i))
           ≡ (λ i → pf i (transport-filler P₀ x' i))
             ∙ cong f₁ (λ k → transport (Q k) x')
subst-line {T = T} {f₀ = f₀} {f₁ = f₁} P₀ pf P₁ Q =
  J (λ P₁' Q' → (x' : _)
       → (λ i → subst (λ p → PathP (λ i' → p i' → T) f₀ f₁) Q' pf i
                      (transport-filler P₁' x' i))
       ≡ (λ i → pf i (transport-filler P₀ x' i))
         ∙ cong f₁ (λ k → transport (Q' k) x'))
    (λ x' →
        (λ j i → substRefl {B = λ p → PathP (λ i' → p i' → T) f₀ f₁}
                           {x = P₀} pf j i
                           (transport-filler P₀ x' i))
      ∙ rUnit (λ i → pf i (transport-filler P₀ x' i)))
    Q

-- ◁ with a refl prefix is the identity (the hfill caps the ◁ hcomp).
◁-idl : {A : I → Type ℓ} {a₀ : A i0} {a₁ : A i1}
        (q : PathP A a₀ a₁) → refl ◁ q ≡ q
◁-idl {a₀ = a₀} {a₁ = a₁} q j i =
  hfill (λ k → λ { (i = i0) → a₀ ; (i = i1) → a₁ })
        (inS (q i)) (~ j)

-- Naturality of a map through hcomp (the hfill is the candidate lid).
g-hcomp : {A : Type ℓ} {B : Type ℓ'} {φ : I}
          (g : A → B) (u : I → Partial φ A) (u0 : A [ φ ↦ u i0 ])
        → g (hcomp u (outS u0)) ≡ hcomp (λ i o → g (u i o)) (g (outS u0))
g-hcomp g u u0 =
  sym (outS (hcomp-unique (λ i o → g (u i o))
                          (inS (g (outS u0)))
                          (λ i → inS (g (hfill u u0 i)))))

-- Postcomposition commutes with ◁ on function-valued PathPs: pointwise the
-- ◁ hcomp computes in the function space, and g passes through it by
-- g-hcomp; the faces of the resulting cube are degenerate by the
-- φ-constancy of hcomp-unique.
◁-post : {X : I → Type ℓ} {T : Type ℓ'} {T' : Type ℓ''}
         {f₀ f₀' : X i0 → T} {f₁ : X i1 → T}
         (g : T → T')
         (p : f₀ ≡ f₀') (q : PathP (λ i → X i → T) f₀' f₁)
       → (λ i → g ∘ (p ◁ q) i)
       ≡ (cong (g ∘_) p ◁ (λ i → g ∘ q i))
◁-post {f₁ = f₁} g p q m i s =
  g-hcomp g (λ j → λ { (i = i0) → p (~ j) s ; (i = i1) → f₁ s })
            (inS (q i s)) m

-- A function-valued PathP line into a fixed codomain is determined by its
-- evaluations along traces of the domain (funExtDep extensionality).
funPathP-ext : {A : I → Type ℓ} {T : Type ℓ'}
               {d₀ : A i0 → T} {d₁ : A i1 → T}
               (u v : PathP (λ i → A i → T) d₀ d₁)
             → ({x₀ : A i0} {x₁ : A i1} (γ : PathP A x₀ x₁)
                  → (λ i → u i (γ i)) ≡ (λ i → v i (γ i)))
             → u ≡ v
funPathP-ext {A = A} {T = T} {d₀ = d₀} {d₁ = d₁} u v h =
    sym (secEq (funExtDepEquiv {A = A} {B = λ _ _ → T} {f = d₀} {g = d₁}) u)
  ∙ (λ t → funExtDep {A = A} {B = λ _ _ → T} {f = d₀} {g = d₁}
             (λ {x₀} {x₁} γ → h γ t))
  ∙ secEq (funExtDepEquiv {A = A} {B = λ _ _ → T} {f = d₀} {g = d₁}) v

-- Evaluating a function line transported along a 2-cell σ between base
-- paths, on a trace of the target path, equals evaluating the original
-- line on any same-endpoint trace of the source path: with set-valued
-- domain fibres the trace spaces are propositions, so the matching trace
-- is unique (J on σ; transportRefl and the trace proposition at refl).
fun-line-transport-eval :
  {Z : Type ℓ} {F : Z → Type ℓ'} {T : Type ℓ''}
  (isSetF : (z : Z) → isSet (F z))
  {z₀ z₁ : Z} {p q : z₀ ≡ z₁} (σ : p ≡ q)
  {d₀ : F z₀ → T} {d₁ : F z₁ → T}
  (u : PathP (λ i → F (p i) → T) d₀ d₁)
  {x₀ : F z₀} {x₁ : F z₁}
  (γp : PathP (λ i → F (p i)) x₀ x₁)
  (γq : PathP (λ i → F (q i)) x₀ x₁)
  → Path (Path T (d₀ x₀) (d₁ x₁))
         (λ i → transport (λ j → PathP (λ i' → F (σ j i') → T) d₀ d₁) u i (γq i))
         (λ i → u i (γp i))
fun-line-transport-eval {F = F} {T = T} isSetF {z₀} {z₁} {p} {q} σ
                        {d₀} {d₁} u {x₀} {x₁} γp γq =
  J (λ q' σ' → (γ : PathP (λ i → F (q' i)) x₀ x₁)
       → Path (Path T (d₀ x₀) (d₁ x₁))
              (λ i → transport (λ j → PathP (λ i' → F (σ' j i') → T) d₀ d₁) u i (γ i))
              (λ i → u i (γp i)))
    base σ γq
  where
    base : (γ : PathP (λ i → F (p i)) x₀ x₁)
         → Path (Path T (d₀ x₀) (d₁ x₁))
                (λ i → transport (λ j → PathP (λ i' → F (p i') → T) d₀ d₁) u i (γ i))
                (λ i → u i (γp i))
    base γ = step1 ∙ step2
      where
        step1 : Path (Path T (d₀ x₀) (d₁ x₁))
                     (λ i → transport (λ j → PathP (λ i' → F (p i') → T) d₀ d₁) u i (γ i))
                     (λ i → u i (γ i))
        step1 t i = transportRefl u t i (γ i)

        step2 : Path (Path T (d₀ x₀) (d₁ x₁))
                     (λ i → u i (γ i))
                     (λ i → u i (γp i))
        step2 t i = u i (isOfHLevelPathP' 1 (isSetF z₁) x₀ x₁ γ γp t i)

-- ▷ on ordinary paths is path composition (mirror of ◁≡∙).
▷≡∙ : {T : Type ℓ} {x y z : T} (p : x ≡ y) (q : y ≡ z)
    → p ▷ q ≡ p ∙ q
▷≡∙ {T = T} {x = x} p q =
  J (λ z' q' → p ▷ q' ≡ p ∙ q')
    (lem ∙ rUnit p)
    q
  where
    lem : p ▷ refl ≡ p
    lem j i = hfill (λ k → λ { (i = i0) → x
                              ; (i = i1) → p i1 })
                    (inS (p i)) (~ j)

-- Evaluating a function line along a ▷-extended trace is the evaluation
-- along the trace, ▷-extended by the image of the tail (g-hcomp pointwise;
-- the i-faces are degenerate by the φ-constancy of hcomp-unique).
▷-trace-eval : {A : I → Type ℓ} {T : Type ℓ'}
               {f₀ : A i0 → T} {f₁ : A i1 → T}
               (u : PathP (λ i → A i → T) f₀ f₁)
               {x₀ : A i0} {y z : A i1}
               (P : PathP A x₀ y) (q : y ≡ z)
             → Path (Path T (f₀ x₀) (f₁ z))
                    (λ i → u i ((P ▷ q) i))
                    ((λ i → u i (P i)) ▷ cong f₁ q)
▷-trace-eval u {x₀ = x₀} P q m i =
  g-hcomp (u i) (λ j → λ { (i = i0) → x₀ ; (i = i1) → q j })
            (inS (P i)) m

-- Evaluating a function line along an arbitrary trace of a set-valued
-- domain family is the evaluation along the canonical transport filler,
-- followed by the f₁-image of the trace's fromPathP (the trace equals the
-- ▷-extension of the filler by its fromPathP, by the trace proposition).
eval-arb : {A : I → Type ℓ} {T : Type ℓ'}
           (isSetA1 : isSet (A i1))
           {f₀ : A i0 → T} {f₁ : A i1 → T}
           (u : PathP (λ i → A i → T) f₀ f₁)
           {x₀ : A i0} {x₁ : A i1} (δ : PathP A x₀ x₁)
         → Path (Path T (f₀ x₀) (f₁ x₁))
                (λ i → u i (δ i))
                ((λ i → u i (transport-filler (λ j → A j) x₀ i))
                 ∙ cong f₁ (fromPathP δ))
eval-arb {A = A} {T = T} isSetA1 {f₀} {f₁} u {x₀} {x₁} δ =
    (λ t i → u i (prp t i))
  ∙ ▷-trace-eval u (transport-filler (λ j → A j) x₀) (fromPathP δ)
  ∙ ▷≡∙ (λ i → u i (transport-filler (λ j → A j) x₀ i))
        (cong f₁ (fromPathP δ))
  where
    prp : δ ≡ transport-filler (λ j → A j) x₀ ▷ fromPathP δ
    prp = isOfHLevelPathP' 1 isSetA1 x₀ x₁ δ
            (transport-filler (λ j → A j) x₀ ▷ fromPathP δ)

-- Evaluating a dependent reading along traces of 2-cell-related base paths
-- gives equal results (J on the 2-cell; trace spaces over set-valued
-- fibres are propositions).
trace-eval-2cell :
  {Z : Type ℓ} {F : Z → Type ℓ'} {T : Type ℓ''}
  (isSetF : (z : Z) → isSet (F z))
  (G : (z : Z) → F z → T)
  {z₀ z₁ : Z} {p q : z₀ ≡ z₁} (σ : p ≡ q)
  {x₀ : F z₀} {x₁ : F z₁}
  (γp : PathP (λ i → F (p i)) x₀ x₁)
  (γq : PathP (λ i → F (q i)) x₀ x₁)
  → Path (Path T (G z₀ x₀) (G z₁ x₁))
         (λ i → G (p i) (γp i))
         (λ i → G (q i) (γq i))
trace-eval-2cell {F = F} {T = T} isSetF G {z₀} {z₁} {p} {q} σ
                 {x₀} {x₁} γp γq =
  J (λ q' σ' → (γ : PathP (λ i → F (q' i)) x₀ x₁)
       → Path (Path T (G z₀ x₀) (G z₁ x₁))
              (λ i → G (p i) (γp i))
              (λ i → G (q' i) (γ i)))
    (λ γ t i → G (p i) (isOfHLevelPathP' 1 (isSetF z₁) x₀ x₁ γp γ t i))
    σ γq

-- Evaluating a dependent reading along a trace of a composite base path is
-- the composite of the segment evaluations (J on the second segment; at
-- refl the trace equals the ▷-extension of the first segment's trace by
-- the tail, and ▷-trace-eval/▷≡∙ finish).
trace-eval-∙ :
  {Z : Type ℓ} {F : Z → Type ℓ'} {T : Type ℓ''}
  (isSetF : (z : Z) → isSet (F z))
  (G : (z : Z) → F z → T)
  {z₀ z₁ z₂ : Z} (p : z₀ ≡ z₁) (q : z₁ ≡ z₂)
  {x₀ : F z₀} {x₁ : F z₁} {x₂ : F z₂}
  (γ : PathP (λ i → F ((p ∙ q) i)) x₀ x₂)
  (γ₁ : PathP (λ i → F (p i)) x₀ x₁)
  (γ₂ : PathP (λ i → F (q i)) x₁ x₂)
  → Path (Path T (G z₀ x₀) (G z₂ x₂))
         (λ i → G ((p ∙ q) i) (γ i))
         ((λ i → G (p i) (γ₁ i)) ∙ (λ i → G (q i) (γ₂ i)))
trace-eval-∙ {Z = Z} {F = F} {T = T} isSetF G {z₀} {z₁} {z₂} p q
             {x₀} {x₁} {x₂} γ γ₁ γ₂ =
  J (λ z₂' q' → (x₂' : F z₂')
       (γ' : PathP (λ i → F ((p ∙ q') i)) x₀ x₂')
       (γ₂' : PathP (λ i → F (q' i)) x₁ x₂')
       → Path (Path T (G z₀ x₀) (G z₂' x₂'))
              (λ i → G ((p ∙ q') i) (γ' i))
              ((λ i → G (p i) (γ₁ i)) ∙ (λ i → G (q' i) (γ₂' i))))
    base q x₂ γ γ₂
  where
    base : (x₂' : F z₁)
           (γ' : PathP (λ i → F ((p ∙ refl) i)) x₀ x₂')
           (γ₂' : x₁ ≡ x₂')
         → Path (Path T (G z₀ x₀) (G z₁ x₂'))
                (λ i → G ((p ∙ refl) i) (γ' i))
                ((λ i → G (p i) (γ₁ i)) ∙ (λ i → G z₁ (γ₂' i)))
    base x₂' γ' γ₂' =
        trace-eval-2cell isSetF G (sym (rUnit p)) γ' (γ₁ ▷ γ₂')
      ∙ ▷-trace-eval (λ i → G (p i)) γ₁ γ₂'
      ∙ ▷≡∙ (λ i → G (p i) (γ₁ i)) (cong (G z₁) γ₂')

-- The canonical tail of a trace over a composite base path: the q-filler
-- from the p-transported start, ▷-corrected (substComposite + fromPathP)
-- to the trace's endpoint.
fill-tail : {Z : Type ℓ} {F : Z → Type ℓ'}
            {z₀ z₁ z₂ : Z} (p : z₀ ≡ z₁) (q : z₁ ≡ z₂)
            {x₀ : F z₀} {x₂ : F z₂}
            (γ : PathP (λ i → F ((p ∙ q) i)) x₀ x₂)
          → PathP (λ i → F (q i)) (subst F p x₀) x₂
fill-tail {F = F} p q {x₀ = x₀} γ =
  transport-filler (λ i → F (q i)) (subst F p x₀)
    ▷ (sym (substComposite F p q x₀) ∙ fromPathP γ)

-- Composite-split with canonical segment traces: the head is the p-filler,
-- the tail is fill-tail.
trace-eval-fill :
  {Z : Type ℓ} {F : Z → Type ℓ'} {T : Type ℓ''}
  (isSetF : (z : Z) → isSet (F z))
  (G : (z : Z) → F z → T)
  {z₀ z₁ z₂ : Z} (p : z₀ ≡ z₁) (q : z₁ ≡ z₂)
  {x₀ : F z₀} {x₂ : F z₂}
  (γ : PathP (λ i → F ((p ∙ q) i)) x₀ x₂)
  → Path (Path T (G z₀ x₀) (G z₂ x₂))
         (λ i → G ((p ∙ q) i) (γ i))
         (  (λ i → G (p i) (transport-filler (λ j → F (p j)) x₀ i))
          ∙ (λ i → G (q i) (fill-tail {F = F} p q γ i)))
trace-eval-fill {F = F} isSetF G p q {x₀ = x₀} γ =
  trace-eval-∙ isSetF G p q γ
    (transport-filler (λ j → F (p j)) x₀)
    (fill-tail {F = F} p q γ)

-- The diagonal of a pointwise-homotopy square is the initial pointwise
-- path followed by the image of the base path (J; rUnit at refl).
homotopy-diag : {A : Type ℓ} {B : Type ℓ'} {f g : A → B}
                (h : (v : A) → f v ≡ g v)
                {v₀ v₁ : A} (c : v₀ ≡ v₁)
              → (λ i → h (c i) i) ≡ h v₀ ∙ cong g c
homotopy-diag {f = f} {g = g} h {v₀ = v₀} =
  J (λ v₁' c' → (λ i → h (c' i) i) ≡ h v₀ ∙ cong g c')
    (rUnit (h v₀))

-- Evaluating a subst-transported unglue line along an arbitrary trace of
-- a set-valued codomain: the g-image of the unglued ua-filler, the
-- transported start along the family 2-cell, and the trace's fromPathP
-- (eval-arb + subst-line + congFunct collapse).
unglue-subst-eval :
  {S T : Type ℓ} {Y : Type ℓ'}
  (isSetT : isSet T)
  (e : S ≃ T) (g : T → Y)
  {P₁ : S ≡ T} (Q : ua e ≡ P₁)
  {x₀ : S} {x₁ : T} (δ : PathP (λ i → P₁ i) x₀ x₁)
  → Path (Path Y (g (equivFun e x₀)) (g x₁))
         (λ i → subst (λ p → PathP (λ i' → p i' → Y) (λ s → g (equivFun e s)) g)
                      Q (λ i' el → g (ua-unglue e i' el)) i (δ i))
         (cong g (  (λ i → ua-unglue e i (transport-filler (ua e) x₀ i))
                  ∙ (λ k → transport (Q k) x₀)
                  ∙ fromPathP δ))
unglue-subst-eval {S = S} {T = T} {Y = Y} isSetT e g {P₁} Q {x₀} {x₁} δ =
    eval-arb isSetT
      (subst (λ p → PathP (λ i' → p i' → Y) (λ s → g (equivFun e s)) g)
             Q (λ i' el → g (ua-unglue e i' el)))
      δ
  ∙ cong (_∙ cong g (fromPathP δ))
         (subst-line (ua e) (λ i' el → g (ua-unglue e i' el)) P₁ Q x₀)
  ∙ sym (∙assoc (cong g (λ i → ua-unglue e i (transport-filler (ua e) x₀ i)))
                (cong g (λ k → transport (Q k) x₀))
                (cong g (fromPathP δ)))
  ∙ cong (cong g (λ i → ua-unglue e i (transport-filler (ua e) x₀ i)) ∙_)
         (sym (congFunct g (λ k → transport (Q k) x₀) (fromPathP δ)))
  ∙ sym (congFunct g (λ i → ua-unglue e i (transport-filler (ua e) x₀ i))
                     ((λ k → transport (Q k) x₀) ∙ fromPathP δ))
