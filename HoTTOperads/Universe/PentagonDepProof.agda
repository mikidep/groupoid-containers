{-# OPTIONS --cubical --no-import-sorts #-}
-- ============================================================================
-- HoTTOperads.Universe.PentagonDepProof
--
-- The dependent Mac Lane pentagon for the universe associator, at the
-- canonical homogeneity coherence:
--
--   dep-pentagon : DepPentagon {𝒰} A B C D hg₀
--
-- for every universe 𝒰 whose decode is a family of sets
-- (isSetEl : (Z : Code) → isSet (El Z), a module hypothesis) and every
-- family (A , B , C , D); hg₀ is the canonical two-secEq-slide coherence
-- (HoTTOperads.Universe.Homog).  The statement at an arbitrary coherence
-- hg in place of hg₀ is false in universes with nontrivial
-- El-automorphisms (an hg-wiggle moves the gdp-twisted side of the
-- equation and not the other), so hg₀ is the right level of generality;
-- the OpM pentagon (Monad.TwoCellCoherence) consumes exactly this
-- instance, via Homog.ghomog-natural at g := Index.
--
-- Structure: Code²→Equiv reduces the Code-level 2-cell to an equivalence
-- equation (equiv-pentagon), which by equivEq/funExt is the pointwise
-- LHS≡RHS; both sides are explicit Σ-shuffles of x, canonicalised by
-- ⅀Assoc≃-inv-on-canon (rhs-step1..4, lhs-stepA/lhs-fst-rewrite); the
-- residual data-fibre equation d-step-2-2-eq is settled in the triple
-- space T³ (Homog): every transport in sight is a subst of (El ∘ F̂)
-- along a path in the SET T³ — the traced L1-carrier line is computed by
-- HomogLine.gdp-line-eq, the secEq Q σ₁ law is flattened by fromPathP,
-- and the two resulting base paths agree by isSetT³.
--
-- Sub-lemma layout mirrors the development order; definitional probes
-- (lhs-defn, inner-3-inv-def, inv-Q-fst-probe, …) record by refl the
-- unfoldings the proof relies on.
-- ============================================================================

module HoTTOperads.Universe.PentagonDepProof where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.Univalence
open import Cubical.Data.Sigma using (ΣPathP ; fst ; snd ; _,_ ; Σ ; Σ-syntax)
open import Cubical.Data.Sigma.Properties using (Σ-cong-equiv ; Σ-cong-equiv-snd ; Σ-cong-equiv-fst ; Σ-assoc-≃)
open import Cubical.Foundations.Transport using (substComposite)
open import Cubical.Foundations.HLevels using (isSetΣ)

open import Cubical.Foundations.Transport using (subst⁻Subst)

open import HoTTOperads.Universe.Base
import HoTTOperads.Universe.Derived as Der
import HoTTOperads.Universe.Pentagon as Pent
import HoTTOperads.Universe.Assoc as Assoc
open import HoTTOperads.Universe.PentagonDep
open import HoTTOperads.Universe.Homog using (module GH ; hg₀)
open import HoTTOperads.Universe.HomogLine using (inj-bridge ; gdp-line-eq)

private variable ℓc ℓe : Level

module _ {𝒰 : Universe ℓc ℓe} where
  open Universe 𝒰

  module _ (A : Code) (B : El A → Code)
           (C : (a : El A) → El (B a) → Code)
           (D : (a : El A) (b : El (B a)) → El (C a b) → Code)
           (isSetEl : (Z : Code) → isSet (El Z)) where

    -- The coherence is the CANONICAL hg₀ (GenHomog: the two-secEq-slide
    -- construction, = Laws.homog's shape at X := Code, F := D).  The
    -- dependent pentagon is provable only at this hg₀: at abstract hg the
    -- statement is hg-dependent on the left and hg-free on the right,
    -- hence false in universes with nontrivial El-automorphisms.
    hg : dNR₀ {𝒰 = 𝒰} A B C D
       ≡ dNL₀ {𝒰 = 𝒰} A B C D ∘ equivFun (⅀Assoc≃ A B C)
    hg = hg₀ {𝒰 = 𝒰} A B C D

    -- Local abbreviations (verbatim PentagonDep `DepPentagon` body shape).
    ALB : El A → Code
    ALB a = ⅀ (B a) (C a)
    ALC : (a : El A) → El (ALB a) → Code
    ALC a = ⅀Assoc-C' (B a) (C a) (D a)
    Bᶜ : El (⅀ A B) → Code
    Bᶜ = ⅀Assoc-C' A B C
    Cnᶜ : (ab : El (⅀ A B)) → El (Bᶜ ab) → Code
    Cnᶜ ab = D (fst (equivFun (⟦⅀⟧ A B) ab))
                (snd (equivFun (⟦⅀⟧ A B) ab))
    RG : (a : El A) → El (B a) → Code
    RG a b = ⅀ (C a b) (D a b)

    gdp : PathP (λ i → El (Inj (⅀Assoc≃ A B C) i) → Code)
                (dNR₀ {𝒰 = 𝒰} A B C D) (dNL₀ {𝒰 = 𝒰} A B C D)
    gdp = gen-data-path {𝒰 = 𝒰} A B C
                        (dNR₀ {𝒰 = 𝒰} A B C D)
                        (dNL₀ {𝒰 = 𝒰} A B C D) hg

    L1fwd : ⅀ (⅀ A (λ a → ⅀ (B a) (C a))) (dNR₀ {𝒰 = 𝒰} A B C D)
          ≡ ⅀ (⅀ (⅀ A B) (⅀Assoc-C' A B C)) (dNL₀ {𝒰 = 𝒰} A B C D)
    L1fwd = λ i → ⅀ (Inj (⅀Assoc≃ A B C) i) (gdp i)

    pL : ⅀ (⅀ (⅀ A B) (⅀Assoc-C' A B C)) (dNL₀ {𝒰 = 𝒰} A B C D)
       ≡ ⅀ A (λ a → ⅀ (⅀ (B a) (C a)) (⅀Assoc-C' (B a) (C a) (D a)))
    pL = sym L1fwd ∙ sym (Inj (⅀Assoc≃ A ALB ALC))

    pR : ⅀ (⅀ (⅀ A B) (⅀Assoc-C' A B C)) (dNL₀ {𝒰 = 𝒰} A B C D)
       ≡ ⅀ A (λ a → ⅀ (⅀ (B a) (C a)) (⅀Assoc-C' (B a) (C a) (D a)))
    pR = sym (Inj (⅀Assoc≃ (⅀ A B) Bᶜ Cnᶜ))
       ∙ sym (Inj (⅀Assoc≃ A B RG))
       ∙ cong (⅀ A) (qR3 {𝒰 = 𝒰} A B C D)

    -- ============================================================
    -- The higher-level pentagon at the `El (⅀ A RGG)` level: the
    -- L1-leg equivalence (the ⟦⅀⟧-natural conjugation of ⅀Assoc≃
    -- A B C with gdp) composed with α₃ equals the pure chain of
    -- deeper associators on the RHS side.
    -- ============================================================
    equiv-pentagon-Type :
      Type ℓe
    equiv-pentagon-Type =
      compEquiv
        (invEquiv
          (compEquiv (⟦⅀⟧ (⅀ A (λ a → ⅀ (B a) (C a))) (dNR₀ {𝒰 = 𝒰} A B C D))
            (compEquiv
              (Σ-cong-equiv (pathToEquiv (cong El (Inj (⅀Assoc≃ A B C))))
                (λ x → pathToEquiv (cong El
                         (λ i → gdp i (transport-filler
                                        (cong El (Inj (⅀Assoc≃ A B C))) x i)))))
              (invEquiv (⟦⅀⟧ (⅀ (⅀ A B) (⅀Assoc-C' A B C))
                             (dNL₀ {𝒰 = 𝒰} A B C D))))))
        (invEquiv (⅀Assoc≃ A ALB ALC))
      ≡ compEquiv (invEquiv (⅀Assoc≃ (⅀ A B) Bᶜ Cnᶜ))
          (compEquiv (invEquiv (⅀Assoc≃ A B RG))
            (compEquiv (⟦⅀⟧ A (λ a → ⅀ (B a) (λ b → ⅀ (C a b) (D a b))))
              (compEquiv (Σ-cong-equiv-snd (λ a → ⅀Assoc≃ (B a) (C a) (D a)))
                (invEquiv (⟦⅀⟧ A (λ a → ⅀ (⅀ (B a) (C a))
                                          (⅀Assoc-C' (B a) (C a) (D a))))))))

    D'' : (a : El A) (b : El (ALB a)) → El (ALC a b) → Code
    D'' a b dd = 𝜏  -- arbitrary; Pent's pair-type doesn't reference it

    -- Probed: equiv-pentagon-Type is NOT refl (cubical Agda rejects:
    -- `C a b != ⅀ (C a b) (D a b)` from the unfolded ⅀Assoc≃ chains).
    -- The propositional content is real — the Mac Lane pentagon for
    -- `⅀Assoc≃` at the equivalence level, OpM-free.
    --
    -- Direct attempt: equivEq + funExt + pointwise factorization
    -- via the inverse equivalences.  Both LHS .fst x and RHS .fst x
    -- end with `invEq (⟦⅀⟧ A RGG)`.  Compute their "inner pair" and
    -- equate via Σ-assoc-≃ strictness + ⟦⅀⟧ secEq cancellations.
    equiv-pentagon : equiv-pentagon-Type
    equiv-pentagon = equivEq (funExt LHS≡RHS)
      where
        LHS≃ : El (⅀ (⅀ (⅀ A B) (⅀Assoc-C' A B C)) (dNL₀ {𝒰 = 𝒰} A B C D))
             ≃ El (⅀ A (λ a → ⅀ (⅀ (B a) (C a)) (ALC a)))
        LHS≃ =
          compEquiv
            (invEquiv
              (compEquiv (⟦⅀⟧ (⅀ A (λ a → ⅀ (B a) (C a))) (dNR₀ {𝒰 = 𝒰} A B C D))
                (compEquiv
                  (Σ-cong-equiv (pathToEquiv (cong El (Inj (⅀Assoc≃ A B C))))
                    (λ x → pathToEquiv (cong El
                             (λ i → gdp i (transport-filler
                                            (cong El (Inj (⅀Assoc≃ A B C))) x i)))))
                  (invEquiv (⟦⅀⟧ (⅀ (⅀ A B) (⅀Assoc-C' A B C))
                                 (dNL₀ {𝒰 = 𝒰} A B C D))))))
            (invEquiv (⅀Assoc≃ A ALB ALC))

        RHS≃ : El (⅀ (⅀ (⅀ A B) (⅀Assoc-C' A B C)) (dNL₀ {𝒰 = 𝒰} A B C D))
             ≃ El (⅀ A (λ a → ⅀ (⅀ (B a) (C a)) (ALC a)))
        RHS≃ =
          compEquiv (invEquiv (⅀Assoc≃ (⅀ A B) Bᶜ Cnᶜ))
            (compEquiv (invEquiv (⅀Assoc≃ A B RG))
              (compEquiv (⟦⅀⟧ A (λ a → ⅀ (B a) (λ b → ⅀ (C a b) (D a b))))
                (compEquiv (Σ-cong-equiv-snd (λ a → ⅀Assoc≃ (B a) (C a) (D a)))
                  (invEquiv (⟦⅀⟧ A (λ a → ⅀ (⅀ (B a) (C a))
                                            (⅀Assoc-C' (B a) (C a) (D a))))))))

        -- The LHS Σ-pair, built DIRECTLY via the unfolded
        -- `invEq (⅀Assoc≃ A ALB ALC)` chain: ⟦⅀⟧ ∘ Σ-cong-equiv-fst ∘
        -- Σ-assoc-≃ ∘ Σ-cong-equiv-snd.  No roundtrip.
        lhs-pair : (x : El (⅀ (⅀ (⅀ A B) (⅀Assoc-C' A B C)) (dNL₀ {𝒰 = 𝒰} A B C D)))
                 → Σ[ a ∈ El A ] El (⅀ (⅀ (B a) (C a)) (⅀Assoc-C' (B a) (C a) (D a)))
        lhs-pair x =
          equivFun
            (Σ-cong-equiv-snd
              (λ a → invEquiv (⟦⅀⟧ (⅀ (B a) (C a))
                                    (⅀Assoc-C' (B a) (C a) (D a)))))
            (equivFun Σ-assoc-≃
              (equivFun
                (Σ-cong-equiv-fst {B = λ ap → El (⅀Assoc-C' (B (fst ap))
                                                              (C (fst ap))
                                                              (D (fst ap))
                                                              (snd ap))}
                  (⟦⅀⟧ A (λ a → ⅀ (B a) (C a))))
                (equivFun
                  (⟦⅀⟧ (⅀ A (λ a → ⅀ (B a) (C a))) (dNR₀ {𝒰 = 𝒰} A B C D))
                  (invEquiv
                    (compEquiv (⟦⅀⟧ (⅀ A (λ a → ⅀ (B a) (C a)))
                                    (dNR₀ {𝒰 = 𝒰} A B C D))
                      (compEquiv
                        (Σ-cong-equiv (pathToEquiv (cong El (Inj (⅀Assoc≃ A B C))))
                          (λ x → pathToEquiv (cong El
                                   (λ i → gdp i (transport-filler
                                                  (cong El (Inj (⅀Assoc≃ A B C))) x i)))))
                        (invEquiv (⟦⅀⟧ (⅀ (⅀ A B) (⅀Assoc-C' A B C))
                                       (dNL₀ {𝒰 = 𝒰} A B C D))))) .fst x))))

        -- The RHS Σ-pair, built DIRECTLY without going through RHS≃.
        rhs-pair : (x : El (⅀ (⅀ (⅀ A B) (⅀Assoc-C' A B C)) (dNL₀ {𝒰 = 𝒰} A B C D)))
                 → Σ[ a ∈ El A ] El (⅀ (⅀ (B a) (C a)) (⅀Assoc-C' (B a) (C a) (D a)))
        rhs-pair x =
          equivFun (Σ-cong-equiv-snd (λ a → ⅀Assoc≃ (B a) (C a) (D a)))
            (equivFun (⟦⅀⟧ A (λ a → ⅀ (B a) (RG a)))
              (invEq (⅀Assoc≃ A B RG)
                (invEq (⅀Assoc≃ (⅀ A B) Bᶜ Cnᶜ) x)))

        -- LHS≃ .fst x ≡ invEq ⟦⅀⟧ (lhs-pair x) is `refl` (definitional
        -- unfolding of invEq (⅀Assoc≃)'s chain).
        lhs-decomp : (x : _) → LHS≃ .fst x
                   ≡ invEq (⟦⅀⟧ A (λ a → ⅀ (⅀ (B a) (C a))
                                          (⅀Assoc-C' (B a) (C a) (D a)))) (lhs-pair x)
        lhs-decomp x = refl

        -- Same for RHS: definitionally `RHS≃ .fst x ≡ invEq ⟦⅀⟧ (rhs-pair x)`.
        rhs-decomp : (x : _) → RHS≃ .fst x
                   ≡ invEq (⟦⅀⟧ A (λ a → ⅀ (⅀ (B a) (C a))
                                          (⅀Assoc-C' (B a) (C a) (D a)))) (rhs-pair x)
        rhs-decomp x = refl

        -- The genuine remaining content: the pair-equation in
        -- Σ[a∈El A] El (RGG a).  Both pairs are explicit Σ-shuffles
        -- of x via standard cubical equivalences; the equation
        -- reduces by Σ-assoc-≃ strictness.
        -- Since lhs-pair / rhs-pair are defined as `equivFun ⟦⅀⟧ A RGG ∘
        -- (LHS≃ / RHS≃).fst`, proving them equal reduces to proving
        -- LHS≃ .fst x ≡ RHS≃ .fst x by `cong (equivFun ⟦⅀⟧)`.  But that
        -- is what we are trying to prove — so this is circular.  The
        -- actual content lives in the direct Σ-shuffles (via the
        -- ⅀Assoc≃ unfolding into Σ-cong-equiv-fst/snd/Σ-assoc-≃).
        -- The pair-equation is the genuine Mac Lane pentagon for ⅀Assoc≃,
        -- in the Σ-pair form Σ[a∈El A] El (RGG a).  Both pairs are
        -- direct Σ-shuffles (not roundtripped through equivFun ⟦⅀⟧ ∘
        -- invEq ⟦⅀⟧), and lhs-decomp/rhs-decomp work as `refl`.  The
        -- equation itself is NOT refl (and not ΣPathP refl,refl) — the
        -- fst components are different functions of x and require a
        -- propositional path.
        --
        -- Strategy: canonicalize BOTH `lhs-pair x` and `rhs-pair x` to
        -- a common form via `Pent.⅀Assoc≃-inv-on-canon` applied to the
        -- `invEq ⅀Assoc≃ ∘ invEq ⟦⅀⟧` cascades inside each.  No `y`,
        -- no Pent `pair_L`/`pair_R` (that route's `rhs-endpoint`
        -- obligation IS the pentagon — circular).
        --
        -- Cubical's `Σ-assoc-≃` pentagon is refl — two routes through
        -- `Σ-assoc-≃` on a 4-object Σ-tower are definitionally equal.
        -- Lifting this to `⅀Assoc≃` requires `⅀Assoc≃-inv-on-canon`
        -- (handles the `invEq ⅀Assoc≃ ∘ invEq ⟦⅀⟧` cascade) plus
        -- secEq ⟦⅀⟧ cancellations; `pair-eq` itself is not refl (the
        -- inner fibre shapes differ).
        pair-eq : (x : _) → lhs-pair x ≡ rhs-pair x
        pair-eq x = lhs-canon ∙ sym rhs-step4
          where
            -- ============================================================
            -- Canonicalisation of the rhs side: apply ⅀Assoc≃-inv-on-canon
            -- twice (once to peel the outer (⅀AB)/Bᶜ/Cnᶜ associator-inverse,
            -- once to peel the (A,B,RG) one) plus Assoc-cont-at-pair
            -- (forward) inside f6 to reduce to a clean invEq ⟦⅀⟧ form.
            -- ============================================================

            -- σ₁ : the canonical Σ-pair form of x after `sym (retEq ⟦⅀⟧ x)`.
            σ₁ : Σ (El (⅀ (⅀ A B) (⅀Assoc-C' A B C)))
                    (λ ab' → El (dNL₀ {𝒰 = 𝒰} A B C D ab'))
            σ₁ = equivFun (⟦⅀⟧ (⅀ (⅀ A B) (⅀Assoc-C' A B C))
                                (dNL₀ {𝒰 = 𝒰} A B C D)) x

            -- Step 1: invEq (⅀Assoc≃ (⅀AB) Bᶜ Cnᶜ) x ≡ invEq ⟦⅀⟧ of a clean
            -- Σ-pair, via ⅀Assoc≃-inv-on-canon at σ₁ (after wrapping x with
            -- sym (retEq ⟦⅀⟧ x)).
            rhs-step1 :
              invEq (⅀Assoc≃ (⅀ A B) Bᶜ Cnᶜ) x
              ≡ invEq (⟦⅀⟧ (⅀ A B) (λ ab → ⅀ (Bᶜ ab) (Cnᶜ ab)))
                      ( fst (equivFun (⟦⅀⟧ (⅀ A B) Bᶜ) (fst σ₁))
                      , invEq (⟦⅀⟧ (Bᶜ (fst (equivFun (⟦⅀⟧ (⅀ A B) Bᶜ) (fst σ₁))))
                                    (Cnᶜ (fst (equivFun (⟦⅀⟧ (⅀ A B) Bᶜ) (fst σ₁)))))
                              ( snd (equivFun (⟦⅀⟧ (⅀ A B) Bᶜ) (fst σ₁))
                              , snd σ₁ ) )
            rhs-step1 =
                cong (invEq (⅀Assoc≃ (⅀ A B) Bᶜ Cnᶜ))
                     (sym (retEq (⟦⅀⟧ (⅀ (⅀ A B) (⅀Assoc-C' A B C))
                                       (dNL₀ {𝒰 = 𝒰} A B C D)) x))
              ∙ Pent.⅀Assoc≃-inv-on-canon {𝒰 = 𝒰} (⅀ A B) Bᶜ Cnᶜ σ₁

            -- σ₂ : the canonical Σ-pair form the rhs-step1 unfolds to,
            -- ready for the second ⅀Assoc≃-inv-on-canon (this time at
            -- level (A, B, RG)).
            σ₂ : Σ (El (⅀ A B)) (λ ab → El (⅀Assoc-C' A B RG ab))
            σ₂ = ( fst (equivFun (⟦⅀⟧ (⅀ A B) Bᶜ) (fst σ₁))
                 , invEq (⟦⅀⟧ (Bᶜ (fst (equivFun (⟦⅀⟧ (⅀ A B) Bᶜ) (fst σ₁))))
                               (Cnᶜ (fst (equivFun (⟦⅀⟧ (⅀ A B) Bᶜ) (fst σ₁)))))
                         ( snd (equivFun (⟦⅀⟧ (⅀ A B) Bᶜ) (fst σ₁))
                         , snd σ₁ ) )

            -- Step 2: invEq (⅀Assoc≃ A B RG) applied to the rhs-step1
            -- result, again via ⅀Assoc≃-inv-on-canon.  Composes into
            -- the full inner-RHS-leg canonicalisation.
            rhs-step2 :
              invEq (⅀Assoc≃ A B RG) (invEq (⅀Assoc≃ (⅀ A B) Bᶜ Cnᶜ) x)
              ≡ invEq (⟦⅀⟧ A (λ a → ⅀ (B a) (RG a)))
                      ( fst (equivFun (⟦⅀⟧ A B) (fst σ₂))
                      , invEq (⟦⅀⟧ (B (fst (equivFun (⟦⅀⟧ A B) (fst σ₂))))
                                    (RG (fst (equivFun (⟦⅀⟧ A B) (fst σ₂)))))
                              ( snd (equivFun (⟦⅀⟧ A B) (fst σ₂))
                              , snd σ₂ ) )
            rhs-step2 =
                cong (invEq (⅀Assoc≃ A B RG)) rhs-step1
              ∙ Pent.⅀Assoc≃-inv-on-canon {𝒰 = 𝒰} A B RG σ₂

            -- σ₃ : the Σ-pair extracted at level (A, ⅀(B)(RG)).  This is
            -- the post-canon form sitting underneath the final outer
            -- `invEq ⟦⅀⟧` in rhs-step2.
            σ₃ : Σ (El A) (λ a → El (⅀ (B a) (RG a)))
            σ₃ = ( fst (equivFun (⟦⅀⟧ A B) (fst σ₂))
                 , invEq (⟦⅀⟧ (B (fst (equivFun (⟦⅀⟧ A B) (fst σ₂))))
                               (RG (fst (equivFun (⟦⅀⟧ A B) (fst σ₂)))))
                         ( snd (equivFun (⟦⅀⟧ A B) (fst σ₂))
                         , snd σ₂ ) )

            -- Step 3: ⟦⅀⟧.fst applied to invEq ⟦⅀⟧ σ₃ is secEq, propositionally σ₃.
            rhs-step3 :
              equivFun (⟦⅀⟧ A (λ a → ⅀ (B a) (RG a)))
                       (invEq (⅀Assoc≃ A B RG) (invEq (⅀Assoc≃ (⅀ A B) Bᶜ Cnᶜ) x))
              ≡ σ₃
            rhs-step3 =
                cong (equivFun (⟦⅀⟧ A (λ a → ⅀ (B a) (RG a)))) rhs-step2
              ∙ secEq (⟦⅀⟧ A (λ a → ⅀ (B a) (RG a))) σ₃

            -- Step 4: apply (Σ-cong-equiv-snd ⅀Assoc≃).fst to σ₃.  Result
            -- is `(σ₃.fst, equivFun (⅀Assoc≃ Ba Ca Da) (snd σ₃))`.
            -- The snd reduces via Assoc-cont-at-pair to a clean Σ-shuffle
            -- form (since snd σ₃ = invEq ⟦⅀⟧ ⋯).
            rhs-step4 :
              rhs-pair x
              ≡ ( fst σ₃
                , Assoc.Assoc-cont 𝒰 (B (fst σ₃)) (C (fst σ₃)) (D (fst σ₃))
                                   ( snd (equivFun (⟦⅀⟧ A B) (fst σ₂))
                                   , snd σ₂ ) )
            rhs-step4 =
                cong (equivFun (Σ-cong-equiv-snd
                                  (λ a → ⅀Assoc≃ (B a) (C a) (D a))))
                     rhs-step3
              ∙ cong (λ z → fst σ₃ , z)
                     (Assoc.Assoc-cont-at-pair 𝒰
                        (B (fst σ₃)) (C (fst σ₃)) (D (fst σ₃))
                        ( snd (equivFun (⟦⅀⟧ A B) (fst σ₂))
                        , snd σ₂ ))

            -- ============================================================
            -- Canonicalisation of the lhs side: the inner `invEq Q` (where
            -- Q is the dependent Σ-cong-equiv of the L1 path-induced
            -- equivalence) decomposes via `transport-sym-Inj-⅀Assoc A B C`
            -- (for the fst-component) and the gdp-induced subst (for the
            -- snd-component).  Then `Pent.⅀Assoc≃-inv-on-canon A B C`
            -- canonicalises the fst, and a chain of secEq ⟦⅀⟧ cancellations
            -- aligns with the rhs-step4 form.
            -- ============================================================
            -- The Q-equivalence inner to LHS≃.  Named for reuse.
            Q : Σ (El (⅀ A (λ a → ⅀ (B a) (C a)))) (λ ab' → El (dNR₀ {𝒰 = 𝒰} A B C D ab'))
              ≃ Σ (El (⅀ (⅀ A B) (⅀Assoc-C' A B C))) (λ ab'' → El (dNL₀ {𝒰 = 𝒰} A B C D ab''))
            Q = Σ-cong-equiv (pathToEquiv (cong El (Inj (⅀Assoc≃ A B C))))
                  (λ x' → pathToEquiv (cong El
                            (λ i → gdp i (transport-filler
                                           (cong El (Inj (⅀Assoc≃ A B C))) x' i))))

            -- The inner-3 equivalence (compEquiv ⟦⅀⟧(dNR) (compEquiv Q (invEquiv ⟦⅀⟧(dNL)))).
            inner-3 : El (⅀ (⅀ A (λ a → ⅀ (B a) (C a))) (dNR₀ {𝒰 = 𝒰} A B C D))
                    ≃ El (⅀ (⅀ (⅀ A B) (⅀Assoc-C' A B C)) (dNL₀ {𝒰 = 𝒰} A B C D))
            inner-3 = compEquiv (⟦⅀⟧ (⅀ A (λ a → ⅀ (B a) (C a))) (dNR₀ {𝒰 = 𝒰} A B C D))
                        (compEquiv Q (invEquiv (⟦⅀⟧ (⅀ (⅀ A B) (⅀Assoc-C' A B C))
                                                     (dNL₀ {𝒰 = 𝒰} A B C D))))

            -- The Σ-shuffle on the outer end of lhs-pair.
            Σ-shuffle :
                Σ (El (⅀ A (λ a → ⅀ (B a) (C a)))) (λ ab' → El (dNR₀ {𝒰 = 𝒰} A B C D ab'))
              → Σ (El A) (λ a → El (⅀ (⅀ (B a) (C a)) (⅀Assoc-C' (B a) (C a) (D a))))
            Σ-shuffle p =
              equivFun (Σ-cong-equiv-snd
                          (λ a → invEquiv (⟦⅀⟧ (⅀ (B a) (C a))
                                                (⅀Assoc-C' (B a) (C a) (D a)))))
                (equivFun Σ-assoc-≃
                  (equivFun
                    (Σ-cong-equiv-fst {B = λ ap → El (⅀Assoc-C' (B (fst ap))
                                                                  (C (fst ap))
                                                                  (D (fst ap))
                                                                  (snd ap))}
                      (⟦⅀⟧ A (λ a → ⅀ (B a) (C a))))
                    p))

            -- Confirm `lhs-pair x ≡ Σ-shuffle (equivFun ⟦⅀⟧(dNR) (invEq inner-3 x))`.
            lhs-defn : lhs-pair x ≡ Σ-shuffle (equivFun (⟦⅀⟧ (⅀ A (λ a → ⅀ (B a) (C a)))
                                                              (dNR₀ {𝒰 = 𝒰} A B C D))
                                                        (invEq inner-3 x))
            lhs-defn = refl

            -- Definitionally check inner-3's inverse structure.
            inner-3-inv-def : invEq inner-3 x ≡ invEq (⟦⅀⟧ (⅀ A (λ a → ⅀ (B a) (C a)))
                                                            (dNR₀ {𝒰 = 𝒰} A B C D))
                                                      (invEq Q σ₁)
            inner-3-inv-def = refl

            -- Probe: what is the fst of `invEq Q σ₁`?  This should be
            -- `invEq (pathToEquiv (cong El (Inj (⅀Assoc≃ A B C)))) (fst σ₁)`
            -- if cubical's Σ-cong-equiv inverse is definitional.
            inv-Q-fst-probe : fst (invEq Q σ₁)
                            ≡ invEq (pathToEquiv (cong El (Inj (⅀Assoc≃ A B C)))) (fst σ₁)
            inv-Q-fst-probe = refl

            -- `invEq (pathToEquiv P) y ≡ transport (sym P) y` is propositional,
            -- via `~uaβ ∘ uaη`.  We use `assocEdge≃` directly instead.
            inv-pTE-Inj : invEq (pathToEquiv (cong El (Inj (⅀Assoc≃ A B C)))) (fst σ₁)
                        ≡ invEq (⅀Assoc≃ A B C) (fst σ₁)
            inv-pTE-Inj = cong (λ e → invEq e (fst σ₁)) (assocEdge≃ {𝒰 = 𝒰} A B C)

            -- Step A: cancel `equivFun ⟦⅀⟧(dNR) ∘ invEq ⟦⅀⟧(dNR)` via secEq.
            lhs-stepA : lhs-pair x ≡ Σ-shuffle (invEq Q σ₁)
            lhs-stepA = cong Σ-shuffle
                             (secEq (⟦⅀⟧ (⅀ A (λ a → ⅀ (B a) (C a)))
                                          (dNR₀ {𝒰 = 𝒰} A B C D))
                                    (invEq Q σ₁))

            -- The Σ-pair p = ⟦⅀⟧(⅀AB)(⅀Assoc-C' A B C).fst (fst σ₁) — input
            -- to Pent.⅀Assoc≃-inv-on-canon A B C.  (Note: this equals
            -- `(fst σ₂, c-thing)` definitionally where `c-thing = snd σ₂'s
            -- ⟦⅀⟧.fst preimage`.)
            p-AB : Σ (El (⅀ A B)) (λ ab → El (⅀Assoc-C' A B C ab))
            p-AB = equivFun (⟦⅀⟧ (⅀ A B) (⅀Assoc-C' A B C)) (fst σ₁)

            -- Step B: rewrite fst (invEq Q σ₁) via assocEdge≃ + retEq +
            -- ⅀Assoc≃-inv-on-canon A B C.
            lhs-fst-rewrite :
              fst (invEq Q σ₁)
              ≡ invEq (⟦⅀⟧ A (λ a → ⅀ (B a) (C a)))
                      ( fst (equivFun (⟦⅀⟧ A B) (fst p-AB))
                      , invEq (⟦⅀⟧ (B (fst (equivFun (⟦⅀⟧ A B) (fst p-AB))))
                                    (C (fst (equivFun (⟦⅀⟧ A B) (fst p-AB)))))
                              ( snd (equivFun (⟦⅀⟧ A B) (fst p-AB))
                              , snd p-AB ) )
            lhs-fst-rewrite =
                cong (λ e → invEq e (fst σ₁)) (assocEdge≃ {𝒰 = 𝒰} A B C)
              ∙ cong (invEq (⅀Assoc≃ A B C))
                     (sym (retEq (⟦⅀⟧ (⅀ A B) (⅀Assoc-C' A B C)) (fst σ₁)))
              ∙ Pent.⅀Assoc≃-inv-on-canon {𝒰 = 𝒰} A B C p-AB

            -- The canonical Σ-pair the inv-on-canon ends at.
            canon-AB : Σ (El A) (λ a → El (⅀ (B a) (C a)))
            canon-AB = ( fst (equivFun (⟦⅀⟧ A B) (fst p-AB))
                       , invEq (⟦⅀⟧ (B (fst (equivFun (⟦⅀⟧ A B) (fst p-AB))))
                                     (C (fst (equivFun (⟦⅀⟧ A B) (fst p-AB)))))
                               ( snd (equivFun (⟦⅀⟧ A B) (fst p-AB))
                               , snd p-AB ) )

            -- The fst component computation: lhs-pair x .fst ≡ fst σ₃.
            -- (Three propositional steps: secEq of inner-3, the inv-on-canon
            -- rewrite of `invEq Q σ₁`, then secEq of ⟦⅀⟧ A (⅀ B C).)
            lhs-fst-eq : fst (lhs-pair x) ≡ fst σ₃
            lhs-fst-eq =
                cong (λ p → fst (equivFun (⟦⅀⟧ A (λ a → ⅀ (B a) (C a)))
                                          (fst p)))
                     (secEq (⟦⅀⟧ (⅀ A (λ a → ⅀ (B a) (C a)))
                                  (dNR₀ {𝒰 = 𝒰} A B C D))
                            (invEq Q σ₁))
              ∙ cong (λ p → fst (equivFun (⟦⅀⟧ A (λ a → ⅀ (B a) (C a))) p))
                     lhs-fst-rewrite
              ∙ cong fst (secEq (⟦⅀⟧ A (λ a → ⅀ (B a) (C a))) canon-AB)

            -- The snd component of the lhs canonical form.  Given by
            -- ΣPathP of the fst-eq and a snd-PathP.  This snd-PathP is
            -- the genuine gdp/hg content: bridges `snd (Σ-shuffle (invEq
            -- Q σ₁))` to `Assoc-cont(...)(snd⟦⅀⟧.fst (fst σ₂), snd σ₂)`
            -- over `lhs-fst-eq`.
            lhs-snd-PathP :
              PathP (λ i → El (⅀ (⅀ (B (lhs-fst-eq i)) (C (lhs-fst-eq i)))
                                  (⅀Assoc-C' (B (lhs-fst-eq i))
                                              (C (lhs-fst-eq i))
                                              (D (lhs-fst-eq i)))))
                    (snd (lhs-pair x))
                    (Assoc.Assoc-cont 𝒰
                       (B (fst σ₃)) (C (fst σ₃)) (D (fst σ₃))
                       ( snd (equivFun (⟦⅀⟧ A B) (fst σ₂)) , snd σ₂ ))
            lhs-snd-PathP = toPathP lhs-snd-after-transport
              where
                lhs-snd-after-transport :
                  transport
                    (λ i → El (⅀ (⅀ (B (lhs-fst-eq i)) (C (lhs-fst-eq i)))
                                  (⅀Assoc-C' (B (lhs-fst-eq i))
                                              (C (lhs-fst-eq i))
                                              (D (lhs-fst-eq i)))))
                    (snd (lhs-pair x))
                  ≡ Assoc.Assoc-cont 𝒰
                       (B (fst σ₃)) (C (fst σ₃)) (D (fst σ₃))
                       ( snd (equivFun (⟦⅀⟧ A B) (fst σ₂)) , snd σ₂ )
                -- Step 1 snd PathP: from `snd (lhs-pair x)` to
                -- `snd (Σ-shuffle (invEq Q σ₁))`, over `cong fst lhs-stepA`.
                snd-step1-PathP :
                  PathP (λ i → El (⅀ (⅀ (B (fst (lhs-stepA i)))
                                         (C (fst (lhs-stepA i))))
                                      (⅀Assoc-C' (B (fst (lhs-stepA i)))
                                                  (C (fst (lhs-stepA i)))
                                                  (D (fst (lhs-stepA i))))))
                        (snd (lhs-pair x))
                        (snd (Σ-shuffle (invEq Q σ₁)))
                snd-step1-PathP i = snd (lhs-stepA i)

                -- The `fromPathP` form: `transport (cong fst lhs-stepA's path family)
                -- (snd (lhs-pair x)) ≡ snd (Σ-shuffle (invEq Q σ₁))`.  By
                -- composing `transport (cong f part1) ∘ transport (cong f part2)
                -- ∘ transport (cong f part3)` via `transportComposite` and
                -- showing each piece's snd evolves correctly, we get
                -- `lhs-snd-after-transport`.  The hard core is the gdp/Q
                -- content in step 2 (the fst-rewrite), which carries the
                -- Mac Lane pentagon for ⅀Assoc≃ at this level.
                snd-step1-fromPathP :
                  transport
                    (λ i → El (⅀ (⅀ (B (fst (lhs-stepA i)))
                                     (C (fst (lhs-stepA i))))
                                  (⅀Assoc-C' (B (fst (lhs-stepA i)))
                                              (C (fst (lhs-stepA i)))
                                              (D (fst (lhs-stepA i))))))
                    (snd (lhs-pair x))
                  ≡ snd (Σ-shuffle (invEq Q σ₁))
                snd-step1-fromPathP = fromPathP snd-step1-PathP

                -- The fibre family `qp i = ⅀Assoc-C'(B (lhs-fst-eq i))(C ...)(D ...)`
                -- depending on the lhs-fst-eq path.  Used to express the
                -- transport via ⟦⅀⟧-natural (both-arg form).
                qp-path : PathP (λ i → El (⅀ (B (lhs-fst-eq i))
                                              (C (lhs-fst-eq i))) → Code)
                                (⅀Assoc-C' (B (fst (lhs-pair x)))
                                            (C (fst (lhs-pair x)))
                                            (D (fst (lhs-pair x))))
                                (⅀Assoc-C' (B (fst σ₃))
                                            (C (fst σ₃))
                                            (D (fst σ₃)))
                qp-path i = ⅀Assoc-C' (B (lhs-fst-eq i)) (C (lhs-fst-eq i))
                                       (D (lhs-fst-eq i))

                p-path : ⅀ (B (fst (lhs-pair x))) (C (fst (lhs-pair x)))
                       ≡ ⅀ (B (fst σ₃)) (C (fst σ₃))
                p-path i = ⅀ (B (lhs-fst-eq i)) (C (lhs-fst-eq i))

                -- Apply ⟦⅀⟧-natural to express the transp.
                nat-eq :
                  pathToEquiv (cong El (λ i → ⅀ (p-path i) (qp-path i)))
                  ≡ compEquiv (⟦⅀⟧ (⅀ (B (fst (lhs-pair x))) (C (fst (lhs-pair x))))
                                    (⅀Assoc-C' (B (fst (lhs-pair x)))
                                                (C (fst (lhs-pair x)))
                                                (D (fst (lhs-pair x)))))
                      (compEquiv
                        (Σ-cong-equiv (pathToEquiv (cong El p-path))
                          (λ y → pathToEquiv (cong El
                                   (λ i → qp-path i (transport-filler
                                                       (cong El p-path) y i)))))
                        (invEquiv (⟦⅀⟧ (⅀ (B (fst σ₃)) (C (fst σ₃)))
                                       (⅀Assoc-C' (B (fst σ₃))
                                                   (C (fst σ₃))
                                                   (D (fst σ₃))))))
                nat-eq = ⟦⅀⟧-natural {𝒰 = 𝒰} p-path qp-path

                -- Apply nat-eq to push the transp inside `invEq ⟦⅀⟧`.
                -- Result: transp ≡ `invEq ⟦⅀⟧ ∘ Σ-cong-equiv.fst ∘ ⟦⅀⟧.fst`.
                push-eq :
                  transport (λ i → El (⅀ (p-path i) (qp-path i)))
                            (snd (lhs-pair x))
                  ≡ (compEquiv (⟦⅀⟧ (⅀ (B (fst (lhs-pair x)))
                                       (C (fst (lhs-pair x))))
                                    (⅀Assoc-C' (B (fst (lhs-pair x)))
                                                (C (fst (lhs-pair x)))
                                                (D (fst (lhs-pair x)))))
                      (compEquiv
                        (Σ-cong-equiv (pathToEquiv (cong El p-path))
                          (λ y → pathToEquiv (cong El
                                   (λ i → qp-path i (transport-filler
                                                       (cong El p-path) y i)))))
                        (invEquiv (⟦⅀⟧ (⅀ (B (fst σ₃)) (C (fst σ₃)))
                                       (⅀Assoc-C' (B (fst σ₃))
                                                   (C (fst σ₃))
                                                   (D (fst σ₃))))))) .fst
                    (snd (lhs-pair x))
                push-eq = cong (λ e → e .fst (snd (lhs-pair x))) nat-eq

                -- ====================================================================
                -- b-component sub-lemmas, at the β (= snd of ⟦⅀⟧A(⅀BC).fst)
                -- level only (no gdp / d-fibre content): the b''-component
                -- pieces of the abstract pentagon for `⅀Assoc≃`.
                -- ====================================================================

                -- β-call: the b-component the Σ-shuffle of `lhs-pair x` ends in
                -- (= `snd ⟦⅀⟧A(⅀BC).fst (fst (⟦⅀⟧.fst (invEq inner-3 x)))`).
                -- Kept as a named binding because β-PathP needs it as a source.
                β-call : El (⅀ (B (fst (lhs-pair x))) (C (fst (lhs-pair x))))
                β-call = snd (equivFun (⟦⅀⟧ A (λ a → ⅀ (B a) (C a)))
                                       (fst (equivFun (⟦⅀⟧ (⅀ A (λ a → ⅀ (B a) (C a)))
                                                             (dNR₀ {𝒰 = 𝒰} A B C D))
                                                       (invEq (compEquiv (⟦⅀⟧ (⅀ A (λ a → ⅀ (B a) (C a)))
                                                                              (dNR₀ {𝒰 = 𝒰} A B C D))
                                                                          (compEquiv Q
                                                                            (invEquiv (⟦⅀⟧ (⅀ (⅀ A B) (⅀Assoc-C' A B C))
                                                                                           (dNL₀ {𝒰 = 𝒰} A B C D)))))
                                                              x))))

                -- β-PathP built piecewise to definitionally match
                -- `lhs-fst-eq = e1 ∙ (e2 ∙ e3)` (right-assoc `_∙_`).  Each
                -- step's snd-component comes from cong of the corresponding
                -- equation at the Σ-pair level.
                β-PathP-step1 :
                  PathP (λ i → El (⅀ (B (fst (equivFun (⟦⅀⟧ A (λ a → ⅀ (B a) (C a)))
                                                          (fst (secEq (⟦⅀⟧ (⅀ A (λ a → ⅀ (B a) (C a)))
                                                                              (dNR₀ {𝒰 = 𝒰} A B C D))
                                                                        (invEq Q σ₁) i)))))
                                      (C (fst (equivFun (⟦⅀⟧ A (λ a → ⅀ (B a) (C a)))
                                                          (fst (secEq (⟦⅀⟧ (⅀ A (λ a → ⅀ (B a) (C a)))
                                                                              (dNR₀ {𝒰 = 𝒰} A B C D))
                                                                        (invEq Q σ₁) i)))))))
                        β-call
                        (snd (equivFun (⟦⅀⟧ A (λ a → ⅀ (B a) (C a)))
                                        (fst (invEq Q σ₁))))
                β-PathP-step1 i = snd (equivFun (⟦⅀⟧ A (λ a → ⅀ (B a) (C a)))
                                                 (fst (secEq (⟦⅀⟧ (⅀ A (λ a → ⅀ (B a) (C a)))
                                                                    (dNR₀ {𝒰 = 𝒰} A B C D))
                                                              (invEq Q σ₁) i)))

                β-PathP-step2 :
                  PathP (λ i → El (⅀ (B (fst (equivFun (⟦⅀⟧ A (λ a → ⅀ (B a) (C a)))
                                                          (lhs-fst-rewrite i))))
                                      (C (fst (equivFun (⟦⅀⟧ A (λ a → ⅀ (B a) (C a)))
                                                          (lhs-fst-rewrite i))))))
                        (snd (equivFun (⟦⅀⟧ A (λ a → ⅀ (B a) (C a)))
                                        (fst (invEq Q σ₁))))
                        (snd (equivFun (⟦⅀⟧ A (λ a → ⅀ (B a) (C a)))
                                        (invEq (⟦⅀⟧ A (λ a → ⅀ (B a) (C a))) canon-AB)))
                β-PathP-step2 i = snd (equivFun (⟦⅀⟧ A (λ a → ⅀ (B a) (C a)))
                                                  (lhs-fst-rewrite i))

                β-PathP-step3 :
                  PathP (λ i → El (⅀ (B (fst (secEq (⟦⅀⟧ A (λ a → ⅀ (B a) (C a))) canon-AB i)))
                                      (C (fst (secEq (⟦⅀⟧ A (λ a → ⅀ (B a) (C a))) canon-AB i)))))
                        (snd (equivFun (⟦⅀⟧ A (λ a → ⅀ (B a) (C a)))
                                        (invEq (⟦⅀⟧ A (λ a → ⅀ (B a) (C a))) canon-AB)))
                        (snd canon-AB)
                β-PathP-step3 i = snd (secEq (⟦⅀⟧ A (λ a → ⅀ (B a) (C a))) canon-AB i)

                β-PathP : PathP (λ i → El (⅀ (B (lhs-fst-eq i)) (C (lhs-fst-eq i))))
                                β-call (snd canon-AB)
                β-PathP =
                  compPathP' {B = λ a → El (⅀ (B a) (C a))}
                    β-PathP-step1
                    (compPathP' {B = λ a → El (⅀ (B a) (C a))}
                      β-PathP-step2 β-PathP-step3)

                -- snd p-AB ≡ c'  (via secEq of ⟦⅀⟧(Bᶜ (fst σ₂))(Cnᶜ (fst σ₂))).
                snd-pAB≡c' :
                  snd p-AB
                  ≡ fst (equivFun (⟦⅀⟧ (C (fst σ₃)
                                            (snd (equivFun (⟦⅀⟧ A B) (fst σ₂))))
                                          (D (fst σ₃)
                                            (snd (equivFun (⟦⅀⟧ A B) (fst σ₂)))))
                                   (snd σ₂))
                snd-pAB≡c' =
                  sym (cong fst
                            (secEq (⟦⅀⟧ (Bᶜ (fst σ₂)) (Cnᶜ (fst σ₂)))
                                   (snd p-AB , snd σ₁)))

                -- b-eq: the b''-component of inner-Σ-eq.
                b-eq :
                  transport (cong El p-path) β-call
                  ≡ invEq (⟦⅀⟧ (B (fst σ₃)) (C (fst σ₃)))
                          ( snd (equivFun (⟦⅀⟧ A B) (fst σ₂))
                          , fst (equivFun (⟦⅀⟧ (C (fst σ₃)
                                                  (snd (equivFun (⟦⅀⟧ A B) (fst σ₂))))
                                               (D (fst σ₃)
                                                  (snd (equivFun (⟦⅀⟧ A B) (fst σ₂)))))
                                          (snd σ₂)))
                b-eq =
                    fromPathP β-PathP
                  ∙ cong (λ c → invEq (⟦⅀⟧ (B (fst σ₃)) (C (fst σ₃)))
                                       ( snd (equivFun (⟦⅀⟧ A B) (fst σ₂)) , c ))
                         snd-pAB≡c'

                -- Names for the canonical RHS-side pair components.  Used by
                -- `step3-fst-content` (a sub-lemma at the β level only).
                b₂' : El (B (fst σ₃))
                b₂' = snd (equivFun (⟦⅀⟧ A B) (fst σ₂))

                c' : El (C (fst σ₃) b₂')
                c' = fst (equivFun (⟦⅀⟧ (C (fst σ₃) b₂') (D (fst σ₃) b₂')) (snd σ₂))

                canon-pair-fst : El (⅀ (B (fst σ₃)) (C (fst σ₃)))
                canon-pair-fst = invEq (⟦⅀⟧ (B (fst σ₃)) (C (fst σ₃))) (b₂' , c')

                -- step3-fst-content: the b''-component PathP from
                -- `snd ⟦⅀⟧.fst (invEq ⟦⅀⟧ canon-AB)` to `canon-pair-fst`
                -- over `cong fst (secEq ⟦⅀⟧A(⅀BC) canon-AB)`.  Verified via
                -- hcomp combining (i) cong snd of secEq, (ii) cong-invEq-
                -- cong-snd of `snd-pAB≡c'`.  STANDALONE sub-lemma at the β
                -- level — does not chain into the main proof; the genuine
                -- d-fibre content is in d-step-2-2-eq below.

                -- b-eq-adapter: bridges the propositional gap
                -- `fst ⟦⅀⟧.fst (snd (lhs-pair x)) ≡ β-call`, which arises
                -- after `push-eq` reduces the transport to
                -- `invEq ⟦⅀⟧ (Σ-cong-equiv .fst (⟦⅀⟧.fst (snd (lhs-pair x))))`.
                -- The `⟦⅀⟧.fst (snd (lhs-pair x))` here is propositionally
                -- (not definitionally) `(β-call, d-of-inner-3)` via secEq
                -- of `⟦⅀⟧ ∘ invEq ⟦⅀⟧`; the adapter is `cong (transport
                -- (cong El p-path))` of `cong fst (secEq ⟦⅀⟧ ...)`, and
                -- composes with `b-eq` to give the full b-component path.
                d-of-inner-3 : El (dNR₀ {𝒰 = 𝒰} A B C D
                                       (fst (equivFun (⟦⅀⟧ (⅀ A (λ a → ⅀ (B a) (C a)))
                                                             (dNR₀ {𝒰 = 𝒰} A B C D))
                                                       (invEq inner-3 x))))
                d-of-inner-3 = snd (equivFun (⟦⅀⟧ (⅀ A (λ a → ⅀ (B a) (C a)))
                                                   (dNR₀ {𝒰 = 𝒰} A B C D))
                                              (invEq inner-3 x))

                b-eq-adapter :
                  transport (cong El p-path)
                            (fst (equivFun (⟦⅀⟧ (⅀ (B (fst (lhs-pair x)))
                                                    (C (fst (lhs-pair x))))
                                                  (⅀Assoc-C' (B (fst (lhs-pair x)))
                                                              (C (fst (lhs-pair x)))
                                                              (D (fst (lhs-pair x)))))
                                            (snd (lhs-pair x))))
                  ≡ transport (cong El p-path) β-call
                b-eq-adapter =
                  cong (transport (cong El p-path))
                       (cong fst (secEq (⟦⅀⟧ (⅀ (B (fst (lhs-pair x)))
                                                  (C (fst (lhs-pair x))))
                                              (⅀Assoc-C' (B (fst (lhs-pair x)))
                                                          (C (fst (lhs-pair x)))
                                                          (D (fst (lhs-pair x)))))
                                       (β-call , d-of-inner-3)))

                step3-fst-content :
                  PathP (λ i → El (⅀ (B (fst (secEq (⟦⅀⟧ A (λ a → ⅀ (B a) (C a))) canon-AB i)))
                                      (C (fst (secEq (⟦⅀⟧ A (λ a → ⅀ (B a) (C a))) canon-AB i)))))
                        (snd (equivFun (⟦⅀⟧ A (λ a → ⅀ (B a) (C a)))
                                        (invEq (⟦⅀⟧ A (λ a → ⅀ (B a) (C a))) canon-AB)))
                        canon-pair-fst
                step3-fst-content i =
                  hcomp (λ j → λ { (i = i0) → snd (equivFun (⟦⅀⟧ A (λ a → ⅀ (B a) (C a)))
                                                            (invEq (⟦⅀⟧ A (λ a → ⅀ (B a) (C a))) canon-AB))
                                  ; (i = i1) → invEq (⟦⅀⟧ (B (fst σ₃)) (C (fst σ₃)))
                                                      ( b₂' , snd-pAB≡c' j ) })
                        (snd (secEq (⟦⅀⟧ A (λ a → ⅀ (B a) (C a))) canon-AB i))

                -- ====================================================================
                -- d-step-adapter-explicit: the d-fibre PathP companion to
                -- `b-eq-adapter`.  Uses
                -- `cong snd (secEq ⟦⅀⟧(⅀(B(lhs-pair x.fst))(C(...)))(⅀Assoc-C'
                -- (...)) (β-call, d-of-inner-3))` as the underlying path,
                -- lifted across the family change (B(lhs-pair x.fst))→(B σ₃)
                -- via the `qp-path`-with-`transport-filler` family.
                --
                -- Endpoints:
                --   - i=0: `transport-tf c''-LHS` (= the LHS of d-PathP).
                --   - i=1: `transport (qp-tf-β-call) d-of-inner-3` (intermediate;
                --          needs a further d-step to reach `subst-d d-canon`).
                --
                -- The construction is well-typed because:
                --   (a) `cong fst (secEq ⟦⅀⟧ ...) 0 = b''-LHS` (definitional;
                --       since `snd (lhs-pair x) = invEq ⟦⅀⟧ (β-call, d-of-inner-3)`
                --       definitionally).
                --   (b) `cong fst (secEq ⟦⅀⟧ ...) 1 = β-call` (definitional).
                --   (c) The family `λ k → ⅀Assoc-C' (B (lhs-fst-eq k))(C ...)(D ...)
                --       (transport-filler (cong El p-path) y k)` runs from
                --       `⅀Assoc-C' (B(lhs-pair x.fst))(...) y` at k=0 to
                --       `⅀Assoc-C' (B σ₃)(...) (transport (cong El p-path) y)`
                --       at k=1.
                d-step-adapter-explicit :
                  PathP (λ i → El (⅀Assoc-C' (B (fst σ₃)) (C (fst σ₃)) (D (fst σ₃))
                                              (b-eq-adapter i)))
                        (transport
                          (cong El (λ k → ⅀Assoc-C' (B (lhs-fst-eq k))
                                                     (C (lhs-fst-eq k))
                                                     (D (lhs-fst-eq k))
                                                     (transport-filler (cong El p-path)
                                                                        (fst (equivFun (⟦⅀⟧ (⅀ (B (fst (lhs-pair x)))
                                                                                                  (C (fst (lhs-pair x))))
                                                                                              (⅀Assoc-C' (B (fst (lhs-pair x)))
                                                                                                          (C (fst (lhs-pair x)))
                                                                                                          (D (fst (lhs-pair x)))))
                                                                                       (snd (lhs-pair x))))
                                                                        k)))
                          (snd (equivFun (⟦⅀⟧ (⅀ (B (fst (lhs-pair x)))
                                                  (C (fst (lhs-pair x))))
                                              (⅀Assoc-C' (B (fst (lhs-pair x)))
                                                          (C (fst (lhs-pair x)))
                                                          (D (fst (lhs-pair x)))))
                                          (snd (lhs-pair x)))))
                        (transport
                          (cong El (λ k → ⅀Assoc-C' (B (lhs-fst-eq k))
                                                     (C (lhs-fst-eq k))
                                                     (D (lhs-fst-eq k))
                                                     (transport-filler (cong El p-path) β-call k)))
                          d-of-inner-3)
                d-step-adapter-explicit i =
                  transport
                    (cong El (λ k → ⅀Assoc-C' (B (lhs-fst-eq k))
                                               (C (lhs-fst-eq k))
                                               (D (lhs-fst-eq k))
                                               (transport-filler (cong El p-path)
                                                                  (cong fst (secEq (⟦⅀⟧ (⅀ (B (fst (lhs-pair x)))
                                                                                              (C (fst (lhs-pair x))))
                                                                                          (⅀Assoc-C' (B (fst (lhs-pair x)))
                                                                                                      (C (fst (lhs-pair x)))
                                                                                                      (D (fst (lhs-pair x)))))
                                                                                   (β-call , d-of-inner-3)) i)
                                                                  k)))
                    (cong snd (secEq (⟦⅀⟧ (⅀ (B (fst (lhs-pair x)))
                                                (C (fst (lhs-pair x))))
                                            (⅀Assoc-C' (B (fst (lhs-pair x)))
                                                        (C (fst (lhs-pair x)))
                                                        (D (fst (lhs-pair x)))))
                                     (β-call , d-of-inner-3)) i)

                -- ====================================================================
                -- d-snd-path: the natural d-fibre path between
                -- `d-canon` (= `snd (⟦⅀⟧(C σ₃ b₂')(D σ₃ b₂').fst (snd σ₂))`)
                -- and `snd σ₁`, over `snd-pAB≡c'`'s underlying `cong fst
                -- secEq`.  Uses `symP (cong snd (secEq ⟦⅀⟧(C σ₃ b₂')(D σ₃ b₂')
                -- (snd p-AB, snd σ₁)))` — VERIFIED structural fact about
                -- `⟦⅀⟧`'s `secEq` (NOT a `subst-filler` tautology).
                d-snd-path :
                  PathP (λ i → El (D (fst σ₃) b₂' (snd-pAB≡c' i)))
                        (snd σ₁)
                        (snd (equivFun (⟦⅀⟧ (C (fst σ₃) b₂') (D (fst σ₃) b₂'))
                                        (snd σ₂)))
                d-snd-path =
                  symP (cong snd (secEq (⟦⅀⟧ (C (fst σ₃) b₂') (D (fst σ₃) b₂'))
                                         (snd p-AB , snd σ₁)))

                -- ====================================================================
                -- d-step-cong-snd-pAB: the d-fibre PathP companion to
                -- `cong-snd-pAB` (=
                -- `cong (λ c → invEq ⟦⅀⟧(B σ₃)(C σ₃)(b₂', c)) snd-pAB≡c'`,
                -- which is the second half of `b-eq`).  Constructed
                -- pointwise by `subst`-ing `d-snd-path` over `sym (secEq
                -- ⟦⅀⟧(B σ₃)(C σ₃)(b₂', snd-pAB≡c' i))` at each i.
                --
                -- Endpoints:
                --   - i=0: `subst (...) (sym (secEq ⟦⅀⟧(b₂', snd p-AB))) (snd σ₁)`
                --          (= subst-snd-σ₁; the d-element at `snd canon-AB`).
                --   - i=1: `subst (...) (sym (secEq ⟦⅀⟧(b₂', c'))) d-canon`
                --          (= the d-component of `Assoc-cont (B σ₃)(C σ₃)(D σ₃)
                --             (b₂', snd σ₂)` AFTER `Assoc-cont` unfolding).
                --
                -- VERIFIED (no `subst-filler`-on-defined-endpoint).  Will
                -- close the rightmost piece of the full d-PathP composition.
                d-step-cong-snd-pAB :
                  PathP (λ i → El (⅀Assoc-C' (B (fst σ₃)) (C (fst σ₃)) (D (fst σ₃))
                                              (invEq (⟦⅀⟧ (B (fst σ₃)) (C (fst σ₃)))
                                                      (b₂' , snd-pAB≡c' i))))
                        (subst (λ p → El (D (fst σ₃) (fst p) (snd p)))
                               (sym (secEq (⟦⅀⟧ (B (fst σ₃)) (C (fst σ₃))) (b₂' , snd p-AB)))
                               (snd σ₁))
                        (subst (λ p → El (D (fst σ₃) (fst p) (snd p)))
                               (sym (secEq (⟦⅀⟧ (B (fst σ₃)) (C (fst σ₃))) (b₂' ,
                                            fst (equivFun (⟦⅀⟧ (C (fst σ₃) b₂') (D (fst σ₃) b₂'))
                                                           (snd σ₂)))))
                               (snd (equivFun (⟦⅀⟧ (C (fst σ₃) b₂') (D (fst σ₃) b₂'))
                                               (snd σ₂))))
                d-step-cong-snd-pAB i =
                  subst (λ p → El (D (fst σ₃) (fst p) (snd p)))
                        (sym (secEq (⟦⅀⟧ (B (fst σ₃)) (C (fst σ₃))) (b₂' , snd-pAB≡c' i)))
                        (d-snd-path i)

                -- ====================================================================
                -- The assembly of lhs-snd-after-transport: push-eq + ΣPathP +
                -- cong (invEq ⟦⅀⟧) over b-eq-adapter, b-eq,
                -- d-step-adapter-explicit, d-step-middle (compositional, from
                -- d-step-2-1/2-2/2-3) and d-step-cong-snd-pAB.  The
                -- substantive Mac Lane content lives in d-step-2-2: the
                -- equality of two cubical transports of snd σ₁ in
                -- El (D σ₃ (fst ⟦⅀⟧.fst (snd canon-AB)) (snd ⟦⅀⟧.fst (snd
                -- canon-AB))) — one via Q's gdp-twisted invEq, the other via
                -- subst along sym (secEq (b₂', snd p-AB)) — the Mac Lane
                -- pentagon for ⅀Assoc≃ at this σ₁/σ₂/σ₃-slice, settled in
                -- the triple set T³.
                --
                -- DEFINITIONAL FACT:
                --   Assoc-cont 𝒰 A B C (b , w) ≡ invEq ⟦⅀⟧ (invEq ⟦⅀⟧ (b, b'),
                --                                          subst (sym secEq) c')
                --   by REFL; the target is invEq ⟦⅀⟧ (canon-pair-fst, subst-d)
                --   definitionally.
                -- ====================================================================
                -- 3-segment decomposition of d-step-middle.  Each `d-step-2.k`
                -- is the d-fibre PathP companion to `β-PathP-stepK`, sharing
                -- the outer (B (lhs-fst-eq i))(...) family.  Endpoints are
                -- d-values at the inner-3 / Q-twist / canon-AB boundaries.
                --
                -- intermediate-1: d-fibre at β-PathP-step1's i=1
                -- (= snd ⟦⅀⟧.fst (fst (invEq Q σ₁))).  This IS `snd (invEq Q σ₁)`
                -- by dNR₀ unfolding.
                intermediate-1 :
                  El (dNR₀ {𝒰 = 𝒰} A B C D (fst (invEq Q σ₁)))
                intermediate-1 = snd (invEq Q σ₁)

                -- H: the d-fibre family over Σ-pairs (a, ab : ⅀(B(a))(C(a))).
                H : Σ (El A) (λ a → El (⅀ (B a) (C a))) → Type ℓe
                H p = El (⅀Assoc-C' (B (fst p)) (C (fst p)) (D (fst p)) (snd p))

                -- intermediate-2: defined as `subst H (sym secEq canon-AB)
                -- subst-snd-σ₁`.  This consolidates ALL the substantive
                -- content into d-step-2-2 (which now must connect
                -- intermediate-1 to this specific subst form, carrying both
                -- the lhs-fst-rewrite content AND the canon-AB-bridge).
                -- d-step-2-3 becomes a mechanical subst-filler.
                intermediate-2 :
                  El (dNR₀ {𝒰 = 𝒰} A B C D (invEq (⟦⅀⟧ A (λ a → ⅀ (B a) (C a))) canon-AB))
                intermediate-2 = subst H
                                       (sym (secEq (⟦⅀⟧ A (λ a → ⅀ (B a) (C a))) canon-AB))
                                       (subst (λ p → El (D (fst σ₃) (fst p) (snd p)))
                                              (sym (secEq (⟦⅀⟧ (B (fst σ₃)) (C (fst σ₃))) (b₂' , snd p-AB)))
                                              (snd σ₁))

                -- d-step-2.1: PathP over β-PathP-step1 (the secEq-of-inner-3
                -- segment).  Bridges d-of-inner-3 to intermediate-1
                -- (= snd (invEq Q σ₁)).
                -- PROVED via cong-snd of secEq ⟦⅀⟧⅀A⅀BC_dNR₀ at (invEq Q σ₁).
                d-step-2-1 :
                  PathP (λ i → El (⅀Assoc-C' (B (fst (equivFun (⟦⅀⟧ A (λ a → ⅀ (B a) (C a)))
                                                                  (fst (secEq (⟦⅀⟧ (⅀ A (λ a → ⅀ (B a) (C a)))
                                                                                     (dNR₀ {𝒰 = 𝒰} A B C D))
                                                                                (invEq Q σ₁) i)))))
                                              (C (fst (equivFun (⟦⅀⟧ A (λ a → ⅀ (B a) (C a)))
                                                                  (fst (secEq (⟦⅀⟧ (⅀ A (λ a → ⅀ (B a) (C a)))
                                                                                     (dNR₀ {𝒰 = 𝒰} A B C D))
                                                                                (invEq Q σ₁) i)))))
                                              (D (fst (equivFun (⟦⅀⟧ A (λ a → ⅀ (B a) (C a)))
                                                                  (fst (secEq (⟦⅀⟧ (⅀ A (λ a → ⅀ (B a) (C a)))
                                                                                     (dNR₀ {𝒰 = 𝒰} A B C D))
                                                                                (invEq Q σ₁) i)))))
                                              (β-PathP-step1 i)))
                        d-of-inner-3
                        intermediate-1
                d-step-2-1 i =
                  snd (secEq (⟦⅀⟧ (⅀ A (λ a → ⅀ (B a) (C a)))
                                    (dNR₀ {𝒰 = 𝒰} A B C D))
                              (invEq Q σ₁) i)

                -- d-step-2.2 reformulated as `toPathP` of a fromPathP-eq.
                -- The substantive Mac Lane content is concentrated in
                -- `d-step-2-2-eq`: the transport over `lhs-fst-rewrite`
                -- of intermediate-1 equals intermediate-2.  This is
                -- BIDIRECTIONALLY EQUIVALENT to d-step-2-2 as a PathP
                -- (toPathP/fromPathP equivalence).  Decomposing it via
                -- substComposite over lhs-fst-rewrite's 3 segments would
                -- give 3 sub-equations, each potentially provable from
                -- universe-internal coherences IF the intermediate
                -- transports are canonically computable.
                -- d-step-2-2-eq: PROVED at the canonical hg₀.
                -- (E1) flatten `cong snd (secEq Q σ₁)`; (gdp-line-eq) the
                -- traced gdp-line is hg₀-pointwise ∙ a cong-dNL₀ bridge;
                -- hg₀-pointwise is cong-F̂ of two T³-slides (GenHomog); so
                -- intermediate-1 is the subst of (snd σ₁) backwards along
                -- an explicit T³-path (E5).  The goal transport is the
                -- subst along cong-readΣ-seg2 and intermediate-2 the subst
                -- along the two canonical sym-secEq slides — ALL substs of
                -- (El ∘ F̂) along paths in the triple SET T³ (isSetEl ⇒
                -- isSetΣ³), so the base paths are equal and transports agree.
                d-step-2-2-eq :
                  transport (λ i → El (⅀Assoc-C' (B (fst (equivFun (⟦⅀⟧ A (λ a → ⅀ (B a) (C a)))
                                                                     (lhs-fst-rewrite i))))
                                                  (C (fst (equivFun (⟦⅀⟧ A (λ a → ⅀ (B a) (C a)))
                                                                     (lhs-fst-rewrite i))))
                                                  (D (fst (equivFun (⟦⅀⟧ A (λ a → ⅀ (B a) (C a)))
                                                                     (lhs-fst-rewrite i))))
                                                  (β-PathP-step2 i)))
                            intermediate-1
                  ≡ intermediate-2
                d-step-2-2-eq =
                    cong (subst ElD (cong readΣ seg2)) E5
                  ∙ sym (substComposite ElD (sym Lpath) (cong readΣ seg2) (snd σ₁))
                  ∙ cong (λ ρ → subst ElD ρ (snd σ₁)) setEq
                  ∙ substComposite ElD R₁ R₂ (snd σ₁)
                  where
                    module GHD = GH {𝒰 = 𝒰} A B C {T = Code} D

                    ElD : GHD.T³ → Type ℓe
                    ElD t = El (GHD.F̂ t)

                    isSetT³ : isSet GHD.T³
                    isSetT³ = isSetΣ (isSetEl A)
                                (λ a → isSetΣ (isSetEl (B a)) (λ b → isSetEl (C a b)))

                    w' : El (⅀ A (λ a → ⅀ (B a) (C a)))
                    w' = fst (invEq Q σ₁)

                    seg2 = cong (equivFun (⟦⅀⟧ A (λ a → ⅀ (B a) (C a)))) lhs-fst-rewrite

                    readΣ : Σ (El A) (λ a → El (⅀ (B a) (C a))) → GHD.T³
                    readΣ p = fst p
                            , fst (equivFun (⟦⅀⟧ (B (fst p)) (C (fst p))) (snd p))
                            , snd (equivFun (⟦⅀⟧ (B (fst p)) (C (fst p))) (snd p))

                    gline : Path Code
                              (dNR₀ {𝒰 = 𝒰} A B C D w')
                              (dNL₀ {𝒰 = 𝒰} A B C D
                                 (transport (cong El (Inj (⅀Assoc≃ A B C))) w'))
                    gline i = gdp i (transport-filler (cong El (Inj (⅀Assoc≃ A B C))) w' i)

                    E1 : subst (λ z → El (dNL₀ {𝒰 = 𝒰} A B C D z))
                               (cong fst (secEq Q σ₁))
                               (transport (cong El gline) intermediate-1)
                       ≡ snd σ₁
                    E1 = fromPathP (λ i → snd (secEq Q σ₁ i))

                    γ₀ : equivFun (⅀Assoc≃ A B C) w' ≡ fst σ₁
                    γ₀ = inj-bridge {𝒰 = 𝒰} isSetEl A B C D w'
                       ∙ cong fst (secEq Q σ₁)

                    Lpath : Path GHD.T³ (GHD.readNR w') (GHD.readNL (fst σ₁))
                    Lpath = GHD.slide1 w'
                          ∙ GHD.slide2 w'
                          ∙ cong GHD.readNL γ₀

                    EA : transport (cong El gline) intermediate-1
                       ≡ subst (λ z → El (dNL₀ {𝒰 = 𝒰} A B C D z))
                               (inj-bridge {𝒰 = 𝒰} isSetEl A B C D w')
                               (subst ElD (GHD.slide2 w')
                                  (subst ElD (GHD.slide1 w') intermediate-1))
                    EA = cong (λ p → transport (cong El p) intermediate-1)
                              (gdp-line-eq {𝒰 = 𝒰} isSetEl A B C D w')
                       ∙ substComposite El
                           (GHD.ghomog-pt w')
                           (cong (dNL₀ {𝒰 = 𝒰} A B C D)
                                 (inj-bridge {𝒰 = 𝒰} isSetEl A B C D w'))
                           intermediate-1
                       ∙ cong (subst El (cong (dNL₀ {𝒰 = 𝒰} A B C D)
                                              (inj-bridge {𝒰 = 𝒰} isSetEl A B C D w')))
                              (substComposite El
                                (cong GHD.F̂ (GHD.slide1 w'))
                                (cong GHD.F̂ (GHD.slide2 w'))
                                intermediate-1)

                    E4 : subst ElD Lpath intermediate-1 ≡ snd σ₁
                    E4 = substComposite ElD (GHD.slide1 w')
                                            (GHD.slide2 w' ∙ cong GHD.readNL γ₀)
                                            intermediate-1
                       ∙ substComposite ElD (GHD.slide2 w') (cong GHD.readNL γ₀)
                                            (subst ElD (GHD.slide1 w') intermediate-1)
                       ∙ substComposite (λ z → El (dNL₀ {𝒰 = 𝒰} A B C D z))
                                        (inj-bridge {𝒰 = 𝒰} isSetEl A B C D w')
                                        (cong fst (secEq Q σ₁))
                                        (subst ElD (GHD.slide2 w')
                                           (subst ElD (GHD.slide1 w') intermediate-1))
                       ∙ cong (subst (λ z → El (dNL₀ {𝒰 = 𝒰} A B C D z))
                                     (cong fst (secEq Q σ₁)))
                              (sym EA)
                       ∙ E1

                    E5 : intermediate-1 ≡ subst ElD (sym Lpath) (snd σ₁)
                    E5 = sym (subst⁻Subst ElD Lpath intermediate-1)
                       ∙ cong (subst ElD (sym Lpath)) E4

                    R₁ : Path GHD.T³
                           (GHD.readNL (fst σ₁))
                           ( fst σ₃
                           , fst (equivFun (⟦⅀⟧ (B (fst σ₃)) (C (fst σ₃)))
                                           (invEq (⟦⅀⟧ (B (fst σ₃)) (C (fst σ₃)))
                                                  (b₂' , snd p-AB)))
                           , snd (equivFun (⟦⅀⟧ (B (fst σ₃)) (C (fst σ₃)))
                                           (invEq (⟦⅀⟧ (B (fst σ₃)) (C (fst σ₃)))
                                                  (b₂' , snd p-AB))) )
                    R₁ = cong (λ p → fst σ₃ , fst p , snd p)
                              (sym (secEq (⟦⅀⟧ (B (fst σ₃)) (C (fst σ₃)))
                                          (b₂' , snd p-AB)))

                    R₂ : Path GHD.T³ _ _
                    R₂ = cong readΣ
                              (sym (secEq (⟦⅀⟧ A (λ a → ⅀ (B a) (C a))) canon-AB))

                    setEq : sym Lpath ∙ cong readΣ seg2 ≡ R₁ ∙ R₂
                    setEq = isSetT³ _ _ (sym Lpath ∙ cong readΣ seg2) (R₁ ∙ R₂)

                d-step-2-2 :
                  PathP (λ i → El (⅀Assoc-C' (B (fst (equivFun (⟦⅀⟧ A (λ a → ⅀ (B a) (C a)))
                                                                  (lhs-fst-rewrite i))))
                                              (C (fst (equivFun (⟦⅀⟧ A (λ a → ⅀ (B a) (C a)))
                                                                  (lhs-fst-rewrite i))))
                                              (D (fst (equivFun (⟦⅀⟧ A (λ a → ⅀ (B a) (C a)))
                                                                  (lhs-fst-rewrite i))))
                                              (β-PathP-step2 i)))
                        intermediate-1
                        intermediate-2
                d-step-2-2 = toPathP d-step-2-2-eq

                -- d-step-2.3: PathP over β-PathP-step3 (the secEq-of-canon-AB
                -- segment).  With intermediate-2 = subst H (sym secEq) subst-snd-σ₁,
                -- this is PROVED as `symP (subst-filler H (sym secEq …) …)`.
                d-step-2-3 :
                  PathP (λ i → El (⅀Assoc-C' (B (fst (secEq (⟦⅀⟧ A (λ a → ⅀ (B a) (C a))) canon-AB i)))
                                              (C (fst (secEq (⟦⅀⟧ A (λ a → ⅀ (B a) (C a))) canon-AB i)))
                                              (D (fst (secEq (⟦⅀⟧ A (λ a → ⅀ (B a) (C a))) canon-AB i)))
                                              (β-PathP-step3 i)))
                        intermediate-2
                        (subst (λ p → El (D (fst σ₃) (fst p) (snd p)))
                               (sym (secEq (⟦⅀⟧ (B (fst σ₃)) (C (fst σ₃))) (b₂' , snd p-AB)))
                               (snd σ₁))
                d-step-2-3 =
                  symP (subst-filler H
                                     (sym (secEq (⟦⅀⟧ A (λ a → ⅀ (B a) (C a))) canon-AB))
                                     (subst (λ p → El (D (fst σ₃) (fst p) (snd p)))
                                            (sym (secEq (⟦⅀⟧ (B (fst σ₃)) (C (fst σ₃))) (b₂' , snd p-AB)))
                                            (snd σ₁)))

                -- d-step-middle: derived (via isSetEl) from d-step-2-1,
                -- d-step-2-2 and d-step-2-3.
                -- The former `_∙_` vs ΣPathP composition gap closes because
                -- the base Σ-type `Σ (El A) (El ∘ ⅀BC)` is a set (isSetΣ of
                -- isSetEl): the segment composite seg1 ∙ (seg2 ∙ seg3) and
                -- pathT ∙ pathM are parallel paths in a set, hence equal,
                -- and the composite PathP transfers across by subst.  Glue:
                -- compPathP' at the H family, substComposite, toPathP.
                d-step-middle :
                  PathP (λ i → El (⅀Assoc-C' (B (fst σ₃)) (C (fst σ₃)) (D (fst σ₃))
                                              (fromPathP β-PathP i)))
                        (transport
                          (cong El (λ k → ⅀Assoc-C' (B (lhs-fst-eq k))
                                                     (C (lhs-fst-eq k))
                                                     (D (lhs-fst-eq k))
                                                     (transport-filler (cong El p-path) β-call k)))
                          d-of-inner-3)
                        (subst (λ p → El (D (fst σ₃) (fst p) (snd p)))
                               (sym (secEq (⟦⅀⟧ (B (fst σ₃)) (C (fst σ₃))) (b₂' , snd p-AB)))
                               (snd σ₁))
                d-step-middle = toPathP split-eq
                  where
                    ΣAB-set : isSet (Σ (El A) (λ a → El (⅀ (B a) (C a))))
                    ΣAB-set = isSetΣ (isSetEl A) (λ a → isSetEl (⅀ (B a) (C a)))

                    seg1 = cong (λ w → equivFun (⟦⅀⟧ A (λ a → ⅀ (B a) (C a))) (fst w))
                                (secEq (⟦⅀⟧ (⅀ A (λ a → ⅀ (B a) (C a)))
                                             (dNR₀ {𝒰 = 𝒰} A B C D))
                                       (invEq Q σ₁))

                    seg2 = cong (equivFun (⟦⅀⟧ A (λ a → ⅀ (B a) (C a)))) lhs-fst-rewrite

                    seg3 = secEq (⟦⅀⟧ A (λ a → ⅀ (B a) (C a))) canon-AB

                    pathT : Path (Σ (El A) (λ a → El (⅀ (B a) (C a))))
                                 (fst (lhs-pair x) , β-call)
                                 (fst σ₃ , transport (cong El p-path) β-call)
                    pathT k = lhs-fst-eq k , transport-filler (cong El p-path) β-call k

                    pathM : Path (Σ (El A) (λ a → El (⅀ (B a) (C a))))
                                 (fst σ₃ , transport (cong El p-path) β-call)
                                 (fst σ₃ , snd canon-AB)
                    pathM i = fst σ₃ , fromPathP β-PathP i

                    P-comp : PathP (λ i → H ((seg1 ∙ (seg2 ∙ seg3)) i))
                                   d-of-inner-3
                                   (subst (λ p → El (D (fst σ₃) (fst p) (snd p)))
                                          (sym (secEq (⟦⅀⟧ (B (fst σ₃)) (C (fst σ₃))) (b₂' , snd p-AB)))
                                          (snd σ₁))
                    P-comp = compPathP' {B = H} {p = seg1} {q = seg2 ∙ seg3}
                               d-step-2-1
                               (compPathP' {B = H} {p = seg2} {q = seg3}
                                 d-step-2-2 d-step-2-3)

                    paths-eq : seg1 ∙ (seg2 ∙ seg3) ≡ pathT ∙ pathM
                    paths-eq = ΣAB-set _ _ (seg1 ∙ (seg2 ∙ seg3)) (pathT ∙ pathM)

                    P-swapped : PathP (λ i → H ((pathT ∙ pathM) i))
                                      d-of-inner-3
                                      (subst (λ p → El (D (fst σ₃) (fst p) (snd p)))
                                             (sym (secEq (⟦⅀⟧ (B (fst σ₃)) (C (fst σ₃))) (b₂' , snd p-AB)))
                                             (snd σ₁))
                    P-swapped = subst (λ pc → PathP (λ i → H (pc i))
                                                    d-of-inner-3
                                                    (subst (λ p → El (D (fst σ₃) (fst p) (snd p)))
                                                           (sym (secEq (⟦⅀⟧ (B (fst σ₃)) (C (fst σ₃))) (b₂' , snd p-AB)))
                                                           (snd σ₁)))
                                      paths-eq P-comp

                    split-eq : subst H pathM (subst H pathT d-of-inner-3)
                             ≡ subst (λ p → El (D (fst σ₃) (fst p) (snd p)))
                                     (sym (secEq (⟦⅀⟧ (B (fst σ₃)) (C (fst σ₃))) (b₂' , snd p-AB)))
                                     (snd σ₁)
                    split-eq = sym (substComposite H pathT pathM d-of-inner-3)
                             ∙ fromPathP P-swapped


                lhs-snd-after-transport =
                    push-eq
                  ∙ cong (invEq (⟦⅀⟧ (⅀ (B (fst σ₃)) (C (fst σ₃)))
                                       (⅀Assoc-C' (B (fst σ₃)) (C (fst σ₃)) (D (fst σ₃)))))
                         (ΣPathP ( b-eq-adapter ∙ b-eq
                                 , compPathP' {B = λ ab → El (⅀Assoc-C' (B (fst σ₃))
                                                                          (C (fst σ₃))
                                                                          (D (fst σ₃)) ab)}
                                     d-step-adapter-explicit
                                     (compPathP' {B = λ ab → El (⅀Assoc-C' (B (fst σ₃))
                                                                             (C (fst σ₃))
                                                                             (D (fst σ₃)) ab)}
                                       d-step-middle
                                       d-step-cong-snd-pAB) ))

            lhs-canon : lhs-pair x
              ≡ ( fst σ₃
                , Assoc.Assoc-cont 𝒰 (B (fst σ₃)) (C (fst σ₃)) (D (fst σ₃))
                                   ( snd (equivFun (⟦⅀⟧ A B) (fst σ₂))
                                   , snd σ₂ ) )
            lhs-canon = ΣPathP (lhs-fst-eq , lhs-snd-PathP)

        LHS≡RHS : (x : El (⅀ (⅀ (⅀ A B) (⅀Assoc-C' A B C)) (dNL₀ {𝒰 = 𝒰} A B C D)))
                → LHS≃ .fst x ≡ RHS≃ .fst x
        LHS≡RHS x =
            lhs-decomp x
          ∙ cong (invEq (⟦⅀⟧ A (λ a → ⅀ (⅀ (B a) (C a))
                                       (⅀Assoc-C' (B a) (C a) (D a))))) (pair-eq x)
          ∙ sym (rhs-decomp x)

    -- The assembly: Code²→Equiv reduces the DepPentagon 2-cell to the
    -- equivalence level, where the §L bricks rewrite both sides into the
    -- chains equated by `equiv-pentagon`.
    dep-pentagon : DepPentagon {𝒰 = 𝒰} A B C D hg
    dep-pentagon = Code²→Equiv {𝒰 = 𝒰} pL pR
      (   pte∙ {𝒰 = 𝒰} (sym L1fwd) (sym (Inj (⅀Assoc≃ A ALB ALC)))
        ∙ cong₂ compEquiv
            ( pte-sym {𝒰 = 𝒰} L1fwd
            ∙ cong invEquiv
                (⟦⅀⟧-natural {𝒰 = 𝒰} (Inj (⅀Assoc≃ A B C)) gdp) )
            ( bareEdge≃ {𝒰 = 𝒰} A ALB ALC )
        ∙ equiv-pentagon
        ∙ sym ( pte∙ {𝒰 = 𝒰} (sym (Inj (⅀Assoc≃ (⅀ A B) Bᶜ Cnᶜ)))
                     (sym (Inj (⅀Assoc≃ A B RG))
                      ∙ cong (⅀ A) (qR3 {𝒰 = 𝒰} A B C D))
              ∙ cong₂ compEquiv
                  ( bareEdge≃ {𝒰 = 𝒰} (⅀ A B) Bᶜ Cnᶜ )
                  ( pte∙ {𝒰 = 𝒰} (sym (Inj (⅀Assoc≃ A B RG)))
                                  (cong (⅀ A) (qR3 {𝒰 = 𝒰} A B C D))
                  ∙ cong₂ compEquiv
                      ( bareEdge≃ {𝒰 = 𝒰} A B RG )
                      ( fibreEdge≃ {𝒰 = 𝒰} A B C D ) ) ) )
