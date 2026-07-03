{-# OPTIONS --cubical --no-import-sorts #-}
-- ============================================================================
-- HoTTOperads.Monad.PointwisePentagon
--
-- The pointwise pentagon for `OpM O` (paper §8 Thm 8.2, Data component):
-- the two reassociation routes' `Data` components, evaluated along
-- same-endpoint traces of their `Index` components, agree as paths in `X`.
--
-- Every evaluation in sight reduces to a `cong`-image of a path in the
-- master leaf SET T̂ = Σ El (Σ El (Σ El El)) under the master 4-level
-- reading G̃: bare `join-assoc` edges evaluate (evalBare) to the reversed
-- canonical stage line — `ghomog`-slides (paths in stage triple sets) and
-- a `data-NL` bridge — and the through-`join`/fibrewise edges re-pair the
-- inner evaluations with the leaf trace.  Parallel paths in the set T̂ are
-- equal, which closes the pentagon without truncating the carrier `X`.
--
-- Hypothesis: `isSetEl` (El a family of sets).  `X` is arbitrary.
-- ============================================================================
module HoTTOperads.Monad.PointwisePentagon where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.GroupoidLaws using (congFunct) renaming (assoc to ∙assoc)
open import Cubical.Foundations.HLevels using (isSetΣ)
open import Cubical.Data.Sigma using (Σ ; Σ-syntax ; _,_ ; fst ; snd)

open import HoTTOperads.Universe.Base
open import HoTTOperads.Operad.Base
open import HoTTOperads.Monad.Base
open import HoTTOperads.Monad.Composition using (join)
open import HoTTOperads.Monad.Functor using (_<$>_)
open import HoTTOperads.Monad.Laws using
  (module JoinAssocAux ; join-assoc ; join-assoc≡sym-aux)
open import HoTTOperads.Universe.Homog using (module GH)
open import HoTTOperads.Universe.HomogLine using (glue-tail ; gen-line-eq)
open import HoTTOperads.PathTrace using
  ( trace-eval-2cell ; trace-eval-∙ ; trace-eval-fill ; fill-tail
  ; eval-arb ; homotopy-diag )

private variable ℓc ℓe ℓk ℓx : Level

module _ {𝒰 : Universe ℓc ℓe} {K : Universe.Code 𝒰 → Type ℓk}
         (O : Operad 𝒰 K)
         (isSetEl : (Z : Universe.Code 𝒰) → isSet (Universe.El 𝒰 Z)) where
  open Universe 𝒰

  -- ==========================================================================
  -- §1  Stage machinery: a single `join-assoc` edge over a 3-deep argument.
  -- ==========================================================================
  module Stage {Y : Type ℓx} (z : OpM O (OpM O (OpM O Y))) where
    I' : Code
    I' = Index z
    Jf : El I' → Code
    Jf a = Index (Data z a)
    Mf : (a : El I') → El (Jf a) → Code
    Mf a b = Index (Data (Data z a) b)

    e : El (⅀ I' (λ a → ⅀ (Jf a) (Mf a))) ≃ El (⅀ (⅀ I' Jf) (⅀Assoc-C' I' Jf Mf))
    e = ⅀Assoc≃ I' Jf Mf

    Fz : (a : El I') (b : El (Jf a)) → El (Mf a b) → Y
    Fz a b = Data (Data (Data z a) b)

    NR = JoinAssocAux.data-NR O I' (Op z) (Data z)
    NL = JoinAssocAux.data-NL O I' (Op z) (Data z)
    hg = JoinAssocAux.homog O I' (Op z) (Data z)
    dp = JoinAssocAux.data-path O I' (Op z) (Data z)

    -- The opaque edge as the reversed aux path.
    jas : join-assoc O z ≡ sym (JoinAssocAux.aux O I' (Op z) (Data z))
    jas = join-assoc≡sym-aux O I' (Op z) (Data z)

    -- The canonical stage line: homog pointwise, then NL across a bridge.
    NRNL : {x₁ : El (⅀ I' (λ a → ⅀ (Jf a) (Mf a)))}
           {x₀ : El (⅀ (⅀ I' Jf) (⅀Assoc-C' I' Jf Mf))}
           (β : equivFun e x₁ ≡ x₀)
         → NR x₁ ≡ NL x₀
    NRNL {x₁ = x₁} β = funExt⁻ hg x₁ ∙ cong NL β

    -- homog is ghomog at the OpM data reading; its pointwise form is the
    -- composite of the cong-images of the two GH slides (refl).
    homog-is-ghomog : hg ≡ GH.ghomog {𝒰 = 𝒰} I' Jf Mf Fz
    homog-is-ghomog = refl

    -- The NR/NL readings are the GH ones (refl).
    NL-is-gNL : NL ≡ GH.gNL {𝒰 = 𝒰} I' Jf Mf Fz
    NL-is-gNL = refl

    NR-is-gNR : NR ≡ GH.gNR {𝒰 = 𝒰} I' Jf Mf Fz
    NR-is-gNR = refl

    F̂z = GH.F̂ {𝒰 = 𝒰} I' Jf Mf Fz
    rNR = GH.readNR {𝒰 = 𝒰} I' Jf Mf Fz
    rNL = GH.readNL {𝒰 = 𝒰} I' Jf Mf Fz

    -- The stage line's triple-set path: the two slides, then the
    -- NL-reading image of the bridge.  Opaque: consumers only ever need
    -- its boundary; the slide structure is re-exposed by `unfolding` where
    -- the collapse is proved.
    opaque
      M : {x₁ : El (⅀ I' (λ a → ⅀ (Jf a) (Mf a)))}
          {x₀ : El (⅀ (⅀ I' Jf) (⅀Assoc-C' I' Jf Mf))}
          (β : equivFun e x₁ ≡ x₀)
        → Path (GH.T³ {𝒰 = 𝒰} I' Jf Mf Fz) (rNR x₁) (rNL x₀)
      M {x₁ = x₁} β =
          (GH.slide1 {𝒰 = 𝒰} I' Jf Mf Fz x₁ ∙ GH.slide2 {𝒰 = 𝒰} I' Jf Mf Fz x₁)
        ∙ cong rNL β

    -- The whole stage line is the F̂-image of its triple-set path.
    opaque
      unfolding M

      NRNL-collapse :
        {x₁ : El (⅀ I' (λ a → ⅀ (Jf a) (Mf a)))}
        {x₀ : El (⅀ (⅀ I' Jf) (⅀Assoc-C' I' Jf Mf))}
        (β : equivFun e x₁ ≡ x₀)
        → NRNL β ≡ cong F̂z (M β)
      NRNL-collapse {x₁ = x₁} β =
        sym ( congFunct F̂z
                (GH.slide1 {𝒰 = 𝒰} I' Jf Mf Fz x₁ ∙ GH.slide2 {𝒰 = 𝒰} I' Jf Mf Fz x₁)
                (cong rNL β)
            ∙ cong (_∙ cong F̂z (cong rNL β))
                   (congFunct F̂z (GH.slide1 {𝒰 = 𝒰} I' Jf Mf Fz x₁)
                                 (GH.slide2 {𝒰 = 𝒰} I' Jf Mf Fz x₁)) )

    -- Evaluation of the bare join-assoc edge along an arbitrary
    -- same-endpoint trace: the reversed canonical stage line, at any
    -- equivalence-action bridge (bridges interchangeable by isSetEl).
    opaque
      evalBare :
        {x₀ : El (Index (join O (join O z)))}
        {x₁ : El (Index (join O ((join O) <$> z)))}
        (δ : PathP (λ i → El (Index (join-assoc O z i))) x₀ x₁)
        (β : equivFun e x₁ ≡ x₀)
        → Path (Path Y (Data (join O (join O z)) x₀)
                       (Data (join O ((join O) <$> z)) x₁))
               (λ i → Data (join-assoc O z i) (δ i))
               (sym (NRNL β))
      evalBare {x₀ = x₀} {x₁ = x₁} δ β =
          trace-eval-2cell (λ z' → isSetEl (Index z')) (λ z' → Data z') jas δ δq
        ∙ cong sym step2
        ∙ cong (λ b → sym (NRNL b)) bridge-swap
        where
          δq : PathP (λ i → El (Index (sym (JoinAssocAux.aux O I' (Op z) (Data z)) i)))
                     x₀ x₁
          δq = transport (λ t → PathP (λ i → El (Index (jas t i))) x₀ x₁) δ

          δ̂ : PathP (λ i → El (Inj e i)) x₁ x₀
          δ̂ = symP δq

          step2 : Path (Path Y (NR x₁) (NL x₀))
                       (λ i → dp i (δ̂ i))
                       (NRNL (glue-tail {𝒰 = 𝒰} I' Jf Mf x₁ ∙ fromPathP δ̂))
          step2 =
              eval-arb (isSetEl (⅀ (⅀ I' Jf) (⅀Assoc-C' I' Jf Mf))) dp δ̂
            ∙ cong (_∙ cong NL (fromPathP δ̂))
                   (gen-line-eq {𝒰 = 𝒰} I' Jf Mf NR NL hg x₁)
            ∙ sym (∙assoc (funExt⁻ hg x₁)
                          (cong NL (glue-tail {𝒰 = 𝒰} I' Jf Mf x₁))
                          (cong NL (fromPathP δ̂)))
            ∙ cong (funExt⁻ hg x₁ ∙_)
                   (sym (congFunct NL (glue-tail {𝒰 = 𝒰} I' Jf Mf x₁)
                                      (fromPathP δ̂)))

          bridge-swap : glue-tail {𝒰 = 𝒰} I' Jf Mf x₁ ∙ fromPathP δ̂ ≡ β
          bridge-swap = isSetEl (⅀ (⅀ I' Jf) (⅀Assoc-C' I' Jf Mf)) _ _ _ β

    opaque
      canonβ : {x₀ : El (Index (join O (join O z)))}
               {x₁ : El (Index (join O ((join O) <$> z)))}
               (δ : PathP (λ i → El (Index (join-assoc O z i))) x₀ x₁)
             → equivFun e x₁ ≡ x₀
      canonβ {x₀ = x₀} {x₁ = x₁} δ =
          glue-tail {𝒰 = 𝒰} I' Jf Mf x₁
        ∙ fromPathP (symP (transport (λ t → PathP (λ i → El (Index (jas t i))) x₀ x₁) δ))

    -- Bare-edge evaluation in fully collapsed form.
    opaque
      evalBareᶜ :
        {x₀ : El (Index (join O (join O z)))}
        {x₁ : El (Index (join O ((join O) <$> z)))}
        (δ : PathP (λ i → El (Index (join-assoc O z i))) x₀ x₁)
        → Path (Path Y (Data (join O (join O z)) x₀)
                       (Data (join O ((join O) <$> z)) x₁))
               (λ i → Data (join-assoc O z i) (δ i))
               (sym (cong F̂z (M (canonβ δ))))
      evalBareᶜ δ =
          evalBare δ (canonβ δ)
        ∙ cong sym (NRNL-collapse (canonβ δ))

  -- ==========================================================================
  -- §2  The pointwise pentagon at a 4-deep argument.
  -- ==========================================================================
  module _ {X : Type ℓx} (w : OpM O (OpM O (OpM O (OpM O X)))) where
    private
      A' : Code
      A' = Index w
      B' : El A' → Code
      B' a = Index (Data w a)
      C' : (a : El A') → El (B' a) → Code
      C' a b = Index (Data (Data w a) b)
      D' : (a : El A') (b : El (B' a)) (c : El (C' a b)) → Code
      D' a b c = Index (Data (Data (Data w a) b) c)

    -- The master leaf set and the master reading.
    T̂ : Type ℓe
    T̂ = Σ[ a ∈ El A' ] Σ[ b ∈ El (B' a) ] Σ[ c ∈ El (C' a b) ] El (D' a b c)

    isSetT̂ : isSet T̂
    isSetT̂ = isSetΣ (isSetEl A') (λ a →
              isSetΣ (isSetEl (B' a)) (λ b →
               isSetΣ (isSetEl (C' a b)) (λ c → isSetEl (D' a b c))))

    G̃ : T̂ → X
    G̃ t = Data (Data (Data (Data w (fst t)) (fst (snd t))) (fst (snd (snd t))))
               (snd (snd (snd t)))

    -- Corner reads: the corner Data functions factor through G̃ (refl).
    read0 : El (Index (join O (join O (join O w)))) → T̂
    read0 el =
      let s2d = equivFun (⟦⅀⟧ (Index (join O (join O w)))
                              (λ s → Index (Data (join O (join O w)) s))) el
          s1c = equivFun (⟦⅀⟧ (Index (join O w))
                              (λ s → Index (Data (join O w) s))) (fst s2d)
          ab  = equivFun (⟦⅀⟧ A' B') (fst s1c)
      in fst ab , snd ab , snd s1c , snd s2d

    probe-read0 : Data (join O (join O (join O w))) ≡ G̃ ∘ read0
    probe-read0 = refl

    read1 : El (Index (join O ((join O) <$> ((join O) <$> w)))) → T̂
    read1 el =
      let ab' = equivFun (⟦⅀⟧ A' (λ a → Index (join O (join O (Data w a))))) el
          a   = fst ab'
          sc  = equivFun (⟦⅀⟧ (Index (join O (Data w a)))
                              (λ s → Index (Data (join O (Data w a)) s))) (snd ab')
          bc  = equivFun (⟦⅀⟧ (B' a) (C' a)) (fst sc)
      in a , fst bc , snd bc , snd sc

    probe-read1 : Data (join O ((join O) <$> ((join O) <$> w))) ≡ G̃ ∘ read1
    probe-read1 = refl

    -- The L-route midpoint corner.
    readM : El (Index (join O (join O ((join O) <$> w)))) → T̂
    readM el =
      let s2d = equivFun (⟦⅀⟧ (Index (join O ((join O) <$> w)))
                              (λ s → Index (Data (join O ((join O) <$> w)) s))) el
          s1c = equivFun (⟦⅀⟧ A' (λ a → Index (join O (Data w a)))) (fst s2d)
          bc  = equivFun (⟦⅀⟧ (B' (fst s1c)) (C' (fst s1c))) (snd s1c)
      in fst s1c , fst bc , snd bc , snd s2d

    probe-readM : Data (join O (join O ((join O) <$> w))) ≡ G̃ ∘ readM
    probe-readM = refl

    -- §2a  Leg L1 (through-`join`): the evaluation re-pairs the inner
    -- stage-w evaluation (an OpM X-valued line) with the leaf trace; the
    -- collapsed inner line is an F̂-image, so the paired evaluation is a
    -- G̃-image definitionally.
    private
      module S1 = Stage w

    pair₁ : (t : GH.T³ {𝒰 = 𝒰} S1.I' S1.Jf S1.Mf S1.Fz)
          → El (Index (S1.F̂z t)) → T̂
    pair₁ t d = fst t , fst (snd t) , snd (snd t) , d

    module Through
      {y₀ : El (Index (join O (join O (join O w))))}
      {y₁ : El (Index (join O (join O ((join O) <$> w))))}
      (δ : PathP (λ i → El (Index (join O (join-assoc O w i)))) y₀ y₁)
      where

      private
        y₀s = equivFun (⟦⅀⟧ (Index (join O (join O w)))
                 (λ s → Index (Data (join O (join O w)) s))) y₀
        y₁s = equivFun (⟦⅀⟧ (Index (join O ((join O) <$> w)))
                 (λ s → Index (Data (join O ((join O) <$> w)) s))) y₁

        aa : PathP (λ i → El (Index (join-assoc O w i))) (fst y₀s) (fst y₁s)
        aa i = fst (equivFun (⟦⅀⟧ (Index (join-assoc O w i))
                     (λ s → Index (Data (join-assoc O w i) s))) (δ i))

        bb : PathP (λ i → El (Index (Data (join-assoc O w i) (aa i))))
                   (snd y₀s) (snd y₁s)
        bb i = snd (equivFun (⟦⅀⟧ (Index (join-assoc O w i))
                     (λ s → Index (Data (join-assoc O w i) s))) (δ i))

        σW : (λ i → Data (join-assoc O w i) (aa i))
           ≡ sym (cong S1.F̂z (S1.M (S1.canonβ aa)))
        σW = S1.evalBareᶜ aa

        bb' : PathP (λ i → El (Index (sym (cong S1.F̂z (S1.M (S1.canonβ aa))) i)))
                    (snd y₀s) (snd y₁s)
        bb' = transport (λ t → PathP (λ i → El (Index (σW t i)))
                                     (snd y₀s) (snd y₁s)) bb

      μ : Path T̂ (read0 y₀) (readM y₁)
      μ = sym (λ i → pair₁ (S1.M (S1.canonβ aa) i) (symP bb' i))

      eval : Path (Path X (Data (join O (join O (join O w))) y₀)
                          (Data (join O (join O ((join O) <$> w))) y₁))
                  (λ i → Data (join O (join-assoc O w i)) (δ i))
                  (cong G̃ μ)
      eval = trace-eval-2cell (λ v → isSetEl (Index v)) (λ v → Data v) σW bb bb'

    -- §2b  Leg R3 (the funExt left-whisker): the evaluation is a diagonal
    -- through the fibrewise join-assoc square; homotopy-diag straightens it
    -- into the a₀-fibre edge followed by the static fully-joined corner
    -- moving along the fibre trace, and the fibre edge is a bare stage.
    -- The R3 corners.
    readP : El (Index (join O ((λ v → join O ((join O) <$> v)) <$> w))) → T̂
    readP el =
      let sd = equivFun (⟦⅀⟧ A' (λ s → Index (join O ((join O) <$> (Data w s))))) el
          a  = fst sd
          bd = equivFun (⟦⅀⟧ (B' a) (λ b → Index (join O (Data (Data w a) b)))) (snd sd)
          cd = equivFun (⟦⅀⟧ (C' a (fst bd)) (D' a (fst bd))) (snd bd)
      in a , fst bd , fst cd , snd cd

    probe-readP : Data (join O ((λ v → join O ((join O) <$> v)) <$> w)) ≡ G̃ ∘ readP
    probe-readP = refl

    pairGG : (a : El A') → El (Index (join O (join O (Data w a)))) → T̂
    pairGG a el =
      let sd = equivFun (⟦⅀⟧ (Index (join O (Data w a)))
                             (λ s → Index (Data (join O (Data w a)) s))) el
          bc = equivFun (⟦⅀⟧ (B' a) (C' a)) (fst sd)
      in a , fst bc , snd bc , snd sd

    probe-pairGG : (a : El A')
                 → Data (join O (join O (Data w a))) ≡ (λ el → G̃ (pairGG a el))
    probe-pairGG a = refl

    module Fib
      {u₀ : El (Index (join O ((λ v → join O ((join O) <$> v)) <$> w)))}
      {u₁ : El (Index (join O ((λ v → join O (join O v)) <$> w)))}
      (δ : PathP (λ i → El (Index (join O ((λ v → sym (join-assoc O v) i) <$> w)))) u₀ u₁)
      where

      private
        u₀s = equivFun (⟦⅀⟧ A' (λ s → Index (join O ((join O) <$> (Data w s))))) u₀
        u₁s = equivFun (⟦⅀⟧ A' (λ s → Index (join O (join O (Data w s))))) u₁

        a : Path (El A') (fst u₀s) (fst u₁s)
        a i = fst (equivFun (⟦⅀⟧ A' (λ s → Index (sym (join-assoc O (Data w s)) i))) (δ i))

        b : PathP (λ i → El (Index (sym (join-assoc O (Data w (a i))) i)))
                  (snd u₀s) (snd u₁s)
        b i = snd (equivFun (⟦⅀⟧ A' (λ s → Index (sym (join-assoc O (Data w s)) i))) (δ i))

        v₀ = Data w (fst u₀s)

        gg : OpM O (OpM O (OpM O X)) → OpM O X
        gg v = join O (join O v)

        σV : (λ i → sym (join-assoc O (Data w (a i))) i)
           ≡ sym (join-assoc O v₀) ∙ cong gg (cong (Data w) a)
        σV = homotopy-diag (λ v → sym (join-assoc O v)) (cong (Data w) a)

        b₂ : PathP (λ i → El (Index ((sym (join-assoc O v₀) ∙ cong gg (cong (Data w) a)) i)))
                   (snd u₀s) (snd u₁s)
        b₂ = transport (λ t → PathP (λ i → El (Index (σV t i)))
                                    (snd u₀s) (snd u₁s)) b

        module SF = Stage v₀

        fillF : PathP (λ j → El (Index (sym (join-assoc O v₀) j)))
                      (snd u₀s)
                      (subst (λ v → El (Index v)) (sym (join-assoc O v₀)) (snd u₀s))
        fillF = transport-filler (λ j → El (Index (sym (join-assoc O v₀) j))) (snd u₀s)

        tailF : PathP (λ i → El (Index (cong gg (cong (Data w) a) i)))
                      (subst (λ v → El (Index v)) (sym (join-assoc O v₀)) (snd u₀s))
                      (snd u₁s)
        tailF = fill-tail {F = λ v → El (Index v)}
                          (sym (join-assoc O v₀)) (cong gg (cong (Data w) a)) b₂

        νGG : Path T̂ (pairGG (fst u₀s)
                        (subst (λ v → El (Index v)) (sym (join-assoc O v₀)) (snd u₀s)))
                     (pairGG (fst u₁s) (snd u₁s))
        νGG i = pairGG (a i) (tailF i)

        shF : GH.T³ {𝒰 = 𝒰} SF.I' SF.Jf SF.Mf SF.Fz → T̂
        shF t = fst u₀s , fst t , fst (snd t) , snd (snd t)

      μ : Path T̂ (readP u₀) (read1 u₁)
      μ = cong shF (SF.M (SF.canonβ (symP fillF))) ∙ νGG

      eval : Path (Path X (Data (join O ((λ v → join O ((join O) <$> v)) <$> w)) u₀)
                          (Data (join O ((λ v → join O (join O v)) <$> w)) u₁))
                  (λ i → Data (join O ((λ v → sym (join-assoc O v) i) <$> w)) (δ i))
                  (cong G̃ μ)
      eval =
          trace-eval-2cell (λ v → isSetEl (Index v)) (λ v → Data v) σV b b₂
        ∙ trace-eval-fill {F = λ v → El (Index v)} (λ v → isSetEl (Index v)) (λ v → Data v)
                          (sym (join-assoc O v₀)) (cong gg (cong (Data w) a)) b₂
        ∙ cong (_∙ (λ i → Data (cong gg (cong (Data w) a) i) (tailF i)))
               (cong sym (SF.evalBareᶜ (symP fillF)))
        ∙ sym (congFunct G̃ (cong shF (SF.M (SF.canonβ (symP fillF)))) νGG)

    -- §2c  Side assemblies: each route evaluation splits along its legs
    -- (canonical fillers and fill-tails), each leg lands in cong-G̃ form,
    -- and congFunct merges the side into the G̃-image of one T̂-path.
    -- Stage shuffles into the master set.
    private
      module S2 = Stage ((join O) <$> w)
      module S3 = Stage (join O w)
      module S4 = Stage ((λ u → join O <$> u) <$> w)

    sh₂ : GH.T³ {𝒰 = 𝒰} S2.I' S2.Jf S2.Mf S2.Fz → T̂
    sh₂ t =
      let bc = equivFun (⟦⅀⟧ (B' (fst t)) (C' (fst t))) (fst (snd t))
      in fst t , fst bc , snd bc , snd (snd t)

    probe-sh₂ : S2.F̂z ≡ G̃ ∘ sh₂
    probe-sh₂ = refl

    sh₃ : GH.T³ {𝒰 = 𝒰} S3.I' S3.Jf S3.Mf S3.Fz → T̂
    sh₃ t =
      let ab = equivFun (⟦⅀⟧ A' B') (fst t)
      in fst ab , snd ab , fst (snd t) , snd (snd t)

    probe-sh₃ : S3.F̂z ≡ G̃ ∘ sh₃
    probe-sh₃ = refl

    sh₄ : GH.T³ {𝒰 = 𝒰} S4.I' S4.Jf S4.Mf S4.Fz → T̂
    sh₄ t =
      let cd = equivFun (⟦⅀⟧ (C' (fst t) (fst (snd t))) (D' (fst t) (fst (snd t))))
                        (snd (snd t))
      in fst t , fst (snd t) , fst cd , snd cd

    probe-sh₄ : S4.F̂z ≡ G̃ ∘ sh₄
    probe-sh₄ = refl

    module SideL
      {x₀ : El (Index (join O (join O (join O w))))}
      {x₁ : El (Index (join O ((join O) <$> ((join O) <$> w))))}
      (γL : PathP (λ i → El (Index ((cong (join O) (join-assoc O w)
                                     ∙ join-assoc O ((join O) <$> w)) i))) x₀ x₁)
      where

      private
        fillerL1 : PathP (λ j → El (Index (join O (join-assoc O w j)))) x₀
                         (subst (λ v → El (Index v)) (cong (join O) (join-assoc O w)) x₀)
        fillerL1 = transport-filler (λ j → El (Index (join O (join-assoc O w j)))) x₀

        tailL : PathP (λ i → El (Index (join-assoc O ((join O) <$> w) i)))
                      (subst (λ v → El (Index v)) (cong (join O) (join-assoc O w)) x₀)
                      x₁
        tailL = fill-tail {F = λ v → El (Index v)}
                          (cong (join O) (join-assoc O w))
                          (join-assoc O ((join O) <$> w)) γL

        module TL = Through fillerL1

      μL : Path T̂ (read0 x₀) (read1 x₁)
      μL = TL.μ ∙ sym (cong sh₂ (S2.M (S2.canonβ tailL)))

      evalL : Path (Path X (Data (join O (join O (join O w))) x₀)
                           (Data (join O ((join O) <$> ((join O) <$> w))) x₁))
                   (λ i → Data ((cong (join O) (join-assoc O w)
                                 ∙ join-assoc O ((join O) <$> w)) i) (γL i))
                   (cong G̃ μL)
      evalL =
          trace-eval-fill {F = λ v → El (Index v)} (λ v → isSetEl (Index v))
                          (λ v → Data v)
                          (cong (join O) (join-assoc O w))
                          (join-assoc O ((join O) <$> w)) γL
        ∙ cong₂ _∙_ TL.eval (S2.evalBareᶜ tailL)
        ∙ sym (congFunct G̃ TL.μ (sym (cong sh₂ (S2.M (S2.canonβ tailL)))))

    module SideR
      {x₀ : El (Index (join O (join O (join O w))))}
      {x₁ : El (Index (join O ((join O) <$> ((join O) <$> w))))}
      (γR : PathP (λ i → El (Index ((join-assoc O (join O w)
                                     ∙ join-assoc O ((λ u → join O <$> u) <$> w)
                                     ∙ cong (λ φ → join O (φ <$> w))
                                            (funExt (λ v → sym (join-assoc O v)))) i)))
                  x₀ x₁)
      where

      private
        R2R3 = join-assoc O ((λ u → join O <$> u) <$> w)
             ∙ cong (λ φ → join O (φ <$> w)) (funExt (λ v → sym (join-assoc O v)))

        fillerR1 : PathP (λ j → El (Index (join-assoc O (join O w) j))) x₀
                         (subst (λ v → El (Index v)) (join-assoc O (join O w)) x₀)
        fillerR1 = transport-filler (λ j → El (Index (join-assoc O (join O w) j))) x₀

        tail1 : PathP (λ i → El (Index (R2R3 i)))
                      (subst (λ v → El (Index v)) (join-assoc O (join O w)) x₀)
                      x₁
        tail1 = fill-tail {F = λ v → El (Index v)}
                          (join-assoc O (join O w)) R2R3 γR

        fillerR2 : PathP (λ j → El (Index (join-assoc O ((λ u → join O <$> u) <$> w) j)))
                         (subst (λ v → El (Index v)) (join-assoc O (join O w)) x₀)
                         (subst (λ v → El (Index v))
                                (join-assoc O ((λ u → join O <$> u) <$> w))
                                (subst (λ v → El (Index v)) (join-assoc O (join O w)) x₀))
        fillerR2 = transport-filler
                     (λ j → El (Index (join-assoc O ((λ u → join O <$> u) <$> w) j)))
                     (subst (λ v → El (Index v)) (join-assoc O (join O w)) x₀)

        tail2 : PathP (λ i → El (Index (cong (λ φ → join O (φ <$> w))
                                             (funExt (λ v → sym (join-assoc O v))) i)))
                      (subst (λ v → El (Index v))
                             (join-assoc O ((λ u → join O <$> u) <$> w))
                             (subst (λ v → El (Index v)) (join-assoc O (join O w)) x₀))
                      x₁
        tail2 = fill-tail {F = λ v → El (Index v)}
                          (join-assoc O ((λ u → join O <$> u) <$> w))
                          (cong (λ φ → join O (φ <$> w))
                                (funExt (λ v → sym (join-assoc O v))))
                          tail1

        module FB = Fib tail2

      μR : Path T̂ (read0 x₀) (read1 x₁)
      μR = sym (cong sh₃ (S3.M (S3.canonβ fillerR1)))
         ∙ (sym (cong sh₄ (S4.M (S4.canonβ fillerR2))) ∙ FB.μ)

      evalR : Path (Path X (Data (join O (join O (join O w))) x₀)
                           (Data (join O ((join O) <$> ((join O) <$> w))) x₁))
                   (λ i → Data ((join-assoc O (join O w)
                                 ∙ join-assoc O ((λ u → join O <$> u) <$> w)
                                 ∙ cong (λ φ → join O (φ <$> w))
                                        (funExt (λ v → sym (join-assoc O v)))) i) (γR i))
                   (cong G̃ μR)
      evalR =
          trace-eval-fill {F = λ v → El (Index v)} (λ v → isSetEl (Index v))
                          (λ v → Data v)
                          (join-assoc O (join O w)) R2R3 γR
        ∙ cong₂ _∙_ (S3.evalBareᶜ fillerR1)
            ( trace-eval-fill {F = λ v → El (Index v)} (λ v → isSetEl (Index v))
                              (λ v → Data v)
                              (join-assoc O ((λ u → join O <$> u) <$> w))
                              (cong (λ φ → join O (φ <$> w))
                                    (funExt (λ v → sym (join-assoc O v))))
                              tail1
            ∙ cong₂ _∙_ (S4.evalBareᶜ fillerR2) FB.eval
            ∙ sym (congFunct G̃ (sym (cong sh₄ (S4.M (S4.canonβ fillerR2)))) FB.μ) )
        ∙ sym (congFunct G̃ (sym (cong sh₃ (S3.M (S3.canonβ fillerR1))))
                           (sym (cong sh₄ (S4.M (S4.canonβ fillerR2))) ∙ FB.μ))

    -- §2d  The pointwise pentagon: both sides are G̃-images of parallel
    -- paths in the SET T̂, hence equal.
    ptw-proof :
      (x₀ : El (Index (join O (join O (join O w)))))
      (x₁ : El (Index (join O ((join O) <$> ((join O) <$> w)))))
      (γL : PathP (λ i → El (Index ((cong (join O) (join-assoc O w)
                                     ∙ join-assoc O ((join O) <$> w)) i))) x₀ x₁)
      (γR : PathP (λ i → El (Index ((join-assoc O (join O w)
                                     ∙ join-assoc O ((λ u → join O <$> u) <$> w)
                                     ∙ cong (λ φ → join O (φ <$> w))
                                            (funExt (λ v → sym (join-assoc O v)))) i)))
                  x₀ x₁)
      → Path (Path X (Data (join O (join O (join O w))) x₀)
                     (Data (join O ((join O) <$> ((join O) <$> w))) x₁))
             (λ i → Data ((cong (join O) (join-assoc O w)
                           ∙ join-assoc O ((join O) <$> w)) i) (γL i))
             (λ i → Data ((join-assoc O (join O w)
                           ∙ join-assoc O ((λ u → join O <$> u) <$> w)
                           ∙ cong (λ φ → join O (φ <$> w))
                                  (funExt (λ v → sym (join-assoc O v)))) i) (γR i))
    ptw-proof x₀ x₁ γL γR =
        SideL.evalL γL
      ∙ cong (cong G̃) (isSetT̂ (read0 x₀) (read1 x₁) (SideL.μL γL) (SideR.μR γR))
      ∙ sym (SideR.evalR γR)
