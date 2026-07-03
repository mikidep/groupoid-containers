{-# OPTIONS --cubical #-}
-- ============================================================================
-- HoTTOperads.Monad.TwoCellCoherence
--
-- 2-cell coherence for the monad `OpM O`: the unit triangle and the
-- associativity pentagon.
--
-- Every monad-law path is a triple `Inj e ▷ idl/idr/assoc ▷ data`, so a
-- 2-cell between two such paths splits into a square of `Index` paths in
-- `Code`, an `Op` square over the h-set family `K` (propositional), and a
-- `Data` square carrying the decorations over the `Index` square.
--
-- The unit triangle needs no hypotheses beyond the operad: at the unit,
-- both unit laws run along equivalences between propositions, with a
-- constant decoration.  The pentagon assumes `isSetEl` (decoding is a
-- family of sets); the carrier is not truncated.  Its `Index` square is
-- the Mac Lane pentagon for the universe associator `⅀Assoc≃`, closed by
-- `Universe.PentagonDepProof.dep-pentagon`; its `Data` square reduces to
-- the pointwise pentagon `Monad.PointwisePentagon.ptw-proof`.
--
-- Formalises from the paper:
--   Section 8 (Monad over an Operad), Theorem 8.2 — the coherence 2-cells
--   of the monad `OpM O`.
-- ============================================================================
module HoTTOperads.Monad.TwoCellCoherence where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_ ; homotopyNatural)
open import Cubical.Foundations.HLevels using (isSet→SquareP)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.GroupoidLaws using (congFunct ; symDistr ; rUnit ; lUnit ; lCancel) renaming (assoc to ∙assoc)
open import Cubical.Foundations.Transport using (substComposite ; transportComposite ; subst⁻Subst ; substSubst⁻)
open import Cubical.Data.Sigma
open import Cubical.Data.Sigma.Properties using
  (Σ-cong-equiv-snd ; Σ-cong-equiv-fst ; Σ-cong-equiv ; Σ-assoc-≃)
open import Cubical.Data.Unit using (tt)

open import HoTTOperads.Universe.Base
open import HoTTOperads.Universe.Derived using
  ( propEquivEq ; isPropEl𝜏 ; isPropEl-⅀𝜏𝜏
  ; InjSec ; InjInv ; InjRefl ; ⟦⅀⟧-natural-snd )
import HoTTOperads.Universe.SigmaBridge as SB
open import HoTTOperads.Operad.Base
open import HoTTOperads.Monad.Base
open import HoTTOperads.Monad.Composition using (return ; join)
open import HoTTOperads.Monad.Functor using (_<$>_)
open import HoTTOperads.Monad.Laws using
  ( join-return₁ ; join-return₂ ; join-assoc ; join-assoc≡sym-aux )
open import HoTTOperads.Monad.Laws using (module JoinAssocAux)
open import HoTTOperads.UA using (ua→→ ; ua→→inv)
open import HoTTOperads.Universe.IRDerived using (⅀IdlD ; ⅀AssocD)
open import HoTTOperads.Universe.Assoc using
  ( adj-coh ; Assoc-cont ; Assoc-cont-at-pair ; step-Assoc-on-pair
  ; ⅀-subst-path ; transp-⅀-subst-path ; transp-⅀AssocD-pair ; transp-⅀IdlD )
import HoTTOperads.Universe.Pentagon as Pent
open import HoTTOperads.Universe.PentagonDep using
  ( postcomp-subst-PathP ; gen-path-ua ; gen-data-path
  ; Code²→Type ; Code²→Equiv ; DepPentagon )
open import HoTTOperads.Universe.Homog using (hg₀ ; ghomog-natural)
open import HoTTOperads.Universe.PentagonDepProof using (dep-pentagon)
open import HoTTOperads.PathTrace using
  (◁-post ; funPathP-ext ; fun-line-transport-eval)
open import HoTTOperads.Monad.PointwisePentagon using (ptw-proof)

private
  variable
    ℓc ℓe ℓk ℓx : Level

module _ {𝒰 : Universe ℓc ℓe} {K : Universe.Code 𝒰 → Type ℓk}
         (O : Operad 𝒰 K) where
  open Universe 𝒰
  open Operad O

  opaque
    unfolding join-return₁ join-return₂

    -- ------------------------------------------------------------------------
    -- Unit triangle: the two unit laws agree at the unit.  At `return O y`
    -- both are paths `join O (return O (return O y)) ≡ return O y`
    -- (`return O <$> return O y` and `return O (return O y)` are
    -- definitionally equal), each of the form `Inj e ▷ idl/idr ▷ data`
    -- where `e` is an equivalence between the propositions
    -- `El (⅀ 𝜏 (λ _ → 𝜏))` and `El 𝜏`.  The `Index` square is therefore
    -- `propEquivEq`, the `Op` square is `isSet→SquareP`, and the
    -- decoration is the constant `λ _ → y` once the `subst` along
    -- `⟦⅀Idl/r⟧` is cancelled (`dpEq₁`/`dpEq₂`, by `J`).
    -- ------------------------------------------------------------------------
    unit-triangle : {X : Type ℓx} (y : X)
                  → join-return₁ O (return O y) ≡ join-return₂ O (return O y)
    unit-triangle {X = X} y = jr₁≡c₁ ∙ middle ∙ sym jr₂≡c₂
      where
        c₁ : join O (return O (return O y)) ≡ return O y
        c₁ i = Inj (⅀Idl≃ 𝜏) i ▷ idl 𝜏 id i ▷ (λ _ → y)

        c₂ : join O (return O (return O y)) ≡ return O y
        c₂ i = Inj (⅀Idr≃ 𝜏) i ▷ idr 𝜏 id i ▷ (λ _ → y)

        dpEq₁ : PathP (λ _ → PathP (λ i → El (Inj (⅀Idl≃ 𝜏) i) → X)
                                   (λ _ → y) (λ _ → y))
                      (subst (λ p → PathP (λ i → p i → X) (λ _ → y) (λ _ → y))
                             (⟦⅀Idl⟧ 𝜏) (λ i _ → y))
                      (λ i _ → y)
        dpEq₁ = J (λ (b : El (⅀ 𝜏 (λ _ → 𝜏)) ≡ El 𝜏)
                     (q : ua (⅀Idl≃ 𝜏) ≡ b)
                   → subst (λ p → PathP (λ i → p i → X)
                                        (λ _ → y) (λ _ → y))
                           q (λ i _ → y)
                   ≡ (λ i (_ : b i) → y))
                  (substRefl {B = λ p → PathP (λ i → p i → X)
                                              (λ _ → y) (λ _ → y)}
                             {x = ua (⅀Idl≃ 𝜏)}
                             (λ i _ → y))
                  (⟦⅀Idl⟧ 𝜏)

        dpEq₂ : PathP (λ _ → PathP (λ i → El (Inj (⅀Idr≃ 𝜏) i) → X)
                                   (λ _ → y) (λ _ → y))
                      (subst (λ p → PathP (λ i → p i → X) (λ _ → y) (λ _ → y))
                             (⟦⅀Idr⟧ 𝜏) (λ i _ → y))
                      (λ i _ → y)
        dpEq₂ = J (λ (b : El (⅀ 𝜏 (λ _ → 𝜏)) ≡ El 𝜏)
                     (q : ua (⅀Idr≃ 𝜏) ≡ b)
                   → subst (λ p → PathP (λ i → p i → X)
                                        (λ _ → y) (λ _ → y))
                           q (λ i _ → y)
                   ≡ (λ i (_ : b i) → y))
                  (substRefl {B = λ p → PathP (λ i → p i → X)
                                              (λ _ → y) (λ _ → y)}
                             {x = ua (⅀Idr≃ 𝜏)}
                             (λ i _ → y))
                  (⟦⅀Idr⟧ 𝜏)

        jr₁≡c₁ : join-return₁ O (return O y) ≡ c₁
        jr₁≡c₁ j i = Inj (⅀Idl≃ 𝜏) i ▷ idl 𝜏 id i ▷ dpEq₁ j i

        jr₂≡c₂ : join-return₂ O (return O y) ≡ c₂
        jr₂≡c₂ j i = Inj (⅀Idr≃ 𝜏) i ▷ idr 𝜏 id i ▷ dpEq₂ j i

        idxSq : Inj (⅀Idl≃ 𝜏) ≡ Inj (⅀Idr≃ 𝜏)
        idxSq = cong Inj (propEquivEq (isPropEl-⅀𝜏𝜏 𝒰) (isPropEl𝜏 𝒰)
                                      (⅀Idl≃ 𝜏) (⅀Idr≃ 𝜏))

        opSq : SquareP (λ j i → K (idxSq j i))
                       (idl 𝜏 id) (idr 𝜏 id) refl refl
        opSq = isSet→SquareP (λ j i → isSetK (idxSq j i))
                             (idl 𝜏 id) (idr 𝜏 id) refl refl

        middle : c₁ ≡ c₂
        middle j i = idxSq j i ▷ opSq j i ▷ (λ (_ : El (idxSq j i)) → y)

  -- --------------------------------------------------------------------------
  -- The two reassociation routes from `join O (join O (join O w))` to
  -- `join O ((join O) <$> ((join O) <$> w))`.  `_<$>_` preserves `Index`
  -- and `g <$> join O z ≡ join O ((g <$>_) <$> z)` holds by refl, so the
  -- pentagon's naturality edges are degenerate: `route-L` is two
  -- `join-assoc` edges, and `route-R` is two `join-assoc` edges followed
  -- by the left-whisker
  -- `cong (λ φ → join O (φ <$> w)) (funExt (sym ∘ join-assoc))`.
  -- The pentagon (§P below) is `route-L w ≡ route-R w`.
  -- --------------------------------------------------------------------------
  route-L : {X : Type ℓx} (w : OpM O (OpM O (OpM O (OpM O X))))
          → join O (join O (join O w))
          ≡ join O ((join O) <$> ((join O) <$> w))
  route-L w = cong (join O) (join-assoc O w)
            ∙ join-assoc O ((join O) <$> w)

  route-R : {X : Type ℓx} (w : OpM O (OpM O (OpM O (OpM O X))))
          → join O (join O (join O w))
          ≡ join O ((join O) <$> ((join O) <$> w))
  route-R w =
      join-assoc O (join O w)
    ∙ join-assoc O ((λ u → join O <$> u) <$> w)
    ∙ cong (λ φ → join O (φ <$> w)) (funExt (λ v → sym (join-assoc O v)))

  -- ==========================================================================
  -- Index component of a single `join-assoc` edge: under `unfolding
  -- join-assoc` it is the reversed associator edge `sym (Inj (⅀Assoc≃ …))`.
  -- ==========================================================================
  opaque
    unfolding join-assoc

    idx-join-assoc :
      {X : Type ℓx} (z : OpM O (OpM O (OpM O X)))
      → cong Index (join-assoc O z)
      ≡ sym (Inj (⅀Assoc≃ (Index z)
                          (λ a → Index (Data z a))
                          (λ a b → Index (Data (Data z a) b))))
    idx-join-assoc (I ▷ k ▷ D) = refl

  -- ==========================================================================
  -- Data component of a single `join-assoc` edge.  `Index` lands in the
  -- constant `Code`, so `idx-join-assoc` is a plain `_≡_`, but `Data` is a
  -- `PathP` whose type does not reduce through the opaque `join-assoc`;
  -- the statement is heterogeneous, over `join-assoc≡sym-aux`.  Its right
  -- endpoint `cong Data (sym (JoinAssocAux.aux …))` is
  -- `symP (JoinAssocAux.data-path …)` by record-η.
  -- ==========================================================================
  data-join-assoc :
    {X : Type ℓx} (I : Code) (k : K I) (D : El I → OpM O (OpM O X))
    → PathP (λ t → PathP (λ i → El (Index (join-assoc≡sym-aux O I k D t i)) → X)
                          (Data (join O (join O (I ▷ k ▷ D))))
                          (Data (join O ((join O) <$> (I ▷ k ▷ D)))))
            (cong Data (join-assoc O (I ▷ k ▷ D)))
            (symP (JoinAssocAux.data-path O I k D))
  data-join-assoc I k D = cong (cong Data) (join-assoc≡sym-aux O I k D)

  -- ==========================================================================
  -- The through-`join` edge `cong (join O) (join-assoc O w)`.  Since
  -- `join O (P ▷ p ▷ Q) = ⅀ P (λ s → Index (Q s)) ▷ … ▷ …`, its `Index`
  -- is a `⅀`-path whose base moves by `Inj (⅀Assoc≃ …)` and whose family
  -- moves by `Index ∘ data-path` (`idxL1≡`, through `join-assoc≡sym-aux`);
  -- `idxL1≡'` rewrites the family into `subst` form along `⟦⅀Assoc⟧` via
  -- `postcomp-subst-PathP` at `f = Index`.
  -- ==========================================================================
  idxL1≡ :
    {X : Type ℓx} (w : OpM O (OpM O (OpM O (OpM O X))))
    → cong Index (cong (join O) (join-assoc O w))
    ≡ sym (λ i → ⅀ (Inj (⅀Assoc≃ (Index w)
                                  (λ a → Index (Data w a))
                                  (λ a b → Index (Data (Data w a) b))) i)
                   (λ s → Index (JoinAssocAux.data-path O (Index w) (Op w)
                                                          (Data w) i s)))
  idxL1≡ (I ▷ k ▷ D) =
    cong (λ p → cong Index (cong (join O) p)) (join-assoc≡sym-aux O I k D)

  idxL1-data :
    {X : Type ℓx} (w : OpM O (OpM O (OpM O (OpM O X))))
    → (λ i s → Index (JoinAssocAux.data-path O (Index w) (Op w) (Data w) i s))
    ≡ subst (λ p → PathP (λ i → p i → Code)
                    (λ s → Index (JoinAssocAux.data-NR O (Index w) (Op w)
                                                       (Data w) s))
                    (λ s → Index (JoinAssocAux.data-NL O (Index w) (Op w)
                                                       (Data w) s)))
            (⟦⅀Assoc⟧ (Index w) (λ a → Index (Data w a))
                       (λ a b → Index (Data (Data w a) b)))
            (λ i s → Index (JoinAssocAux.path-ua O (Index w) (Op w)
                                                  (Data w) i s))
  idxL1-data w =
    postcomp-subst-PathP Index
      (⟦⅀Assoc⟧ (Index w) (λ a → Index (Data w a))
                 (λ a b → Index (Data (Data w a) b)))
      (JoinAssocAux.path-ua O (Index w) (Op w) (Data w))

  idxL1≡' :
    {X : Type ℓx} (w : OpM O (OpM O (OpM O (OpM O X))))
    → cong Index (cong (join O) (join-assoc O w))
    ≡ sym (λ i → ⅀ (Inj (⅀Assoc≃ (Index w) (λ a → Index (Data w a))
                                  (λ a b → Index (Data (Data w a) b))) i)
                   (subst (λ p → PathP (λ i' → p i' → Code)
                            (λ s → Index (JoinAssocAux.data-NR O (Index w)
                                                              (Op w) (Data w) s))
                            (λ s → Index (JoinAssocAux.data-NL O (Index w)
                                                              (Op w) (Data w) s)))
                          (⟦⅀Assoc⟧ (Index w) (λ a → Index (Data w a))
                                     (λ a b → Index (Data (Data w a) b)))
                          (λ i' s → Index (JoinAssocAux.path-ua O (Index w)
                                                               (Op w) (Data w) i' s))
                          i))
  idxL1≡' w =
      idxL1≡ w
    ∙ cong (λ fam → sym (λ i → ⅀ (Inj (⅀Assoc≃ (Index w) (λ a → Index (Data w a))
                                                (λ a b → Index (Data (Data w a) b))) i)
                                 (fam i)))
           (idxL1-data w)

  -- The `Data` side of the through-`join` edge: the `join-assoc≡sym-aux`
  -- rewrite again (it does not distinguish `Index` from `Data`), under the
  -- extra `cong (join O)`; heterogeneous for the same reason as
  -- `data-join-assoc`.
  data-L1≡ :
    {X : Type ℓx} (I : Code) (k : K I) (D : El I → OpM O (OpM O (OpM O X)))
    → PathP (λ t → PathP (λ i → El (Index (cong (join O)
                                              (join-assoc≡sym-aux O I k D t) i)) → X)
                          (Data (join O (join O (join O (I ▷ k ▷ D)))))
                          (Data (join O (join O ((join O) <$> (I ▷ k ▷ D))))))
            (cong Data (cong (join O) (join-assoc O (I ▷ k ▷ D))))
            (cong Data (cong (join O) (sym (JoinAssocAux.aux O I k D))))
  data-L1≡ I k D = cong (λ p → cong Data (cong (join O) p)) (join-assoc≡sym-aux O I k D)

  -- ==========================================================================
  -- The left-whisker edge (`route-R`'s last).  `_<$>_` preserves `Index`,
  -- so `Index (join O (φ <$> w)) = ⅀ (Index w) (λ a → Index (φ (Data w a)))`
  -- and the whisker moves only the fibres: its `Index` is
  -- `cong (⅀ (Index w))` of the per-fibre `Inj (⅀Assoc≃ …)`.
  -- ==========================================================================
  idx-cong-fmap-join-assoc :
    {X : Type ℓx} (w : OpM O (OpM O (OpM O (OpM O X))))
    → cong Index (cong (λ φ → join O (φ <$> w))
                       (funExt (λ v → sym (join-assoc O v))))
    ≡ cong (⅀ (Index w))
           (funExt (λ a → Inj (⅀Assoc≃ (Index (Data w a))
                                       (λ b → Index (Data (Data w a) b))
                                       (λ b c → Index (Data (Data (Data w a) b) c)))))
  idx-cong-fmap-join-assoc (I ▷ k ▷ D) =
    cong (λ g → cong (⅀ I) (funExt g))
         (funExt (λ a → cong sym (idx-join-assoc (D a))))

  -- The `Data` side of the whisker.  `join`'s `Data` threads through the
  -- per-fibre reindexing, so this side is not a `cong (⅀ …) (funExt …)`;
  -- the statement exposes it through the opaque `join-assoc` pointwise
  -- via `join-assoc≡sym-aux`, as in `data-L1≡`.
  data-cong-fmap-join-assoc :
    {X : Type ℓx} (w : OpM O (OpM O (OpM O (OpM O X))))
    → PathP
        (λ t → PathP
          (λ i → El (Index (cong (λ φ → join O (φ <$> w))
                                  (funExt (λ v → cong sym
                                            (join-assoc≡sym-aux O (Index v) (Op v)
                                                                (Data v)) t)) i)) → X)
          (Data (join O ((λ v → join O ((join O) <$> v)) <$> w)))
          (Data (join O ((λ v → join O (join O v)) <$> w))))
        (cong Data (cong (λ φ → join O (φ <$> w))
                         (funExt (λ v → sym (join-assoc O v)))))
        (cong Data (cong (λ φ → join O (φ <$> w))
                         (funExt (λ v → sym (sym (JoinAssocAux.aux O (Index v)
                                                                   (Op v) (Data v)))))))
  data-cong-fmap-join-assoc w =
    cong (λ h → cong Data (cong (λ φ → join O (φ <$> w)) (funExt h)))
         (funExt (λ v → cong sym (join-assoc≡sym-aux O (Index v) (Op v) (Data v))))

  -- ==========================================================================
  -- §P  The associativity pentagon.
  --
  -- `pentagon = idxSq ▷ opSq ▷ dataSq`, componentwise as in
  -- `unit-triangle`.
  --
  -- `idxSq`: the two `cong Index (route-L/R w)` decompose through
  -- `congFunct`, `idx-join-assoc`, `idxL1≡'` and
  -- `idx-cong-fmap-join-assoc` into `Inj (⅀Assoc≃ …)` edges plus the
  -- through-`join` family; `◁-post` pushes `Index` through the `path-ua`
  -- whisker, `ghomog-natural` at `g := Index` identifies the resulting
  -- coherence with the canonical `hg₀`, and `dep-pentagon` closes the
  -- 2-cell.
  --
  -- `dataSq`: a `PathP` over `idxSq` in the family of function lines
  -- `λ p → PathP (λ i → El (p i) → X) _ _`.  With `isSetEl` the traces of
  -- such lines form propositions, so a line is determined by its
  -- evaluations along traces (`funPathP-ext`), and the `idxSq`-transport
  -- of a line evaluates as the line itself on the matching trace
  -- (`fun-line-transport-eval`).  What remains is the pointwise pentagon
  -- `ptw`, supplied by `Monad.PointwisePentagon.ptw-proof`.
  --
  -- Hypothesis: `isSetEl`.  The carrier `X` is an arbitrary type.
  -- ==========================================================================
  module _ {X : Type ℓx}
           (isSetEl : (Z : Code) → isSet (El Z))
           (w : OpM O (OpM O (OpM O (OpM O X)))) where

    idxSq : cong Index (route-L w) ≡ cong Index (route-R w)
    idxSq = L-rw ∙ middle ∙ sym R-rw
      where
        L-rw = congFunct Index (cong (join O) (join-assoc O w))
                               (join-assoc O ((join O) <$> w))
             ∙ cong₂ _∙_ (idxL1≡' w) (idx-join-assoc ((join O) <$> w))

        -- The universe-level families of w and the OpM data reading.
        A' = Index w
        B' = λ a → Index (Data w a)
        C' = λ a b → Index (Data (Data w a) b)
        D' = λ a b c → Index (Data (Data (Data w a) b) c)
        Fd = λ a b c → Data (Data (Data w a) b) c

        -- The through-`join` family is `gen-data-path` at the coherence
        -- `cong (Index ∘_) homog`: `◁-post` pushes `Index` through the
        -- `path-ua` whisker.
        fam-bridge :
          subst (λ p → PathP (λ i' → p i' → Code)
                              (λ s → Index (JoinAssocAux.data-NR O (Index w) (Op w) (Data w) s))
                              (λ s → Index (JoinAssocAux.data-NL O (Index w) (Op w) (Data w) s)))
                (⟦⅀Assoc⟧ A' B' C')
                (λ i' s → Index (JoinAssocAux.path-ua O (Index w) (Op w) (Data w) i' s))
          ≡ gen-data-path {𝒰 = 𝒰} A' B' C'
                          (λ s → Index (JoinAssocAux.data-NR O (Index w) (Op w) (Data w) s))
                          (λ s → Index (JoinAssocAux.data-NL O (Index w) (Op w) (Data w) s))
                          (cong (Index ∘_) (JoinAssocAux.homog O (Index w) (Op w) (Data w)))
        fam-bridge =
          cong (subst (λ p → PathP (λ i' → p i' → Code)
                              (λ s → Index (JoinAssocAux.data-NR O (Index w) (Op w) (Data w) s))
                              (λ s → Index (JoinAssocAux.data-NL O (Index w) (Op w) (Data w) s)))
                      (⟦⅀Assoc⟧ A' B' C'))
               (◁-post Index
                       (JoinAssocAux.homog O (Index w) (Op w) (Data w))
                       (λ i' el → JoinAssocAux.data-NL O (Index w) (Op w) (Data w)
                                    (ua-unglue (⅀Assoc≃ A' B' C') i' el)))

        -- That coherence is the canonical hg₀: `ghomog-natural` at
        -- `g := Index`, since `Laws.homog` is `ghomog` at the data reading.
        hg-stone :
          cong (Index ∘_) (JoinAssocAux.homog O (Index w) (Op w) (Data w))
          ≡ hg₀ {𝒰 = 𝒰} A' B' C' D'
        hg-stone = ghomog-natural {𝒰 = 𝒰} A' B' C' Fd Index

        middle =
            cong (λ fam → sym (λ i → ⅀ (Inj (⅀Assoc≃ A' B' C') i) (fam i))
                        ∙ sym (Inj (⅀Assoc≃ A'
                                     (λ a → ⅀ (B' a) (C' a))
                                     (λ a → ⅀Assoc-C' (B' a) (C' a) (D' a)))))
                 fam-bridge
          ∙ subst (λ h → DepPentagon {𝒰 = 𝒰} A' B' C' D' h)
                  (sym hg-stone)
                  (dep-pentagon {𝒰 = 𝒰} A' B' C' D' isSetEl)
        R-rw = congFunct Index (join-assoc O (join O w))
                               ( join-assoc O ((λ u → join O <$> u) <$> w)
                               ∙ cong (λ φ → join O (φ <$> w))
                                      (funExt (λ v → sym (join-assoc O v))) )
             ∙ cong₂ _∙_ (idx-join-assoc (join O w))
                 ( congFunct Index (join-assoc O ((λ u → join O <$> u) <$> w))
                                   (cong (λ φ → join O (φ <$> w))
                                         (funExt (λ v → sym (join-assoc O v))))
                 ∙ cong₂ _∙_ (idx-join-assoc ((λ u → join O <$> u) <$> w))
                             (idx-cong-fmap-join-assoc w) )

    opSq : SquareP (λ j i → K (idxSq j i))
                   (cong Op (route-L w)) (cong Op (route-R w))
                   refl refl
    opSq = isSet→SquareP (λ j i → isSetK (idxSq j i))
                         (cong Op (route-L w)) (cong Op (route-R w))
                         refl refl

    -- The pointwise pentagon: the two routes' `Data` components, evaluated
    -- along same-endpoint traces of their `Index` components, agree as
    -- paths in `X`.  Stated without reference to `idxSq`.
    ptw :
      (x₀ : El (Index (join O (join O (join O w)))))
      (x₁ : El (Index (join O ((join O) <$> ((join O) <$> w)))))
      (γL : PathP (λ i → El (Index (route-L w i))) x₀ x₁)
      (γR : PathP (λ i → El (Index (route-R w i))) x₀ x₁)
      → Path (Path X (Data (join O (join O (join O w))) x₀)
                     (Data (join O ((join O) <$> ((join O) <$> w))) x₁))
             (λ i → Data (route-L w i) (γL i))
             (λ i → Data (route-R w i) (γR i))
    ptw = ptw-proof O isSetEl w

    -- `dataSq` is `toPathP` of an equation between two function lines over
    -- `cong Index (route-R w)`: by `funPathP-ext` it suffices that they
    -- evaluate equally along traces, `fun-line-transport-eval` replaces
    -- the transported evaluation by the original on the matching trace,
    -- and the remaining equation is `ptw`.
    dataSq : SquareP (λ j i → El (idxSq j i) → X)
                     (cong Data (route-L w)) (cong Data (route-R w))
                     refl refl
    dataSq = toPathP
      (funPathP-ext
        (transport (λ j → PathP (λ i → El (idxSq j i) → X)
                                (Data (join O (join O (join O w))))
                                (Data (join O ((join O) <$> ((join O) <$> w)))))
                   (cong Data (route-L w)))
        (cong Data (route-R w))
        (λ {x₀} {x₁} γ →
            fun-line-transport-eval isSetEl idxSq
              (cong Data (route-L w))
              (transport (λ j → PathP (λ i → El (idxSq (~ j) i)) x₀ x₁) γ)
              γ
          ∙ ptw x₀ x₁
                (transport (λ j → PathP (λ i → El (idxSq (~ j) i)) x₀ x₁) γ)
                γ))

    pentagon : route-L w ≡ route-R w
    pentagon j i = idxSq j i ▷ opSq j i ▷ dataSq j i
