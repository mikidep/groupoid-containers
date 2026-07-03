{-# OPTIONS --cubical --no-import-sorts #-}

-- The carrier-generic dependent Mac Lane pentagon for `⅀Assoc≃`, decoupled
-- from `OpM`/`join`/`Operad`.  Parametric in a codomain `T` and the minimal
-- carrier interface `(dNR , dNL , homog)`; the `JoinAssocAux.path-ua` /
-- `data-path` shape is rebuilt here from the universe's `⟦⅀Assoc⟧` /
-- `ua-unglue`.  Instantiated (at the `OpM` bridge) with `T = Code` it gives
-- the index square, with `T = X` the data square.
--
-- Tier U of the pentagon decomposition (see
-- `docs/pentagon-coherence-roadmap.md`): this module mentions only the
-- universe `𝒰` and `Pent.*`; it never mentions `OpM`/`join`/`Operad`.
module HoTTOperads.Universe.PentagonDep where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.Univalence

open import Cubical.Foundations.GroupoidLaws using (congFunct)
open import Cubical.Foundations.Transport using (transportComposite)
open import Cubical.Data.Sigma using (ΣPathP)
open import Cubical.Data.Sigma.Properties using (Σ-cong-equiv ; Σ-cong-equiv-snd)

open import HoTTOperads.Universe.Base
import HoTTOperads.Universe.Derived as Der
import HoTTOperads.Universe.Pentagon as Pent

private
  variable
    ℓc ℓe ℓt : Level

-- ============================================================================
-- Generic combinator (pure cubical; no universe).  Post-composition by a
-- function commutes with `subst` over a type-path used as the *domain* inside
-- a `PathP` of functions: `f ∘ -` only touches the codomain, so it slides
-- past the `subst Φ (⟦⅀Assoc⟧ …)` that turns `path-ua` into `data-path`.
-- Proof by path induction; at `refl` both sides collapse by `substRefl`.
-- Used (Tier B) at `f = Index` to read `gen-data-path` at `T = Code`.
-- ============================================================================
postcomp-subst-PathP :
  {ℓy ℓz ℓt : Level} {Y : Type ℓy} {Z : Type ℓz}
  (f : Y → Z) {S T : Type ℓt} {g : S → Y} {h : T → Y}
  {p₀ p₁ : S ≡ T} (q : p₀ ≡ p₁)
  (r : PathP (λ i → p₀ i → Y) g h)
  → (λ i x → f (subst (λ p → PathP (λ i₁ → p i₁ → Y) g h) q r i x))
  ≡ subst (λ p → PathP (λ i₁ → p i₁ → Z) (λ s → f (g s)) (λ t → f (h t))) q
          (λ i x → f (r i x))
postcomp-subst-PathP {Y = Y} {Z = Z} f {S = S} {T = T} {g = g} {h = h}
                     {p₀ = p₀} q r =
  J (λ (p₁' : S ≡ T) (q' : p₀ ≡ p₁')
       → (λ i x → f (subst (λ p → PathP (λ i₁ → p i₁ → Y) g h) q' r i x))
       ≡ subst (λ p → PathP (λ i₁ → p i₁ → Z)
                             (λ s → f (g s)) (λ t → f (h t))) q'
               (λ i x → f (r i x)))
    ( (λ k i x → f (substRefl {B = λ p → PathP (λ i₁ → p i₁ → Y) g h}
                              {x = p₀} r k i x))
    ∙ sym (substRefl {B = λ p → PathP (λ i₁ → p i₁ → Z)
                                       (λ s → f (g s)) (λ t → f (h t))}
                     {x = p₀} (λ i x → f (r i x))) )
    q

module _ {𝒰 : Universe ℓc ℓe} where
  open Universe 𝒰

  -- ==========================================================================
  -- Generic descent from a `Code`-path 2-cell to a `Type`-path 2-cell.
  -- `Inj` is opaque on `Code`, so a pentagon between `Code`-paths admits no
  -- univalence/`equivEq` reasoning directly; but `InjSec` (Prop 6.2) makes
  -- every `Code`-path the `Inj` of `pathToEquiv ∘ cong El`, so a 2-cell of
  -- `Code`-paths is the `Inj∘pathToEquiv` image of the corresponding 2-cell
  -- of `Type`-paths.  Not a restatement: it relocates the obligation from
  -- the opaque `Code` groupoid to `Type`, where `ua`/`uaCompEquiv`/`equivEq`
  -- and the verified pointwise `Pent.⅀Assoc-pentagon` apply.
  -- ==========================================================================
  Code²→Type : {c₀ c₁ : Code} (pL pR : c₀ ≡ c₁)
             → cong El pL ≡ cong El pR → pL ≡ pR
  Code²→Type pL pR e =
      sym (Der.InjSec 𝒰 pL)
    ∙ cong (λ t → Inj (pathToEquiv t)) e
    ∙ Der.InjSec 𝒰 pR

  -- Sharper descent: straight to the *equivalence* groupoid.  `equivEq`
  -- then reduces `pathToEquiv (cong El pL) ≡ pathToEquiv (cong El pR)` to a
  -- `funExt` of the pointwise underlying-function 2-cell — exactly the form
  -- of the verified pointwise `Pent.⅀Assoc-pentagon`.
  Code²→Equiv : {c₀ c₁ : Code} (pL pR : c₀ ≡ c₁)
              → pathToEquiv (cong El pL) ≡ pathToEquiv (cong El pR)
              → pL ≡ pR
  Code²→Equiv pL pR e =
      sym (Der.InjSec 𝒰 pL) ∙ cong Inj e ∙ Der.InjSec 𝒰 pR

  module _ (A : Code) (B : El A → Code)
           (C : (a : El A) → El (B a) → Code) where

    -- Per-edge bridge: the transport carried by a bare `Inj (⅀Assoc≃ …)`
    -- edge is the associator's `equivFun`.  `⟦⅀Assoc⟧` rewrites `cong El ∘
    -- Inj` to `ua`, then `uaβ` computes the transport.  This turns the
    -- function-level pentagon (post-`Code²→Equiv`) into a composite of
    -- `equivFun/invEq (⅀Assoc≃ …)` — the form the verified pointwise
    -- `Pent.⅀Assoc-pentagon` is stated in.
    transport-Inj-⅀Assoc :
      transport (cong El (Inj (⅀Assoc≃ A B C)))
      ≡ equivFun (⅀Assoc≃ A B C)
    transport-Inj-⅀Assoc =
        cong transport (sym (⟦⅀Assoc⟧ A B C))
      ∙ funExt (uaβ (⅀Assoc≃ A B C))

    -- The `sym (Inj (⅀Assoc≃ …))` companion: a reversed bare edge carries
    -- the associator's `invEq`.
    transport-sym-Inj-⅀Assoc :
      transport (cong El (sym (Inj (⅀Assoc≃ A B C))))
      ≡ invEq (⅀Assoc≃ A B C)
    transport-sym-Inj-⅀Assoc =
        cong (λ p → transport (sym p)) (sym (⟦⅀Assoc⟧ A B C))
      ∙ funExt (~uaβ (⅀Assoc≃ A B C))

    -- ========================================================================
    -- U0  Carrier-generic `path-ua` / `data-path` (infrastructure).
    --
    -- Verbatim the `JoinAssocAux.path-ua` / `data-path` shape (Monad.Laws),
    -- but `OpM`-free and parametric in the codomain `T` and the carrier
    -- endpoints `(dNR , dNL)` coherent via `hg`.  No hard content: the
    -- pentagon's data is *defined* by these; the open theorem (U2) is the
    -- 2-cell of their `route-L`/`route-R` composites over the verified
    -- `Pent.⅀Assoc-pentagon`.
    -- ========================================================================
    gen-path-ua :
      {T : Type ℓt}
      (dNR : El (⅀ A (λ a → ⅀ (B a) (C a))) → T)
      (dNL : El (⅀ (⅀ A B) (⅀Assoc-C' A B C)) → T)
      (hg  : dNR ≡ dNL ∘ equivFun (⅀Assoc≃ A B C))
      → PathP (λ i → ua (⅀Assoc≃ A B C) i → T) dNR dNL
    gen-path-ua dNR dNL hg =
      hg ◁ (λ i el → dNL (ua-unglue (⅀Assoc≃ A B C) i el))

    gen-data-path :
      {T : Type ℓt}
      (dNR : El (⅀ A (λ a → ⅀ (B a) (C a))) → T)
      (dNL : El (⅀ (⅀ A B) (⅀Assoc-C' A B C)) → T)
      (hg  : dNR ≡ dNL ∘ equivFun (⅀Assoc≃ A B C))
      → PathP (λ i → El (Inj (⅀Assoc≃ A B C) i) → T) dNR dNL
    gen-data-path {T = T} dNR dNL hg =
      subst (λ p → PathP (λ i → p i → T) dNR dNL)
            (⟦⅀Assoc⟧ A B C)
            (gen-path-ua dNR dNL hg)

    -- ========================================================================
    -- U2  The carrier-generic Mac Lane pentagon for `⅀Assoc≃` over
    -- `(A , B , C , D)`, at the index (`Code`) level.
    --
    -- The OpM `idxSq` residual stated *abstractly*: every code is a
    -- `⅀`/`⅀Assoc-C'` of the four families `(A,B,C,D)` (the definitional
    -- reductions of `Index/Data` of `join`/`<$>`); no `OpM`/`join`
    -- mentioned.  The L1 (through-`join`) carrier is **not** arbitrary —
    -- the RHS is carrier-free, so an arbitrary `PathP` would make the
    -- 2-cell false (path space in `El → Code` is not a proposition).  It
    -- is the *canonical* `gen-data-path dNR₀ dNL₀ hg` for the minimal
    -- coherence `hg` (the locked `(dNR,dNL,homog)` interface); in OpM,
    -- `hg` is `cong Index ∘ JoinAssocAux.homog`.  An inhabitant
    -- (`DepPentagon hg`) is the genuine open theorem.
    -- ========================================================================
    module _ (D : (a : El A) (b : El (B a)) → El (C a b) → Code) where

      -- The pentagon geometry forces the L1 carrier's endpoints: the
      -- through-`join` edge's `⅀`-fibre must be the `⅀Assoc-C'` families
      -- that the L2/R1 associators reassociate (in OpM these are exactly
      -- `Index ∘ JoinAssocAux.data-NR / data-NL`, definitionally).
      dNR₀ : El (⅀ A (λ a → ⅀ (B a) (C a))) → Code
      dNR₀ = ⅀Assoc-C' A (λ a → ⅀ (B a) (C a))
                         (λ a → ⅀Assoc-C' (B a) (C a) (D a))

      dNL₀ : El (⅀ (⅀ A B) (⅀Assoc-C' A B C)) → Code
      dNL₀ = ⅀Assoc-C' (⅀ A B) (⅀Assoc-C' A B C)
               (λ ab → D (fst (equivFun (⟦⅀⟧ A B) ab))
                         (snd (equivFun (⟦⅀⟧ A B) ab)))

      -- The abstract 2-cell *as a proposition* (hole-free `Type`-valued,
      -- so this Tier-U module stays importable / EXIT=0).  Carrier =
      -- canonical `gen-data-path dNR₀ dNL₀ hg`.  An inhabitant is the
      -- carrier-generic Mac Lane pentagon for `⅀Assoc≃` over `(A,B,C,D)`;
      -- proving it is the genuine open theorem.
      DepPentagon :
        (hg : dNR₀ ≡ dNL₀ ∘ equivFun (⅀Assoc≃ A B C))
        → Type ℓc
      DepPentagon hg =
        let gdp = gen-data-path dNR₀ dNL₀ hg in
            sym (λ i → ⅀ (Inj (⅀Assoc≃ A B C) i) (gdp i))
          ∙ sym (Inj (⅀Assoc≃ A (λ a → ⅀ (B a) (C a))
                                (λ a → ⅀Assoc-C' (B a) (C a) (D a))))
        ≡   sym (Inj (⅀Assoc≃ (⅀ A B) (⅀Assoc-C' A B C)
                              (λ ab → D (fst (equivFun (⟦⅀⟧ A B) ab))
                                        (snd (equivFun (⟦⅀⟧ A B) ab)))))
          ∙ sym (Inj (⅀Assoc≃ A B (λ a b → ⅀ (C a b) (D a b))))
          ∙ cong (⅀ A) (funExt (λ a → Inj (⅀Assoc≃ (B a) (C a) (D a))))


  -- ==========================================================================
  -- §L  Lift bricks for the `DepPentagon` assembly.  Six clean equivalence-
  -- level reductions built on the verified universe coherences above and
  -- standard stdlib (`uaβ`, `~uaβ`, `pathToEquivRefl`, `invEquivIdEquiv`,
  -- `transportComposite`, `transport-filler`).  Together with the
  -- inner-module pieces they reduce a Mac Lane pentagon between `Code`-paths
  -- to a single pure-equivalence pentagon over `⅀Assoc≃`/`⟦⅀⟧`/`Σ-cong`.
  -- ==========================================================================

  -- A bare reversed associator edge is the inverse equivalence.
  bareEdge≃ :
    (P : Code) (Q : El P → Code) (R : (p : El P) → El (Q p) → Code)
    → pathToEquiv (cong El (sym (Inj (⅀Assoc≃ P Q R))))
    ≡ invEquiv (⅀Assoc≃ P Q R)
  bareEdge≃ P Q R = equivEq (transport-sym-Inj-⅀Assoc P Q R)

  -- A forward associator edge is the associator equivalence.
  assocEdge≃ :
    (P : Code) (Q : El P → Code) (R : (p : El P) → El (Q p) → Code)
    → pathToEquiv (cong El (Inj (⅀Assoc≃ P Q R)))
    ≡ ⅀Assoc≃ P Q R
  assocEdge≃ P Q R = equivEq (transport-Inj-⅀Assoc P Q R)

  -- `pathToEquiv ∘ cong El` is monoidal over path composition.
  pte∙ :
    {x y z : Code} (p : x ≡ y) (q : y ≡ z)
    → pathToEquiv (cong El (p ∙ q))
    ≡ compEquiv (pathToEquiv (cong El p)) (pathToEquiv (cong El q))
  pte∙ p q =
    equivEq ( cong transport (congFunct El p q)
            ∙ funExt (transportComposite (cong El p) (cong El q)) )

  -- `pathToEquiv ∘ cong El` sends `sym` to `invEquiv`.  Path induction; at
  -- `refl`, `pathToEquivRefl` + `invEquivIdEquiv` close it.
  pte-sym :
    {x y : Code} (p : x ≡ y)
    → pathToEquiv (cong El (sym p)) ≡ invEquiv (pathToEquiv (cong El p))
  pte-sym {x} =
    J (λ y q → pathToEquiv (cong El (sym q))
             ≡ invEquiv (pathToEquiv (cong El q)))
      ( pathToEquivRefl
      ∙ sym (cong invEquiv pathToEquivRefl ∙ invEquivIdEquiv (El x)) )

  -- Both-argument `⟦⅀⟧`-naturality.  Path induction on the base reduces it
  -- to the verified fibre-only `Der.⟦⅀⟧-natural-snd`; at the base case the
  -- `i ∧ k` connection closes via the *definitional* equality
  -- `transport-filler refl a k ≡ transportRefl a (~ k)`.
  ⟦⅀⟧-natural :
    {X Y : Code} (p : X ≡ Y)
    {Q₀ : El X → Code} {Q₁ : El Y → Code}
    (qp : PathP (λ i → El (p i) → Code) Q₀ Q₁)
    → pathToEquiv (cong El (λ i → ⅀ (p i) (qp i)))
    ≡ compEquiv (⟦⅀⟧ X Q₀)
        (compEquiv
          (Σ-cong-equiv (pathToEquiv (cong El p))
            (λ x → pathToEquiv (cong El
                     (λ i → qp i (transport-filler (cong El p) x i)))))
          (invEquiv (⟦⅀⟧ Y Q₁)))
  ⟦⅀⟧-natural {X} =
    J (λ Y p → {Q₀ : El X → Code} {Q₁ : El Y → Code}
               (qp : PathP (λ i → El (p i) → Code) Q₀ Q₁)
             → pathToEquiv (cong El (λ i → ⅀ (p i) (qp i)))
             ≡ compEquiv (⟦⅀⟧ X Q₀)
                 (compEquiv
                   (Σ-cong-equiv (pathToEquiv (cong El p))
                     (λ x → pathToEquiv (cong El
                              (λ i → qp i (transport-filler (cong El p) x i)))))
                   (invEquiv (⟦⅀⟧ Y Q₁))))
      nat-refl
    where
      nat-refl : {Q₀ Q₁ : El X → Code} (qp : Q₀ ≡ Q₁)
               → pathToEquiv (cong El (λ i → ⅀ X (qp i)))
               ≡ compEquiv (⟦⅀⟧ X Q₀)
                   (compEquiv
                     (Σ-cong-equiv (pathToEquiv (cong El (refl {x = X})))
                       (λ x → pathToEquiv (cong El
                                (λ i → qp i (transport-filler (cong El (refl {x = X})) x i)))))
                     (invEquiv (⟦⅀⟧ X Q₁)))
      nat-refl {Q₀} {Q₁} qp =
          Der.⟦⅀⟧-natural-snd 𝒰 X qp
        ∙ cong (λ m → compEquiv (⟦⅀⟧ X Q₀)
                        (compEquiv m (invEquiv (⟦⅀⟧ X Q₁))))
               middleEq
        where
          middleEq :
            Σ-cong-equiv-snd (λ a → pathToEquiv (cong El (funExt⁻ qp a)))
            ≡ Σ-cong-equiv (pathToEquiv (cong El (refl {x = X})))
                (λ x → pathToEquiv (cong El
                         (λ i → qp i (transport-filler (cong El (refl {x = X})) x i))))
          middleEq =
            equivEq (funExt (λ pr → ΣPathP
              ( sym (transportRefl (fst pr))
              , (λ k → transport
                         (cong El (λ i → qp i
                            (transport-filler (cong El (refl {x = X}))
                                              (fst pr) (i ∧ k))))
                         (snd pr)) )))

  -- The R3 fibrewise edge.  `⟦⅀⟧`-naturality in the second argument turns
  -- a fibrewise `Inj (⅀Assoc≃ …)` whisker into the fibrewise associator
  -- equivalence, conjugated by `⟦⅀⟧`.
  module _ (A : Code) (B : El A → Code)
           (C : (a : El A) → El (B a) → Code)
           (D : (a : El A) (b : El (B a)) → El (C a b) → Code) where

    qR3 : (λ a → ⅀ (B a) (λ b → ⅀ (C a b) (D a b)))
        ≡ (λ a → ⅀ (⅀ (B a) (C a)) (⅀Assoc-C' (B a) (C a) (D a)))
    qR3 = funExt (λ a → Inj (⅀Assoc≃ (B a) (C a) (D a)))

    fibreEdge≃ :
      pathToEquiv (cong El (cong (⅀ A) qR3))
      ≡ compEquiv (⟦⅀⟧ A (λ a → ⅀ (B a) (λ b → ⅀ (C a b) (D a b))))
          (compEquiv (Σ-cong-equiv-snd (λ a → ⅀Assoc≃ (B a) (C a) (D a)))
                     (invEquiv (⟦⅀⟧ A (λ a → ⅀ (⅀ (B a) (C a))
                                               (⅀Assoc-C' (B a) (C a) (D a))))))
    fibreEdge≃ =
        Der.⟦⅀⟧-natural-snd 𝒰 A qR3
      ∙ cong (λ s → compEquiv (⟦⅀⟧ A (λ a → ⅀ (B a) (λ b → ⅀ (C a b) (D a b))))
                       (compEquiv (Σ-cong-equiv-snd s)
                         (invEquiv (⟦⅀⟧ A (λ a → ⅀ (⅀ (B a) (C a))
                                                   (⅀Assoc-C' (B a) (C a) (D a)))))))
             (funExt (λ a → assocEdge≃ (B a) (C a) (D a)))
