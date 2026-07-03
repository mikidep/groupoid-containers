{-# OPTIONS --cubical #-}
-- ============================================================================
-- HoTTOperads.Universe.Assoc
--
-- The dependent-Σ reassociation toolkit: how the universe paths
-- `Inj (⅀Assoc≃ A B C)`, `⅀AssocD 𝒰 A B C`, `⅀-subst-path p C` and
-- `⅀IdlD 𝒰 D` act on a *canonical pair* `invEq (⟦⅀⟧ …) (a , z)`. Every such
-- site follows the same five-step recipe; this module extracts it once.
--
-- This machinery is operad-independent universe content. It is reused both
-- by Section 9 (Free Operad, `Free.HIT`'s `graft`-law proofs) and by the
-- monad pentagon coherence (Section 8, `Monad.TwoCellCoherence`).
--
-- Recipe (see the named lemmas below):
--   (a) `Assoc-cont A B C p` — the explicit Σ-shuffle that
--       `equivFun (⅀Assoc≃ A B C)` unfolds to.
--   (b) `Assoc-cont-at-pair` — `equivFun (⅀Assoc≃ A B C) (invEq ⟦⅀⟧ p) ≡
--       Assoc-cont A B C p`.
--   (c) `step-Assoc-on-pair` — `transport (cong El (Inj (⅀Assoc≃ A B C)))`
--       on a canonical pair equals `Assoc-cont A B C`.
--   (d) `transp-⅀AssocD-pair` — the analogous fact for the whole
--       `⅀AssocD 𝒰 A B C` path.
--   (e) `adj-coh` — adjunction coherence for an arbitrary equivalence.
--
-- No paper-numbered statements live here; this is infrastructure.
-- ============================================================================
module HoTTOperads.Universe.Assoc where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Transport using (substComposite)
open import Cubical.Foundations.GroupoidLaws using (lCancel ; congFunct)
open import Cubical.Foundations.Univalence
  using (ua ; uaβ ; uaInvEquiv ; pathToEquiv ; pathToEquivRefl ; EquivJ)
open import Cubical.Data.Sigma using (_,_ ; fst ; snd ; Σ ; ΣPathP)
open import Cubical.Data.Sigma.Properties
  using (Σ-cong-equiv-snd ; Σ-cong-equiv-fst ; Σ-assoc-≃)
open import Cubical.Data.Unit using (tt)

open import HoTTOperads.Universe.Base
open import HoTTOperads.Universe.Derived
open import HoTTOperads.Universe.IRDerived

private
  variable
    ℓc ℓe : Level

-- (e) Adjunction coherence: `invEq` of `secEq` equals `retEq` of `invEq`.
--     A general groupoid fact derived from `EquivJ` at `idEquiv`.
adj-coh : ∀ {ℓ} {X Y : Type ℓ} (e : X ≃ Y) (y : Y)
        → cong (invEq e) (secEq e y) ≡ retEq e (invEq e y)
adj-coh {Y = Y} e =
  EquivJ (λ _ e' → (y : Y) → cong (invEq e') (secEq e' y) ≡ retEq e' (invEq e' y))
         (λ _ → refl) e

module _ (𝒰 : Universe ℓc ℓe) where
  open Universe 𝒰

  -- The cubical index path along which the *first* argument of `graft`
  -- reindexes when its tree is substed along `p : A ≡ A'`.
  ⅀-subst-path : {A A' : Code} (p : A ≡ A') (C : El A' → Code)
               → ⅀ A (λ a → C (transport (cong El p) a)) ≡ ⅀ A' C
  ⅀-subst-path p C i = ⅀ (p i) (λ a → C (transp (λ j → El (p (i ∨ j))) i a))

  -- Transport along `⅀IdlD 𝒰 D` coincides with the canonical inverse-Σ
  -- pre-image `invEq (⟦⅀⟧ 𝜏 D) (α , b)`.
  opaque
   transp-⅀IdlD : (D : El 𝜏 → Code) (b : El (D (invEq ⟦𝜏⟧ tt)))
               → transport (cong El (⅀IdlD 𝒰 D)) b ≡ invEq (⟦⅀⟧ 𝜏 D) (invEq ⟦𝜏⟧ tt , b)
   transp-⅀IdlD D b =
      transport (cong El (sym (⅀Idl 𝒰 (D α)) ∙ cong (⅀ 𝜏) const-X-D)) b
    ≡⟨ cong (λ p → transport p b) (congFunct El (sym (⅀Idl 𝒰 (D α))) (cong (⅀ 𝜏) const-X-D)) ⟩
      transport (cong El (sym (⅀Idl 𝒰 (D α))) ∙ cong El (cong (⅀ 𝜏) const-X-D)) b
    ≡⟨ substComposite (λ X → X)
                      (cong El (sym (⅀Idl 𝒰 (D α))))
                      (cong El (cong (⅀ 𝜏) const-X-D)) b ⟩
      transport (cong El (cong (⅀ 𝜏) const-X-D))
                (transport (cong El (sym (⅀Idl 𝒰 (D α)))) b)
    ≡⟨ cong (transport (cong El (cong (⅀ 𝜏) const-X-D))) half-1 ⟩
      transport (cong El (cong (⅀ 𝜏) const-X-D))
                (invEq (⟦⅀⟧ 𝜏 (λ _ → D α)) (α , b))
    ≡⟨ half-2 ⟩
      invEq (⟦⅀⟧ 𝜏 D) (α , b)
    ∎
    where
      α : El 𝜏
      α = invEq ⟦𝜏⟧ tt

      const-X-D : (λ (_ : El 𝜏) → D α) ≡ D
      const-X-D = funExt (λ e → cong D (retEq ⟦𝜏⟧ e))

      half-1 : transport (cong El (sym (⅀Idl 𝒰 (D α)))) b
             ≡ invEq (⟦⅀⟧ 𝜏 (λ _ → D α)) (α , b)
      half-1 =
          transport (sym (cong El (⅀Idl 𝒰 (D α)))) b
        ≡⟨ cong (λ p → transport (sym p) b) (sym (⟦⅀Idl⟧ (D α))) ⟩
          transport (sym (ua (⅀Idl≃ (D α)))) b
        ≡⟨ cong (λ p → transport p b) (sym (uaInvEquiv (⅀Idl≃ (D α)))) ⟩
          transport (ua (invEquiv (⅀Idl≃ (D α)))) b
        ≡⟨ uaβ (invEquiv (⅀Idl≃ (D α))) b ⟩
          invEq (⅀Idl≃ (D α)) b
        ≡⟨ sym (invEq-⅀Idl (D α) b) ⟩
          invEq (⟦⅀⟧ 𝜏 (λ _ → D α)) (α , b)
        ∎

      retEq-𝜏-refl : retEq ⟦𝜏⟧ α ≡ refl
      retEq-𝜏-refl = isProp→isSet (isPropEl𝜏 𝒰) α α (retEq ⟦𝜏⟧ α) refl

      σ-snd-α-id : pathToEquiv (cong El (funExt⁻ const-X-D α)) ≡ idEquiv (El (D α))
      σ-snd-α-id = cong pathToEquiv (cong (cong El) (cong (cong D) retEq-𝜏-refl))
                 ∙ pathToEquivRefl

      half-2 : transport (cong El (cong (⅀ 𝜏) const-X-D))
                         (invEq (⟦⅀⟧ 𝜏 (λ _ → D α)) (α , b))
             ≡ invEq (⟦⅀⟧ 𝜏 D) (α , b)
      half-2 =
          transport (cong (λ B' → El (⅀ 𝜏 B')) const-X-D)
                    (invEq (⟦⅀⟧ 𝜏 (λ _ → D α)) (α , b))
        ≡⟨ cong (λ e → equivFun e (invEq (⟦⅀⟧ 𝜏 (λ _ → D α)) (α , b)))
                (⟦⅀⟧-natural-snd 𝒰 𝜏 const-X-D) ⟩
          equivFun (compEquiv (⟦⅀⟧ 𝜏 (λ _ → D α))
                              (compEquiv (Σ-cong-equiv-snd {A = El 𝜏}
                                            {B = λ _ → El (D α)} {B' = λ a → El (D a)}
                                            (λ a → pathToEquiv (cong El (funExt⁻ const-X-D a))))
                                         (invEquiv (⟦⅀⟧ 𝜏 D))))
                   (invEq (⟦⅀⟧ 𝜏 (λ _ → D α)) (α , b))
        ≡⟨ cong (equivFun (compEquiv (Σ-cong-equiv-snd {A = El 𝜏}
                                         {B = λ _ → El (D α)} {B' = λ a → El (D a)}
                                         (λ a → pathToEquiv (cong El (funExt⁻ const-X-D a))))
                                      (invEquiv (⟦⅀⟧ 𝜏 D))))
                (secEq (⟦⅀⟧ 𝜏 (λ _ → D α)) (α , b)) ⟩
          equivFun (invEquiv (⟦⅀⟧ 𝜏 D))
                   (equivFun (Σ-cong-equiv-snd {A = El 𝜏}
                                {B = λ _ → El (D α)} {B' = λ a → El (D a)}
                                (λ a → pathToEquiv (cong El (funExt⁻ const-X-D a))))
                            (α , b))
        ≡⟨ cong (equivFun (invEquiv (⟦⅀⟧ 𝜏 D)))
                (ΣPathP (refl , cong (λ e → equivFun e b) σ-snd-α-id)) ⟩
          invEq (⟦⅀⟧ 𝜏 D) (α , b)
        ∎

  -- Transport along `⅀-subst-path p C` computes via the canonical Σ-rebase.
  transp-⅀-subst-path : {A A' : Code} (p : A ≡ A') (C : El A' → Code)
                        (y : El (⅀ A (λ a → C (transport (cong El p) a))))
                      → transport (cong El (⅀-subst-path p C)) y
                      ≡ invEq (⟦⅀⟧ A' C)
                              (transport (cong El p)
                                         (fst (equivFun (⟦⅀⟧ A (λ a → C (transport (cong El p) a))) y)) ,
                               snd (equivFun (⟦⅀⟧ A (λ a → C (transport (cong El p) a))) y))
  transp-⅀-subst-path {A} {A'} = J motive at-refl
    where
      motive : (A' : Code) → A ≡ A' → Type _
      motive A' p = (C : El A' → Code)
                    (y : El (⅀ A (λ a → C (transport (cong El p) a))))
                  → transport (cong El (⅀-subst-path p C)) y
                  ≡ invEq (⟦⅀⟧ A' C)
                          (transport (cong El p)
                                     (fst (equivFun (⟦⅀⟧ A (λ a → C (transport (cong El p) a))) y)) ,
                           snd (equivFun (⟦⅀⟧ A (λ a → C (transport (cong El p) a))) y))

      at-refl : motive A refl
      at-refl C y =
          transport (cong (λ B → El (⅀ A B)) B-path) y
        ≡⟨ cong (λ e → equivFun e y) (⟦⅀⟧-natural-snd 𝒰 A B-path) ⟩
          invEq (⟦⅀⟧ A C) (a , transport (cong El (funExt⁻ B-path a)) c)
        ≡⟨ cong (invEq (⟦⅀⟧ A C)) pair-eq ⟩
          invEq (⟦⅀⟧ A C) (transport refl a , c)
        ∎
        where
          B-path : (λ (a' : El A) → C (transport refl a')) ≡ C
          B-path i a' = C (transp (λ _ → El A) i a')

          ⟦⅀⟧-of-y : Σ (El A) (λ a' → El (C (transport refl a')))
          ⟦⅀⟧-of-y = equivFun (⟦⅀⟧ A (λ a' → C (transport refl a'))) y

          a : El A
          a = fst ⟦⅀⟧-of-y

          c : El (C (transport refl a))
          c = snd ⟦⅀⟧-of-y

          pair-eq : (a , transport (cong El (funExt⁻ B-path a)) c) ≡ (transport refl a , c)
          pair-eq = ΣPathP ( sym (transportRefl a)
                          , λ i → transport-filler (cong El (funExt⁻ B-path a)) c (~ i))

  -- Equivalence-form of `transp-⅀-subst-path`.
  opaque
    ⅀-subst-path-equiv :
      {A A' : Code} (p : A ≡ A') (C : El A' → Code)
      → pathToEquiv (cong El (⅀-subst-path p C))
      ≡ compEquiv (⟦⅀⟧ A (λ a → C (transport (cong El p) a)))
                  (compEquiv (Σ-cong-equiv-fst {B = λ a → El (C a)}
                                (pathToEquiv (cong El p)))
                             (invEquiv (⟦⅀⟧ A' C)))
    ⅀-subst-path-equiv p C = equivEq (funExt (transp-⅀-subst-path p C))

  -- (a) The explicit Σ-shuffle behind `equivFun (⅀Assoc≃ A B C)`.
  Assoc-cont : (A : Code) (B : El A → Code)
               (C : (a : El A) → El (B a) → Code)
               (p : Σ (El A) (λ a → El (⅀ (B a) (C a))))
             → El (⅀ (⅀ A B) (⅀Assoc-C' A B C))
  Assoc-cont A B C p =
    invEq (⟦⅀⟧ (⅀ A B) (⅀Assoc-C' A B C))
          (invEq (Σ-cong-equiv-fst {B = λ ab → El (C (fst ab) (snd ab))} (⟦⅀⟧ A B))
                 (invEq Σ-assoc-≃
                        (equivFun (Σ-cong-equiv-snd (λ a → ⟦⅀⟧ (B a) (C a))) p)))

  opaque
    -- (b) Apply `⅀Assoc≃` to a canonical pair `invEq ⟦⅀⟧ p`.
    Assoc-cont-at-pair
      : (A : Code) (B : El A → Code) (C : (a : El A) → El (B a) → Code)
        (p : Σ (El A) (λ a → El (⅀ (B a) (C a))))
      → equivFun (⅀Assoc≃ A B C)
                 (invEq (⟦⅀⟧ A (λ a → ⅀ (B a) (C a))) p)
      ≡ Assoc-cont A B C p
    Assoc-cont-at-pair A B C p =
      cong (Assoc-cont A B C) (secEq (⟦⅀⟧ A (λ a → ⅀ (B a) (C a))) p)

  opaque
    -- (c) Push `transport (cong El (Inj (⅀Assoc≃ …)))` through a canonical pair.
    step-Assoc-on-pair
      : (A : Code) (B : El A → Code) (C : (a : El A) → El (B a) → Code)
        (p : Σ (El A) (λ a → El (⅀ (B a) (C a))))
      → transport (cong El (Inj (⅀Assoc≃ A B C)))
                  (invEq (⟦⅀⟧ A (λ a → ⅀ (B a) (C a))) p)
      ≡ Assoc-cont A B C p
    step-Assoc-on-pair A B C p =
        cong (λ q → transport q (invEq (⟦⅀⟧ A (λ a → ⅀ (B a) (C a))) p))
             (sym (⟦⅀Assoc⟧ A B C))
      ∙ uaβ (⅀Assoc≃ A B C) (invEq (⟦⅀⟧ A (λ a → ⅀ (B a) (C a))) p)
      ∙ Assoc-cont-at-pair A B C p

  opaque
    -- (d) Push `transport (cong El (⅀AssocD 𝒰 A B C))` through a canonical pair.
    transp-⅀AssocD-pair
      : (A : Code) (B : El A → Code) (C : El (⅀ A B) → Code)
        (a : El A)
        (z : El (⅀ (B a) (λ b → C (invEq (⟦⅀⟧ A B) (a , b)))))
      → transport (cong El (⅀AssocD 𝒰 A B C))
                  (invEq (⟦⅀⟧ A (λ a' → ⅀ (B a') (λ b → C (invEq (⟦⅀⟧ A B) (a' , b)))))
                         (a , z))
      ≡ invEq (⟦⅀⟧ (⅀ A B) C)
              ( invEq (⟦⅀⟧ A B) (a , fst (equivFun (⟦⅀⟧ (B a) (λ b → C (invEq (⟦⅀⟧ A B) (a , b)))) z))
              , snd (equivFun (⟦⅀⟧ (B a) (λ b → C (invEq (⟦⅀⟧ A B) (a , b)))) z))
    transp-⅀AssocD-pair A B C a z =
        cong (λ q → transport q input)
             (congFunct El (Inj (⅀Assoc≃ A B C')) (cong (⅀ (⅀ A B)) C'-eq))
      ∙ substComposite (λ X → X)
                       (cong El (Inj (⅀Assoc≃ A B C')))
                       (cong El (cong (⅀ (⅀ A B)) C'-eq))
                       input
      ∙ cong transp-C'-eq (step-Assoc-on-pair A B C' (a , z))
      ∙ transp-C'-eq-canonical
      ∙ cong (λ w → invEq (⟦⅀⟧ (⅀ A B) C) (paired-ab , w))
             (sym c-restore)
      where
        C' : (a : El A) → El (B a) → Code
        C' a' b = C (invEq (⟦⅀⟧ A B) (a' , b))

        C'-eq : ⅀Assoc-C' A B C' ≡ C
        C'-eq = funExt (λ x → cong C (retEq (⟦⅀⟧ A B) x))

        transp-C'-eq : El (⅀ (⅀ A B) (⅀Assoc-C' A B C')) → El (⅀ (⅀ A B) C)
        transp-C'-eq = transport (cong (λ B'' → El (⅀ (⅀ A B) B'')) C'-eq)

        input : El (⅀ A (λ a' → ⅀ (B a') (λ b → C (invEq (⟦⅀⟧ A B) (a' , b)))))
        input = invEq (⟦⅀⟧ A (λ a' → ⅀ (B a') (λ b → C (invEq (⟦⅀⟧ A B) (a' , b))))) (a , z)

        b-of : El (B a)
        b-of = fst (equivFun (⟦⅀⟧ (B a) (λ b → C (invEq (⟦⅀⟧ A B) (a , b)))) z)

        w-of : El (C (invEq (⟦⅀⟧ A B) (a , b-of)))
        w-of = snd (equivFun (⟦⅀⟧ (B a) (λ b → C (invEq (⟦⅀⟧ A B) (a , b)))) z)

        paired-ab : El (⅀ A B)
        paired-ab = invEq (⟦⅀⟧ A B) (a , b-of)

        substed-w : El (⅀Assoc-C' A B C' paired-ab)
        substed-w = subst (λ ab → El (C' (fst ab) (snd ab)))
                          (sym (secEq (⟦⅀⟧ A B) (a , b-of))) w-of

        opaque
          c-restore : w-of ≡ transport (cong El (funExt⁻ C'-eq paired-ab)) substed-w
          c-restore =
              sym (transportRefl w-of)
            ∙ cong (λ q → transport q w-of)
                   (sym (lCancel (cong (λ ab → El (C' (fst ab) (snd ab)))
                                        (secEq (⟦⅀⟧ A B) (a , b-of)))))
            ∙ cong (λ q → transport (cong (λ ab → El (C' (fst ab) (snd ab)))
                                            (sym (secEq (⟦⅀⟧ A B) (a , b-of))) ∙ q)
                                     w-of)
                   (sym key-eq-local)
            ∙ substComposite (λ X → X)
                             (cong (λ ab → El (C' (fst ab) (snd ab)))
                                   (sym (secEq (⟦⅀⟧ A B) (a , b-of))))
                             (cong El (funExt⁻ C'-eq paired-ab))
                             w-of
            where
              key-eq-local : cong El (funExt⁻ C'-eq paired-ab)
                           ≡ cong (λ ab → El (C' (fst ab) (snd ab)))
                                  (secEq (⟦⅀⟧ A B) (a , b-of))
              key-eq-local = cong (cong (λ x → El (C x)))
                                  (sym (adj-coh (⟦⅀⟧ A B) (a , b-of)))

        opaque
          transp-C'-eq-canonical
            : transp-C'-eq (Assoc-cont A B C' (a , z))
            ≡ invEq (⟦⅀⟧ (⅀ A B) C)
                    ( paired-ab
                    , transport (cong El (funExt⁻ C'-eq paired-ab)) substed-w)
          transp-C'-eq-canonical =
              cong (λ e → equivFun e (Assoc-cont A B C' (a , z)))
                   (⟦⅀⟧-natural-snd 𝒰 (⅀ A B) C'-eq)
            ∙ cong (λ p → invEq (⟦⅀⟧ (⅀ A B) C)
                                (fst p ,
                                 transport (cong El (funExt⁻ C'-eq (fst p))) (snd p)))
                   (secEq (⟦⅀⟧ (⅀ A B) (⅀Assoc-C' A B C'))
                          (paired-ab , substed-w))
