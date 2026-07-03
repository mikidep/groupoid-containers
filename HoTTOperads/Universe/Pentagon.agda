{-# OPTIONS --cubical --no-import-sorts #-}

-- The abstract universe Mac Lane pentagon for `⅀Assoc≃`, decoupled from
-- `OpM`/`route-L`/`reidxL`.  This is a faithful parametric port of the
-- VERIFIED `Monad.TwoCellCoherence.ΣPenta` (route-L's doubly-canonical
-- Σ-pair ≡ route-R's) to abstract code families `(A , B , C , D)`.
-- Instantiated at `(Index w , Bj , Bm , Bn)` it discharges the pentagon's
-- index-third kernel.  Proof shape (unchanged from `ΣPenta`):
-- `cong G Py'-secEq ∙ tailR`, `tailR = Ggap ∙ sym (cong H rE-canon)`,
-- `Ggap = ΣPathP (refl , sym (Φ …))`, `Φ` the `J`-on-`secEq` kernel; the
-- non-dependent core is `Σ-assoc-≃` strictness (definitional).
module HoTTOperads.Universe.Pentagon where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma using (_,_ ; fst ; snd ; Σ ; ΣPathP)
open import Cubical.Data.Sigma.Properties
  using (Σ-cong-equiv-snd ; Σ-cong-equiv-fst ; Σ-assoc-≃)

open import Cubical.Foundations.Transport using (substComposite ; subst⁻Subst ; substSubst⁻)
open import Cubical.Foundations.GroupoidLaws using (symDistr ; congFunct ; symInvo)

open import HoTTOperads.Universe.Base
open import HoTTOperads.Universe.Derived
open import HoTTOperads.Universe.Assoc using (Assoc-cont)

private
  variable
    ℓc ℓe : Level

module _ {𝒰 : Universe ℓc ℓe} where
  open Universe 𝒰

  -- The inverse-trick-clean `invEq (⅀Assoc≃ …) ∘ invEq ⟦⅀⟧` reduction
  -- (verbatim from `TwoCellCoherence.⅀Assoc≃-inv-on-canon`; universe-only).
  ⅀Assoc≃-inv-on-canon :
    (A : Code) (B : El A → Code) (C : (a : El A) → El (B a) → Code)
    (σ : Σ (El (⅀ A B)) (λ ab → El (⅀Assoc-C' A B C ab)))
    → invEq (⅀Assoc≃ A B C)
            (invEq (⟦⅀⟧ (⅀ A B) (⅀Assoc-C' A B C)) σ)
    ≡ invEq (⟦⅀⟧ A (λ a → ⅀ (B a) (C a)))
            ( fst (equivFun (⟦⅀⟧ A B) (fst σ))
            , invEq (⟦⅀⟧ (B (fst (equivFun (⟦⅀⟧ A B) (fst σ))))
                          (C (fst (equivFun (⟦⅀⟧ A B) (fst σ)))))
                    ( snd (equivFun (⟦⅀⟧ A B) (fst σ))
                    , snd σ ) )
  ⅀Assoc≃-inv-on-canon A B C σ =
    cong (λ z → invEq (⟦⅀⟧ A (λ a → ⅀ (B a) (C a)))
                      (invEq (Σ-cong-equiv-snd (λ a → ⟦⅀⟧ (B a) (C a)))
                             (equivFun Σ-assoc-≃
                                       (equivFun
                                         (Σ-cong-equiv-fst
                                            {B = λ ab → El (C (fst ab) (snd ab))}
                                            (⟦⅀⟧ A B)) z))))
         (secEq (⟦⅀⟧ (⅀ A B) (⅀Assoc-C' A B C)) σ)

  -- ========================================================================
  -- The abstract universe Mac Lane pentagon over `(A , B , C , D)`.
  -- ========================================================================
  module _ (A : Code) (B : El A → Code)
           (C : (a : El A) → El (B a) → Code)
           (D : (a : El A) (b : El (B a)) → El (C a b) → Code) where

    -- Derived families (the `Bᶜ`/`Cnᶜ`/`pf-pair`/`b''-of`/`RGG`/`Rg`/
    -- `ALB`/`ALC` of `ΣPenta`, here over abstract `(A,B,C,D)`).
    Bᶜ : El (⅀ A B) → Code
    Bᶜ = ⅀Assoc-C' A B C

    Cnᶜ : (ab : El (⅀ A B)) → El (Bᶜ ab) → Code
    Cnᶜ ab b'' = D (fst (equivFun (⟦⅀⟧ A B) ab))
                   (snd (equivFun (⟦⅀⟧ A B) ab))
                   b''

    pf-pair : (a : El A) → El (B a) → El (⅀ A B)
    pf-pair a b = invEq (⟦⅀⟧ A B) (a , b)

    C'-out : (a : El A) → El (B a) → Code
    C'-out a b = ⅀ (Bᶜ (pf-pair a b)) (Cnᶜ (pf-pair a b))

    b''-of : (a : El A) (b : El (B a)) (w : El (C'-out a b))
           → El (Bᶜ (pf-pair a b))
    b''-of a b w = fst (equivFun (⟦⅀⟧ (Bᶜ (pf-pair a b))
                                      (Cnᶜ (pf-pair a b))) w)

    ALB : El A → Code
    ALB a = ⅀ (B a) (C a)

    ALC : (a : El A) → El (ALB a) → Code
    ALC a = ⅀Assoc-C' (B a) (C a) (D a)

    RGG : El A → Code
    RGG a = ⅀ (⅀ (B a) (C a)) (⅀Assoc-C' (B a) (C a) (D a))

    Rg : (a : El A) → El (⅀ (B a) (λ b → ⅀ (C a b) (D a b))) ≃ El (RGG a)
    Rg a = ⅀Assoc≃ (B a) (C a) (D a)

    AcontShuffleL :
      El (⅀ A (λ a → ⅀ (ALB a) (ALC a)))
      → Σ[ ab ∈ El (⅀ A ALB) ] El (⅀Assoc-C' A ALB ALC ab)
    AcontShuffleL y =
      invEq (Σ-cong-equiv-fst
               {B = λ ab → El (ALC (fst ab) (snd ab))} (⟦⅀⟧ A ALB))
            (invEq Σ-assoc-≃
                   (equivFun (Σ-cong-equiv-snd (λ a → ⟦⅀⟧ (ALB a) (ALC a)))
                             (equivFun (⟦⅀⟧ A (λ a → ⅀ (ALB a) (ALC a))) y)))

    Py' : El (⅀ A (λ a → ⅀ (ALB a) (ALC a)))
        → Σ[ a ∈ El A ] El (⅀ (B a) (C a))
    Py' y = equivFun (⟦⅀⟧ A (λ a → ⅀ (B a) (C a)))
                     (fst (AcontShuffleL y))

    rA : El (⅀ A RGG) → El A
    rA y = fst (equivFun (⟦⅀⟧ A RGG) y)

    rE : (y : El (⅀ A RGG))
       → Σ[ b ∈ El (B (rA y)) ] El (⅀ (C (rA y) b) (D (rA y) b))
    rE y = equivFun (⟦⅀⟧ (B (rA y)) (λ b → ⅀ (C (rA y) b) (D (rA y) b)))
                    (invEq (Rg (rA y))
                           (snd (equivFun (⟦⅀⟧ A RGG) y)))

    RW : (y : El (⅀ A RGG)) → El (C'-out (rA y) (fst (rE y)))
    RW y = subst (λ ab → El (⅀ (C (fst ab) (snd ab))
                               (D (fst ab) (snd ab))))
                 (sym (secEq (⟦⅀⟧ A B) (rA y , fst (rE y))))
                 (snd (rE y))

    -- The `J`-on-`secEq` kernel: `equivFun ⟦⅀⟧` of a `subst (sym T)`'d
    -- canonical pair, `fst`-projected, is `subst (sym T)` of the
    -- original `fst` (base = `secEq`).  `y`-independent; top-level for
    -- reuse (`Ggap` here, and the `OpM` pentagon's `pent-RHS≡SB`).
    Φ : {p q : Σ[ a ∈ El A ] El (B a)}
        (T : p ≡ q)
        (u : El (C (fst q) (snd q)))
        (v : El (D (fst q) (snd q) u))
      → fst (equivFun (⟦⅀⟧ (C (fst p) (snd p))
                           (D (fst p) (snd p)))
                      (subst (λ x → El (⅀ (C (fst x) (snd x))
                                          (D (fst x) (snd x))))
                             (sym T)
                             (invEq (⟦⅀⟧ (C (fst q) (snd q))
                                         (D (fst q) (snd q)))
                                    (u , v))))
      ≡ subst (λ x → El (C (fst x) (snd x))) (sym T) u
    Φ {p = p} =
      J (λ q' T' → (u : El (C (fst q') (snd q')))
                   (v : El (D (fst q') (snd q') u))
                 → fst (equivFun (⟦⅀⟧ (C (fst p) (snd p))
                                      (D (fst p) (snd p)))
                          (subst (λ x → El (⅀ (C (fst x) (snd x))
                                              (D (fst x) (snd x))))
                                 (sym T')
                                 (invEq (⟦⅀⟧ (C (fst q') (snd q'))
                                             (D (fst q') (snd q')))
                                        (u , v))))
                 ≡ subst (λ x → El (C (fst x) (snd x))) (sym T') u)
        (λ u v →
            cong (λ X → fst (equivFun (⟦⅀⟧ (C (fst p) (snd p))
                                           (D (fst p) (snd p))) X))
                 (transportRefl
                   (invEq (⟦⅀⟧ (C (fst p) (snd p))
                               (D (fst p) (snd p)))
                          (u , v)))
          ∙ cong fst
                 (secEq (⟦⅀⟧ (C (fst p) (snd p))
                             (D (fst p) (snd p)))
                        (u , v))
          ∙ sym (transportRefl u))

    -- Combined `(C,D)`-Σ kernel: `Φ`'s `J`-on-`secEq` technique WITHOUT
    -- the `fst`-projection — returns the full Σ-pair move.  `Φ` is its
    -- `fst`; its `snd` is the genuine `D`-fibre carry (a `PathP` over
    -- `Φ`), the abstract analogue of the `OpM` deep data pentagon.
    -- Same proof as `Φ` (NOT a `subst-filler`): `J` then `secEq`.
    ΦΣ : {p q : Σ[ a ∈ El A ] El (B a)}
         (T : p ≡ q)
         (u : El (C (fst q) (snd q)))
         (v : El (D (fst q) (snd q) u))
       → equivFun (⟦⅀⟧ (C (fst p) (snd p)) (D (fst p) (snd p)))
                  (subst (λ x → El (⅀ (C (fst x) (snd x))
                                      (D (fst x) (snd x))))
                         (sym T)
                         (invEq (⟦⅀⟧ (C (fst q) (snd q))
                                     (D (fst q) (snd q)))
                                (u , v)))
       ≡ subst (λ x → Σ[ c ∈ El (C (fst x) (snd x)) ]
                         El (D (fst x) (snd x) c))
               (sym T) (u , v)
    ΦΣ {p = p} =
      J (λ q' T' → (u : El (C (fst q') (snd q')))
                   (v : El (D (fst q') (snd q') u))
                 → equivFun (⟦⅀⟧ (C (fst p) (snd p))
                                 (D (fst p) (snd p)))
                            (subst (λ x → El (⅀ (C (fst x) (snd x))
                                                (D (fst x) (snd x))))
                                   (sym T')
                                   (invEq (⟦⅀⟧ (C (fst q') (snd q'))
                                               (D (fst q') (snd q')))
                                          (u , v)))
                 ≡ subst (λ x → Σ[ c ∈ El (C (fst x) (snd x)) ]
                                  El (D (fst x) (snd x) c))
                         (sym T') (u , v))
        (λ u v →
            cong (equivFun (⟦⅀⟧ (C (fst p) (snd p))
                               (D (fst p) (snd p))))
                 (transportRefl
                   (invEq (⟦⅀⟧ (C (fst p) (snd p))
                               (D (fst p) (snd p)))
                          (u , v)))
          ∙ secEq (⟦⅀⟧ (C (fst p) (snd p))
                       (D (fst p) (snd p)))
                  (u , v)
          ∙ sym (transportRefl (u , v)))

    -- `Φ` is `ΦΣ`'s `fst`: both are the same `J`-on-`secEq`; the base
    -- difference is only the `cong fst`/`∙` distribution (`congFunct`),
    -- `cong fst ∘ cong g = cong (fst ∘ g)` and `cong fst (transportRefl
    -- {Σ}) = transportRefl` (both definitional).
    Φ≡fstΦΣ :
      {p q : Σ[ a ∈ El A ] El (B a)} (T : p ≡ q)
      (u : El (C (fst q) (snd q))) (v : El (D (fst q) (snd q) u))
      → Φ T u v ≡ cong fst (ΦΣ T u v)
    Φ≡fstΦΣ {p = p} =
      J (λ q' T' → (u : El (C (fst q') (snd q')))
                   (v : El (D (fst q') (snd q') u))
                 → Φ T' u v ≡ cong π₁ (ΦΣ T' u v))
        (λ u v →
          let tr   = transportRefl (invEq ⟦⟧cd (u , v))
              sec  = secEq ⟦⟧cd (u , v)
              Asg  = cong (equivFun ⟦⟧cd) tr
              cfsym : cong π₁ (sym (transportRefl (u , v)))
                    ≡ sym (transportRefl u)
              cfsym = refl
              -- `Φ`/`ΦΣ` are `J`; at `refl` they reduce (definitionally)
              -- to `transport refl` of their base clauses, then
              -- `transportRefl` to the base.
              dφ : (u' : El (C (fst p) (snd p)))
                   (v' : El (D (fst p) (snd p) u'))
                 → π₁ (equivFun ⟦⟧cd
                          (subst (λ x → El (⅀ (C (fst x) (snd x))
                                              (D (fst x) (snd x))))
                                 (sym (refl {x = p}))
                                 (invEq ⟦⟧cd (u' , v'))))
                 ≡ subst (λ x → El (C (fst x) (snd x))) (sym (refl {x = p})) u'
              dφ u' v' =
                  cong (λ X → π₁ (equivFun ⟦⟧cd X))
                       (transportRefl (invEq ⟦⟧cd (u' , v')))
                ∙ cong π₁ (secEq ⟦⟧cd (u' , v'))
                ∙ sym (transportRefl u')
              dΣ : (u' : El (C (fst p) (snd p)))
                   (v' : El (D (fst p) (snd p) u'))
                 → equivFun ⟦⟧cd
                     (subst (λ x → El (⅀ (C (fst x) (snd x))
                                         (D (fst x) (snd x))))
                            (sym (refl {x = p})) (invEq ⟦⟧cd (u' , v')))
                 ≡ subst (λ x → Σ[ c ∈ El (C (fst x) (snd x)) ]
                                  El (D (fst x) (snd x) c))
                         (sym (refl {x = p})) (u' , v')
              dΣ u' v' =
                  cong (equivFun ⟦⟧cd)
                       (transportRefl (invEq ⟦⟧cd (u' , v')))
                ∙ secEq ⟦⟧cd (u' , v')
                ∙ sym (transportRefl (u' , v'))
              ΦR : Φ refl u v ≡ dφ u v
              ΦR = funExt⁻ (funExt⁻ (transportRefl dφ) u) v
              ΦΣR : ΦΣ refl u v ≡ dΣ u v
              ΦΣR = funExt⁻ (funExt⁻ (transportRefl dΣ) u) v
          in ΦR
           ∙ sym
             ( congFunct π₁ Asg (sec ∙ sym (transportRefl (u , v)))
             ∙ cong (cong π₁ Asg ∙_)
                    (congFunct π₁ sec (sym (transportRefl (u , v))))
             ∙ cong (λ z → cong π₁ Asg ∙ (cong π₁ sec ∙ z)) cfsym )
           ∙ cong (cong π₁) (sym ΦΣR))
      where
        ⟦⟧cd = ⟦⅀⟧ (C (fst p) (snd p)) (D (fst p) (snd p))
        π₁ : Σ[ c ∈ El (C (fst p) (snd p)) ] El (D (fst p) (snd p) c)
           → El (C (fst p) (snd p))
        π₁ = fst

    -- The abstract universe Mac Lane pentagon (= `ΣPenta`, parametric).
    -- `El (⅀ A RGG) = El (⅀ A (λ a → ⅀ (ALB a) (ALC a)))` definitionally.
    ⅀Assoc-pentagon :
      (y : El (⅀ A RGG))
      → Path (Σ[ ab ∈ El (⅀ A B) ] El (Bᶜ ab))
             ( pf-pair (fst (Py' y))
                       (fst (equivFun (⟦⅀⟧ (B (fst (Py' y)))
                                           (C (fst (Py' y))))
                                      (snd (Py' y))))
             , subst (λ ab → El (C (fst ab) (snd ab)))
                     (sym (secEq (⟦⅀⟧ A B)
                           ( fst (Py' y)
                           , fst (equivFun (⟦⅀⟧ (B (fst (Py' y)))
                                               (C (fst (Py' y))))
                                          (snd (Py' y))))))
                     (snd (equivFun (⟦⅀⟧ (B (fst (Py' y)))
                                         (C (fst (Py' y))))
                                    (snd (Py' y)))) )
             ( pf-pair (rA y) (fst (rE y))
             , b''-of (rA y) (fst (rE y)) (RW y) )
    ⅀Assoc-pentagon y = cong G Py'-secEq ∙ tailR
      where
        a₀ : El A
        a₀ = fst (Py' y)

        eb' : El (B a₀)
        eb' = fst (equivFun (⟦⅀⟧ (B a₀) (C a₀)) (snd (Py' y)))

        ec' : El (⅀Assoc-C' A B C (pf-pair a₀ eb'))
        ec' = subst (λ ab → El (C (fst ab) (snd ab)))
                    (sym (secEq (⟦⅀⟧ A B) (a₀ , eb')))
                    (snd (equivFun (⟦⅀⟧ (B a₀) (C a₀)) (snd (Py' y))))

        Py'-secEq :
          Py' y
          ≡ fst (invEq Σ-assoc-≃
                       (equivFun (Σ-cong-equiv-snd (λ a → ⟦⅀⟧ (ALB a) (ALC a)))
                                 (equivFun (⟦⅀⟧ A (λ a → ⅀ (ALB a) (ALC a)))
                                           y)))
        Py'-secEq =
          secEq (⟦⅀⟧ A (λ a → ⅀ (B a) (C a)))
                (fst (invEq Σ-assoc-≃
                            (equivFun (Σ-cong-equiv-snd
                                         (λ a → ⟦⅀⟧ (ALB a) (ALC a)))
                                      (equivFun
                                        (⟦⅀⟧ A (λ a → ⅀ (ALB a) (ALC a)))
                                        y))))

        G : Σ[ a ∈ El A ] El (⅀ (B a) (C a))
          → Σ[ ab ∈ El (⅀ A B) ] El (Bᶜ ab)
        G p =
          ( pf-pair (fst p)
                    (fst (equivFun (⟦⅀⟧ (B (fst p)) (C (fst p))) (snd p)))
          , subst (λ ab → El (C (fst ab) (snd ab)))
                  (sym (secEq (⟦⅀⟧ A B)
                        ( fst p
                        , fst (equivFun (⟦⅀⟧ (B (fst p)) (C (fst p)))
                                        (snd p)))))
                  (snd (equivFun (⟦⅀⟧ (B (fst p)) (C (fst p))) (snd p))) )

        tailR :
          G (fst (invEq Σ-assoc-≃
                        (equivFun (Σ-cong-equiv-snd
                                     (λ a → ⟦⅀⟧ (ALB a) (ALC a)))
                                  (equivFun
                                    (⟦⅀⟧ A (λ a → ⅀ (ALB a) (ALC a)))
                                    y))))
          ≡ ( pf-pair (rA y) (fst (rE y))
            , b''-of (rA y) (fst (rE y)) (RW y))
        tailR = Ggap ∙ sym (cong H rE-canon)
          where
            Yr : Σ[ a ∈ El A ] El (RGG a)
            Yr = equivFun (⟦⅀⟧ A RGG) y

            Bᵣ : El (B (rA y)) → Code
            Bᵣ = C (rA y)
            Dᵣ : (b : El (B (rA y))) → El (C (rA y) b) → Code
            Dᵣ = D (rA y)

            σ : Σ[ ab ∈ El (⅀ (B (rA y)) Bᵣ) ]
                  El (⅀Assoc-C' (B (rA y)) Bᵣ Dᵣ ab)
            σ = equivFun (⟦⅀⟧ (⅀ (B (rA y)) Bᵣ)
                              (⅀Assoc-C' (B (rA y)) Bᵣ Dᵣ))
                         (snd Yr)

            invAssoc-eq :
              invEq (⅀Assoc≃ (B (rA y)) Bᵣ Dᵣ) (snd Yr)
              ≡ invEq (⟦⅀⟧ (B (rA y)) (λ a → ⅀ (Bᵣ a) (Dᵣ a)))
                      ( fst (equivFun (⟦⅀⟧ (B (rA y)) Bᵣ) (fst σ))
                      , invEq (⟦⅀⟧ (Bᵣ (fst (equivFun (⟦⅀⟧ (B (rA y)) Bᵣ)
                                                       (fst σ))))
                                   (Dᵣ (fst (equivFun (⟦⅀⟧ (B (rA y)) Bᵣ)
                                                       (fst σ)))))
                              ( snd (equivFun (⟦⅀⟧ (B (rA y)) Bᵣ) (fst σ))
                              , snd σ))
            invAssoc-eq =
                cong (invEq (⅀Assoc≃ (B (rA y)) Bᵣ Dᵣ))
                     (sym (retEq (⟦⅀⟧ (⅀ (B (rA y)) Bᵣ)
                                      (⅀Assoc-C' (B (rA y)) Bᵣ Dᵣ))
                                 (snd Yr)))
              ∙ ⅀Assoc≃-inv-on-canon (B (rA y)) Bᵣ Dᵣ σ

            rE-canon :
              rE y
              ≡ ( fst (equivFun (⟦⅀⟧ (B (rA y)) Bᵣ) (fst σ))
                , invEq (⟦⅀⟧ (Bᵣ (fst (equivFun (⟦⅀⟧ (B (rA y)) Bᵣ)
                                                 (fst σ))))
                             (Dᵣ (fst (equivFun (⟦⅀⟧ (B (rA y)) Bᵣ)
                                                 (fst σ)))))
                        ( snd (equivFun (⟦⅀⟧ (B (rA y)) Bᵣ) (fst σ))
                        , snd σ))
            rE-canon =
                cong (equivFun (⟦⅀⟧ (B (rA y)) (λ b → ⅀ (Bᵣ b) (Dᵣ b))))
                     invAssoc-eq
              ∙ secEq (⟦⅀⟧ (B (rA y)) (λ b → ⅀ (Bᵣ b) (Dᵣ b)))
                      ( fst (equivFun (⟦⅀⟧ (B (rA y)) Bᵣ) (fst σ))
                      , invEq (⟦⅀⟧ (Bᵣ (fst (equivFun (⟦⅀⟧ (B (rA y)) Bᵣ)
                                                       (fst σ))))
                                   (Dᵣ (fst (equivFun (⟦⅀⟧ (B (rA y)) Bᵣ)
                                                       (fst σ)))))
                              ( snd (equivFun (⟦⅀⟧ (B (rA y)) Bᵣ) (fst σ))
                              , snd σ))

            H : Σ[ b ∈ El (B (rA y)) ]
                  El (⅀ (C (rA y) b) (D (rA y) b))
              → Σ[ ab ∈ El (⅀ A B) ] El (Bᶜ ab)
            H r =
              ( pf-pair (rA y) (fst r)
              , b''-of (rA y) (fst r)
                  (subst (λ ab → El (⅀ (C (fst ab) (snd ab))
                                       (D (fst ab) (snd ab))))
                         (sym (secEq (⟦⅀⟧ A B)
                                     (rA y , fst r)))
                         (snd r)))

            Ggap :
              G (fst (invEq Σ-assoc-≃
                            (equivFun (Σ-cong-equiv-snd
                                         (λ a → ⟦⅀⟧ (ALB a) (ALC a)))
                                      (equivFun
                                        (⟦⅀⟧ A (λ a → ⅀ (ALB a) (ALC a)))
                                        y))))
              ≡ H ( fst (equivFun (⟦⅀⟧ (B (rA y)) Bᵣ) (fst σ))
                  , invEq (⟦⅀⟧ (Bᵣ (fst (equivFun (⟦⅀⟧ (B (rA y)) Bᵣ)
                                                   (fst σ))))
                               (Dᵣ (fst (equivFun (⟦⅀⟧ (B (rA y)) Bᵣ)
                                                   (fst σ)))))
                          ( snd (equivFun (⟦⅀⟧ (B (rA y)) Bᵣ) (fst σ))
                          , snd σ))
            Ggap =
              ΣPathP
                ( refl
                , sym (Φ (secEq (⟦⅀⟧ A B)
                                ( rA y
                                , fst (equivFun (⟦⅀⟧ (B (rA y)) Bᵣ)
                                                (fst σ))))
                         (snd (equivFun (⟦⅀⟧ (B (rA y)) Bᵣ) (fst σ)))
                         (snd σ)))

    -- Public copies of `⅀Assoc-pentagon`'s sealed decomposition
    -- (`G` / `Py'-secEq` / `tailR`), byte-faithful to the `where`-bound
    -- originals, exposed at module scope so a downstream proof can
    -- unfold the pentagon.  `⅀Assoc-pentagon-explicit` is `refl`:
    -- the copies are definitionally the sealed ones, so
    -- `⅀Assoc-pentagon y` reduces to
    -- `cong (⅀Assoc-pentagon-G y) (⅀Assoc-pentagon-Py'-secEq y)
    --   ∙ ⅀Assoc-pentagon-tailR y`.
    ⅀Assoc-pentagon-G :
      (y : El (⅀ A RGG))
      → Σ[ a ∈ El A ] El (⅀ (B a) (C a))
      → Σ[ ab ∈ El (⅀ A B) ] El (Bᶜ ab)
    ⅀Assoc-pentagon-G y p =
      ( pf-pair (fst p)
                (fst (equivFun (⟦⅀⟧ (B (fst p)) (C (fst p))) (snd p)))
      , subst (λ ab → El (C (fst ab) (snd ab)))
              (sym (secEq (⟦⅀⟧ A B)
                    ( fst p
                    , fst (equivFun (⟦⅀⟧ (B (fst p)) (C (fst p)))
                                    (snd p)))))
              (snd (equivFun (⟦⅀⟧ (B (fst p)) (C (fst p))) (snd p))) )

    ⅀Assoc-pentagon-Py'-secEq :
      (y : El (⅀ A RGG))
      → Py' y
      ≡ fst (invEq Σ-assoc-≃
                   (equivFun (Σ-cong-equiv-snd (λ a → ⟦⅀⟧ (ALB a) (ALC a)))
                             (equivFun (⟦⅀⟧ A (λ a → ⅀ (ALB a) (ALC a)))
                                       y)))
    ⅀Assoc-pentagon-Py'-secEq y =
      secEq (⟦⅀⟧ A (λ a → ⅀ (B a) (C a)))
            (fst (invEq Σ-assoc-≃
                        (equivFun (Σ-cong-equiv-snd
                                     (λ a → ⟦⅀⟧ (ALB a) (ALC a)))
                                  (equivFun
                                    (⟦⅀⟧ A (λ a → ⅀ (ALB a) (ALC a)))
                                    y))))

    ⅀Assoc-pentagon-tailR :
      (y : El (⅀ A RGG))
      → ⅀Assoc-pentagon-G y
          (fst (invEq Σ-assoc-≃
                      (equivFun (Σ-cong-equiv-snd
                                   (λ a → ⟦⅀⟧ (ALB a) (ALC a)))
                                (equivFun
                                  (⟦⅀⟧ A (λ a → ⅀ (ALB a) (ALC a)))
                                  y))))
      ≡ ( pf-pair (rA y) (fst (rE y))
        , b''-of (rA y) (fst (rE y)) (RW y))
    ⅀Assoc-pentagon-tailR y = Ggap ∙ sym (cong H rE-canon)
      where
        Yr : Σ[ a ∈ El A ] El (RGG a)
        Yr = equivFun (⟦⅀⟧ A RGG) y

        Bᵣ : El (B (rA y)) → Code
        Bᵣ = C (rA y)
        Dᵣ : (b : El (B (rA y))) → El (C (rA y) b) → Code
        Dᵣ = D (rA y)

        σ : Σ[ ab ∈ El (⅀ (B (rA y)) Bᵣ) ]
              El (⅀Assoc-C' (B (rA y)) Bᵣ Dᵣ ab)
        σ = equivFun (⟦⅀⟧ (⅀ (B (rA y)) Bᵣ)
                          (⅀Assoc-C' (B (rA y)) Bᵣ Dᵣ))
                     (snd Yr)

        invAssoc-eq :
          invEq (⅀Assoc≃ (B (rA y)) Bᵣ Dᵣ) (snd Yr)
          ≡ invEq (⟦⅀⟧ (B (rA y)) (λ a → ⅀ (Bᵣ a) (Dᵣ a)))
                  ( fst (equivFun (⟦⅀⟧ (B (rA y)) Bᵣ) (fst σ))
                  , invEq (⟦⅀⟧ (Bᵣ (fst (equivFun (⟦⅀⟧ (B (rA y)) Bᵣ)
                                                   (fst σ))))
                               (Dᵣ (fst (equivFun (⟦⅀⟧ (B (rA y)) Bᵣ)
                                                   (fst σ)))))
                          ( snd (equivFun (⟦⅀⟧ (B (rA y)) Bᵣ) (fst σ))
                          , snd σ))
        invAssoc-eq =
            cong (invEq (⅀Assoc≃ (B (rA y)) Bᵣ Dᵣ))
                 (sym (retEq (⟦⅀⟧ (⅀ (B (rA y)) Bᵣ)
                                  (⅀Assoc-C' (B (rA y)) Bᵣ Dᵣ))
                             (snd Yr)))
          ∙ ⅀Assoc≃-inv-on-canon (B (rA y)) Bᵣ Dᵣ σ

        rE-canon :
          rE y
          ≡ ( fst (equivFun (⟦⅀⟧ (B (rA y)) Bᵣ) (fst σ))
            , invEq (⟦⅀⟧ (Bᵣ (fst (equivFun (⟦⅀⟧ (B (rA y)) Bᵣ)
                                             (fst σ))))
                         (Dᵣ (fst (equivFun (⟦⅀⟧ (B (rA y)) Bᵣ)
                                             (fst σ)))))
                    ( snd (equivFun (⟦⅀⟧ (B (rA y)) Bᵣ) (fst σ))
                    , snd σ))
        rE-canon =
            cong (equivFun (⟦⅀⟧ (B (rA y)) (λ b → ⅀ (Bᵣ b) (Dᵣ b))))
                 invAssoc-eq
          ∙ secEq (⟦⅀⟧ (B (rA y)) (λ b → ⅀ (Bᵣ b) (Dᵣ b)))
                  ( fst (equivFun (⟦⅀⟧ (B (rA y)) Bᵣ) (fst σ))
                  , invEq (⟦⅀⟧ (Bᵣ (fst (equivFun (⟦⅀⟧ (B (rA y)) Bᵣ)
                                                   (fst σ))))
                               (Dᵣ (fst (equivFun (⟦⅀⟧ (B (rA y)) Bᵣ)
                                                   (fst σ)))))
                          ( snd (equivFun (⟦⅀⟧ (B (rA y)) Bᵣ) (fst σ))
                          , snd σ))

        H : Σ[ b ∈ El (B (rA y)) ]
              El (⅀ (C (rA y) b) (D (rA y) b))
          → Σ[ ab ∈ El (⅀ A B) ] El (Bᶜ ab)
        H r =
          ( pf-pair (rA y) (fst r)
          , b''-of (rA y) (fst r)
              (subst (λ ab → El (⅀ (C (fst ab) (snd ab))
                                   (D (fst ab) (snd ab))))
                     (sym (secEq (⟦⅀⟧ A B)
                                 (rA y , fst r)))
                     (snd r)))

        Ggap :
          ⅀Assoc-pentagon-G y
            (fst (invEq Σ-assoc-≃
                        (equivFun (Σ-cong-equiv-snd
                                     (λ a → ⟦⅀⟧ (ALB a) (ALC a)))
                                  (equivFun
                                    (⟦⅀⟧ A (λ a → ⅀ (ALB a) (ALC a)))
                                    y))))
          ≡ H ( fst (equivFun (⟦⅀⟧ (B (rA y)) Bᵣ) (fst σ))
              , invEq (⟦⅀⟧ (Bᵣ (fst (equivFun (⟦⅀⟧ (B (rA y)) Bᵣ)
                                               (fst σ))))
                           (Dᵣ (fst (equivFun (⟦⅀⟧ (B (rA y)) Bᵣ)
                                               (fst σ)))))
                      ( snd (equivFun (⟦⅀⟧ (B (rA y)) Bᵣ) (fst σ))
                      , snd σ))
        Ggap =
          ΣPathP
            ( refl
            , sym (Φ (secEq (⟦⅀⟧ A B)
                            ( rA y
                            , fst (equivFun (⟦⅀⟧ (B (rA y)) Bᵣ)
                                            (fst σ))))
                     (snd (equivFun (⟦⅀⟧ (B (rA y)) Bᵣ) (fst σ)))
                     (snd σ)))

    ⅀Assoc-pentagon-explicit :
      (y : El (⅀ A RGG))
      → ⅀Assoc-pentagon y
      ≡ cong (⅀Assoc-pentagon-G y) (⅀Assoc-pentagon-Py'-secEq y)
        ∙ ⅀Assoc-pentagon-tailR y
    ⅀Assoc-pentagon-explicit y = refl

    -- Module-scope public copies of `⅀Assoc-pentagon-tailR`'s sealed
    -- `where`-binds (`Yr`/`Bᵣ`/`Dᵣ`/`σ`/`rE-canon`/`H`/`Ggap`),
    -- byte-faithful to the originals, so the deep-fibre lemma below can
    -- reduce the `Cnᶜ`-fibre carry over `tailR = Ggap ∙ sym (cong H
    -- rE-canon)` using the `Φ`-kernel directly.
    ⅀p-Yr : (y : El (⅀ A RGG)) → Σ[ a ∈ El A ] El (RGG a)
    ⅀p-Yr y = equivFun (⟦⅀⟧ A RGG) y

    ⅀p-Bᵣ : (y : El (⅀ A RGG)) → El (B (rA y)) → Code
    ⅀p-Bᵣ y = C (rA y)

    ⅀p-Dᵣ : (y : El (⅀ A RGG))
          → (b : El (B (rA y))) → El (C (rA y) b) → Code
    ⅀p-Dᵣ y = D (rA y)

    ⅀p-σ : (y : El (⅀ A RGG))
         → Σ[ ab ∈ El (⅀ (B (rA y)) (⅀p-Bᵣ y)) ]
             El (⅀Assoc-C' (B (rA y)) (⅀p-Bᵣ y) (⅀p-Dᵣ y) ab)
    ⅀p-σ y = equivFun (⟦⅀⟧ (⅀ (B (rA y)) (⅀p-Bᵣ y))
                           (⅀Assoc-C' (B (rA y)) (⅀p-Bᵣ y) (⅀p-Dᵣ y)))
                      (snd (⅀p-Yr y))

    ⅀p-invAssoc-eq :
      (y : El (⅀ A RGG))
      → invEq (⅀Assoc≃ (B (rA y)) (⅀p-Bᵣ y) (⅀p-Dᵣ y)) (snd (⅀p-Yr y))
      ≡ invEq (⟦⅀⟧ (B (rA y)) (λ a → ⅀ (⅀p-Bᵣ y a) (⅀p-Dᵣ y a)))
              ( fst (equivFun (⟦⅀⟧ (B (rA y)) (⅀p-Bᵣ y)) (fst (⅀p-σ y)))
              , invEq (⟦⅀⟧ (⅀p-Bᵣ y (fst (equivFun (⟦⅀⟧ (B (rA y))
                                            (⅀p-Bᵣ y)) (fst (⅀p-σ y)))))
                           (⅀p-Dᵣ y (fst (equivFun (⟦⅀⟧ (B (rA y))
                                            (⅀p-Bᵣ y)) (fst (⅀p-σ y))))))
                      ( snd (equivFun (⟦⅀⟧ (B (rA y)) (⅀p-Bᵣ y))
                                      (fst (⅀p-σ y)))
                      , snd (⅀p-σ y)))
    ⅀p-invAssoc-eq y =
        cong (invEq (⅀Assoc≃ (B (rA y)) (⅀p-Bᵣ y) (⅀p-Dᵣ y)))
             (sym (retEq (⟦⅀⟧ (⅀ (B (rA y)) (⅀p-Bᵣ y))
                              (⅀Assoc-C' (B (rA y)) (⅀p-Bᵣ y) (⅀p-Dᵣ y)))
                         (snd (⅀p-Yr y))))
      ∙ ⅀Assoc≃-inv-on-canon (B (rA y)) (⅀p-Bᵣ y) (⅀p-Dᵣ y) (⅀p-σ y)

    ⅀p-rE-canon :
      (y : El (⅀ A RGG))
      → rE y
      ≡ ( fst (equivFun (⟦⅀⟧ (B (rA y)) (⅀p-Bᵣ y)) (fst (⅀p-σ y)))
        , invEq (⟦⅀⟧ (⅀p-Bᵣ y (fst (equivFun (⟦⅀⟧ (B (rA y))
                                      (⅀p-Bᵣ y)) (fst (⅀p-σ y)))))
                     (⅀p-Dᵣ y (fst (equivFun (⟦⅀⟧ (B (rA y))
                                      (⅀p-Bᵣ y)) (fst (⅀p-σ y))))))
                ( snd (equivFun (⟦⅀⟧ (B (rA y)) (⅀p-Bᵣ y))
                                (fst (⅀p-σ y)))
                , snd (⅀p-σ y)))
    ⅀p-rE-canon y =
        cong (equivFun (⟦⅀⟧ (B (rA y))
                            (λ b → ⅀ (⅀p-Bᵣ y b) (⅀p-Dᵣ y b))))
             (⅀p-invAssoc-eq y)
      ∙ secEq (⟦⅀⟧ (B (rA y)) (λ b → ⅀ (⅀p-Bᵣ y b) (⅀p-Dᵣ y b)))
              ( fst (equivFun (⟦⅀⟧ (B (rA y)) (⅀p-Bᵣ y)) (fst (⅀p-σ y)))
              , invEq (⟦⅀⟧ (⅀p-Bᵣ y (fst (equivFun (⟦⅀⟧ (B (rA y))
                                            (⅀p-Bᵣ y)) (fst (⅀p-σ y)))))
                           (⅀p-Dᵣ y (fst (equivFun (⟦⅀⟧ (B (rA y))
                                            (⅀p-Bᵣ y)) (fst (⅀p-σ y))))))
                      ( snd (equivFun (⟦⅀⟧ (B (rA y)) (⅀p-Bᵣ y))
                                      (fst (⅀p-σ y)))
                      , snd (⅀p-σ y)))

    ⅀p-H : (y : El (⅀ A RGG))
         → Σ[ b ∈ El (B (rA y)) ] El (⅀ (C (rA y) b) (D (rA y) b))
         → Σ[ ab ∈ El (⅀ A B) ] El (Bᶜ ab)
    ⅀p-H y r =
      ( pf-pair (rA y) (fst r)
      , b''-of (rA y) (fst r)
          (subst (λ ab → El (⅀ (C (fst ab) (snd ab))
                               (D (fst ab) (snd ab))))
                 (sym (secEq (⟦⅀⟧ A B) (rA y , fst r)))
                 (snd r)))

    ⅀p-Ggap :
      (y : El (⅀ A RGG))
      → ⅀Assoc-pentagon-G y
          (fst (invEq Σ-assoc-≃
                      (equivFun (Σ-cong-equiv-snd
                                   (λ a → ⟦⅀⟧ (ALB a) (ALC a)))
                                (equivFun
                                  (⟦⅀⟧ A (λ a → ⅀ (ALB a) (ALC a)))
                                  y))))
      ≡ ⅀p-H y
          ( fst (equivFun (⟦⅀⟧ (B (rA y)) (⅀p-Bᵣ y)) (fst (⅀p-σ y)))
          , invEq (⟦⅀⟧ (⅀p-Bᵣ y (fst (equivFun (⟦⅀⟧ (B (rA y))
                                        (⅀p-Bᵣ y)) (fst (⅀p-σ y)))))
                       (⅀p-Dᵣ y (fst (equivFun (⟦⅀⟧ (B (rA y))
                                        (⅀p-Bᵣ y)) (fst (⅀p-σ y))))))
                  ( snd (equivFun (⟦⅀⟧ (B (rA y)) (⅀p-Bᵣ y))
                                  (fst (⅀p-σ y)))
                  , snd (⅀p-σ y)))
    ⅀p-Ggap y =
      ΣPathP
        ( refl
        , sym (Φ (secEq (⟦⅀⟧ A B)
                        ( rA y
                        , fst (equivFun (⟦⅀⟧ (B (rA y)) (⅀p-Bᵣ y))
                                        (fst (⅀p-σ y)))))
                 (snd (equivFun (⟦⅀⟧ (B (rA y)) (⅀p-Bᵣ y))
                                (fst (⅀p-σ y))))
                 (snd (⅀p-σ y))))

    -- The public `tailR` decomposition: `⅀Assoc-pentagon-tailR y` is
    -- definitionally `⅀p-Ggap y ∙ sym (cong (⅀p-H y) (⅀p-rE-canon y))`
    -- (the public copies are byte-faithful to the sealed binds).
    ⅀p-tailR-explicit :
      (y : El (⅀ A RGG))
      → ⅀Assoc-pentagon-tailR y
      ≡ ⅀p-Ggap y ∙ sym (cong (⅀p-H y) (⅀p-rE-canon y))
    ⅀p-tailR-explicit y = refl

    -- The pentagon in `Assoc-cont`-canonical form (the form
    -- `Universe.Assoc` gives every call site).  `Assoc-cont 𝒰 A B C p`
    -- is *definitionally* `invEq ⟦⅀⟧` of `⅀Assoc-pentagon`'s LHS pair
    -- (same `Σ-cong-equiv-fst`/`Σ-assoc-≃` unfold that
    -- `SigmaBridge.canonical-form-on-pair-Σ` is `refl` on), so this is a
    -- thin `cong (invEq ⟦⅀⟧)` wrapper of the proven pentagon.  Lands at
    -- `El (⅀ (⅀ A B) (⅀Assoc-C' A B C))` — the level the `OpM`
    -- pentagon's `pentagon-core` consumes (no Σ-pair split, no fibre
    -- hole).
    ⅀Assoc-pentagon-Acont :
      (y : El (⅀ A RGG))
      → Assoc-cont 𝒰 A B C (Py' y)
      ≡ invEq (⟦⅀⟧ (⅀ A B) (⅀Assoc-C' A B C))
              ( pf-pair (rA y) (fst (rE y))
              , b''-of (rA y) (fst (rE y)) (RW y) )
    ⅀Assoc-pentagon-Acont y =
      cong (invEq (⟦⅀⟧ (⅀ A B) (⅀Assoc-C' A B C))) (⅀Assoc-pentagon y)

    -- ========================================================================
    -- The abstract `Cnᶜ`/`D`-fibre Mac Lane data pentagon over the
    -- VERIFIED Σ-pentagon `⅀Assoc-pentagon`.  `Fcn` is the `Cnᶜ`-fibre
    -- of the pentagon's pair type; route-R's `Cnᶜ`-datum is
    -- `shifted-c''-outer-P` (the abstract analogue of
    -- `SigmaBridge.Fam.shifted-c''-outer` for `Fam A B Bᶜ Cnᶜ`).
    -- ========================================================================
    Fcn : Σ[ ab ∈ El (⅀ A B) ] El (Bᶜ ab) → Type ℓe
    Fcn p = El (Cnᶜ (fst p) (snd p))

    c''-of-P : (a : El A) (b : El (B a)) (w : El (C'-out a b))
             → El (Cnᶜ (pf-pair a b) (b''-of a b w))
    c''-of-P a b w =
      snd (equivFun (⟦⅀⟧ (Bᶜ (pf-pair a b)) (Cnᶜ (pf-pair a b))) w)

    shifted-c''-outer-P :
      (a : El A) (b : El (B a)) (w : El (C'-out a b))
      → El (⅀Assoc-C' (⅀ A B) Bᶜ Cnᶜ
              (invEq (⟦⅀⟧ (⅀ A B) Bᶜ) (pf-pair a b , b''-of a b w)))
    shifted-c''-outer-P a b w =
      subst (λ p → El (Cnᶜ (fst p) (snd p)))
            (sym (secEq (⟦⅀⟧ (⅀ A B) Bᶜ) (pf-pair a b , b''-of a b w)))
            (c''-of-P a b w)

    -- Public base segments of `⅀Assoc-pentagon` (refl-faithful copies,
    -- so `⅀Assoc-pentagon y` is *definitionally* `pL ∙ (pG ∙ pR)`).
    pL-D : (y : El (⅀ A RGG))
         → Path (Σ[ ab ∈ El (⅀ A B) ] El (Bᶜ ab)) _ _
    pL-D y = cong (⅀Assoc-pentagon-G y) (⅀Assoc-pentagon-Py'-secEq y)

    pG-D : (y : El (⅀ A RGG))
         → Path (Σ[ ab ∈ El (⅀ A B) ] El (Bᶜ ab)) _ _
    pG-D y = ⅀p-Ggap y

    pR-D : (y : El (⅀ A RGG))
         → Path (Σ[ ab ∈ El (⅀ A B) ] El (Bᶜ ab)) _ _
    pR-D y = sym (cong (⅀p-H y) (⅀p-rE-canon y))

    -- Structural route-L leg: `Cnᶜ`-fibre carried along the genuine
    -- (non-`refl`) midpoint `cong G Py'-secEq`.
    ⅀p-D-legL :
      (y : El (⅀ A RGG)) (dL : Fcn (⅀Assoc-pentagon y i0))
      → PathP (λ i → Fcn (pL-D y i)) dL (subst Fcn (pL-D y) dL)
    ⅀p-D-legL y dL = subst-filler Fcn (pL-D y) dL

    -- Structural route-R leg: `Cnᶜ`-fibre carried along the genuine
    -- (non-`refl`) midpoint `sym (cong H rE-canon)`.
    ⅀p-D-legR :
      (y : El (⅀ A RGG)) (m : Fcn (pG-D y i1))
      → PathP (λ i → Fcn (pR-D y i)) m (subst Fcn (pR-D y) m)
    ⅀p-D-legR y m = subst-filler Fcn (pR-D y) m

    -- The `Φ`/`ΦΣ` instantiation `⅀p-Ggap y` uses (refl-faithful copies
    -- of the inline `secEq`/`snd`-destructurings in `⅀p-Ggap`'s body).
    ⅀p-GgT : (y : El (⅀ A RGG))
           → Path (Σ[ a ∈ El A ] El (B a)) _ _
    ⅀p-GgT y =
      secEq (⟦⅀⟧ A B)
            ( rA y
            , fst (equivFun (⟦⅀⟧ (B (rA y)) (⅀p-Bᵣ y)) (fst (⅀p-σ y))))

    ⅀p-Ggu : (y : El (⅀ A RGG))
           → El (C (rA y)
                   (fst (equivFun (⟦⅀⟧ (B (rA y)) (⅀p-Bᵣ y))
                                  (fst (⅀p-σ y)))))
    ⅀p-Ggu y = snd (equivFun (⟦⅀⟧ (B (rA y)) (⅀p-Bᵣ y)) (fst (⅀p-σ y)))

    ⅀p-Ggv : (y : El (⅀ A RGG))
           → El (D (rA y)
                   (fst (equivFun (⟦⅀⟧ (B (rA y)) (⅀p-Bᵣ y))
                                  (fst (⅀p-σ y))))
                   (⅀p-Ggu y))
    ⅀p-Ggv y = snd (⅀p-σ y)

    -- `⅀p-Ggap y` is *definitionally* `ΣPathP (refl , sym (Φ T u v))`.
    _⅀p-Ggap-explicit :
      (y : El (⅀ A RGG))
      → ⅀p-Ggap y
      ≡ ΣPathP (refl , sym (Φ (⅀p-GgT y) (⅀p-Ggu y) (⅀p-Ggv y)))
    _⅀p-Ggap-explicit y = refl

    -- The two explicit `Ggap`-leg endpoints (route-R-side `subst (sym T)`
    -- Σ-snd; route-L-side `equivFun ⟦⅀⟧`-of-`subst (sym T)` Σ-snd).
    ⅀p-DLegG-i0 :
      (y : El (⅀ A RGG))
      → El (D (fst (⅀p-GgT y i0)) (snd (⅀p-GgT y i0))
              (subst (λ x → El (C (fst x) (snd x))) (sym (⅀p-GgT y))
                     (⅀p-Ggu y)))
    ⅀p-DLegG-i0 y =
      snd (subst (λ x → Σ[ c ∈ El (C (fst x) (snd x)) ]
                          El (D (fst x) (snd x) c))
                 (sym (⅀p-GgT y))
                 (⅀p-Ggu y , ⅀p-Ggv y))

    ⅀p-DLegG-i1 :
      (y : El (⅀ A RGG))
      → El (D (fst (⅀p-GgT y i0)) (snd (⅀p-GgT y i0))
              (fst (equivFun (⟦⅀⟧ (C (fst (⅀p-GgT y i0))
                                       (snd (⅀p-GgT y i0)))
                                  (D (fst (⅀p-GgT y i0))
                                       (snd (⅀p-GgT y i0))))
                             (subst (λ x → El (⅀ (C (fst x) (snd x))
                                                 (D (fst x) (snd x))))
                                    (sym (⅀p-GgT y))
                                    (invEq (⟦⅀⟧ (C (fst (⅀p-GgT y i1))
                                                     (snd (⅀p-GgT y i1)))
                                                (D (fst (⅀p-GgT y i1))
                                                     (snd (⅀p-GgT y i1))))
                                           (⅀p-Ggu y , ⅀p-Ggv y))))))
    ⅀p-DLegG-i1 y =
      snd (equivFun (⟦⅀⟧ (C (fst (⅀p-GgT y i0))
                              (snd (⅀p-GgT y i0)))
                         (D (fst (⅀p-GgT y i0))
                              (snd (⅀p-GgT y i0))))
                    (subst (λ x → El (⅀ (C (fst x) (snd x))
                                        (D (fst x) (snd x))))
                           (sym (⅀p-GgT y))
                           (invEq (⟦⅀⟧ (C (fst (⅀p-GgT y i1))
                                            (snd (⅀p-GgT y i1)))
                                       (D (fst (⅀p-GgT y i1))
                                            (snd (⅀p-GgT y i1))))
                                  (⅀p-Ggu y , ⅀p-Ggv y))))

    -- The genuine `D`-fibre carry over the `Ggap` move: the `Cnᶜ`-fibre
    -- `PathP` over `⅀p-Ggap y = ΣPathP (refl , sym (Φ T u v))` is the
    -- `snd`-component of the VERIFIED `ΦΣ T u v`, re-based onto `Φ` via
    -- the VERIFIED wire `Φ≡fstΦΣ` (NOT a `subst-filler`: both endpoints
    -- are the explicit `equivFun ⟦⅀⟧`/`subst (sym T)` Σ-images).
    ⅀p-D-legG :
      (y : El (⅀ A RGG))
      → PathP (λ i → Fcn (⅀p-Ggap y i))
              (⅀p-DLegG-i0 y)
              (⅀p-DLegG-i1 y)
    ⅀p-D-legG y =
      symP
        (subst
          (λ φ → PathP
                   (λ i → El (D (fst (⅀p-GgT y i0)) (snd (⅀p-GgT y i0))
                                (φ i)))
                   (snd (equivFun (⟦⅀⟧ (C (fst (⅀p-GgT y i0))
                                            (snd (⅀p-GgT y i0)))
                                       (D (fst (⅀p-GgT y i0))
                                            (snd (⅀p-GgT y i0))))
                                  (subst (λ x → El (⅀ (C (fst x) (snd x))
                                                      (D (fst x) (snd x))))
                                         (sym (⅀p-GgT y))
                                         (invEq (⟦⅀⟧ (C (fst (⅀p-GgT y i1))
                                                          (snd (⅀p-GgT y i1)))
                                                     (D (fst (⅀p-GgT y i1))
                                                          (snd (⅀p-GgT y i1))))
                                                (⅀p-Ggu y , ⅀p-Ggv y)))))
                   (snd (subst (λ x → Σ[ c ∈ El (C (fst x) (snd x)) ]
                                        El (D (fst x) (snd x) c))
                               (sym (⅀p-GgT y))
                               (⅀p-Ggu y , ⅀p-Ggv y))))
          (sym (Φ≡fstΦΣ (⅀p-GgT y) (⅀p-Ggu y) (⅀p-Ggv y)))
          (cong snd (ΦΣ (⅀p-GgT y) (⅀p-Ggu y) (⅀p-Ggv y))))

    -- The abstract `Cnᶜ`/`D`-fibre Mac Lane data pentagon: the
    -- `Cnᶜ`-fibre carries along the VERIFIED Σ-pentagon
    -- `⅀Assoc-pentagon y` (`= cong G Py'-secEq ∙ (⅀p-Ggap ∙ sym (cong
    -- ⅀p-H ⅀p-rE-canon))` definitionally) by `compPathP'` of: the
    -- structural route-L leg (`subst-filler` over the genuine
    -- non-`refl` midpoint `cong G Py'-secEq`); the genuine `ΦΣ`-snd
    -- `Ggap` carry `⅀p-D-legG`; the structural route-R leg
    -- (`subst-filler` over `sym (cong ⅀p-H ⅀p-rE-canon)`).  Endpoints:
    -- route-L's `⅀p-DLegG-i0` carried back through `cong G Py'-secEq`,
    -- and route-R's `⅀p-DLegG-i1` carried through `sym (cong ⅀p-H
    -- ⅀p-rE-canon)`.
    -- `⅀Assoc-pentagon y` *definitionally* `= pL-D ∙ (pG-D ∙ pR-D)`
    -- (`⅀Assoc-pentagon-explicit`/`⅀p-tailR-explicit` are `refl`).
    D-dec :
      (y : El (⅀ A RGG))
      → ⅀Assoc-pentagon y ≡ pL-D y ∙ (pG-D y ∙ pR-D y)
    D-dec y =
        ⅀Assoc-pentagon-explicit y
      ∙ cong (pL-D y ∙_) (⅀p-tailR-explicit y)

    ⅀Assoc-pentagon-D-raw :
      (y : El (⅀ A RGG))
      → PathP (λ i → Fcn ((pL-D y ∙ (pG-D y ∙ pR-D y)) i))
              (subst Fcn (sym (pL-D y)) (⅀p-DLegG-i0 y))
              (subst Fcn (pR-D y) (⅀p-DLegG-i1 y))
    ⅀Assoc-pentagon-D-raw y =
      compPathP' {B = Fcn} {p = pL-D y} {q = pG-D y ∙ pR-D y}
        (symP (subst-filler Fcn (sym (pL-D y)) (⅀p-DLegG-i0 y)))
        (compPathP' {B = Fcn} {p = pG-D y} {q = pR-D y}
          (⅀p-D-legG y)
          (subst-filler Fcn (pR-D y) (⅀p-DLegG-i1 y)))

    ⅀Assoc-pentagon-D :
      (y : El (⅀ A RGG))
      → PathP (λ i → Fcn (⅀Assoc-pentagon y i))
              (subst Fcn (sym (pL-D y)) (⅀p-DLegG-i0 y))
              (subst Fcn (pR-D y) (⅀p-DLegG-i1 y))
    ⅀Assoc-pentagon-D y =
      subst (λ q → PathP (λ i → Fcn (q i))
                      (subst Fcn (sym (pL-D y)) (⅀p-DLegG-i0 y))
                      (subst Fcn (pR-D y) (⅀p-DLegG-i1 y)))
            (sym (D-dec y))
            (⅀Assoc-pentagon-D-raw y)

    -- The `fromPathP` transport equation (the form the `OpM` pentagon's
    -- deep `Cnᶜ`-fibre obligation consumes after the verified
    -- `_probe-seg3-Cnᶜ`/`FL1-canon` bridge).
    ⅀Assoc-pentagon-D-eq :
      (y : El (⅀ A RGG))
      → transport (λ i → Fcn (⅀Assoc-pentagon y i))
                  (subst Fcn (sym (pL-D y)) (⅀p-DLegG-i0 y))
      ≡ subst Fcn (pR-D y) (⅀p-DLegG-i1 y)
    ⅀Assoc-pentagon-D-eq y =
      fromPathP {A = λ i → Fcn (⅀Assoc-pentagon y i)}
        (⅀Assoc-pentagon-D y)

    -- Abstract route-R endpoint identification: the `Ggap`-i1 datum
    -- carried back over `sym (cong ⅀p-H ⅀p-rE-canon)` is route-R's
    -- `c''-of-P` (= `snd (equivFun ⟦⅀⟧ (RW y))`).
    ⅀p-D-Rend :
      (y : El (⅀ A RGG))
      → subst Fcn (pR-D y) (⅀p-DLegG-i1 y)
      ≡ c''-of-P (rA y) (fst (rE y)) (RW y)
    ⅀p-D-Rend y =
        cong (subst Fcn (sym K))
             (sym (fromPathP {A = λ i → Fcn (K i)} cong-c''-path))
      ∙ subst⁻Subst Fcn K (c''-of-P (rA y) (fst (rE y)) (RW y))
      where
        K : Path (Σ[ ab ∈ El (⅀ A B) ] El (Bᶜ ab)) _ _
        K = cong (⅀p-H y) (⅀p-rE-canon y)

        cong-c''-path :
          PathP (λ i → Fcn (K i))
                (c''-of-P (rA y) (fst (rE y)) (RW y))
                (⅀p-DLegG-i1 y)
        cong-c''-path i =
          c''-of-P (rA y) (fst (⅀p-rE-canon y i))
            (subst (λ ab → El (⅀ (C (fst ab) (snd ab))
                                 (D (fst ab) (snd ab))))
                   (sym (secEq (⟦⅀⟧ A B)
                               (rA y , fst (⅀p-rE-canon y i))))
                   (snd (⅀p-rE-canon y i)))
