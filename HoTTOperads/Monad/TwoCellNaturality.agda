{-# OPTIONS --cubical --no-import-sorts #-}
-- ============================================================================
-- HoTTOperads.Monad.TwoCellNaturality
--
-- Naturality of the monad law 2-cells in the carrier (paper §8 Thm 8.2):
-- for every map f, the functorial image of each law component is the
-- component at the mapped argument:
--
--   join-return₁-fmap : cong (f <$>_) (join-return₁ x) ≡ join-return₁ (f <$> x)
--   join-return₂-fmap : cong (f <$>_) (join-return₂ x) ≡ join-return₂ (f <$> x)
--   join-assoc-fmap   : cong (f <$>_) (join-assoc z)
--                     ≡ join-assoc ((_<$>_ (_<$>_ f)) <$> z)
--
-- These make the unitors and the associator modifications, completing the
-- 2-monad structure together with the unit triangle and the pentagon.
--
-- All three go through OpM-path-ext: two parallel `OpM` paths are equal
-- given a 2-cell of their `Index` components and pointwise agreement of
-- their `Data` evaluations along traces (trace spaces are propositions by
-- `isSetEl`).  The `Data` agreements close in sets: both evaluations are
-- images of parallel paths in an El-set (unitors: `unglue-subst-eval`) or
-- in the stage triple set (associator: `Stage.evalBareᶜ`).
--
-- Hypothesis: `isSetEl`.  The carriers are arbitrary types.
-- ============================================================================
module HoTTOperads.Monad.TwoCellNaturality where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.HLevels using (isSet→SquareP ; isSetΣ)
open import Cubical.Data.Sigma using (Σ ; _,_ ; fst ; snd)

open import HoTTOperads.Universe.Base
open import HoTTOperads.Operad.Base
open import HoTTOperads.Monad.Base
open import HoTTOperads.Monad.Composition using (return ; join)
open import HoTTOperads.Monad.Functor using (_<$>_)
open import HoTTOperads.Monad.Laws using
  (join-return₁ ; join-return₂ ; join-assoc)
open import HoTTOperads.Universe.Homog using (module GH)
import HoTTOperads.Monad.PointwisePentagon as PP
open import HoTTOperads.PathTrace using
  (funPathP-ext ; fun-line-transport-eval ; unglue-subst-eval)

private variable ℓc ℓe ℓk ℓx ℓy : Level

module _ {𝒰 : Universe ℓc ℓe} {K : Universe.Code 𝒰 → Type ℓk}
         (O : Operad 𝒰 K)
         (isSetEl : (Z : Universe.Code 𝒰) → isSet (Universe.El 𝒰 Z)) where
  open Universe 𝒰
  open Operad O using (isSetK)

  -- ==========================================================================
  -- Parallel `OpM` paths are equal given an `Index` 2-cell and pointwise
  -- `Data` agreement along traces (the trace-extensionality reduction).
  -- ==========================================================================
  OpM-path-ext :
    {Y : Type ℓx} {u v : OpM O Y} (p q : u ≡ v)
    (idx2 : cong Index p ≡ cong Index q)
    (dataPtw : {x₀ : El (Index u)} {x₁ : El (Index v)}
               (γp : PathP (λ i → El (Index (p i))) x₀ x₁)
               (γq : PathP (λ i → El (Index (q i))) x₀ x₁)
             → Path (Path Y (Data u x₀) (Data v x₁))
                    (λ i → Data (p i) (γp i))
                    (λ i → Data (q i) (γq i)))
    → p ≡ q
  OpM-path-ext {Y = Y} {u = u} {v = v} p q idx2 dataPtw j i =
    idx2 j i ▷ opSq j i ▷ dataSq j i
    where
      opSq : SquareP (λ j i → K (idx2 j i))
                     (cong Op p) (cong Op q) (λ _ → Op u) (λ _ → Op v)
      opSq = isSet→SquareP (λ j i → isSetK (idx2 j i))
                           (cong Op p) (cong Op q) (λ _ → Op u) (λ _ → Op v)

      dataSq : SquareP (λ j i → El (idx2 j i) → Y)
                       (cong Data p) (cong Data q) refl refl
      dataSq = toPathP
        (funPathP-ext
          (transport (λ t → PathP (λ i → El (idx2 t i) → Y) (Data u) (Data v))
                     (cong Data p))
          (cong Data q)
          (λ {x₀} {x₁} γ →
              fun-line-transport-eval isSetEl idx2 (cong Data p)
                (transport (λ t → PathP (λ i → El (idx2 (~ t) i)) x₀ x₁) γ) γ
            ∙ dataPtw
                (transport (λ t → PathP (λ i → El (idx2 (~ t) i)) x₀ x₁) γ) γ))

  module _ {X : Type ℓx} {Y : Type ℓy} (f : X → Y) where

    -- ========================================================================
    -- Unitor naturality.  Under `unfolding`, both `Index` components are
    -- the same `Inj` edge (idx2 = refl), and both `Data` evaluations are
    -- `unglue-subst-eval` images of parallel paths in an El-set.
    -- ========================================================================
    opaque
      unfolding join-return₁ join-return₂

      join-return₁-fmap : (x : OpM O X)
        → cong (_<$>_ f) (join-return₁ O x) ≡ join-return₁ O (f <$> x)
      join-return₁-fmap x =
        OpM-path-ext (cong (_<$>_ f) (join-return₁ O x))
                     (join-return₁ O (f <$> x)) refl dataPtw
        where
          I' : Code
          I' = Index x

          e : El (⅀ 𝜏 (λ _ → I')) ≃ El I'
          e = ⅀Idl≃ I'

          D : El I' → X
          D = Data x

          dataPtw : {x₀ : El (⅀ 𝜏 (λ _ → I'))} {x₁ : El I'}
                    (γp : PathP (λ i → El (Inj e i)) x₀ x₁)
                    (γq : PathP (λ i → El (Inj e i)) x₀ x₁)
                  → Path (Path Y (f (D (equivFun e x₀))) (f (D x₁)))
                         (λ i → Data (cong (_<$>_ f) (join-return₁ O x) i) (γp i))
                         (λ i → Data (join-return₁ O (f <$> x) i) (γq i))
          dataPtw {x₀ = x₀} {x₁ = x₁} γp γq = step1 ∙ step2 ∙ step3
            where
              νp : equivFun e x₀ ≡ x₁
              νp = (λ i → ua-unglue e i (transport-filler (ua e) x₀ i))
                 ∙ (λ k → transport (⟦⅀Idl⟧ I' k) x₀)
                 ∙ fromPathP γp

              νq : equivFun e x₀ ≡ x₁
              νq = (λ i → ua-unglue e i (transport-filler (ua e) x₀ i))
                 ∙ (λ k → transport (⟦⅀Idl⟧ I' k) x₀)
                 ∙ fromPathP γq

              step1 : Path (Path Y (f (D (equivFun e x₀))) (f (D x₁)))
                           (λ i → Data (cong (_<$>_ f) (join-return₁ O x) i) (γp i))
                           (cong (λ s → f (D s)) νp)
              step1 = cong (cong f)
                           (unglue-subst-eval (isSetEl I') e D (⟦⅀Idl⟧ I') γp)

              step2 : Path (Path Y (f (D (equivFun e x₀))) (f (D x₁)))
                           (cong (λ s → f (D s)) νp)
                           (cong (λ s → f (D s)) νq)
              step2 = cong (cong (λ s → f (D s))) (isSetEl I' _ _ νp νq)

              step3 : Path (Path Y (f (D (equivFun e x₀))) (f (D x₁)))
                           (cong (λ s → f (D s)) νq)
                           (λ i → Data (join-return₁ O (f <$> x) i) (γq i))
              step3 = sym (unglue-subst-eval (isSetEl I') e (λ s → f (D s))
                                             (⟦⅀Idl⟧ I') γq)

      join-return₂-fmap : (x : OpM O X)
        → cong (_<$>_ f) (join-return₂ O x) ≡ join-return₂ O (f <$> x)
      join-return₂-fmap x =
        OpM-path-ext (cong (_<$>_ f) (join-return₂ O x))
                     (join-return₂ O (f <$> x)) refl dataPtw
        where
          I' : Code
          I' = Index x

          e : El (⅀ I' (λ _ → 𝜏)) ≃ El I'
          e = ⅀Idr≃ I'

          D : El I' → X
          D = Data x

          dataPtw : {x₀ : El (⅀ I' (λ _ → 𝜏))} {x₁ : El I'}
                    (γp : PathP (λ i → El (Inj e i)) x₀ x₁)
                    (γq : PathP (λ i → El (Inj e i)) x₀ x₁)
                  → Path (Path Y (f (D (equivFun e x₀))) (f (D x₁)))
                         (λ i → Data (cong (_<$>_ f) (join-return₂ O x) i) (γp i))
                         (λ i → Data (join-return₂ O (f <$> x) i) (γq i))
          dataPtw {x₀ = x₀} {x₁ = x₁} γp γq = step1 ∙ step2 ∙ step3
            where
              νp : equivFun e x₀ ≡ x₁
              νp = (λ i → ua-unglue e i (transport-filler (ua e) x₀ i))
                 ∙ (λ k → transport (⟦⅀Idr⟧ I' k) x₀)
                 ∙ fromPathP γp

              νq : equivFun e x₀ ≡ x₁
              νq = (λ i → ua-unglue e i (transport-filler (ua e) x₀ i))
                 ∙ (λ k → transport (⟦⅀Idr⟧ I' k) x₀)
                 ∙ fromPathP γq

              step1 : Path (Path Y (f (D (equivFun e x₀))) (f (D x₁)))
                           (λ i → Data (cong (_<$>_ f) (join-return₂ O x) i) (γp i))
                           (cong (λ s → f (D s)) νp)
              step1 = cong (cong f)
                           (unglue-subst-eval (isSetEl I') e D (⟦⅀Idr⟧ I') γp)

              step2 : Path (Path Y (f (D (equivFun e x₀))) (f (D x₁)))
                           (cong (λ s → f (D s)) νp)
                           (cong (λ s → f (D s)) νq)
              step2 = cong (cong (λ s → f (D s))) (isSetEl I' _ _ νp νq)

              step3 : Path (Path Y (f (D (equivFun e x₀))) (f (D x₁)))
                           (cong (λ s → f (D s)) νq)
                           (λ i → Data (join-return₂ O (f <$> x) i) (γq i))
              step3 = sym (unglue-subst-eval (isSetEl I') e (λ s → f (D s))
                                             (⟦⅀Idr⟧ I') γq)

    -- ========================================================================
    -- Associator naturality.  The `Index` 2-cell comes from the exposed
    -- aux paths (both sides' `Inj` edges coincide); both `Data`
    -- evaluations are stage-line images of parallel paths in the (shared)
    -- stage triple set.
    -- ========================================================================
    join-assoc-fmap : (z : OpM O (OpM O (OpM O X)))
      → cong (_<$>_ f) (join-assoc O z)
      ≡ join-assoc O ((_<$>_ (_<$>_ f)) <$> z)
    join-assoc-fmap z =
      OpM-path-ext (cong (_<$>_ f) (join-assoc O z))
                   (join-assoc O ((_<$>_ (_<$>_ f)) <$> z)) idx2 dataPtw
      where
        zf : OpM O (OpM O (OpM O Y))
        zf = (_<$>_ (_<$>_ f)) <$> z

        module Sz = PP.Stage O isSetEl z
        module Szf = PP.Stage O isSetEl zf

        idx2 : cong Index (cong (_<$>_ f) (join-assoc O z))
             ≡ cong Index (join-assoc O zf)
        idx2 = cong (cong Index) Sz.jas ∙ sym (cong (cong Index) Szf.jas)

        isSetT³z : isSet (GH.T³ {𝒰 = 𝒰} Sz.I' Sz.Jf Sz.Mf Sz.Fz)
        isSetT³z = isSetΣ (isSetEl Sz.I')
                     (λ a → isSetΣ (isSetEl (Sz.Jf a))
                                   (λ b → isSetEl (Sz.Mf a b)))

        dataPtw : {x₀ : El (Index (join O (join O z)))}
                  {x₁ : El (Index (join O ((join O) <$> z)))}
                  (γp : PathP (λ i → El (Index (cong (_<$>_ f) (join-assoc O z) i))) x₀ x₁)
                  (γq : PathP (λ i → El (Index (join-assoc O zf i))) x₀ x₁)
                → Path (Path Y (f (Data (join O (join O z)) x₀))
                               (f (Data (join O ((join O) <$> z)) x₁)))
                       (λ i → Data (cong (_<$>_ f) (join-assoc O z) i) (γp i))
                       (λ i → Data (join-assoc O zf i) (γq i))
        dataPtw {x₀ = x₀} {x₁ = x₁} γp γq = step1 ∙ step2 ∙ step3
          where
            EndT : Type _
            EndT = Path (Path Y (f (Data (join O (join O z)) x₀))
                                (f (Data (join O ((join O) <$> z)) x₁)))
                        (λ i → Data (cong (_<$>_ f) (join-assoc O z) i) (γp i))
                        (λ i → Data (join-assoc O zf i) (γq i))

            step1 : Path (Path Y (f (Data (join O (join O z)) x₀))
                                 (f (Data (join O ((join O) <$> z)) x₁)))
                         (λ i → Data (cong (_<$>_ f) (join-assoc O z) i) (γp i))
                         (sym (cong (λ t → f (Sz.F̂z t)) (Sz.M (Sz.canonβ γp))))
            step1 = cong (cong f) (Sz.evalBareᶜ γp)

            step2 : Path (Path Y (f (Data (join O (join O z)) x₀))
                                 (f (Data (join O ((join O) <$> z)) x₁)))
                         (sym (cong (λ t → f (Sz.F̂z t)) (Sz.M (Sz.canonβ γp))))
                         (sym (cong (λ t → f (Sz.F̂z t)) (Szf.M (Szf.canonβ γq))))
            step2 = cong (λ m → sym (cong (λ t → f (Sz.F̂z t)) m))
                         (isSetT³z _ _ (Sz.M (Sz.canonβ γp)) (Szf.M (Szf.canonβ γq)))

            step3 : Path (Path Y (f (Data (join O (join O z)) x₀))
                                 (f (Data (join O ((join O) <$> z)) x₁)))
                         (sym (cong (λ t → f (Sz.F̂z t)) (Szf.M (Szf.canonβ γq))))
                         (λ i → Data (join-assoc O zf i) (γq i))
            step3 = sym (Szf.evalBareᶜ γq)
