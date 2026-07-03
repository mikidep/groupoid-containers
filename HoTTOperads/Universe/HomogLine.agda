{-# OPTIONS --cubical --no-import-sorts #-}
-- The traced-line characterization of the canonical L1 carrier: the
-- pointwise Code-path traced by `gen-data-path dNR₀ dNL₀ hg₀` along the
-- Inj-transport filler is `funExt⁻ hg₀ x'` followed by a `cong dNL₀`
-- correction whose argument is a path in an El-set — hence (isSetEl)
-- interchangeable with the canonical `transport-Inj-⅀Assoc` bridge.
--
-- Chain: gen-data-path = subst(⟦⅀Assoc⟧)(gen-path-ua)  [definitional]
--   → subst-line (J on ⟦⅀Assoc⟧) → ◁-line (gen-path-ua = hg₀ ◁ unglue)
--   → ∙assoc + congFunct⁻¹ + isSetEl-swap of the El-set residue.

module HoTTOperads.Universe.HomogLine where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.GroupoidLaws using (congFunct) renaming (assoc to ∙assoc)
open import Cubical.Data.Sigma using (fst ; snd ; _,_ ; Σ ; Σ-syntax)

open import HoTTOperads.Universe.Base
open import HoTTOperads.Universe.PentagonDep using
  (dNR₀ ; dNL₀ ; gen-data-path ; gen-path-ua ; transport-Inj-⅀Assoc)
open import HoTTOperads.Universe.Homog using (module GH ; hg₀)
open import HoTTOperads.PathTrace using (◁-line ; subst-line)

private variable ℓc ℓe ℓt : Level

-- ============================================================================
-- T-parametric traced line: for ANY codomain T and carrier interface
-- (dNR , dNL , hg), the line traced by `gen-data-path dNR dNL hg` along the
-- Inj-transport filler is `funExt⁻ hg` followed by the `cong dNL` image of
-- the explicit unglue/⟦⅀Assoc⟧ element path (`glue-tail`).  No h-level
-- hypotheses; the chain is subst-line → ◁-line → ∙assoc → congFunct⁻¹.
-- ============================================================================
module _ {𝒰 : Universe ℓc ℓe} where
  open Universe 𝒰

  module _ (A : Code) (B : El A → Code)
           (C : (a : El A) → El (B a) → Code) where

    private
      e' = ⅀Assoc≃ A B C

    glue-tail : (x' : El (⅀ A (λ a → ⅀ (B a) (C a))))
              → equivFun e' x' ≡ transport (cong El (Inj e')) x'
    glue-tail x' =
        (λ i → ua-unglue e' i (transport-filler (ua e') x' i))
      ∙ (λ k → transport (⟦⅀Assoc⟧ A B C k) x')

    gen-line-eq :
      {T : Type ℓt}
      (dNR : El (⅀ A (λ a → ⅀ (B a) (C a))) → T)
      (dNL : El (⅀ (⅀ A B) (⅀Assoc-C' A B C)) → T)
      (hg : dNR ≡ dNL ∘ equivFun e')
      (x' : El (⅀ A (λ a → ⅀ (B a) (C a))))
      → (λ i → gen-data-path {𝒰 = 𝒰} A B C dNR dNL hg i
                 (transport-filler (cong El (Inj e')) x' i))
      ≡ funExt⁻ hg x' ∙ cong dNL (glue-tail x')
    gen-line-eq {T = T} dNR dNL hg x' =
        subst-line (ua e') (gen-path-ua {𝒰 = 𝒰} A B C dNR dNL hg)
                   (cong El (Inj e')) (⟦⅀Assoc⟧ A B C) x'
      ∙ cong (_∙ cong dNL (λ k → transport (⟦⅀Assoc⟧ A B C k) x'))
             (◁-line hg (λ i el → dNL (ua-unglue e' i el))
                     (transport-filler (ua e') x'))
      ∙ sym (∙assoc (funExt⁻ hg x')
                    (λ i → dNL (ua-unglue e' i (transport-filler (ua e') x' i)))
                    (cong dNL (λ k → transport (⟦⅀Assoc⟧ A B C k) x')))
      ∙ cong (funExt⁻ hg x' ∙_)
             (sym (congFunct dNL
                     (λ i → ua-unglue e' i (transport-filler (ua e') x' i))
                     (λ k → transport (⟦⅀Assoc⟧ A B C k) x')))

module _ {𝒰 : Universe ℓc ℓe}
         (isSetEl : (Z : Universe.Code 𝒰) → isSet (Universe.El 𝒰 Z)) where
  open Universe 𝒰

  module _ (A : Code) (B : El A → Code)
           (C : (a : El A) → El (B a) → Code)
           (D : (a : El A) (b : El (B a)) → El (C a b) → Code) where

    private
      e = ⅀Assoc≃ A B C
      hg0 = hg₀ {𝒰 = 𝒰} A B C D
      gdp0 : PathP (λ i → El (Inj e i) → Code)
                   (dNR₀ {𝒰 = 𝒰} A B C D) (dNL₀ {𝒰 = 𝒰} A B C D)
      gdp0 = gen-data-path {𝒰 = 𝒰} A B C
                           (dNR₀ {𝒰 = 𝒰} A B C D) (dNL₀ {𝒰 = 𝒰} A B C D) hg0

    -- The canonical bridge from the equivalence-action to the Inj-transport
    -- (an element path in the El-set of the ⅀Assoc≃-codomain).
    inj-bridge : (x' : El (⅀ A (λ a → ⅀ (B a) (C a))))
               → equivFun e x' ≡ transport (cong El (Inj e)) x'
    inj-bridge x' = sym (funExt⁻ (transport-Inj-⅀Assoc {𝒰 = 𝒰} A B C) x')

    -- C1: the traced gdp₀-line is hg₀-pointwise followed by the bridge.
    gdp-line-eq : (x' : El (⅀ A (λ a → ⅀ (B a) (C a))))
      → (λ i → gdp0 i (transport-filler (cong El (Inj e)) x' i))
      ≡ funExt⁻ hg0 x'
        ∙ cong (dNL₀ {𝒰 = 𝒰} A B C D) (inj-bridge x')
    gdp-line-eq x' =
        subst-line (ua e)
                   (gen-path-ua {𝒰 = 𝒰} A B C
                                (dNR₀ {𝒰 = 𝒰} A B C D)
                                (dNL₀ {𝒰 = 𝒰} A B C D) hg0)
                   (cong El (Inj e)) (⟦⅀Assoc⟧ A B C) x'
      ∙ cong (_∙ cong (dNL₀ {𝒰 = 𝒰} A B C D) (λ k → transport (⟦⅀Assoc⟧ A B C k) x'))
             (◁-line hg0
                     (λ i el → dNL₀ {𝒰 = 𝒰} A B C D (ua-unglue e i el))
                     (transport-filler (ua e) x'))
      ∙ sym (∙assoc (funExt⁻ hg0 x')
                    (λ i → dNL₀ {𝒰 = 𝒰} A B C D
                             (ua-unglue e i (transport-filler (ua e) x' i)))
                    (cong (dNL₀ {𝒰 = 𝒰} A B C D) (λ k → transport (⟦⅀Assoc⟧ A B C k) x')))
      ∙ cong (funExt⁻ hg0 x' ∙_)
             ( sym (congFunct (dNL₀ {𝒰 = 𝒰} A B C D)
                              (λ i → ua-unglue e i (transport-filler (ua e) x' i))
                              (λ k → transport (⟦⅀Assoc⟧ A B C k) x'))
             ∙ cong (cong (dNL₀ {𝒰 = 𝒰} A B C D))
                    (isSetEl (⅀ (⅀ A B) (⅀Assoc-C' A B C)) _ _
                       ( (λ i → ua-unglue e i (transport-filler (ua e) x' i))
                       ∙ (λ k → transport (⟦⅀Assoc⟧ A B C k) x'))
                       (inj-bridge x')) )
