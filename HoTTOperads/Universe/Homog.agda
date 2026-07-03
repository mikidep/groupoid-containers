{-# OPTIONS --cubical --no-import-sorts #-}
-- The canonical homogeneity coherence for the universe associator: for any
-- T-valued leaf decoration F over (A , B , C), the two Σ-shuffle readings
-- (gNR / gNL) agree along `equivFun (⅀Assoc≃ A B C)` via two secEq slides.
-- The slides are paths in the triple space T³ = Σ a (Σ b (El (C a b))),
-- with the coherence their cong-F̂ composite; T³ is a set whenever El is a
-- family of sets, which is what lets El-valued consumers settle transport
-- equations by base-path equality in T³.
--
-- At T := Code, F := D this is the canonical hg₀ : dNR₀ ≡ dNL₀ ∘ eqv that
-- the OpM pentagon instantiates: `Monad.Laws.JoinAssocAux.homog` is this
-- construction verbatim (at X, the deep data reading), and
-- `cong (Index ∘_)` carries it to hg₀ by `ghomog-natural` at g := Index.
-- The dependent pentagon (PentagonDepProof) holds at hg₀; the analogous
-- statement at an arbitrary hg is false in universes with nontrivial
-- El-automorphisms (an hg-wiggle moves the gdp-twisted side only).

module HoTTOperads.Universe.Homog where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.GroupoidLaws using (congFunct)
open import Cubical.Data.Sigma using (fst ; snd ; _,_ ; Σ ; Σ-syntax)

open import HoTTOperads.Universe.Base
open import HoTTOperads.Universe.PentagonDep using (dNR₀ ; dNL₀)

private variable ℓc ℓe ℓt ℓt' : Level

module _ {𝒰 : Universe ℓc ℓe} where
  open Universe 𝒰

  module GH (A : Code) (B : El A → Code)
            (C : (a : El A) → El (B a) → Code)
            {T : Type ℓt}
            (F : (a : El A) (b : El (B a)) → El (C a b) → T) where

    -- The triple set of leaf positions, and the leaf decoration over it.
    -- Both slides below are paths IN T³ (cong-F̂ images give the steps),
    -- which is what lets El-valued consumers rewrite every transport as
    -- a subst over T³ (a set whenever El is a family of sets).
    T³ : Type ℓe
    T³ = Σ[ a ∈ El A ] Σ[ b ∈ El (B a) ] El (C a b)

    F̂ : T³ → T
    F̂ t = F (fst t) (fst (snd t)) (snd (snd t))

    readNR : El (⅀ A (λ a → ⅀ (B a) (C a))) → T³
    readNR abc =
      let aBc = equivFun (⟦⅀⟧ A (λ a → ⅀ (B a) (C a))) abc
          a = fst aBc
          bC = equivFun (⟦⅀⟧ (B a) (C a)) (snd aBc)
      in a , fst bC , snd bC

    readNL : El (⅀ (⅀ A B) (⅀Assoc-C' A B C)) → T³
    readNL abc =
      let abC = equivFun (⟦⅀⟧ (⅀ A B) (⅀Assoc-C' A B C)) abc
          aB = equivFun (⟦⅀⟧ A B) (fst abC)
      in fst aB , snd aB , snd abC

    gNR : El (⅀ A (λ a → ⅀ (B a) (C a))) → T
    gNR = F̂ ∘ readNR

    gNL : El (⅀ (⅀ A B) (⅀Assoc-C' A B C)) → T
    gNL = F̂ ∘ readNL

    B' : Σ[ a ∈ El A ] El (B a) → Type ℓe
    B' ab-pair = El (C (fst ab-pair) (snd ab-pair))

    module _ (abc : El (⅀ A (λ a → ⅀ (B a) (C a)))) where
      private
        aBc : Σ[ a ∈ El A ] El (⅀ (B a) (C a))
        aBc = equivFun (⟦⅀⟧ A (λ a → ⅀ (B a) (C a))) abc
        a : El A
        a = fst aBc
        bC : Σ[ b ∈ El (B a) ] El (C a b)
        bC = equivFun (⟦⅀⟧ (B a) (C a)) (snd aBc)
        b : El (B a)
        b = fst bC
        c : El (C a b)
        c = snd bC

        ab* : El (⅀ A B)
        ab* = invEq (⟦⅀⟧ A B) (a , b)

        c-bd : El (⅀Assoc-C' A B C ab*)
        c-bd = subst B' (sym (secEq (⟦⅀⟧ A B) (a , b))) c

      slide1 : Path T³
                 (readNR abc)
                 ( fst (equivFun (⟦⅀⟧ A B) ab*)
                 , snd (equivFun (⟦⅀⟧ A B) ab*)
                 , c-bd )
      slide1 i =
        let p  = sym (secEq (⟦⅀⟧ A B) (a , b)) i
            c-i = transp (λ k → B' (sym (secEq (⟦⅀⟧ A B) (a , b)) (i ∧ k)))
                         (~ i) c
        in fst p , snd p , c-i

      slide2 : Path T³
                 ( fst (equivFun (⟦⅀⟧ A B) ab*)
                 , snd (equivFun (⟦⅀⟧ A B) ab*)
                 , c-bd )
                 (readNL (equivFun (⅀Assoc≃ A B C) abc))
      slide2 i =
        let q = sym (secEq (⟦⅀⟧ (⅀ A B) (⅀Assoc-C' A B C)) (ab* , c-bd)) i
        in fst (equivFun (⟦⅀⟧ A B) (fst q))
         , snd (equivFun (⟦⅀⟧ A B) (fst q))
         , snd q

      ghomog-pt : gNR abc ≡ gNL (equivFun (⅀Assoc≃ A B C) abc)
      ghomog-pt = cong F̂ slide1 ∙ cong F̂ slide2

    ghomog : gNR ≡ gNL ∘ equivFun (⅀Assoc≃ A B C)
    ghomog = funExt ghomog-pt

  -- ==========================================================================
  -- Postcomposition naturality: a map g : T → T' carries ghomog at F to
  -- ghomog at g∘F.  The slides are F-independent (paths in T³), the funExt/
  -- cong-distribution is judgmental; the only propositional step is
  -- congFunct over the two-slide composite.  At g := Index this bridges the
  -- OpM coherence `cong (Index ∘_) homog` to the canonical hg₀.
  -- ==========================================================================
  module _ (A : Code) (B : El A → Code)
           (C : (a : El A) → El (B a) → Code)
           {T : Type ℓt} {T' : Type ℓt'}
           (F : (a : El A) (b : El (B a)) → El (C a b) → T)
           (g : T → T') where

    ghomog-natural :
      cong (g ∘_) (GH.ghomog A B C F)
      ≡ GH.ghomog A B C (λ a b c → g (F a b c))
    ghomog-natural =
      cong funExt (funExt (λ abc →
        congFunct g (cong (GH.F̂ A B C F) (GH.slide1 A B C F abc))
                    (cong (GH.F̂ A B C F) (GH.slide2 A B C F abc))))

  -- ==========================================================================
  -- Instantiation at T := Code, F := D: gNR/gNL are DEFINITIONALLY the
  -- dNR₀/dNL₀ of the DepPentagon, and ghomog is the canonical hg₀.
  -- ==========================================================================
  module _ (A : Code) (B : El A → Code)
           (C : (a : El A) → El (B a) → Code)
           (D : (a : El A) (b : El (B a)) → El (C a b) → Code) where

    gNR-is-dNR₀ : GH.gNR A B C D ≡ dNR₀ {𝒰 = 𝒰} A B C D
    gNR-is-dNR₀ = refl

    gNL-is-dNL₀ : GH.gNL A B C D ≡ dNL₀ {𝒰 = 𝒰} A B C D
    gNL-is-dNL₀ = refl

    hg₀ : dNR₀ {𝒰 = 𝒰} A B C D
        ≡ dNL₀ {𝒰 = 𝒰} A B C D ∘ equivFun (⅀Assoc≃ A B C)
    hg₀ = GH.ghomog A B C D
