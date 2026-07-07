open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Unit
open import Cubical.Data.Sigma

open import Cubical.Container.Base
open import Cubical.Container.Constructions
open import Cubical.Container.MonoidContainer
open import HoTTOperads.Operad.Base
open import HoTTOperads.Monad.Base
open import HoTTOperads.Universe.Base

module Cubical.Container.GenOperad where

open Universe
open UniverseBase
open UniverseCoh

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence

U : Universe _ _
U .base .Code = Type
U .base .El = idfun _
U .base .⅀ = Σ
U .base .𝜏 = Unit
U .base .⟦⅀⟧ A B = idEquiv _
U .base .⟦𝜏⟧ = idEquiv _
U .base .Inj = ua -- need UA
U .base .InjComp = uaCompEquiv
U .coh .⟦⅀Idl⟧ A = refl
U .coh .⟦⅀Idr⟧ A = refl
U .coh .⟦⅀Assoc⟧ A B C = refl

open Extent

module _ (T : Container) where
  private module T = Container T

  K : U .Code → Type
  K = ⟦ T ⟧₀

  open import Cubical.Data.Sigma

  record DefOperad : Type₁ where
    field
      isSetK : (A : Type) → isSet (K A)
      id     : K Unit
      compₒ   : (A : Type) (B : A → Type)
             → K A → ((a : A) → K (B a)) → K (Σ A B)

      idl : (A : Type) (k : K A)
          → ⟦ T ⟧₁ snd (compₒ Unit (λ _ → A) id (λ _ → k)) ≡ k

      idr : (A : Type) (k : K A)
        → ⟦ T ⟧₁ fst (compₒ A (λ _ → Unit) k (λ _ → id)) ≡ k

      assoc : (A : Type) (B : A → Type)
              (C : (a : A) → B a → Type)
              (k : K A) (ks : (a : A) → K (B a))
              (kss : (a : A) (b : B a) → K (C a b))
              → compₒ A (λ a → Σ (B a) (C a)) k 
                  (λ a → compₒ (B a) (C a) (ks a) (kss a)) 
                ≡ ⟦ T ⟧₁ (Σ-assoc-≃ .fst)
                  (compₒ (Σ A B) (λ ab → C (ab .fst) (ab .snd)) 
                    (compₒ A B k ks) 
                    (λ ab → kss (ab .fst) (ab .snd)))


  module To (PmT : PsMndCont T) where
    private module M = PsMndCont PmT

    open Container T
    open DefOperad

    DefMOp : DefOperad
    DefMOp .isSetK = {! !}
    DefMOp .id = M.e , _
    DefMOp .compₒ A B (s , πs) vπ = M.m s s′ , λ p → remap (M.↖ p) (M.↗ p)
      where
      s′ : P s → S
      s′ p = 
        let a = πs p
        in vπ a .fst
      remap : (p : P s) → P (s′ p) → Σ A B
      remap p p′ = let a = πs p 
        in a , vπ a .snd p′
    DefMOp .idl A (s , πs) i .fst = M.rUnit-σ s i
    DefMOp .idl A (s , πs) i .snd p = πs (M.rUnit-π i p)
    DefMOp .idr A (s , πs) i .fst = M.lUnit-σ s i
    DefMOp .idr A (s , πs) i .snd p = πs (M.lUnit-π i p)
    DefMOp .assoc A B C (s , πs) ks kss = goal
      where
      s′ : P s → S
      s′ p = ks (πs p) .fst 
      s″ : (p : P s) → P (s′ p) → S 
      s″ p p′ = kss (πs p) (ks (πs p) .snd p′) .fst
      goal : _
      goal i .fst = M.assoc-σ s s′ s″ i
      goal i .snd p .fst = πs (M.assoc-π₁ i p)
      goal i .snd p .snd .fst = 
        ks (πs (M.assoc-π₁ i p)) .snd (M.assoc-π₂ i p)
      goal i .snd p .snd .snd = 
        kss (πs (M.assoc-π₁ i p)) 
          (ks (πs (M.assoc-π₁ i p)) .snd (M.assoc-π₂ i p)) .snd 
          (M.assoc-π₃ i p)
    
    -- TODO: prove equivalence

  module From (DefMOp : DefOperad) where
    
    private module DM = DefOperad DefMOp
    open PsMndCont
    open Container T

    private
      cmp : ∀ s (s′ : P s → S) → Σ S (λ t → P t → Σ (P s) (λ p → P (s′ p)))
      cmp s s′ = DM.compₒ (P s) (λ p → P (s′ p)) 
        (s , idfun (P s))
        λ t → s′ t , idfun (P (s′ t)) 

    PmT : PsMndCont T
    PmT .e = DM.id .fst
    PmT .m s s′ = cmp s s′ .fst
    PmT .↖ {s} {s′} p = cmp s s′ .snd p .fst
    PmT .↗ {s} {s′} p = cmp s s′ .snd p .snd
    PmT .lUnit-σ s = {! smth !}
      where
      smth = DM.idr (P s) (s , idfun _)
    PmT .lUnit-π = {! DM.id .snd !}
    PmT .rUnit-σ s = {!  congP (λ i → fst) smth !}
      where
      smth = DM.idl (P (DM.id .fst) → P s) (s , λ p _ → p)
    PmT .rUnit-π = {! !}
    PmT .assoc-σ = {! !}
    PmT .assoc-π₁ = {! !}
    PmT .assoc-π₂ = {! !}
    PmT .assoc-π₃ = {! !}
