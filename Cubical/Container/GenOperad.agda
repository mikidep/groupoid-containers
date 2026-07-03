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

module Cubical.Container.GenOperad 
  (T : Container) (PmT : PsMndCont T) where

open Universe
open UniverseBase
open UniverseCoh

U : Universe _ _
U .base .Code = Type
U .base .El = idfun _
U .base .⅀ = Σ
U .base .𝜏 = Unit
U .base .⟦⅀⟧ A B = {! !} , {! !}
U .base .⟦𝜏⟧ = {! !}
U .base .Inj = {! !} -- need UA
U .base .InjComp = {! !}
U .coh .⟦⅀Idl⟧ A = {! !}
U .coh .⟦⅀Idr⟧ = {! !}
U .coh .⟦⅀Assoc⟧ = {! !}

private module T = Container T
private module M = PsMndCont PmT

K : U .Code → Type
K Q = Σ[ s ∈ T.S ] (T.P s → Q)

open Operad

MOp : Operad U K
MOp .isSetK = {! !}
MOp .id = M.e , _
MOp .compₒ A B (s , πs) vπ = M.m s s′ , λ p → remap (M.↖ p) (M.↗ p)
  where
  s′ : T.P s → T.S
  s′ p = 
    let a = πs p
    in vπ a .fst
  remap : (p : T.P s) → T.P (s′ p) → Σ A B
  remap p p′ = let a = πs p 
    in a , vπ a .snd p′
MOp .idl A (s , π) = ΣPathP (M.rUnit-σ s , {! !})
MOp .idr A (s , π) = ΣPathP (M.lUnit-σ s , {! !})
MOp .assoc A B C = {! !}

open Extent

module _ (X : Type) where
  open import Cubical.Foundations.Isomorphism
  open import Cubical.Reflection.RecordEquiv

  unquoteDecl OpMIsoΣ = declareRecordIsoΣ OpMIsoΣ (quote OpM)

  OpM-⟦T⟧-Iso : Iso (OpM MOp X) (⟦ T ⟧₀ X)
  OpM-⟦T⟧-Iso = compIso OpMIsoΣ OpMΣ-⟦T⟧-Iso
    where
    open Iso
    open import Prelude.Utils
    OpMΣ-⟦T⟧-Iso : Iso _ _
    OpMΣ-⟦T⟧-Iso .fun (Idx , (s , π) , dat) = s , (π » dat)
    OpMΣ-⟦T⟧-Iso .inv (s , px) = (T.P s , (s , idfun _) , px)
    OpMΣ-⟦T⟧-Iso .rightInv (s , px) = refl
    OpMΣ-⟦T⟧-Iso .leftInv (Idx , (s , π) , dat) = {! !}
    -- ————————————————————————————————————————————————————————————
    -- Goal: (T.P s , (s , (λ x → x)) , (λ x → dat (π x))) ≡ (Idx , (s , π) , dat)
    -- ————————————————————————————————————————————————————————————
    -- π is moved from Op .snd to Data, and Index changes accordingly.
    -- I'm trying to define an isomorphism between objects of two cats,
    -- but maybe an equivalence of cats works.
