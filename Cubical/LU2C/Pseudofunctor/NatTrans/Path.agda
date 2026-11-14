open import Cubical.Foundations.Prelude

open import Cubical.WildCat.Base
open import Cubical.WildCat.Functor
open import Cubical.WildCat.NaturalTransformation.Base

open import Cubical.LU2C.Base hiding (_[_,_])
open import Cubical.LU2C.Pseudofunctor
open import Cubical.LU2C.Pseudofunctor.NatTrans.Base

module Cubical.LU2C.Pseudofunctor.NatTrans.Path 
  {ℓC ℓC' ℓD ℓD' : Level}
  where

module _
  {C : WildCat ℓC ℓC'} {D : WildCat ℓD ℓD'} 
  {isGpdHomD : ∀ {x y} → isGroupoid (D [ x , y ])}
  {F G : WildFunctor C D}
  where
  open import Cubical.Foundations.HLevels

  open IsPseudonat

  isPropIsPseudonat : {α : WildNatTrans _ _ F G} → isProp (IsPseudonat α)
  isPropIsPseudonat is₁ is₂ i .N-hom-id {x} = aux i
    where
    aux : is₁ .N-hom-id {x} ≡ is₂ .N-hom-id
    aux = isGpdHomD _ _ _ _ (is₁ .N-hom-id) (is₂ .N-hom-id)
  isPropIsPseudonat is₁ is₂ i .N-hom-seq f g = aux i
    where
    aux : is₁ .N-hom-seq f g ≡ is₂ .N-hom-seq f g
    aux = isGpdHomD _ _ _ _ (is₁ .N-hom-seq f g) (is₂ .N-hom-seq f g)

module _ 
  {C : LU2C ℓC ℓC'} {D : LU2C ℓD ℓD'} 
  {F G : Pseudofunctor C D} where

  open import Cubical.Data.Sigma.Properties
  open import Cubical.Foundations.Equiv
  open import Cubical.WildCat.AsLU2C.Instances
  private module C = LU2C C
  private module D = LU2C D
  open Not2C D

  open Pseudofunctor {C = C} {D} F using (F₀; F₁; F₂)
  open Pseudofunctor {C = C} {D} G using () renaming 
    ( F₀ to G₀
    ; F₁ to G₁
    ; F₂ to G₂
    )

  open WildNatTrans

  PseudonatTrans≡ : {α β : PseudonatTrans {C = C} {D} F G}
    (N-ob≡ : α .fst .N-ob ≡ β .fst .N-ob)
    (N-hom≡ : ∀ {x y} (f : C.Hom[ x , y ]) → 
      PathP (λ i → F₁ f ⋆ N-ob≡ i _ ≡ N-ob≡ i _ ⋆ G₁ f)
        (α .fst .N-hom f) (β .fst .N-hom f))
    → α ≡ β
  PseudonatTrans≡ N-ob≡ N-hom≡ = Σ≡Prop 
    (λ _ → isPropIsPseudonat {isGpdHomD = D.isGpdHom})
    (makeNatTransPath N-ob≡ N-hom≡) 


