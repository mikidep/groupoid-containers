open import Cubical.Foundations.Prelude
open import Cubical.WildCat.Base
open import Cubical.WildCat.FullSub
open import Cubical.WildCat.Functor

module Cubical.WildCat.FullSub.Functor.Notation
  {ℓC ℓC' ℓD ℓD' : Level}
  {C : WildCat ℓC ℓC'}
  {P : _}
  {D : WildCat ℓD ℓD'} 
  (F : WildFunctor (FullSubWildCat C P) D)
  where

import Cubical.WildCat.AsLU2C.Functor.Notation F as FN

open WildCat

private
  C₀ = C .ob
  Cₚ = FullSubWildCat C P

open FN using (F₀) public

F₁ : {x y : C₀} 
  {isx : P x} {isy : P y} 
  → Cₚ [ (x , isx) , (y , isy) ]
  → D [ _ , _ ]
F₁ {x} {y} {isx} {isy} = FN.F₁ {(x , isx)} {(y , isy)}

F-id : {x : C₀} {isx : P x} → _
F-id {x} {isx} = FN.F-id {(x , isx)}

F-seq : {x y z : C₀} 
  {isx : P x}
  {isy : P y}
  {isz : P z}
  → _
F-seq {x} {y} {z} {isx} {isy} {isz} = 
  FN.F-seq {(x , isx)} {(y , isy)} {(z , isz)}

F₂ : {x y : C₀} 
  {isx : P x} {isy : P y} 
  {f g : C [ x , y ]} → _
F₂ {x} {y} {isx} {isy} {f} {g} = FN.F₂ {(x , isx)} {(y , isy)} {f} {g}
