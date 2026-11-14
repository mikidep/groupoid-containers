open import Cubical.Foundations.Prelude

open import Cubical.LU2C.Base hiding (_[_,_])
open import Cubical.LU2C.Pseudofunctor
open import Cubical.LU2C.Pseudofunctor.NatTrans.Base
open import Cubical.WildCat.Instances.WildFunctLU2C 

open import Cubical.WildCat.Base
open import Cubical.WildCat.FullSub

open import Cubical.LU2C.GpdEndo.NatTrans.Base
import Cubical.LU2C.GpdEndo.NatTrans.Constructions as NC
open import Cubical.LU2C.Pseudofunctor.NatTrans.Path

open import Cubical.LU2C.Instances.Groupoids ℓ-zero

open import Reflection.Reassoc

open LU2C HGpd using () renaming (str to ⟨HGpd⟩)

module Cubical.WildCat.Instances.GpdEndo where

private
  FS = FullSubWildCat (WildFunctWC ⟨HGpd⟩ HGpd) IsPseudofunctor
  module FS = WildCat FS

open WildCat

GpdEndo : WildCat (ℓ-suc ℓ-zero) (ℓ-suc ℓ-zero)
GpdEndo .ob = FS.ob
GpdEndo .Hom[_,_] F G = GpdEndoTrans F G
GpdEndo .id {x = F} = NC.idPseudonatTrans F
GpdEndo ._⋆_ {x = F} {y = G} {z = H} α β = 
  NC.compPseudonatTrans {F = F} {G} {H} α β
GpdEndo .⋆IdL {x = F} {y = G} α = GpdEndoTrans≡ {F = F} {G}
  refl λ _ → reassoc!
GpdEndo .⋆IdR {x = F} {y = G} α = GpdEndoTrans≡ {F = F} {G}
  refl λ _ → reassoc!
GpdEndo .⋆Assoc {u = F} {x = G} α β γ = GpdEndoTrans≡ {F = F} {G} 
  refl λ _ → reassoc!
