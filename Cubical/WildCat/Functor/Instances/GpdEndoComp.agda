open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.WildCat.Product
open import Cubical.WildCat.Functor
open import Cubical.WildCat.Instances.GpdEndo 

open import Cubical.LU2C.GpdEndo.Constructions.Comp0 {ℓ-zero}
open import Cubical.LU2C.GpdEndo.Constructions.Comp1
open import Cubical.LU2C.GpdEndo.NatTrans.Base

module Cubical.WildCat.Functor.Instances.GpdEndoComp where

open import Cubical.LU2C.Base
open import Cubical.LU2C.Instances.Groupoids ℓ-zero

open WildFunctor

open LU2C HGpd using () renaming (str to ⟨HGpd⟩)

compWild : WildFunctor (GpdEndo × GpdEndo) GpdEndo
compWild .F-ob = uncurry _⨾₀_
compWild .F-hom {F , G} {F′ , G′} = uncurry (_⨾₁_ {F = F} {F′} {G} {G′})
compWild .F-id = GpdEndoTrans≡ {! !} ? 
compWild .F-seq = {! !}

