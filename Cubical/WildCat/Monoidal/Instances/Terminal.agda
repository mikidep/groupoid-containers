open import Cubical.Foundations.Prelude
open import Cubical.Data.Unit

open import Cubical.WildCat.Base
open import Cubical.WildCat.Monoidal.Base
open import Cubical.WildCat.Functor
open import Cubical.WildCat.Product 
open import Cubical.Data.Sigma hiding (_×_)

module Cubical.WildCat.Monoidal.Instances.Terminal where

open WildCat

Terminal : WildCat ℓ-zero ℓ-zero
Terminal .ob = Unit
Terminal .Hom[_,_] _ _ = Unit
Terminal .id = tt
Terminal ._⋆_ _ _ = tt
Terminal .⋆IdL _ = refl
Terminal .⋆IdR _ = refl
Terminal .⋆Assoc _ _ _ = refl

open WildFunctor
open WildNatTrans
open WildNatIso
open wildIsIso
open isMonoidalWildCat

isMonoidalTerminal : isMonoidalWildCat Terminal
isMonoidalTerminal ._⊗_ .F-ob _ = _
isMonoidalTerminal ._⊗_ .F-hom _ = _
isMonoidalTerminal ._⊗_ .F-id = refl
isMonoidalTerminal ._⊗_ .F-seq _ _ = refl
isMonoidalTerminal .𝟙 = _
isMonoidalTerminal .⊗assoc .trans .N-ob _ = _
isMonoidalTerminal .⊗assoc .trans .N-hom _ = refl
isMonoidalTerminal .⊗assoc .isIs _ .inv' = _
isMonoidalTerminal .⊗assoc .isIs _ .sect = refl
isMonoidalTerminal .⊗assoc .isIs _ .retr = refl
isMonoidalTerminal .⊗lUnit .trans .N-ob _ = _
isMonoidalTerminal .⊗lUnit .trans .N-hom _ = refl
isMonoidalTerminal .⊗lUnit .isIs _ .inv' = _
isMonoidalTerminal .⊗lUnit .isIs _ .sect = refl
isMonoidalTerminal .⊗lUnit .isIs _ .retr = refl
isMonoidalTerminal .⊗rUnit .trans .N-ob _ = _
isMonoidalTerminal .⊗rUnit .trans .N-hom _ = refl
isMonoidalTerminal .⊗rUnit .isIs _ .inv' = _
isMonoidalTerminal .⊗rUnit .isIs _ .sect = refl
isMonoidalTerminal .⊗rUnit .isIs _ .retr = refl
isMonoidalTerminal .triang _ _        = refl
isMonoidalTerminal .⊗pentagon _ _ _ _ = refl

MonoidalTerminal : MonoidalWildCat _ _
MonoidalTerminal = Terminal , isMonoidalTerminal
