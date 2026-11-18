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

module Cubical.Container.GenOperadT (T : Container) (PmT : PsMndCont T) where

open Container T
open PsMndCont PmT

open Universe
open UniverseBase
open UniverseCoh

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence

-- Cartesian monad container as universe?

U : Universe _ _
U .base .Code = S
U .base .El = P
U .base .⅀ = m
U .base .𝜏 = e
U .base .⟦⅀⟧ s s′ = {! !}
U .base .⟦𝜏⟧ = {! !}
U .base .Inj = {! !}
U .base .InjComp = {! !}
U .coh = {! !}

open Extent

