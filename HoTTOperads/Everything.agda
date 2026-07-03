{-# OPTIONS --cubical #-}
-- Single entry point that imports every module in the library.
-- CI target: `agda --cubical src/HoTTOperads/Everything.agda` succeeds with exit 0.
module HoTTOperads.Everything where

open import HoTTOperads.Prelude.Equiv
open import HoTTOperads.Prelude.HLevels
open import HoTTOperads.Prelude.Path
open import HoTTOperads.Prelude.Nat
open import HoTTOperads.Prelude.FinSet

open import HoTTOperads.UA
open import HoTTOperads.PathTrace

open import HoTTOperads.Universe.Base
open import HoTTOperads.Universe.Derived
open import HoTTOperads.Universe.IRDerived
open import HoTTOperads.Universe.Assoc
open import HoTTOperads.Universe.Pentagon
open import HoTTOperads.Universe.PentagonDep
open import HoTTOperads.Universe.Homog
open import HoTTOperads.Universe.HomogLine
open import HoTTOperads.Universe.PentagonDepProof
open import HoTTOperads.Universe.SigmaBridge
open import HoTTOperads.Universe.Instances.Nat
open import HoTTOperads.Universe.Instances.FinSet
open import HoTTOperads.Universe.Instances.Type
open import HoTTOperads.Universe.Instances.NType

open import HoTTOperads.Operad.Base
open import HoTTOperads.Operad.Morphism
open import HoTTOperads.Operad.Endo
open import HoTTOperads.Operad.HLevel
open import HoTTOperads.Operad.Specialised.NonSymm
open import HoTTOperads.Operad.Specialised.Symm

open import HoTTOperads.Monad.Base
open import HoTTOperads.Monad.Functor
open import HoTTOperads.Monad.Composition
open import HoTTOperads.Monad.Laws
open import HoTTOperads.Monad.PointwisePentagon
open import HoTTOperads.Monad.Algebra
open import HoTTOperads.Monad.TwoCellCoherence
open import HoTTOperads.Monad.TwoCellNaturality

open import HoTTOperads.Examples.IExpr
open import HoTTOperads.Examples.PartialList
open import HoTTOperads.Examples.PartialListAlgebra
open import HoTTOperads.Examples.PartialListMonad
open import HoTTOperads.Examples.SymExpr
open import HoTTOperads.Examples.Associative
open import HoTTOperads.Examples.Commutative

open import HoTTOperads.Free.HIT
open import HoTTOperads.Free.IR.Base
open import HoTTOperads.Free.IR.FiberEquiv
open import HoTTOperads.Free.IR
open import HoTTOperads.Free.Universal
open import HoTTOperads.Free.Examples
