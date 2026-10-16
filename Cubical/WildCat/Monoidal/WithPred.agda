open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.WildCat.Base
open import Cubical.WildCat.Functor
open import Cubical.WildCat.NaturalTransformation.Base
open import Cubical.WildCat.WithPred
open import Cubical.WildCat.Monoidal.Base

module Cubical.WildCat.Monoidal.WithPred 
  {ℓ ℓ' : _} (MC : MonoidalWildCat ℓ ℓ') where

private variable ℓ'' : Level

open Σ MC renaming (fst to C; snd to isMonC)

private module iMC = isMonoidalWildCat isMonC

open WildCat C using () renaming (ob to C₀)

record isMonPred (P : ℙ C₀) : Type ℓ where
  open iMC
  open WildFunctor
  private _⊗₀_ = curry (_⊗_ .F-ob)  
  field
    P𝟙 : P 𝟙
    P⊗ : {x y : C₀} → P x → P y → P (x ⊗₀ y) 
    
module _ (P : ℙ C₀) (isMonP : isMonPred P) where
  open isMonPred isMonP
  open isMonoidalWildCat
  open WildFunctor
  open WildNatTrans
  open WildNatIso
  open wildIsIso
  
  -- Could be defined as a smarter construction without
  -- introducing extra paths? Perhaps...

  isMonΣPred : isMonoidalWildCat (ΣPredWildCat C P)
  isMonΣPred ._⊗_ .F-ob ((x , isx) , (y , isy)) = 
    iMC._⊗_ .F-ob (x , y) , P⊗ isx isy
  isMonΣPred ._⊗_ .F-hom = iMC._⊗_ .F-hom
  isMonΣPred ._⊗_ .F-id = iMC._⊗_ .F-id
  isMonΣPred ._⊗_ .F-seq = iMC._⊗_ .F-seq
  isMonΣPred .𝟙 = iMC.𝟙 , P𝟙
  isMonΣPred .⊗assoc .trans .N-ob ((x , _) , (y , _) , (z , _)) = 
    iMC.⊗assoc .trans .N-ob (x , y , z)
  isMonΣPred .⊗assoc .trans .N-hom = iMC.⊗assoc .trans .N-hom
  isMonΣPred .⊗assoc .isIs ((x , _) , (y , _) , (z , _)) .inv' = 
    iMC.⊗assoc .isIs (x , y , z) .inv'
  isMonΣPred .⊗assoc .isIs ((x , _) , (y , _) , (z , _)) .sect = 
    iMC.⊗assoc .isIs (x , y , z) .sect
  isMonΣPred .⊗assoc .isIs ((x , _) , (y , _) , (z , _)) .retr = 
    iMC.⊗assoc .isIs (x , y , z) .retr
  isMonΣPred .⊗lUnit .trans .N-ob (x , _) = iMC.⊗lUnit .trans .N-ob x
  isMonΣPred .⊗lUnit .trans .N-hom = iMC.⊗lUnit .trans .N-hom
  isMonΣPred .⊗lUnit .isIs (x , _) .inv' = iMC.⊗lUnit .isIs x .inv'
  isMonΣPred .⊗lUnit .isIs (x , _) .sect = iMC.⊗lUnit .isIs x .sect
  isMonΣPred .⊗lUnit .isIs (x , _) .retr = iMC.⊗lUnit .isIs x .retr
  isMonΣPred .⊗rUnit .trans .N-ob (x , _) = iMC.⊗rUnit .trans .N-ob x
  isMonΣPred .⊗rUnit .trans .N-hom = iMC.⊗rUnit .trans .N-hom
  isMonΣPred .⊗rUnit .isIs (x , _) .inv' = iMC.⊗rUnit .isIs x .inv'
  isMonΣPred .⊗rUnit .isIs (x , _) .sect = iMC.⊗rUnit .isIs x .sect
  isMonΣPred .⊗rUnit .isIs (x , _) .retr = iMC.⊗rUnit .isIs x .retr
  isMonΣPred .⊗triangle i .N-ob ((x , _) , (y , _)) =
    iMC.⊗triangle i .N-ob (x , y)
  isMonΣPred .⊗triangle i .N-hom = iMC.⊗triangle i .N-hom
  isMonΣPred .⊗pentagon i .N-ob ((x , _) , (y , _) , (z , _) , (w , _)) =
    iMC.⊗pentagon i .N-ob (x , y , z , w)
  isMonΣPred .⊗pentagon i .N-hom = iMC.⊗pentagon i .N-hom

  MonΣPred : MonoidalWildCat _ _
  MonΣPred .fst = ΣPredWildCat C P
  MonΣPred .snd = isMonΣPred


