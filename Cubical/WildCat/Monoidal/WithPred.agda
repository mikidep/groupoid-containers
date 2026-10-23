open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.WildCat.Base
open import Cubical.WildCat.Functor
open import Cubical.WildCat.NaturalTransformation.Base
open import Cubical.WildCat.FullSub
open import Cubical.WildCat.Monoidal.Base

module Cubical.WildCat.Monoidal.FullSub 
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

  isMonFullSub : isMonoidalWildCat (FullSubWildCat C P)
  isMonFullSub ._⊗_ .F-ob ((x , isx) , (y , isy)) = 
    iMC._⊗_ .F-ob (x , y) , P⊗ isx isy
  isMonFullSub ._⊗_ .F-hom = iMC._⊗_ .F-hom
  isMonFullSub ._⊗_ .F-id = iMC._⊗_ .F-id
  isMonFullSub ._⊗_ .F-seq = iMC._⊗_ .F-seq
  isMonFullSub .𝟙 = iMC.𝟙 , P𝟙
  isMonFullSub .⊗assoc .trans .N-ob ((x , _) , (y , _) , (z , _)) = 
    iMC.⊗assoc .trans .N-ob (x , y , z)
  isMonFullSub .⊗assoc .trans .N-hom = iMC.⊗assoc .trans .N-hom
  isMonFullSub .⊗assoc .isIs ((x , _) , (y , _) , (z , _)) .inv' = 
    iMC.⊗assoc .isIs (x , y , z) .inv'
  isMonFullSub .⊗assoc .isIs ((x , _) , (y , _) , (z , _)) .sect = 
    iMC.⊗assoc .isIs (x , y , z) .sect
  isMonFullSub .⊗assoc .isIs ((x , _) , (y , _) , (z , _)) .retr = 
    iMC.⊗assoc .isIs (x , y , z) .retr
  isMonFullSub .⊗lUnit .trans .N-ob (x , _) = iMC.⊗lUnit .trans .N-ob x
  isMonFullSub .⊗lUnit .trans .N-hom = iMC.⊗lUnit .trans .N-hom
  isMonFullSub .⊗lUnit .isIs (x , _) .inv' = iMC.⊗lUnit .isIs x .inv'
  isMonFullSub .⊗lUnit .isIs (x , _) .sect = iMC.⊗lUnit .isIs x .sect
  isMonFullSub .⊗lUnit .isIs (x , _) .retr = iMC.⊗lUnit .isIs x .retr
  isMonFullSub .⊗rUnit .trans .N-ob (x , _) = iMC.⊗rUnit .trans .N-ob x
  isMonFullSub .⊗rUnit .trans .N-hom = iMC.⊗rUnit .trans .N-hom
  isMonFullSub .⊗rUnit .isIs (x , _) .inv' = iMC.⊗rUnit .isIs x .inv'
  isMonFullSub .⊗rUnit .isIs (x , _) .sect = iMC.⊗rUnit .isIs x .sect
  isMonFullSub .⊗rUnit .isIs (x , _) .retr = iMC.⊗rUnit .isIs x .retr
  isMonFullSub .⊗triangle i .N-ob ((x , _) , (y , _)) =
    iMC.⊗triangle i .N-ob (x , y)
  isMonFullSub .⊗triangle i .N-hom = iMC.⊗triangle i .N-hom
  isMonFullSub .⊗pentagon i .N-ob ((x , _) , (y , _) , (z , _) , (w , _)) =
    iMC.⊗pentagon i .N-ob (x , y , z , w)
  isMonFullSub .⊗pentagon i .N-hom = iMC.⊗pentagon i .N-hom

  MonFullSub : MonoidalWildCat _ _
  MonFullSub .fst = FullSubWildCat C P
  MonFullSub .snd = isMonFullSub


