module Cubical.LU2C.Product.Base where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Sigma renaming (_×_ to _×'_)

open import Cubical.LU2C.Base
import Cubical.WildCat.Product as W

private
  variable
    ℓC ℓC' ℓD ℓD' : Level

open LU2C
open IsLU2C
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.GroupoidLaws
open import Prelude.Square
open import Prelude.ExtraGpdLaws

_×_ :  (C : LU2C ℓC ℓC') (D : LU2C ℓD ℓD') → LU2C _ _
(C × D) .str = C .str W.× D .str 
(C × D) .isLU2C .triangle _ _ = 
  ΣSquare 
    ( congFunct fst _ _ ∙ C .isLU2C .triangle _ _ 
    , congFunct snd _ _ ∙ D .isLU2C .triangle _ _
    )
(C × D) .isLU2C .pentagon _ _ _ _ = 
  ΣSquare 
    ( congFunct fst _ _ 
      ∙ ∙l congFunct fst _ _ 
      ∙ C .isLU2C .pentagon _ _ _ _
      ∙ sym (congFunct fst _ _)
    , congFunct snd _ _ 
      ∙ ∙l congFunct snd _ _ 
      ∙ D .isLU2C .pentagon _ _ _ _
      ∙ sym (congFunct snd _ _)
    )
(C × D) .isLU2C .isGpdHom = isGroupoid× (C .isGpdHom) (D .isGpdHom)
