module Cubical.Bicategory.Product.Base where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Sigma renaming (_×_ to _×'_)

open import Cubical.Bicategory.Base
import Cubical.WildCat.Product as W

private
  variable
    ℓC ℓC' ℓD ℓD' : Level

open Bicategory
open IsBicategory
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.GroupoidLaws
open import Prelude.Square
open import Prelude.ExtraGpdLaws

_×_ :  (C : Bicategory ℓC ℓC') (D : Bicategory ℓD ℓD') → Bicategory _ _
(C × D) .str = C .str W.× D .str 
(C × D) .isBicat .triangle _ _ = 
  ΣSquare 
    ( congFunct fst _ _ ∙ C .isBicat .triangle _ _ 
    , congFunct snd _ _ ∙ D .isBicat .triangle _ _
    )
(C × D) .isBicat .pentagon _ _ _ _ = 
  ΣSquare 
    ( congFunct fst _ _ 
      ∙ ∙l congFunct fst _ _ 
      ∙ C .isBicat .pentagon _ _ _ _
      ∙ sym (congFunct fst _ _)
    , congFunct snd _ _ 
      ∙ ∙l congFunct snd _ _ 
      ∙ D .isBicat .pentagon _ _ _ _
      ∙ sym (congFunct snd _ _)
    )
(C × D) .isBicat .isGpdHom = isGroupoid× (C .isGpdHom) (D .isGpdHom)
