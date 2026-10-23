open import Cubical.Foundations.Prelude

open import Cubical.LU2C.Base
open import Cubical.Foundations.GroupoidLaws
open import Prelude.ExtraGpdLaws

open import Cubical.WildCat.Base
open import Cubical.WildCat.Functor
open import Cubical.WildCat.AsLU2C.Instances
import Cubical.WildCat.AsLU2C.Functor.Notation as NotF
open import CubicalCompat.WildCat.Functor
open import Cubical.WildCat.NaturalTransformation.Base

module Cubical.LU2C.Instances.WildFunctor where

private
  variable
    ℓC ℓC' ℓD ℓD' : Level

module _ (C : WildCat ℓC ℓC') (D : LU2C ℓD ℓD') where
  private 
    module W = WildCat
    module L = LU2C
    module D = LU2C D

  open Not2C D

  open import Cubical.WildCat.Instances.WildFunctLU2C
  open IsLU2C

  WildFunctLU2C : LU2C _ _ 
  WildFunctLU2C .L.str = WildFunctWC C D
  WildFunctLU2C .L.isLU2C .triangle α β = 
    natTransSquareGpdHom D.isGpdHom path
    where
    open WildNatTrans α renaming (N-ob to α₀; N-hom to α□)
    open WildNatTrans β renaming (N-ob to β₀; N-hom to β□)
    open import Prelude.Square
    path = congFunct WildNatTrans.N-ob _ _ ∙ funExtTriangle
      where
      funExtTriangle = funExtSquare λ x → D.triangle (α₀ x) (β₀ x)
  WildFunctLU2C .L.isLU2C .pentagon α β γ δ = 
    natTransSquareGpdHom D.isGpdHom path
    where
    open WildNatTrans α renaming (N-ob to α₀; N-hom to α□)
    open WildNatTrans β renaming (N-ob to β₀; N-hom to β□)
    open WildNatTrans γ renaming (N-ob to γ₀; N-hom to γ□)
    open WildNatTrans δ renaming (N-ob to δ₀; N-hom to δ□)
    open import Prelude.Square
    path = congFunct WildNatTrans.N-ob _ _ 
      ∙ ∙l congFunct WildNatTrans.N-ob _ _ 
      ∙ funExtPentagon
      ∙ sym (congFunct WildNatTrans.N-ob _ _)
      where
      funExtPentagon = funExtSquare λ x → D.pentagon (α₀ x) (β₀ x) (γ₀ x) (δ₀ x)
  WildFunctLU2C .L.isLU2C .isGpdHom = isGroupoidWildNatTransGpdHom D.isGpdHom

