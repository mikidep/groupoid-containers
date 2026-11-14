open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws

module Cubical.LU2C.Pseudofunctor where

open import Cubical.WildCat.Base -- hiding (_[_,_])
open import Cubical.LU2C.Base hiding (_[_,_])
open import Cubical.WildCat.Functor

open import Cubical.WildCat.AsLU2C.Instances
import Cubical.WildCat.AsLU2C.Functor.Notation as NotF

private
  variable
    ℓC ℓC' ℓD ℓD' : Level

module _ {C : WildCat ℓC ℓC'} {D : WildCat ℓD ℓD'} where
  record IsPseudofunctor
    (F : WildFunctor C D)
    : Type (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓD ℓD')) where

    open NotWC C
    open NotWC D
    open NotF F

    field
      F-IdL : ∀ {x y} (f : C [ x , y ])
        → F-seq id f
          ∙ F-id ▹ F₁ f
          ∙ ⋆IdL (F₁ f)
          ≡ F₂ (⋆IdL f)
      F-IdR : ∀ {x y} (f : C [ x , y ])
        → F-seq f id
          ∙ F₁ f ◃ F-id
          ∙ ⋆IdR (F₁ f)
          ≡ F₂ (⋆IdR f)
      F-Assoc : ∀ {x y z w}
        (f : C [ x , y ])
        (g : C [ y , z ])
        (h : C [ z , w ])
        → F-seq (f ⋆ g) h
          ∙ F-seq f g ▹ F₁ h
          ∙ ⋆Assoc (F₁ f) (F₁ g) (F₁ h)
          ≡ F₂ (⋆Assoc f g h)
          ∙ F-seq f (g ⋆ h)
          ∙ F₁ f ◃ F-seq g h

module _ (C : LU2C ℓC ℓC') (D : LU2C ℓD ℓD') where
  open LU2C using (str)
  Pseudofunctor = Σ _ (IsPseudofunctor {C = C .str} {D .str})

module _ {C : LU2C ℓC ℓC'} {D : LU2C ℓD ℓD'}
  where

  module Pseudofunctor (F : Pseudofunctor C D) where
    open Σ F renaming (fst to str; snd to isPseudofunctor) public
    open NotF str public
    open IsPseudofunctor isPseudofunctor public
