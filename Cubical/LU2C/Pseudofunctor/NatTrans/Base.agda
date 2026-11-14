open import Cubical.Foundations.Prelude

open import Cubical.WildCat.Base -- hiding (_[_,_])
open import Cubical.WildCat.Functor
import Cubical.WildCat.AsLU2C.Functor.Notation as NotF
open import Cubical.WildCat.AsLU2C.Instances

open import Cubical.LU2C.Base hiding (_[_,_])
open import Cubical.LU2C.Pseudofunctor

module Cubical.LU2C.Pseudofunctor.NatTrans.Base 
  {ℓC ℓC' ℓD ℓD' : Level}
  where

module _ 
  {C : WildCat ℓC ℓC'} {D : WildCat ℓD ℓD'} 
  {F G : WildFunctor C D} where

  private module C = WildCat C 
  private module D = WildCat D 
  private module F = NotF F 
  private module G = NotF G 

  open F using (F₀; F₁; F₂)
  open G using () renaming 
    ( F₀ to G₀
    ; F₁ to G₁
    ; F₂ to G₂
    )
  open NotWC C
  open NotWC D

  record IsPseudonat (α : WildNatTrans _ _ F G) 
    : Type (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓD ℓD')) where
    open WildNatTrans α using ()
      renaming (N-ob to α₀; N-hom to α□)
    field
      N-hom-id : ∀ {x : C.ob} 
        → α□ (id {x = x}) 
          ∙ α₀ x ◃ G.F-id 
          ∙ D.⋆IdR (α₀ x)
          ≡ F.F-id ▹ α₀ x 
          ∙ D.⋆IdL (α₀ x)
      N-hom-seq : ∀ {x y z} 
        (f : C [ x , y ])
        (g : C [ y , z ])
        → α□ (f ⋆ g)
          ∙ α₀ x ◃ G.F-seq f g
          ≡ F.F-seq f g ▹ α₀ z
          ∙ D.⋆Assoc (F₁ f) (F₁ g) (α₀ z)
          ∙ F₁ f ◃ α□ g
          ∙ sym (D.⋆Assoc (F₁ f) (α₀ y) (G₁ g))
          ∙ α□ f ▹ G₁ g
          ∙ D.⋆Assoc (α₀ x) (G₁ f) (G₁ g)

module _ 
  {C : LU2C ℓC ℓC'} {D : LU2C ℓD ℓD'} 
  (F G : Pseudofunctor C D) where

  PseudonatTrans = Σ (WildNatTrans _ _ (F .fst) (G .fst)) IsPseudonat
