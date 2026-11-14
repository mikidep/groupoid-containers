open import Cubical.Foundations.Prelude 
open import Cubical.WildCat.Base

open import Cubical.WildCat.AsLU2C.Instances
open import Cubical.WildCat.FullSub

module Cubical.WildCat.Subcat where

private
  variable
    ℓC ℓC' : Level

open WildCat using (ob)

module _ (C : WildCat ℓC ℓC')
  (P₀ : ℙ (C .ob))
  where
  
  open NotWC C

  private 
    FS = FullSubWildCat C P₀
    module FS = WildCat FS

  record Homℙ : Type (ℓ-max ℓC (ℓ-suc ℓC')) where
    field
      P₁ : (x y : FS.ob) → ℙ (FS [ x , y ])
      P₁-id : (x : FS.ob) → P₁ x x (FS.id {x = x})
      P₁-⋆ : {x y z : FS.ob} 
        {f : FS [ x , y ]}
        {g : FS [ y , z ]}
        → P₁ x y f → P₁ y z g → P₁ x z (f ⋆ g)

  
  module _ (HomP : Homℙ) where
    open Homℙ HomP
    
    SubWildCat : WildCat ℓC ℓC'
    SubWildCat = record where
      ob = FS.ob
      Hom[_,_] x y = Σ _ (P₁ x y)
      id {x} = FS.id {x} , P₁-id x
      _⋆_ {x} {y} {z} f g = 
        FS._⋆_ {x} {y} {z} (f .fst) (g .fst) , P₁-⋆ (f .snd) (g .snd)
      ⋆IdL (f , _) = {! !}
      ⋆IdR = {! !}
      ⋆Assoc = {! !}

      

