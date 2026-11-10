open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws
open import Prelude.ExtraGpdLaws

open import Cubical.WildCat.Base
open import Cubical.WildCat.Functor

module Cubical.WildCat.AsLU2C.Functor.Notation 
  {ℓC ℓC' ℓD ℓD' : Level}
  {C : WildCat ℓC ℓC'}
  {D : WildCat ℓD ℓD'} 
  (F : WildFunctor C D)
  where

open WildFunctor F using (
    F-id;
    F-seq
  ) renaming (
    F-ob to F₀; F-hom to F₁
  ) public

F₂ : ∀ {x y} {f g : C [ x , y ]}
  (f≡g : f ≡ g)
  → F₁ f ≡ F₁ g
F₂ = cong F₁

-- reassoc helper
open import Prelude.Reassoc
F₂′ : ∀ {x y} {f g : C [ x , y ]}
  (f≡g : Term f g)
  → Term (F₁ f) (F₁ g)
F₂′ = cong′ F₁ 

