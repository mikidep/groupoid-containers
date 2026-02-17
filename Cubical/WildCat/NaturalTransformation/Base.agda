module Cubical.WildCat.NaturalTransformation.Base where

open import Cubical.Foundations.Prelude

open import Cubical.WildCat.Base
open import Cubical.WildCat.Functor

private
  variable
    ℓC ℓC′ ℓD ℓD′ : Level

module _ {C : WildCat ℓC ℓC′} {D : WildCat ℓD ℓD′} where
  module _ {F G : WildFunctor C D} {α β : WildNatTrans _ _ F G} where
    open WildCat
    open WildFunctor
    open WildNatTrans

    makeNatTransPath : 
      (p : α .N-ob ≡ β .N-ob)
      → (∀ {x y} f → PathP (λ i → (F .F-hom {x} {y} f) ⋆⟨ D ⟩ (p i _) ≡ (p i _) ⋆⟨ D ⟩ (G .F-hom f))
          (α .N-hom f) (β .N-hom f))
      → α ≡ β
    makeNatTransPath p q i .N-ob = p i
    makeNatTransPath p q i .N-hom f = q f i
