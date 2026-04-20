module Cubical.WildCat.NaturalTransformation.Base where

open import Cubical.Foundations.Prelude

open import Cubical.WildCat.Base
open import Cubical.WildCat.Functor

private
  variable
    ℓC ℓC′ ℓD ℓD′ ℓE ℓE′ : Level

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

module _ {C : WildCat ℓC ℓC′} {D : WildCat ℓD ℓD′} {E : WildCat ℓE ℓE′} where
  module _ {F G : WildFunctor C D} (α : WildNatTrans _ _ F G) (H : WildFunctor D E) where
    open WildNatTrans
    open WildNatTrans α using () renaming (N-ob to α₀)
    open WildFunctor 
    open WildFunctor F using () renaming (F-hom to F₁)
    open WildFunctor G using () renaming (F-hom to G₁)
    open WildFunctor H using () renaming (F-hom to H₁)
    open WildCat D renaming (Hom[_,_] to E[_,_]; _⋆_ to _⋆ᵈ_)
    open WildCat E using (_⋆_) renaming (Hom[_,_] to E[_,_])

    private
      _⋆F_ = comp-WildFunctor {C = C} {D} {E}

    whiskerR-natTrans : WildNatTrans _ _ (F ⋆F H) (G ⋆F H)
    whiskerR-natTrans .N-ob X = H .F-hom (α .N-ob X)
    whiskerR-natTrans .N-hom f = 
      sym (H .F-seq _ _) 
      ∙ cong H₁ (α .N-hom f) 
      ∙ H .F-seq _ _ 
      --   H₁ (F₁ f) ⋆ H₁ (α₀ Y) 
      -- ≡⟨ sym (H .F-seq _ _) ⟩ 
      --   H₁ (F₁ f ⋆ᵈ α₀ Y) 
      -- ≡⟨ cong H₁ (α .N-hom f)⟩ 
      --   H₁ (α₀ X ⋆ᵈ G₁ f) 
      -- ≡⟨ H .F-seq _ _ ⟩ 
      --   H₁ (α₀ X) ⋆ H₁ (G₁ f)
      -- ∎
