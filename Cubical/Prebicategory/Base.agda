-- Adapted from:
-- E. Finster, S. Mimram, M. Lucas, and T. Seiller, 
-- “A Cartesian Bicategory of Polynomial Functors in Homotopy Type Theory,” 
-- EPTCS 351, 2021, pp. 67-83, vol. 351, pp. 67–83, Dec. 2021, doi: 10.4204/eptcs.351.5.

-- Shouldn′t these be called Pre-2,1-categories?

open import Prelude
open import Cubical.WildCat.Base

module Cubical.Prebicategory.Base where

module _ {ℓC ℓC′} (WC : WildCat ℓC ℓC′) where
  open WildCat WC

  record is-Prebicategory : Type (ℓ-max ℓC ℓC′) where
    field
      triangle  : {a b c : ob} 
                  (f : Hom[ a , b ]) (g : Hom[ b , c ])
                  → ⋆Assoc f id g ∙ cong (f ⋆_) (⋆IdL g) 
                    ≡ cong (_⋆ g) (⋆IdR f)
      pentagon  : {a b c d e : ob} 
                  (f : Hom[ a , b ]) (g : Hom[ b , c ]) 
                  (h : Hom[ c , d ]) (i : Hom[ d , e ]) 
                  → cong (_⋆ i) (⋆Assoc f g h) 
                      ∙ ⋆Assoc f (g ⋆ h) i ∙ cong (f ⋆_) (⋆Assoc g h i) 
                    ≡ ⋆Assoc (f ⋆ g) h i ∙ ⋆Assoc f g (h ⋆ i)  
      isGpdHom : ∀ {a b} → isGroupoid (Hom[ a , b ])

module _ (ℓC ℓC′ : Level) where
  record Prebicategory : Type (ℓ-suc (ℓ-max ℓC ℓC′)) where
    field
      str : WildCat ℓC ℓC′
      is-prebicat : is-Prebicategory str
    open WildCat str public
    open is-Prebicategory is-prebicat public
    _◃_ : ∀ {a b c : ob}
      (f : Hom[ a , b ])
      {g h : Hom[ b , c ]}
      → g ≡ h
      → f ⋆ g ≡ f ⋆ h
    f ◃ g≡h = cong (f ⋆_) g≡h

    _▹_ : ∀ {a b c : ob}
      {f g : Hom[ a , b ]}
      → f ≡ g
      → (h : Hom[ b , c ])
      → f ⋆ h ≡ g ⋆ h
    f≡g ▹ h = cong (_⋆ h) f≡g
