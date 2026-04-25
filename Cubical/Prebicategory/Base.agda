-- Adapted from:
-- E. Finster, S. Mimram, M. Lucas, and T. Seiller, 
-- “A Cartesian Bicategory of Polynomial Functors in Homotopy Type Theory,” 
-- EPTCS 351, 2021, pp. 67-83, vol. 351, pp. 67–83, Dec. 2021, doi: 10.4204/eptcs.351.5.

-- Shouldn′t these be called Pre-2,1-categories?

open import Prelude
open import Cubical.WildCat.Base

module Cubical.Prebicategory.Base where

module Whiskering {ℓC ℓC′} (WC : WildCat ℓC ℓC′) where
  open WildCat WC

  infixr 41 _◃_
  infixl 40 _▹_ 

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

module 2CellLaws {ℓC ℓC′} (WC : WildCat ℓC ℓC′) where
  open WildCat WC
  open import Cubical.Foundations.GroupoidLaws
  open Whiskering WC

  ◃-∙ : ∀ {a b c : ob}
    {f : Hom[ a , b ]}
    {g h k : Hom[ b , c ]}
    (p : g ≡ h)
    (q : h ≡ k)
    → f ◃ (p ∙ q)
      ≡ f ◃ p ∙ f ◃ q
  ◃-∙ {f} p q = congFunct (f ⋆_) p q

  ▹-∙ : ∀ {a b c : ob}
    {f g h : Hom[ a , b ]}
    {k : Hom[ b , c ]}
    (p : f ≡ g)
    (q : g ≡ h)
    → (p ∙ q) ▹ k
      ≡ p ▹ k ∙ q ▹ k
  ▹-∙ {k} p q = congFunct (_⋆ k) p q

  whisk-interchange : ∀ {a b c : ob}
    {f g : Hom[ a , b ]}
    {h k : Hom[ b , c ]}
    (p : f ≡ g)
    (q : h ≡ k)
    → f ◃ q ∙ p ▹ k
      ≡ p ▹ h ∙ g ◃ q
  whisk-interchange {f} {g} {h} {k} p q = aux₁ ∙ aux₂
    where
    open import Prelude.ExtraGpdLaws
    open import Cubical.Foundations.Function using (flip)
    aux₁ : cong (f ⋆_) q ∙ cong (_⋆ k) p ≡ cong₂ _⋆_ p q
    aux₁ = sym (cong₂Funct′ (flip _⋆_) q p)
    aux₂ : cong₂ _⋆_ p q ≡ cong (_⋆ h) p ∙ cong (g ⋆_) q
    aux₂ = cong₂Funct′ _⋆_ p q

module _ {ℓC ℓC′} (WC : WildCat ℓC ℓC′) where
  open WildCat WC
  open Whiskering WC

  record IsPrebicategory' : Type (ℓ-max ℓC ℓC′) where
    field
      triangle  : {a b c : ob}
                  (f : Hom[ a , b ]) (g : Hom[ b , c ])
                  → Square (⋆Assoc f id g) (⋆IdR f ▹ g) refl (f ◃ ⋆IdL g)
      pentagon-α : {a b c d e : ob}
                  (f : Hom[ a , b ]) (g : Hom[ b , c ])
                  (h : Hom[ c , d ]) (i : Hom[ d , e ])
                  → ((f ⋆ g) ⋆ h) ⋆ i ≡ f ⋆ (g ⋆ (h ⋆ i))
      pentagon₁  : {a b c d e : ob}
                  (f : Hom[ a , b ]) (g : Hom[ b , c ])
                  (h : Hom[ c , d ]) (i : Hom[ d , e ])
                  → Square (⋆Assoc f (g ⋆ h) i) (pentagon-α f g h i) (sym $ ⋆Assoc f g h ▹ i) (f ◃ ⋆Assoc g h i)
      pentagon₂  : {a b c d e : ob}
                  (f : Hom[ a , b ]) (g : Hom[ b , c ])
                  (h : Hom[ c , d ]) (i : Hom[ d , e ])
                  → Square (⋆Assoc (f ⋆ g) h i) (pentagon-α f g h i) refl (⋆Assoc f g (h ⋆ i))
      isGpdHom : ∀ {a b} → isGroupoid (Hom[ a , b ])

  record IsPrebicategory : Type (ℓ-max ℓC ℓC′) where
    field
      triangle  : {a b c : ob} 
                  (f : Hom[ a , b ]) (g : Hom[ b , c ])
                  → ⋆Assoc f id g ∙ f ◃ ⋆IdL g
                    ≡ ⋆IdR f ▹ g
      pentagon  : {a b c d e : ob} 
                  (f : Hom[ a , b ]) (g : Hom[ b , c ]) 
                  (h : Hom[ c , d ]) (i : Hom[ d , e ]) 
                  → ⋆Assoc f g h ▹ i
                      ∙ ⋆Assoc f (g ⋆ h) i ∙ f ◃ ⋆Assoc g h i 
                    ≡ ⋆Assoc (f ⋆ g) h i ∙ ⋆Assoc f g (h ⋆ i)  
      isGpdHom : ∀ {a b} → isGroupoid (Hom[ a , b ])

module _ (ℓC ℓC′ : Level) where
  record Prebicategory : Type (ℓ-suc (ℓ-max ℓC ℓC′)) where
    field
      str : WildCat ℓC ℓC′
      isPrebicat : IsPrebicategory str
    open WildCat str public
    open Whiskering str public
    open IsPrebicategory isPrebicat public

