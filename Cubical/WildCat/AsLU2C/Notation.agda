open import Cubical.Foundations.Prelude

open import Cubical.WildCat.Base

module Cubical.WildCat.AsLU2C.Notation 
  {ℓC ℓC' : Level}
  (C : WildCat ℓC ℓC')
  where

  open WildCat C using (ob; Hom[_,_])
  open WildCat C using 
      ( id
      ; _⋆_
      ; ⋆IdL
      ; ⋆IdR
      ; ⋆Assoc
      ) public

  infixr 41 _◃_
  infixl 40 _▹_
  infixr 42 _⋆₂_

  _⋆₂_ : 
    {a b c : ob}
    {f f′ : Hom[ a , b ]}
    {g g′ : Hom[ b , c ]}
    → f ≡ f′
    → g ≡ g′
    → f ⋆ g ≡ f′ ⋆ g′
  _⋆₂_ p q = cong₂ _⋆_ p q

  _◃_ : 
    {a b c : ob}
    {g g′ : Hom[ b , c ]}
    (f : Hom[ a , b ])
    → g ≡ g′
    → f ⋆ g ≡ f ⋆ g′
  f ◃ g≡g′ = refl {x = f} ⋆₂ g≡g′

  _▹_ : 
    {a b c : ob}
    {f f′ : Hom[ a , b ]}
    → f ≡ f′
    → (g : Hom[ b , c ])
    → f ⋆ g ≡ f′ ⋆ g
  f≡f′ ▹ g = f≡f′ ⋆₂ refl {x = g}

