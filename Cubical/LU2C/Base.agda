-- Adapted from:
-- E. Finster, S. Mimram, M. Lucas, and T. Seiller,
-- “A Cartesian LU2C of Polynomial Pseudofunctors in Homotopy Type Theory,”
-- EPTCS 351, 2021, pp. 67-83, vol. 351, pp. 67–83, Dec. 2021, doi: 10.4204/eptcs.351.5.

open import Cubical.Foundations.Prelude
open import Cubical.WildCat.Base hiding (_[_,_])
open import Cubical.WildCat.AsLU2C.Instances

module Cubical.LU2C.Base where

open import Cubical.Foundations.GroupoidLaws

module _ {ℓC ℓC'} {WC : WildCat ℓC ℓC'} where
  open WildCat WC using (ob; Hom[_,_])
  open NotWC WC

  triangleFromSquare : {a b c : ob}
    {f : Hom[ a , b ]} {g : Hom[ b , c ]}
    → Square
      (⋆Assoc f id g)
      (⋆IdR f ▹ g)
      refl
      (f ◃ ⋆IdL g)
    → ⋆Assoc f id g ∙ f ◃ ⋆IdL g ≡ ⋆IdR f ▹ g
  triangleFromSquare = PathP→compPathL∙∙
    where
    open import Prelude.Square

module _ {ℓC ℓC'} (WC : WildCat ℓC ℓC') where
  open WildCat WC using (ob; Hom[_,_])
  open NotWC WC

  record IsLU2C : Type (ℓ-max ℓC ℓC') where
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

module _ (ℓC ℓC' : Level) where
  record LU2C : Type (ℓ-suc (ℓ-max ℓC ℓC')) where
    field
      str : WildCat ℓC ℓC'
      isLU2C : IsLU2C str
    open WildCat str public
    open IsLU2C isLU2C public

open LU2C

module _ {ℓC ℓC' : Level} where
  -- Helpful syntax/notation
  _[_,_] : (C : LU2C ℓC ℓC') → (x y : C .ob) → Type ℓC'
  _[_,_] = Hom[_,_]

module Not2C {ℓC ℓC'} (C : LU2C ℓC ℓC') where
  private module C = LU2C C

  instance
    NotC : Notation C.str
    NotC = record { }
