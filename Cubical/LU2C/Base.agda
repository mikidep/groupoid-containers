-- Adapted from:
-- E. Finster, S. Mimram, M. Lucas, and T. Seiller,
-- “A Cartesian LU2C of Polynomial Pseudofunctors in Homotopy Type Theory,”
-- EPTCS 351, 2021, pp. 67-83, vol. 351, pp. 67–83, Dec. 2021, doi: 10.4204/eptcs.351.5.

-- TODO: Rename to Locally Univalent (2,1)-categories

open import Cubical.Foundations.Prelude
open import Cubical.WildCat.Base hiding (_[_,_])

module Cubical.LU2C.Base where

private variable
  ℓC ℓC' : Level

open import Cubical.Foundations.GroupoidLaws

record LU2CSyntax (WC : WildCat ℓC ℓC') : Type (ℓ-max ℓC ℓC') where
  open WildCat WC using (ob; Hom[_,_])
  open WildCat WC using 
      ( id
      ; _⋆_
      ; ⋆IdL
      ; ⋆IdR
      ; ⋆Assoc
      ) public

  infixr 41 _◃_
  infixl 40 _▹_
  infixr 42 _⋆₂_

  private variable
    a b c : ob
    f f′ f″ : Hom[ a , b ]
    g g′ g″ : Hom[ b , c ]

  _⋆₂_ : 
    f ≡ f′
    → g ≡ g′
    → f ⋆ g ≡ f′ ⋆ g′
  _⋆₂_ p q = cong₂ _⋆_ p q

  _◃_ : 
    (f : Hom[ a , b ])
    → g ≡ g′
    → f ⋆ g ≡ f ⋆ g′
  f ◃ g≡g′ = refl {x = f} ⋆₂ g≡g′

  _▹_ : 
    f ≡ f′
    → (g : Hom[ b , c ])
    → f ⋆ g ≡ f′ ⋆ g
  f≡f′ ▹ g = f≡f′ ⋆₂ refl {x = g}

  ◃-∙ : 
    (p : g ≡ g′)
    (q : g′ ≡ g″)
    → f ◃ (p ∙ q)
      ≡ f ◃ p ∙ f ◃ q
  ◃-∙ {f} p q = congFunct (f ⋆_) p q

  ▹-∙ : 
    (p : f ≡ f′)
    (q : f′ ≡ f″)
    → (p ∙ q) ▹ g
      ≡ p ▹ g ∙ q ▹ g
  ▹-∙ {g} p q = congFunct (_⋆ g) p q

  whisk-interchange : 
    (p : f ≡ f′)
    (q : g ≡ g′)
    → f ◃ q ∙ p ▹ g′
      ≡ p ▹ g ∙ f′ ◃ q
  whisk-interchange p q = aux₁ ∙ aux₂
    where
    open import Prelude.ExtraGpdLaws
    open import Cubical.Foundations.Function using (flip)
    aux₁ = sym (cong₂Funct' (flip _⋆_) q p)
    aux₂ = cong₂Funct' _⋆_ p q

open LU2CSyntax {{...}}

module LU2CSynWC {ℓC ℓC'} (WC : WildCat ℓC ℓC') where
  instance
    LU2CSynWC : LU2CSyntax WC
    LU2CSynWC = record { }
    
module _ {ℓC ℓC'} {WC : WildCat ℓC ℓC'} where
  open WildCat WC using (ob; Hom[_,_])
  open LU2CSynWC WC

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
  open LU2CSynWC WC
  open LU2CSynWC WC

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

module LU2CSyn2C {ℓC ℓC'} (C : LU2C ℓC ℓC') where
  private module C = LU2C C

  instance
    LU2CSyn2C : LU2CSyntax C.str
    LU2CSyn2C = record { }
