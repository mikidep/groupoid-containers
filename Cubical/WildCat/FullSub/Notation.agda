-- Import this instead of AsLU2C.Instances to recover implicit Σ objects.
-- Existing NotWC and Not2C registrations work unchanged: the instance type
-- is the usual Notation, only the exported operations carry tactics.
open import Cubical.Foundations.Prelude
open import Cubical.WildCat.Base
open import CubicalCompat.Reflection.InferSigma using (inferΣ)

module Cubical.WildCat.FullSub.Notation
  {ℓC ℓC' : Level}
  where

open import Cubical.WildCat.AsLU2C.Instances public
  using (Notation; module NotWC)

module _ {C : WildCat ℓC ℓC'} {{_ : Notation C}} where
  private module C = WildCat C
  open C using (ob; Hom[_,_])

  id : {@(tactic inferΣ C.ob) x : C.ob} → C.Hom[ x , x ]
  id {x} = C.id {x}

  _⋆_ : {@(tactic inferΣ C.ob) x y z : C.ob}
    → C.Hom[ x , y ] → C.Hom[ y , z ] → C.Hom[ x , z ]
  _⋆_ {x} {y} {z} = C._⋆_ {x} {y} {z}

  ⋆IdL : {@(tactic inferΣ ob) x y : ob}
    (f : Hom[ x , y ]) → id ⋆ f ≡ f
  ⋆IdL {x} {y} = C.⋆IdL {x} {y}

  ⋆IdR : {@(tactic inferΣ ob) x y : ob}
    (f : Hom[ x , y ]) → f ⋆ id ≡ f
  ⋆IdR {x} {y} = C.⋆IdR {x} {y}

  ⋆Assoc : {@(tactic inferΣ ob) u v w x : ob}
    (f : Hom[ u , v ]) (g : Hom[ v , w ]) (h : Hom[ w , x ])
    → (f ⋆ g) ⋆ h ≡ f ⋆ (g ⋆ h)
  ⋆Assoc {u} {v} {w} {x} = C.⋆Assoc {u} {v} {w} {x}

  infixr 41 _◃_
  infixl 40 _▹_
  infixr 42 _⋆₂_

  _⋆₂_ :
    {@(tactic inferΣ ob) a b c : ob}
    {f f′ : Hom[ a , b ]}
    {g g′ : Hom[ b , c ]}
    → f ≡ f′
    → g ≡ g′
    → f ⋆ g ≡ f′ ⋆ g′
  _⋆₂_ p q = cong₂ _⋆_ p q

  _◃_ :
    {@(tactic inferΣ ob) a b c : ob}
    {g g′ : Hom[ b , c ]}
    (f : Hom[ a , b ])
    → g ≡ g′
    → f ⋆ g ≡ f ⋆ g′
  f ◃ g≡g′ = refl {x = f} ⋆₂ g≡g′

  _▹_ :
    {@(tactic inferΣ ob) a b c : ob}
    {f f′ : Hom[ a , b ]}
    → f ≡ f′
    → (g : Hom[ b , c ])
    → f ⋆ g ≡ f′ ⋆ g
  f≡f′ ▹ g = f≡f′ ⋆₂ refl {x = g}
