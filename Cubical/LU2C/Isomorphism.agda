open import Cubical.Foundations.Prelude

open import Cubical.LU2C.Base
open import Cubical.WildCat.AsLU2C.Instances

module Cubical.LU2C.Isomorphism {ℓC ℓC' : Level} {C : LU2C ℓC ℓC'} where

private module C = LU2C C

open Not2C C

record isIso 
  {x y : C.ob} (f : C [ x , y ]) : Type ℓC' where
  field
    f⁻ : C [ y , x ]
    sec : f⁻ ⋆ f ≡ id {x = y}
    ret : f ⋆ f⁻ ≡ id {x = x}
    -- a triangle?
    -- cf. https://arxiv.org/abs/1903.01152
    -- look into prop. 3.11

Iso : (x y : C.ob) → Type _
Iso x y = Σ (C [ x , y ]) isIso

idIso : (x : C.ob) → Iso x x
idIso x = id , record where
  f⁻ = id
  sec = ⋆IdL _
  ret = ⋆IdR _

idToIso : (x y : C.ob) → x ≡ y → Iso x y
idToIso x y = J Q d
  -- J Q d
  where
  Q = λ y _ → Iso x y
  d = idIso _

