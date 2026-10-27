-- Import this instead of AsLU2C.Instances to recover implicit Σ objects.
-- Existing NotWC and Not2C registrations work unchanged: the instance type
-- is the usual Notation, only the exported operations carry tactics.
open import Cubical.Foundations.Prelude
open import Cubical.WildCat.Base
open import Reflection.InferSigma using (inferΣ)

import Cubical.WildCat.AsLU2C.Instances as LI

module Cubical.WildCat.FullSub.Notation
  {ℓC ℓC' : Level} {C : WildCat ℓC ℓC'} {{_ : LI.Notation C}}
  where

open LI public using (Notation; module NotWC)

open WildCat C using (ob; Hom[_,_])

import Cubical.WildCat.AsLU2C.Notation C as LN
import Cubical.WildCat.AsLU2C.Properties {C = C} as LP

id : {@(tactic inferΣ ob) x : ob} → _
id {x} = LN.id {x}

_⋆_ : {@(tactic inferΣ ob) x y z : ob} → _
_⋆_ {x} {y} {z} = LN._⋆_ {x} {y} {z}

⋆IdL : {@(tactic inferΣ ob) x y : ob} → _
⋆IdL {x} {y} = LN.⋆IdL {x} {y}

⋆IdR : {@(tactic inferΣ ob) x y : ob} → _
⋆IdR {x} {y} = LN.⋆IdR {x} {y}

⋆Assoc : {@(tactic inferΣ ob) u v w x : ob} → _ 
⋆Assoc {u} {v} {w} {x} = LN.⋆Assoc {u} {v} {w} {x}

infixr 41 _◃_
infixl 40 _▹_
infixr 42 _⋆₂_

_⋆₂_ :
  {@(tactic inferΣ ob) a b c : ob}
  {f f′ : Hom[ a , b ]}
  {g g′ : Hom[ b , c ]} 
  → _
_⋆₂_ {a} {b} {c} {f} {f′} {g} {g′} 
  = LN._⋆₂_ {a = a} {b} {c} {f} {f′} {g} {g′}

_◃_ :
  {@(tactic inferΣ ob) a b c : ob}
  {g g′ : Hom[ b , c ]} 
  → _
_◃_ {a} {b} {c} {g} {g′} = LN._◃_ {a = a} {b} {c} {g} {g′} 

_▹_ :
  {@(tactic inferΣ ob) a b c : ob}
  {f f′ : Hom[ a , b ]}
  → _
_▹_ {a} {b} {c} {f} {f′} = LN._▹_ {a = a} {b} {c} {f} {f′} 

◃-∙ : 
  {@(tactic inferΣ ob) a b c : ob}
  {f : Hom[ a , b ]}
  {g g′ g″ : C [ b , c ]}
  → _
◃-∙ {a} {b} {c} {f} {g} {g′} {g″} = 
  LP.◃-∙ {a = a} {b} {c} {f} {g} {g′} {g″}

▹-∙ : 
  {@(tactic inferΣ ob) a b c : ob}
  {f f′ f″ : Hom[ a , b ]}
  {g : Hom[ b , c ]}
  → _
▹-∙ {a} {b} {c} {f} {f′} {f″} {g} = 
  LP.▹-∙ {a = a} {b} {c} {f} {f′} {f″} {g}

whisk-interchange : 
  {@(tactic inferΣ ob) a b c : ob}
  {f f′ : Hom[ a , b ]}
  {g g′ : Hom[ b , c ]}
  → _
whisk-interchange 
  {a} {b} {c} {f} {f′} {g} {g′} = 
  LP.whisk-interchange {a = a} {b} {c} {f} {f′} {g} {g′} 

-- reassoc

infixr 41 _◃′_
infixl 40 _▹′_

_◃′_ :
  {@(tactic inferΣ ob) a b c : ob}
  {g g′ : Hom[ b , c ]} 
  → _
_◃′_ {a} {b} {c} {g} {g′} = LN._◃′_ {a = a} {b} {c} {g} {g′} 

_▹′_ :
  {@(tactic inferΣ ob) a b c : ob}
  {f f′ : Hom[ a , b ]}
  → _
_▹′_ {a} {b} {c} {f} {f′} = LN._▹′_ {a = a} {b} {c} {f} {f′} 
