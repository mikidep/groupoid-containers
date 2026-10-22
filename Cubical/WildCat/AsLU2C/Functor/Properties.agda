open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws
open import Prelude.ExtraGpdLaws

open import Cubical.WildCat.Base
open import Cubical.WildCat.Functor

open import Cubical.WildCat.AsLU2C.Instances

module Cubical.WildCat.AsLU2C.Functor.Properties 
  {ℓC ℓC' ℓD ℓD' : Level}
  {C : WildCat ℓC ℓC'}
  {D : WildCat ℓD ℓD'} 
  {F : WildFunctor C D}
  where

open NotWC C
open NotWC D

open import Cubical.WildCat.AsLU2C.Functor.Notation F

F₂-funct : ∀ {x y}
  {f g h : C [ x , y ]}
  (α : f ≡ g)
  (β : g ≡ h)
  → F₂ (α ∙ β) ≡ F₂ α ∙ F₂ β
F₂-funct = congFunct F₁

F□ : ∀ {x y z w}
  {f : C [ x , y ]}
  {g : C [ y , z ]}
  {h : C [ x , w ]}
  {k : C [ w , z ]}
  → f ⋆ g ≡ h ⋆ k
  → F₁ f ⋆ F₁ g ≡ F₁ h ⋆ F₁ k
F□ {f} {g} {h} {k} sq =
  sym (F-seq f g)
  ∙ F₂ sq
  ∙ F-seq h k

F-seq-nat : ∀ {x y z}
    {f f′ : C [ x , y ]}
    {g g′ : C [ y , z ]}
    (p : f ≡ f′)
    (q : g ≡ g′)
  → F-seq f g
    ∙ F₂ p ⋆₂ F₂ q
    ≡ F₂ (p ⋆₂ q)
    ∙ F-seq f′ g′
F-seq-nat {x} {y} {z} {f} {g} p q = J2 Q r p q
  where
  Q :
    (f' : C [ x , y ])
    (p' : f ≡ f')
    (g' : C [ y , z ])
    (q' : g ≡ g')
    → Type ℓD'
  Q f' p' g' q' =
    F-seq f g
    ∙ F₂ p' ⋆₂ F₂ q'
    ≡ F₂ (p' ⋆₂ q')
    ∙ F-seq f' g'
  r = sym (rUnit _) ∙ lUnit _

F□-◃ : ∀ {x y z}
  {f : C [ x , y ]}
  {g h : C [ y , z ]}
  (g≡h : g ≡ h)
  → F□ (f ◃ g≡h)
    ≡ F₁ f ◃ F₂ g≡h
F□-◃ g≡h =
  shuffleSymL (sym (F-seq-nat refl g≡h))

F□-▹ : ∀ {x y z}
  {f g : C [ x , y ]}
  {h : C [ y , z ]}
  (f≡g : f ≡ g)
  → F□ (f≡g ▹ h)
    ≡ F₂ f≡g ▹ F₁ h
F□-▹ f≡g =
  shuffleSymL (sym (F-seq-nat f≡g refl))

-- In other words...
F₂-◃ : ∀ {x y z}
  {f : C [ x , y ]}
  {g h : C [ y , z ]}
  (g≡h : g ≡ h)
  → F₂ (f ◃ g≡h)
    ≡ F-seq f g
    ∙ F₁ f ◃ F₂ g≡h
    ∙ sym (F-seq f h)
F₂-◃ g≡h =
  shuffleSymR (sym (shuffleSymL (sym (F□-◃ g≡h))))
  ∙ sym assoc-inf

F₂-▹ : ∀ {x y z}
  {f g : C [ x , y ]}
  {h : C [ y , z ]}
  (f≡g : f ≡ g)
  → F₂ (f≡g ▹ h)
    ≡ F-seq f h
    ∙ F₂ f≡g ▹ F₁ h
    ∙ sym (F-seq g h)
F₂-▹ f≡g =
  shuffleSymR (sym (shuffleSymL (sym (F□-▹ f≡g))))
  ∙ sym assoc-inf

