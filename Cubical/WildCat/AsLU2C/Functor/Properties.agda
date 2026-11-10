open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws
open import Prelude.ExtraGpdLaws

open import Cubical.WildCat.Base
open import Cubical.WildCat.Functor
import Cubical.WildCat.AsLU2C.Functor.Notation as NotF

open import Cubical.WildCat.AsLU2C.Instances

module Cubical.WildCat.AsLU2C.Functor.Properties 
  {ℓC ℓC' ℓD ℓD' : Level}
  {C : WildCat ℓC ℓC'}
  {D : WildCat ℓD ℓD'} 
  -- {E : WildCat ℓE ℓE'} 
  {F : WildFunctor C D}
  -- {G : WildFunctor C D}
  where

open NotWC C
open NotWC D
-- open NotWC E

private module F = NotF F
open F using (F₀; F₁; F₂)
-- private module G = NotF G
-- open G using () renaming 
--   ( F₀ to G₀
--   ; F₁ to G₁
--   ; F₂ to G₂
--   )

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
  sym (F.F-seq f g)
  ∙ F₂ sq
  ∙ F.F-seq h k

F-seq-nat : ∀ {x y z}
    {f f′ : C [ x , y ]}
    {g g′ : C [ y , z ]}
    (p : f ≡ f′)
    (q : g ≡ g′)
  → F.F-seq f g
    ∙ F₂ p ⋆₂ F₂ q
    ≡ F₂ (p ⋆₂ q)
    ∙ F.F-seq f′ g′
F-seq-nat {f} {g} p q = J2 Q r p q
  where
  Q = λ f′ p g′ q
        → F.F-seq f g
          ∙ F₂ p ⋆₂ F₂ q
          ≡ F₂ (p ⋆₂ q)
          ∙ F.F-seq f′ g′
  r = sym (rUnit _) ∙ lUnit _

F-seq-nat-Square : ∀ {x y z}
    {f f′ : C [ x , y ]}
    {g g′ : C [ y , z ]}
    (p : f ≡ f′)
    (q : g ≡ g′)
  → Square
    (F.F-seq f g)
    (F.F-seq f′ g′)
    (F₂ (p ⋆₂ q))
    (F₂ p ⋆₂ F₂ q)
F-seq-nat-Square p q i j = F.F-seq (p i) (q i) j

F-seq-nat-sym : ∀ {x y z}
    {f f′ : C [ x , y ]}
    {g g′ : C [ y , z ]}
    (p : f ≡ f′)
    (q : g ≡ g′)
  → F₂ p ⋆₂ F₂ q
    ∙ sym (F.F-seq f′ g′)
    ≡ sym (F.F-seq f g)
    ∙ F₂ (p ⋆₂ q)
F-seq-nat-sym {f} {g} p q = J2 Q r p q
  where
  Q = λ f′ p g′ q
        → F₂ p ⋆₂ F₂ q
          ∙ sym (F.F-seq f′ g′)
          ≡ sym (F.F-seq f g)
          ∙ F₂ (p ⋆₂ q)
  r = sym (lUnit _) ∙ rUnit _

-- F□-◃ : ∀ {x y z}
--   {f : C [ x , y ]}
--   {g h : C [ y , z ]}
--   (g≡h : g ≡ h)
--   → F□ (f ◃ g≡h)
--     ≡ F₁ f ◃ F₂ g≡h
-- F□-◃ g≡h =
--   shuffleSymL (sym (F-seq-nat refl g≡h))

-- F□-▹ : ∀ {x y z}
--   {f g : C [ x , y ]}
--   {h : C [ y , z ]}
--   (f≡g : f ≡ g)
--   → F□ (f≡g ▹ h)
--     ≡ F₂ f≡g ▹ F₁ h
-- F□-▹ f≡g =
--   shuffleSymL (sym (F-seq-nat f≡g refl))

-- -- In other words...
-- F₂-◃ : ∀ {x y z}
--   {f : C [ x , y ]}
--   {g h : C [ y , z ]}
--   (g≡h : g ≡ h)
--   → F₂ (f ◃ g≡h)
--     ≡ F.F-seq f g
--     ∙ F₁ f ◃ F₂ g≡h
--     ∙ sym (F.F-seq f h)
-- F₂-◃ g≡h =
--   shuffleSymR (sym (shuffleSymL (sym (F□-◃ g≡h))))
--   ∙ sym assoc-inf

-- F₂-▹ : ∀ {x y z}
--   {f g : C [ x , y ]}
--   {h : C [ y , z ]}
--   (f≡g : f ≡ g)
--   → F₂ (f≡g ▹ h)
--     ≡ F.F-seq f h
--     ∙ F₂ f≡g ▹ F₁ h
--     ∙ sym (F.F-seq g h)
-- F₂-▹ f≡g =
--   shuffleSymR (sym (shuffleSymL (sym (F□-▹ f≡g))))
--   ∙ sym assoc-inf

