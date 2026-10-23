open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws

open import Cubical.WildCat.Base

module Cubical.WildCat.AsLU2C.Properties 
  {ℓC ℓC' : Level}
  {C : WildCat ℓC ℓC'}
  where

open import Cubical.WildCat.AsLU2C.Notation C

open WildCat C using (ob)

◃-∙ : 
  {a b c : ob}
  {f : C [ a , b ]}
  {g g′ g″ : C [ b , c ]}
  (p : g ≡ g′)
  (q : g′ ≡ g″)
  → f ◃ (p ∙ q)
    ≡ f ◃ p ∙ f ◃ q
◃-∙ {f} p q = congFunct (f ⋆_) p q

▹-∙ : 
  {a b c : ob}
  {f f′ f″ : C [ a , b ]}
  {g : C [ b , c ]}
  (p : f ≡ f′)
  (q : f′ ≡ f″)
  → (p ∙ q) ▹ g
    ≡ p ▹ g ∙ q ▹ g
▹-∙ {g} p q = congFunct (_⋆ g) p q

whisk-interchange : 
  {a b c : ob}
  {f f′ : C [ a , b ]}
  {g g′ : C [ b , c ]}
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

