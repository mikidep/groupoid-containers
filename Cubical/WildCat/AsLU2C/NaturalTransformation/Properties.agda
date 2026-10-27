open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws
open import Cubical.WildCat.Base 
open import Cubical.WildCat.Functor

open import Cubical.WildCat.AsLU2C.Instances
import Cubical.WildCat.AsLU2C.Functor.Notation as NotF

module Cubical.WildCat.AsLU2C.NaturalTransformation.Properties 
  {ℓC ℓC' ℓD ℓD' : Level}
  {C : WildCat ℓC ℓC'}
  {D : WildCat ℓD ℓD'} 
  {F G : WildFunctor C D}
  where

open NotWC C
open NotWC D
open NotF F using (F₁; F₂)
open NotF G using () renaming 
  ( F₁ to G₁
  ; F₂ to G₂
  )

module _ (α : WildNatTrans _ _ F G) where
  open WildNatTrans α using ()
    renaming (N-ob to α₀; N-hom to α□)

  N-hom-nat :
    ∀ {X} {Y}
      {f g : C [ X , Y ]}
      (f≡g : f ≡ g)
    →   α□ f ∙ α₀ X ◃ G₂ f≡g
      ≡ F₂ f≡g ▹ α₀ Y ∙ α□ g
  N-hom-nat {X} {Y} {f} {g = _} = J Q d
    where
    Q = λ f' f≡f' →
      α□ f ∙ α₀ X ◃ G₂ f≡f'
      ≡ F₂ f≡f' ▹ α₀ Y ∙ α□ f'
    d = sym (rUnit _) ∙ lUnit _

module _ {α β : WildNatTrans _ _ F G} where
  open WildNatTrans α using ()
    renaming (N-ob to α₀; N-hom to α□)
  open WildNatTrans β using ()
    renaming (N-ob to β₀; N-hom to β□)

  -- TODO: Surely an equivalence
  natTransPath→mod :
    (m : ∀ x → α₀ x ≡ β₀ x)
    → ∀ {x y} (f : C [ x , y ])
    → Square
      (α□ f)      
      (β□ f)
      (F₁ f ◃ m y)
      (m x ▹ G₁ f)
    → α□ f ∙ m x ▹ G₁ f
      ≡ F₁ f ◃ m y ∙ β□ f
  natTransPath→mod _ _ sq = 
    Square→compPath (flipSquare sq)
    where open import Cubical.Foundations.Path

  mod→natTransPath :
    (m : ∀ x → α₀ x ≡ β₀ x)
    → ∀ {x y} (f : C [ x , y ])
    → α□ f ∙ m x ▹ G₁ f
      ≡ F₁ f ◃ m y ∙ β□ f
    → Square
      (α□ f)      
      (β□ f)
      (F₁ f ◃ m y)
      (m x ▹ G₁ f)
  mod→natTransPath _ _ cmp = 
    flipSquare (compPath→Square cmp)
    where open import Cubical.Foundations.Path

