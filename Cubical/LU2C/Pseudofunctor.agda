open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws

module Cubical.LU2C.Pseudofunctor where

open import Cubical.LU2C.Base hiding (_[_,_])
open import Cubical.WildCat.Base hiding (_[_,_])
open import Cubical.WildCat.Functor

open import Cubical.WildCat.AsLU2C.Instances
import Cubical.WildCat.AsLU2C.Functor.Notation as NotF

private
  variable
    ℓC ℓC' ℓD ℓD' : Level

module _ {C : WildCat ℓC ℓC'}
  {D : WildCat ℓD ℓD'} {F G : WildFunctor C D}
  (α : WildNatTrans _ _ F G) where

  open import Cubical.WildCat.Base using (_[_,_])

  open NotWC C
  open NotWC D

  open WildNatTrans α using ()
    renaming (N-ob to α₀; N-hom to α□)
  open NotF F using (F₁; F₂)
  open NotF G using ()
    renaming (
      F₁ to G₁;
      F₂ to G₂
    )

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


module _ {C : WildCat ℓC ℓC'}
  {D : WildCat ℓD ℓD'} {F G : WildFunctor C D}
  {α β : WildNatTrans _ _ F G} where

  open import Cubical.WildCat.Base using (_[_,_])

  open NotWC C
  open NotWC D

  open WildNatTrans α using ()
    renaming (N-ob to α₀; N-hom to α□)
  open WildNatTrans β using ()
    renaming (N-ob to β₀; N-hom to β□)
  open NotF F using (F₁; F₂)
  open NotF G using ()
    renaming (
      F₁ to G₁;
      F₂ to G₂
    )

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

module _ (C : LU2C ℓC ℓC')
  (D : LU2C ℓD ℓD') where

  open import Cubical.LU2C.Base using (_[_,_])

  private
    module C = LU2C C
    module D = LU2C D

  record IsPseudofunctor
    (F : WildFunctor C.str D.str)
    : Type (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓD ℓD')) where

    open NotWC C.str
    open NotWC D.str
    open NotF F

    field
      F-IdL : ∀ {x y} {f : C [ x , y ]}
        → F-seq id f
          ∙ F-id ▹ F₁ f
          ∙ ⋆IdL (F₁ f)
          ≡ F₂ (⋆IdL f)
      F-IdR : ∀ {x y} {f : C [ x , y ]}
        → F-seq f id
          ∙ F₁ f ◃ F-id
          ∙ ⋆IdR (F₁ f)
          ≡ F₂ (⋆IdR f)
      F-Assoc : ∀ {x y z w}
        {f : C [ x , y ]}
        {g : C [ y , z ]}
        {h : C [ z , w ]}
        → F-seq (f ⋆ g) h
          ∙ F-seq f g ▹ F₁ h
          ∙ ⋆Assoc (F₁ f) (F₁ g) (F₁ h)
          ≡ F₂ (⋆Assoc f g h)
          ∙ F-seq f (g ⋆ h)
          ∙ F₁ f ◃ F-seq g h

  record Pseudofunctor
    : Type (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓD ℓD')) where
    field
      str : WildFunctor C.str D.str
      isPseudofunctor : IsPseudofunctor str
    open NotF str public
    open IsPseudofunctor isPseudofunctor public

module _ {C : LU2C ℓC ℓC'} {D : LU2C ℓD ℓD'}
  where

  open import Cubical.LU2C.Base using (_[_,_])

  private
    module C = LU2C C
    module D = LU2C D

  open Not2C C
  open Not2C D

  open Pseudofunctor using () renaming (str to ⟨_⟩)

  module _ {F G : Pseudofunctor C D}
    (α : WildNatTrans _ _ ⟨ F ⟩ ⟨ G ⟩) where

    open import Cubical.Foundations.GroupoidLaws

    open WildNatTrans α using ()
      renaming (N-ob to α₀; N-hom to α□)
    open Pseudofunctor F using (F-id; F-seq; F₁; F₂)
    open Pseudofunctor G using ()
      renaming (
        F₁ to G₁;
        F-id to G-id;
        F-seq to G-seq;
        F₂ to G₂
      )

    record IsPseudonat : Type (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓD ℓD')) where
      field
        N-hom-id :
          ∀ {X : C.ob}
          →   α□ (id {x = X})
              ∙ α₀ X ◃ G-id
              ∙ ⋆IdR (α₀ X)
            ≡ F-id ▹ α₀ X
              ∙ ⋆IdL (α₀ X)
        N-hom-seq :
          ∀ {X} {Y} {Z} (f : C [ X , Y ]) (g : C [ Y , Z ])
          →   α□ (f ⋆ g)
              ∙ α₀ X ◃ G-seq f g
            ≡ F-seq f g ▹ α₀ Z
              ∙ ⋆Assoc (F₁ f) (F₁ g) (α₀ Z)
              ∙ F₁ f ◃ α□ g
              ∙ sym (⋆Assoc (F₁ f) (α₀ Y) (G₁ g))
              ∙ α□ f ▹ G₁ g
              ∙ ⋆Assoc (α₀ X) (G₁ f) (G₁ g)

    open import Cubical.Foundations.HLevels
    open IsPseudonat
    isPropIsPseudonat : isProp IsPseudonat
    isPropIsPseudonat αis βis i .N-hom-id {X} = aux i
      where
      aux : αis .N-hom-id {X} ≡ βis .N-hom-id
      aux = D.isGpdHom _ _ _ _ (αis .N-hom-id) (βis .N-hom-id)
    isPropIsPseudonat αis βis i .N-hom-seq f g = aux i
      where
      aux : αis .N-hom-seq f g ≡ βis .N-hom-seq f g
      aux = D.isGpdHom _ _ _ _ (αis .N-hom-seq f g) (βis .N-hom-seq f g)

  module _ (F G : Pseudofunctor C D) where
    PseudonatTrans = Σ (WildNatTrans _ _ ⟨ F ⟩ ⟨ G ⟩) (IsPseudonat {F} {G})
