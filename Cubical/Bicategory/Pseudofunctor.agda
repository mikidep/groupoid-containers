open import Prelude

module Cubical.Bicategory.Pseudofunctor where

open import Cubical.Bicategory.Base hiding (_[_,_])
open import Cubical.WildCat.Base hiding (_[_,_])
open import Cubical.WildCat.Functor

private
  variable
    ℓC ℓC' ℓD ℓD' : Level

open BicatSyntax {{...}}

module 2FunctNotation {C : WildCat ℓC ℓC'}
  {D : WildCat ℓD ℓD'} (F : WildFunctor C D) where

  open import Cubical.WildCat.Base using (_[_,_])
  open import Cubical.Foundations.GroupoidLaws
  open import Prelude.ExtraGpdLaws
  
  open BicatSynInstWC C
  open BicatSynInstWC D

  -- private instance
  --   _ : BicatSyntax C
  --   _ = record { }
  --   _ : BicatSyntax D
  --   _ = record { }

  open WildFunctor F using (
      F-id;
      F-seq
    ) renaming (
      F-ob to F₀; F-hom to F₁
    ) public

  F₂ : ∀ {X} {Y} {f g : C [ X , Y ]}
    (f≡g : f ≡ g)
    → F₁ f ≡ F₁ g
  F₂ = cong F₁

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

  -- reassoc helper
  open import Prelude.Reassoc
  F₂′ : ∀ {X} {Y} {f g : C [ X , Y ]}
    (f≡g : Term f g)
    → Term (F₁ f) (F₁ g)
  F₂′ = cong′ F₁ 


module _ {C : WildCat ℓC ℓC'}
  {D : WildCat ℓD ℓD'} {F G : WildFunctor C D}
  (α : WildNatTrans _ _ F G) where

  open import Cubical.WildCat.Base using (_[_,_])

  open BicatSynInstWC C
  open BicatSynInstWC D

  open import Cubical.Foundations.GroupoidLaws

  open WildNatTrans α using ()
    renaming (N-ob to α₀; N-hom to α□)
  open 2FunctNotation F using (F₁; F₂)
  open 2FunctNotation G using ()
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

  open BicatSynInstWC C
  open BicatSynInstWC D

  open WildNatTrans α using ()
    renaming (N-ob to α₀; N-hom to α□)
  open WildNatTrans β using ()
    renaming (N-ob to β₀; N-hom to β□)
  open 2FunctNotation F using (F₁; F₂)
  open 2FunctNotation G using ()
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

module _ (C : Bicategory ℓC ℓC')
  (D : Bicategory ℓD ℓD') where

  open import Cubical.Bicategory.Base using (_[_,_])

  private
    module C = Bicategory C
    module D = Bicategory D

  record IsPseudofunctor
    (F : WildFunctor C.str D.str)
    : Type (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓD ℓD')) where

    open BicatSynInstBC C
    open BicatSynInstBC D
    open 2FunctNotation F

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
    open 2FunctNotation str public
    open IsPseudofunctor isPseudofunctor public

module _ {C : Bicategory ℓC ℓC'} {D : Bicategory ℓD ℓD'}
  where

  open import Cubical.Bicategory.Base using (_[_,_])

  private
    module C = Bicategory C
    module D = Bicategory D

  open BicatSynInstBC C
  open BicatSynInstBC D

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
