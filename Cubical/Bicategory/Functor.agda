open import Prelude

-- Pseudofunctor?

module Cubical.Bicategory.Functor where

open import Cubical.Bicategory.Base
open import Cubical.WildCat.Base
open import Cubical.WildCat.Functor

private
  variable
    ℓC ℓC' ℓD ℓD' : Level

module 2FunctNotation {C : WildCat ℓC ℓC'}
  {D : WildCat ℓD ℓD'} (F : WildFunctor C D) where

  open import Cubical.Foundations.GroupoidLaws

  open WildCat C using () 
    renaming (Hom[_,_] to C[_,_]; id to idᶜ)
  open WildCat D using () 
    renaming (⋆IdL to D-⋆IdL)

  open Whiskering C using ()
    renaming (_⋆₂_ to _⋆₂ᶜ_)
  open Whiskering D using (_◃_; _▹_)
    renaming (_⋆₂_ to _⋆₂ᵈ_)

  open WildFunctor F using (
      F-id;
      F-seq
    ) renaming (
      F-ob to F₀; F-hom to F₁
    ) public

  F₂ : ∀ {X} {Y} {f g : C[ X , Y ]}
    (f≡g : f ≡ g)
    → F₁ f ≡ F₁ g
  F₂ = cong F₁

  F₂-funct : ∀ {x y} 
    {f g h : C[ x , y ]}
    (α : f ≡ g)
    (β : g ≡ h)
    → F₂ (α ∙ β) ≡ F₂ α ∙ F₂ β
  F₂-funct = congFunct F₁

  F-seq-nat : ∀ {x y z} 
      {f f′ : C[ x , y ]}
      {g g′ : C[ y , z ]}
      (p : f ≡ f′)
      (q : g ≡ g′)
    → F-seq f g 
      ∙ F₂ p ⋆₂ᵈ F₂ q
      ≡ F₂ (p ⋆₂ᶜ q) 
      ∙ F-seq f′ g′
  F-seq-nat {x} {y} {z} {f} {g} p q = J2 Q r p q
    where
    Q : 
      (f' : C[ x , y ]) 
      (p' : f ≡ f') 
      (g' : C[ y , z ]) 
      (q' : g ≡ g') 
      → Type ℓD'
    Q f' p' g' q' = 
      F-seq f g 
      ∙ F₂ p' ⋆₂ᵈ F₂ q'
      ≡ F₂ (p' ⋆₂ᶜ q') 
      ∙ F-seq f' g'
    r = sym (rUnit _) ∙ lUnit _

module _ (C : Bicategory ℓC ℓC') 
  (D : Bicategory ℓD ℓD') where

  open Bicategory C using () 
    renaming (
      str to ⟨C⟩;
      Hom[_,_] to C[_,_]; 
      id to idᶜ; 
      _⋆_ to _⋆ᶜ_;
      ⋆IdL to C-⋆IdL;
      ⋆IdR to C-⋆IdR;
      ⋆Assoc to C-⋆Assoc
    )
  open Bicategory D using (_◃_; _▹_) 
    renaming (
      str to ⟨D⟩;
      _⋆_ to _⋆ᵈ_; 
      id to idᵈ; 
      ⋆IdL to D-⋆IdL;
      ⋆IdR to D-⋆IdR;
      ⋆Assoc to D-⋆Assoc;
      isGpdHom to isGpdHomD
    )

  record Is2Functor 
    (F : WildFunctor ⟨C⟩ ⟨D⟩)
    : Type (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓD ℓD')) where
    open 2FunctNotation F
    field
      F-IdL : ∀ {x y} {f : C[ x , y ]} 
        → F-seq idᶜ f
          ∙ F-id ▹ F₁ f
          ∙ D-⋆IdL (F₁ f) 
          ≡ F₂ (C-⋆IdL f)
      F-IdR : ∀ {x y} {f : C[ x , y ]} 
        → F-seq f idᶜ 
          ∙ F₁ f ◃ F-id
          ∙ D-⋆IdR (F₁ f)
          ≡ F₂ (C-⋆IdR f)
      F-Assoc : ∀ {x y z w} 
        {f : C[ x , y ]} 
        {g : C[ y , z ]} 
        {h : C[ z , w ]} 
        → F-seq (f ⋆ᶜ g) h
          ∙ F-seq f g ▹ F₁ h
          ∙ D-⋆Assoc (F₁ f) (F₁ g) (F₁ h)
          ≡ F₂ (C-⋆Assoc f g h)
          ∙ F-seq f (g ⋆ᶜ h)
          ∙ F₁ f ◃ F-seq g h

  record Functor 
    : Type (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓD ℓD')) where
    field
      str : WildFunctor ⟨C⟩ ⟨D⟩
      is2Functor : Is2Functor str
    open 2FunctNotation str public
    open Is2Functor is2Functor public

module _ {C : Bicategory ℓC ℓC'} {D : Bicategory ℓD ℓD'}
  where

  open Bicategory C using () 
    renaming (Hom[_,_] to C[_,_]; id to idᶜ; _⋆_ to _⋆ᶜ_)
  open Bicategory D using (_◃_; _▹_) 
    renaming (
      str to ⟨D⟩;
      _⋆_ to _⋆ᵈ_; 
      id to idᵈ; 
      ⋆IdL to D-⋆IdL;
      ⋆IdR to D-⋆IdR;
      ⋆Assoc to D-⋆Assoc;
      isGpdHom to isGpdHomD
    )

  open Functor using () renaming (str to ⟨_⟩)

  module _ {F G : Functor C D}
    (α : WildNatTrans _ _ ⟨ F ⟩ ⟨ G ⟩) where

    open import Cubical.Foundations.GroupoidLaws

    open WildNatTrans α using ()
      renaming (N-ob to α₀; N-hom to α□)
    open Functor F using (F-id; F-seq; F₁; F₂)
    open Functor G using ()
      renaming (
        F₁ to G₁;
        F-id to G-id;
        F-seq to G-seq;
        F₂ to G₂
      )

    N-hom-nat : 
      ∀ {X} {Y} 
        (f g : C[ X , Y ])
        (f≡g : f ≡ g)
      →   α□ f ∙ α₀ X ◃ G₂ f≡g
        ≡ F₂ f≡g ▹ α₀ Y ∙ α□ g
    N-hom-nat {X} {Y} f _ = J Q d
      where
      Q = λ f' f≡f' → 
        α□ f ∙ α₀ X ◃ G₂ f≡f'
        ≡ F₂ f≡f' ▹ α₀ Y ∙ α□ f'
      d = sym (rUnit _) ∙ lUnit _

    record Is2NatTrans : Type (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓD ℓD')) where
      field
        N-hom-id :
          ∀ {X} 
          →   α□ (idᶜ {X})
              ∙ α₀ X ◃ G-id
              ∙ D-⋆IdR (α₀ X)
            ≡ F-id ▹ α₀ X 
              ∙ D-⋆IdL (α₀ X)
        N-hom-seq : 
          ∀ {X} {Y} {Z} (f : C[ X , Y ]) (g : C[ Y , Z ])
          →   α□ (f ⋆ᶜ g) 
              ∙ α₀ X ◃ G-seq f g 
            ≡ F-seq f g ▹ α₀ Z
              ∙ D-⋆Assoc (F₁ f) (F₁ g) (α₀ Z)
              ∙ F₁ f ◃ α□ g
              ∙ sym (D-⋆Assoc (F₁ f) (α₀ Y) (G₁ g))
              ∙ α□ f ▹ G₁ g
              ∙ D-⋆Assoc (α₀ X) (G₁ f) (G₁ g)

    open import Cubical.Foundations.HLevels
    open Is2NatTrans
    isPropIs2NatTrans : isProp Is2NatTrans
    isPropIs2NatTrans αis βis i .N-hom-id {X} = aux i
      where
      aux : αis .N-hom-id {X} ≡ βis .N-hom-id 
      aux = isGpdHomD _ _ _ _ (αis .N-hom-id) (βis .N-hom-id)
    isPropIs2NatTrans αis βis i .N-hom-seq f g = aux i
      where
      aux : αis .N-hom-seq f g ≡ βis .N-hom-seq f g
      aux = isGpdHomD _ _ _ _ (αis .N-hom-seq f g) (βis .N-hom-seq f g)

  module _ (F G : Functor C D) where
    2NatTrans = Σ (WildNatTrans _ _ ⟨ F ⟩ ⟨ G ⟩) (Is2NatTrans {F} {G}) 
