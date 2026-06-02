open import Cubical.Foundations.Prelude

module Cubical.Bicategory.Copresheaf.Base (ℓ : Level) where

open import Cubical.Bicategory.Base
open import Cubical.Bicategory.Instances.Groupoids
import Cubical.Bicategory.Functor

module 2FunctNotation = Cubical.Bicategory.Functor.2FunctNotation

open import Cubical.WildCat.Base
open import Cubical.WildCat.Functor

private
  variable
    ℓC ℓC' : Level

GPD = GpdBicat ℓ
-- In GPD, whiskering
-- commutes with composition
-- definitionally, i.e.
-- f ⋆ g ◃ p ≡def f ◃ g ◃ p
-- and viceversa

open Bicategory GPD using ()
  renaming (
    str to ⟨GPD⟩;
    Hom[_,_] to D[_,_];
    _⋆_ to _⋆ᵈ_;
    _⋆₂_ to _⋆₂ᵈ_;
    id to idᵈ
  )
open Whiskering ⟨GPD⟩
open 2CellLaws ⟨GPD⟩

module _ (C : Bicategory ℓC ℓC') where
  private module C = Bicategory C
  open C using ()
    renaming (
      str to ⟨C⟩;
      Hom[_,_] to C[_,_];
      id to idᶜ;
      _⋆_ to _⋆ᶜ_;
      _⋆₂_ to _⋆₂ᶜ_
    )

  record Is2Copresheaf
    (F : WildFunctor ⟨C⟩ ⟨GPD⟩)
    : Type (ℓ-max (ℓ-max ℓC ℓC') (ℓ-suc ℓ)) where
    open 2FunctNotation F
    field
      F-IdL : ∀ {x y} (f : C[ x , y ])
        → F-seq idᶜ f
          ∙ F-id ▹ F₁ f
          ≡ F₂ (C.⋆IdL f)
      F-IdR : ∀ {x y} (f : C[ x , y ])
        → F-seq f idᶜ
          ∙ F₁ f ◃ F-id
          ≡ F₂ (C.⋆IdR f)
      F-Assoc : ∀ {x y z w}
        (f : C[ x , y ])
        (g : C[ y , z ])
        (h : C[ z , w ])
        → F-seq (f ⋆ᶜ g) h
          ∙ F-seq f g ▹ F₁ h
          ≡ F₂ (C.⋆Assoc f g h)
          ∙ F-seq f (g ⋆ᶜ h)
          ∙ F₁ f ◃ F-seq g h

  record Copresheaf
    : Type (ℓ-max (ℓ-max ℓC ℓC') (ℓ-suc ℓ)) where
    field
      str : WildFunctor ⟨C⟩ ⟨GPD⟩
      is2Copresheaf : Is2Copresheaf str
    open 2FunctNotation str public
    open Is2Copresheaf is2Copresheaf public

