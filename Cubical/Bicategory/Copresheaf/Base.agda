open import Cubical.Foundations.Prelude

module Cubical.Bicategory.Copresheaf.Base (ℓ : Level) where

open import Cubical.Bicategory.Base
open import Cubical.Bicategory.Instances.Groupoids
import Cubical.Bicategory.Pseudofunctor

module 2FunctNotation = Cubical.Bicategory.Pseudofunctor.2FunctNotation

open import Cubical.WildCat.Base hiding (_[_,_])
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

open BicatSyntax {{...}}

open Bicategory GPD using ()
  renaming (str to ⟨GPD⟩)

open BicatSynInstBC GPD

module _ (C : Bicategory ℓC ℓC') where
  private module C = Bicategory C

  open C using ()
    renaming (str to ⟨C⟩)

  open BicatSynInstBC C

  record Is2Copresheaf
    (F : WildFunctor ⟨C⟩ ⟨GPD⟩)
    : Type (ℓ-max (ℓ-max ℓC ℓC') (ℓ-suc ℓ)) where
    open 2FunctNotation F
    field
      F-IdL : ∀ {x y} (f : C [ x , y ])
        → F-seq id f
          ∙ F-id ▹ F₁ f
          ≡ F₂ (⋆IdL f)
      F-IdR : ∀ {x y} (f : C [ x , y ])
        → F-seq f id
          ∙ F₁ f ◃ F-id
          ≡ F₂ (⋆IdR f)
      F-Assoc : ∀ {x y z w}
        (f : C [ x , y ])
        (g : C [ y , z ])
        (h : C [ z , w ])
        → F-seq (f ⋆ g) h
          ∙ F-seq f g ▹ F₁ h
          ≡ F₂ (⋆Assoc f g h)
          ∙ F-seq f (g ⋆ h)
          ∙ F₁ f ◃ F-seq g h

  record Copresheaf
    : Type (ℓ-max (ℓ-max ℓC ℓC') (ℓ-suc ℓ)) where
    field
      str : WildFunctor ⟨C⟩ ⟨GPD⟩
      is2Copresheaf : Is2Copresheaf str
    open 2FunctNotation str public
    open Is2Copresheaf is2Copresheaf public

