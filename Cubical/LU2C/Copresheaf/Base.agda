open import Cubical.Foundations.Prelude

module Cubical.LU2C.Copresheaf.Base (ℓ : Level) where

open import Cubical.LU2C.Base
open import Cubical.LU2C.Instances.Groupoids ℓ
import Cubical.LU2C.Pseudofunctor

module 2FunctNotation = Cubical.LU2C.Pseudofunctor.2FunctNotation

open import Cubical.WildCat.Base hiding (_[_,_])
open import Cubical.WildCat.Functor

private
  variable
    ℓC ℓC' : Level

-- In HGpd, whiskering
-- commutes with composition
-- definitionally, i.e.
-- f ⋆ g ◃ p ≡def f ◃ g ◃ p
-- and viceversa

open LU2CSyntax {{...}}

private module HGpd = LU2C HGpd

open LU2C HGpd using ()
  renaming (str to ⟨HGpd⟩)

open LU2CSyn2C HGpd

module _ (C : LU2C ℓC ℓC') where
  private module C = LU2C C

  open C using ()
    renaming (str to ⟨C⟩)

  open LU2CSyn2C C

  record Is2Copresheaf
    (F : WildFunctor ⟨C⟩ ⟨HGpd⟩)
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

  module _ {F : WildFunctor ⟨C⟩ ⟨HGpd⟩} where
    open import Cubical.Foundations.HLevels
    open Is2Copresheaf
    isPropIs2Copresheaf : isProp (Is2Copresheaf F)
    isPropIs2Copresheaf is₁ is₂ i = record where
      F-IdL f = HGpd.isGpdHom _ _ _ _ (is₁ .F-IdL f) (is₂ .F-IdL f) i
      F-IdR f = HGpd.isGpdHom _ _ _ _ (is₁ .F-IdR f) (is₂ .F-IdR f) i
      F-Assoc f g h = HGpd.isGpdHom _ _ _ _ 
        (is₁ .F-Assoc f g h) (is₂ .F-Assoc f g h) i

  record Copresheaf
    : Type (ℓ-max (ℓ-max ℓC ℓC') (ℓ-suc ℓ)) where
    field
      str : WildFunctor ⟨C⟩ ⟨HGpd⟩
      is2Copresheaf : Is2Copresheaf str
    open 2FunctNotation str public
    open Is2Copresheaf is2Copresheaf public

  -- module _ {F G : Copresheaf} where
  --   open Copresheaf
  --
  --   Copresheaf≡ : F .str ≡ G .str → F ≡ G 
  --   Copresheaf≡ str≡ i .str = str≡ i
  --   Copresheaf≡ str≡ i .is2Copresheaf = isPropIs2Copresheaf
  --     {! !}
  --     {! !}
  --     i
