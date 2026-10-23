open import Cubical.Foundations.Prelude

module Cubical.LU2C.Copresheaf.Base (ℓ : Level) where

open import Cubical.LU2C.Base
open import Cubical.LU2C.Instances.Groupoids ℓ
import Cubical.LU2C.Pseudofunctor

open import Cubical.WildCat.Base hiding (_[_,_])
open import Cubical.WildCat.FullSub.Notation
import Cubical.WildCat.AsLU2C.Functor.Notation as NotF
open import Cubical.WildCat.Functor

private
  variable
    ℓC ℓC' : Level

-- In HGpd, whiskering
-- commutes with composition
-- definitionally, i.e.
-- f ⋆ g ◃ p ≡def f ◃ g ◃ p
-- and viceversa

private module HGpd = LU2C HGpd

open LU2C using ()
  renaming (str to ⟨_⟩)

open Not2C HGpd

module _ (C : LU2C ℓC ℓC') where
  private module C = LU2C C

  open Not2C C

  record Is2Copresheaf
    (F : WildFunctor ⟨ C ⟩ ⟨ HGpd ⟩)
    : Type (ℓ-max (ℓ-max ℓC ℓC') (ℓ-suc ℓ)) where
    open NotF F
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

  module _ {F : WildFunctor ⟨ C ⟩ ⟨ HGpd ⟩} where
    open NotF F
    open import Cubical.Foundations.HLevels
    open Is2Copresheaf
    isPropIs2Copresheaf : isProp (Is2Copresheaf F)
    isPropIs2Copresheaf is₁ is₂ i = record where
      F-IdL f = HGpdIsGpdHom _ _ _ _ (is₁ .F-IdL f) (is₂ .F-IdL f) i
      F-IdR f = HGpdIsGpdHom _ _ _ _ (is₁ .F-IdR f) (is₂ .F-IdR f) i
      F-Assoc f g h = HGpdIsGpdHom _ _ _ _ 
        (is₁ .F-Assoc f g h) (is₂ .F-Assoc f g h) i

  -- record Copresheaf
  --   : Type (ℓ-max (ℓ-max ℓC ℓC') (ℓ-suc ℓ)) where
  --   field
  --     str : WildFunctor ⟨ C ⟩ ⟨ HGpd ⟩
  --     is2Copresheaf : Is2Copresheaf str
  --   open NotF str public
  --   open Is2Copresheaf is2Copresheaf public

  Copresheaf : Type (ℓ-max (ℓ-max ℓC ℓC') (ℓ-suc ℓ)) 
  Copresheaf = Σ _ Is2Copresheaf

  -- module _ {F G : Copresheaf} where
  --   open Copresheaf
  --
  --   Copresheaf≡ : F .str ≡ G .str → F ≡ G 
  --   Copresheaf≡ str≡ i .str = str≡ i
  --   Copresheaf≡ str≡ i .is2Copresheaf = isPropIs2Copresheaf
  --     {! !}
  --     {! !}
  --     i

module Not2P {C : LU2C ℓC ℓC'} (F : Copresheaf C) where
  open NotF (F .fst) public
