open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Path

open import Cubical.WildCat.Functor

module Cubical.LU2C.GpdEndo.Base (ℓ : Level) where

open import Cubical.LU2C.Base
open import Cubical.LU2C.Pseudofunctor
open import Cubical.LU2C.Instances.Groupoids ℓ
open import Cubical.WildCat.AsLU2C.Instances
import Cubical.WildCat.AsLU2C.Functor.Notation as NotF

open import Prelude.ExtraGpdLaws

private module HGpd = LU2C HGpd
open HGpd using () renaming (str to ⟨HGpd⟩)
open NotHGpd

GpdEndo = Pseudofunctor HGpd HGpd

module _ (F : WildFunctor ⟨HGpd⟩ ⟨HGpd⟩) where
  record IsPseudoGpdEndo : Type (ℓ-suc ℓ) where
    open NotF F
    field
      F-IdL : ∀ {x y} (f : HGpd [ x , y ])
        → F-id ▹ F₁ f
          ≡ sym (F-seq {x} {x} {y} id f) 
      F-IdR : ∀ {x y} (f : HGpd [ x , y ])
        → F₁ f ◃ F-id
          ≡ sym (F-seq {x} {y} {y} f id) 
      F-Assoc : ∀ {x y z w}
        (f : HGpd [ x , y ])
        (g : HGpd [ y , z ])
        (h : HGpd [ z , w ])
        → Square
          (F-seq f (g ⋆ h))
          (F-seq f g ▹ F₁ h)
          (F-seq {x} {z} {w} (f ⋆ g) h)
          (F₁ {x} {y} f ◃ F-seq g h)
    F-Assoc-comp : ∀ {x y z w}
      (f : HGpd [ x , y ])
      (g : HGpd [ y , z ])
      (h : HGpd [ z , w ])
      → F-seq {x} {z} {w} (f ⋆ g) h
        ∙ F-seq f g ▹ F₁ h
        ≡ F-seq f (g ⋆ h)
        ∙ F₁ {x} {y} f ◃ F-seq g h
    F-Assoc-comp {x} {y} {z} {w} f g h = 
      Square→compPath (F-Assoc {x} {y} {z} {w} f g h)

module _ {F : WildFunctor ⟨HGpd⟩ ⟨HGpd⟩} where
  mkPseudoGpdEndo : IsPseudoGpdEndo F → IsPseudofunctor HGpd HGpd F
  mkPseudoGpdEndo iE = goal
    where
    module iE = IsPseudoGpdEndo iE
    open IsPseudofunctor
    goal : _
    goal .F-IdL {x} {y} f = shuffleSymLU 
      ( sym (rUnit _) 
      ∙ iE.F-IdL f
      ∙ rUnit _
      )
    goal .F-IdR {x} {y} f = shuffleSymLU 
      ( sym (rUnit _) 
      ∙ iE.F-IdR f
      ∙ rUnit _
      )
    goal .F-Assoc {x} {y} {z} {w} f g h = 
      ∙l sym (rUnit _) 
      ∙ Square→compPath (iE.F-Assoc f g h) 
      ∙ lUnit _

  mkPseudoGpdEndo⁻ : IsPseudofunctor HGpd HGpd F → IsPseudoGpdEndo F
  mkPseudoGpdEndo⁻ iP = goal
    where
    module iP = IsPseudofunctor iP
    open IsPseudoGpdEndo
    goal : _
    goal .F-IdL {x} {y} f = sym (invUniq (∙l rUnit _ ∙ iP.F-IdL f))
    goal .F-IdR {x} {y} f = sym (invUniq (∙l rUnit _ ∙ iP.F-IdR f))
    goal .F-Assoc {x} {y} {z} {w} f g h = compPath→Square 
      ( ∙l rUnit _ 
      ∙ iP.F-Assoc f g h 
      ∙ sym (lUnit _)
      )
