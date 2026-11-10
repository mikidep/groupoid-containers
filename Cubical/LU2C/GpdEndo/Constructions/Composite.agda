open import Cubical.Foundations.Prelude

open import Cubical.Foundations.Function
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Path
open import Prelude.ExtraGpdLaws

open import Cubical.WildCat.Functor hiding (_$_)
open import Cubical.WildCat.Product renaming (_×_ to ProdCat)

open import Cubical.LU2C.Base
open import Cubical.LU2C.Pseudofunctor
open import Cubical.LU2C.GpdEndo.Base


module Cubical.LU2C.GpdEndo.Constructions.Composite
  {ℓ : Level} {F G : GpdEndo ℓ} where

open import Cubical.LU2C.Instances.Groupoids ℓ
open import Cubical.WildCat.AsLU2C.Instances
open import Cubical.WildCat.AsLU2C.Functor.Properties

private module W = WildFunctor

open LU2C HGpd using () renaming (str to ⟨HGpd⟩)
open NotHGpd

-- open import Prelude.Utils

open Pseudofunctor using (isPseudofunctor)
  renaming (str to ⟨_⟩)

private module F = NotHGpdFunct ⟨ F ⟩
open F using (F₀; F₁; F₂)
private module G = NotHGpdFunct ⟨ G ⟩
open G using () renaming 
  ( F₀ to G₀
  ; F₁ to G₁
  ; F₂ to G₂
  )

module Goal where
  module iF = IsPseudoGpdEndo (mkPseudoGpdEndo⁻ ℓ (F .isPseudofunctor))
  module iG = IsPseudoGpdEndo (mkPseudoGpdEndo⁻ ℓ (G .isPseudofunctor))

  str : WildFunctor ⟨HGpd⟩ ⟨HGpd⟩
  str = record where
    F-ob x = G₀ (F₀ x)
    F-hom f = G₁ (F₁ f)
    F-id = G₂ F.F-id ∙ G.F-id
    F-seq f g = G₂ (F.F-seq f g) ∙ G.F-seq (F₁ f) (F₁ g)

  -- F-id' : ∀ {X} → G₁ (F₁ (id )) ≡ id 
  -- F-id' {X} = J (λ f _ → G₁ {x = F₀ X} f ≡ id) 
  --   G.F-id 
  --   (sym (F.F-id {x = X}))

  -- F-id' {X} = J (λ f _ → G₁ {x = F₀ X} f ≡ id) 
  --   G.F-id 
  --   (sym (F.F-id {x = X}))
  --
  -- _ = {! F-id' !}

  open IsPseudoGpdEndo

  isPseudoGpdEndo : IsPseudoGpdEndo ℓ str

  isPseudoGpdEndo .F-IdL {x} f = 
    (G₂ F.F-id ∙ G.F-id) ▹ G₁ (F₁ f)
        ≡⟨ ▹-∙ (G₂ F.F-id) G.F-id ⟩
    G₂ F.F-id ▹ G₁ (F₁ f) 
    ∙ G.F-id ▹ G₁ (F₁ f)
        ≡⟨ ∙l iG.F-IdL (F₁ f) ⟩
    G₂ F.F-id ▹ G₁ (F₁ f) 
    ∙ sym (G.F-seq id (F₁ f))
        ≡⟨ F-seq-nat-sym {F = ⟨ G ⟩} F.F-id refl ⟩
    sym (G.F-seq (F₁ id) (F₁ f)) 
    ∙ G₂ (F.F-id ▹ F₁ f) 
        ≡⟨ ∙l cong G₂ (iF.F-IdL f) ⟩ 
    sym (G.F-seq (F₁ id) (F₁ f)) 
    ∙ G₂ (sym (F.F-seq id f)) 
        ≡⟨ sym (symDistr _ _) ⟩ 
    sym (G₂ (F.F-seq id f) 
      ∙ G.F-seq (F₁ id) (F₁ f)) 
        ∎

  isPseudoGpdEndo .F-IdR = {! !}

  isPseudoGpdEndo .F-Assoc {x} {y} {z} {w} f g h = goal
    where
    goal' : Square
      (G₂ (F.F-seq f (g ⋆ h)) ∙ G.F-seq (F₁ f) (F₁ (g ⋆ h)))
      (G₂ (F.F-seq f g) ▹ G₁ (F₁ h) ∙ G.F-seq (F₁ f) (F₁ g) ▹ G₁ (F₁ h))
      (G₂ (F.F-seq (f ⋆ g) h) ∙ G.F-seq (F₁ (f ⋆ g)) (F₁ h))
      (G₁ (F₁ f) ◃ G₂ (F.F-seq g h) ∙ G₁ (F₁ f) ◃ G.F-seq (F₁ g) (F₁ h))
    goal' = sq
      where
      open import Cubical.Foundations.Path
      sqtl : Square 
        (G₂ (F.F-seq f (g ⋆ h))) 
        (G₂ (F.F-seq f g ▹ F₁ h)) 
        (G₂ (F.F-seq (f ⋆ g) h)) 
        (G₂ (F₁ f ◃ F.F-seq g h)) 
      sqtl = congP (λ i → G₂) (iF.F-Assoc f g h)
      sqtr : Square 
        (G.F-seq (F₁ f) (F₁ (g ⋆ h))) 
        (G.F-seq (F₁ f) (F₁ g ⋆ F₁ h)) 
        (G₂ (F₁ f ◃ F.F-seq g h)) 
        (G₁ (F₁ f) ◃ G₂ (F.F-seq g h))
      sqtr = F-seq-nat-Square {F = ⟨ G ⟩ } refl (F.F-seq g h)
      sqbl : Square 
        (G₂ (F.F-seq f g ▹ F₁ h)) 
        (G₂ (F.F-seq f g) ▹ G₁ (F₁ h)) 
        (G.F-seq (F₁ (f ⋆ g)) (F₁ h)) 
        (G.F-seq (F₁ f ⋆ F₁ g) (F₁ h)) 
      sqbl = flipSquare (F-seq-nat-Square {F = ⟨ G ⟩ } (F.F-seq f g) refl)
      sqbr : Square 
        (G.F-seq (F₁ f) (F₁ g ⋆ F₁ h)) 
        (G.F-seq (F₁ f) (F₁ g) ▹ G₁ (F₁ h)) 
        (G.F-seq (F₁ f ⋆ F₁ g) (F₁ h)) 
        (G₁ (F₁ f) ◃ G.F-seq (F₁ g) (F₁ h))
      sqbr = iG.F-Assoc (F₁ f) (F₁ g) (F₁ h)
      sql = sqtl ∙v sqbl
      sqr = sqtr ∙v sqbr
      sq = sql ∙₂ sqr

    goal : Square
      (G₂ (F.F-seq f (g ⋆ h)) ∙ G.F-seq (F₁ f) (F₁ (g ⋆ h)))
      ((G₂ (F.F-seq f g) ∙ G.F-seq (F₁ f) (F₁ g)) ▹ G₁ (F₁ h))
      (G₂ (F.F-seq (f ⋆ g) h) ∙ G.F-seq (F₁ (f ⋆ g)) (F₁ h))
      (G₁ (F₁ f) ◃ (G₂ (F.F-seq g h) ∙ G.F-seq (F₁ g) (F₁ h)))
    goal = transport (λ i →
        Square
          (G₂ {isx = F₀ x .snd} {isy = F₀ w .snd} (F.F-seq f (g ⋆ h)) 
            ∙ G.F-seq {isy = F₀ y .snd} (F₁ f) (F₁ (g ⋆ h)))
          (▹-∙ {g = G₁ {isx = F₀ z .snd} (F₁ h)} 
            (G₂ (F.F-seq f g)) (G.F-seq (F₁ f) (F₁ g)) (~ i))
          (G₂ (F.F-seq (f ⋆ g) h) 
            ∙ G.F-seq (F₁ (f ⋆ g)) (F₁ h))
          (◃-∙ {f = G₁ (F₁ f)} 
            (G₂ (F.F-seq g h)) (G.F-seq (F₁ g) (F₁ h)) (~ i))
      ) goal'

--   isPseudofunctor : IsPseudofunctor HGpd HGpd str
--   isPseudofunctor = {! !}
--
-- compEndo₀ : GpdEndo ℓ
-- compEndo₀ = {! !}
--
