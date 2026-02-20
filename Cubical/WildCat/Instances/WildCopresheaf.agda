{-# OPTIONS --allow-unsolved-metas #-}

module Cubical.WildCat.Instances.WildCopresheaf where

open import Cubical.Foundations.Prelude

open import Cubical.WildCat.Base
open import Cubical.WildCat.Functor
open import Cubical.WildCat.Instances.Types
open import CubicalCompat.WildCat.Functor
open import Cubical.WildCat.NaturalTransformation.Base

open WildCat

private
  variable
    ℓC ℓC′ : Level

module _ (ℓ : Level) where
  TYPE = TypeCat ℓ

  module _ (C : WildCat ℓC ℓC′) where
    open WildNatTrans

    idWildNatTransTypes : {F : WildFunctor C TYPE} → WildNatTrans _ _ F F
    idWildNatTransTypes .N-ob x = TYPE .id
    idWildNatTransTypes .N-hom f = refl

    module _
      (F G H : WildFunctor C TYPE) where
      open import Prelude
    
      -- Not sure how worth this is
      compWildNatTransTypes : WildNatTrans _ _ F G → WildNatTrans _ _ G H → WildNatTrans _ _ F H
      N-ob (compWildNatTransTypes η γ) X = N-ob η X » N-ob γ X
      N-hom (compWildNatTransTypes η γ) {x = x} {y = y} f = 
        cong (_» (N-ob γ y)) (N-hom η f)
        ∙ cong (N-ob η x »_) (N-hom γ f)

    open import Cubical.Foundations.GroupoidLaws

    WildCopshCat : WildCat _ _
    ob WildCopshCat = WildFunctor C TYPE
    Hom[_,_] WildCopshCat A B = WildNatTrans _ _ A B
    WildCat.id WildCopshCat = idWildNatTransTypes
    _⋆_ WildCopshCat α β = compWildNatTransTypes _ _ _ α β
    ⋆IdL WildCopshCat α = 
      makeNatTransPath
        refl
        λ f → sym (lUnit (α .N-hom f))
    ⋆IdR WildCopshCat α =
      makeNatTransPath
        refl
        λ f → (sym (rUnit (α .N-hom f)))
    ⋆Assoc WildCopshCat α β γ =
      makeNatTransPath
        refl
        λ f → 
          cong (_∙ cong (α .N-ob _ » β .N-ob _ »_) (γ .N-hom f)) (cong-∙ (_» γ .N-ob _) _ _)
          ∙ sym (assoc _ _ _)
          where open import Prelude
          --                 cong (_» γ .N-ob _) (cong (_» β .N-ob _) (N-hom α f) ∙ cong (α .N-ob _ »_) (β .N-hom f))
          --                 ∙ cong (α .N-ob _ » β .N-ob _ »_) (γ .N-hom f)
          -- ≡⟨ cong (_∙ cong (α .N-ob _ » β .N-ob _ »_) (γ .N-hom f)) (cong-∙ (_» γ .N-ob _) _ _) ⟩ 
          --                 (
          --                   cong (_» γ .N-ob _) (cong (_» β .N-ob _) (N-hom α f))
          --                   ∙ cong (_» γ .N-ob _) (cong (α .N-ob _ »_) (β .N-hom f))
          --                 )
          --                 ∙ cong (α .N-ob _ » β .N-ob _ »_) (γ .N-hom f)
          -- ≡⟨ sym (assoc _ _ _) ⟩ 
          --
          --                 cong (_» γ .N-ob _) (cong (_» β .N-ob _) (N-hom α f))
          --                 ∙ (
          --                   cong (_» γ .N-ob _) (cong (α .N-ob _ »_) (β .N-hom f))
          --                   ∙ cong (α .N-ob _ » β .N-ob _ »_) (γ .N-hom f)
          --                 )
          -- ≡⟨ refl ??? ⟩ 
          --                 cong (_» (β .N-ob _ » γ .N-ob _)) (α .N-hom f) 
          --                 ∙ (
          --                   cong (α .N-ob _ »_) (cong (_» γ .N-ob _) (β .N-hom f)) 
          --                   ∙ cong (α .N-ob _ »_) (cong (β .N-ob _ »_) (γ .N-hom f))
          --                 )
          -- ≡⟨
          --   -- cong (cong (_» (β .N-ob _ » γ .N-ob _)) (α .N-hom f) ∙_) (sym (cong-∙ (α .N-ob _ »_) (cong (_» γ .N-ob _) (β .N-hom f)) (cong (β .N-ob _ »_) (γ .N-hom f))))
          --   refl ???
          -- ⟩ 
          --                 cong (_» (β .N-ob _ » γ .N-ob _)) (α .N-hom f) 
          --                 ∙ cong (α .N-ob _ »_) (
          --                   cong (_» γ .N-ob _) (β .N-hom f) 
          --                   ∙ cong (β .N-ob _ »_) (γ .N-hom f)
          --                 )
          -- ∎

