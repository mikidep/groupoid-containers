{-# OPTIONS --lossy-unification #-}
open import Cubical.Foundations.Prelude

module Cubical.Prebicategory.Instances.Copresheaf (ℓ : Level) where

open import Cubical.Prebicategory.Base
open import Cubical.Prebicategory.Copresheaf ℓ

private
  variable
    ℓC ℓC′ : Level

module _ (C : Prebicategory ℓC ℓC′) where
  open Prebicategory C using () renaming (str to ⟨C⟩)
  open import Cubical.WildCat.Base
  open import Cubical.WildCat.NaturalTransformation.Base
    using () renaming (makeNatTransPath to makeWNatTransPath)
  open import Cubical.WildCat.Instances.WildCopresheaf
  open import Cubical.WildCat.Functor
  open WildCat
  open WildNatTrans
  module W = WildCat (WildCopshCat ℓ ⟨C⟩)  
  open import Cubical.Foundations.GroupoidLaws
  
  -- There must be some smart refactoring
  -- through the WildCopshCat
  CopshWildCat : WildCat _ _
  CopshWildCat .ob = Copresheaf C
  CopshWildCat .Hom[_,_] F G = 2NatTrans {C = C} (F .str) (G .str)
    where open Copresheaf
  CopshWildCat .id = id2NatTrans _
  CopshWildCat ._⋆_ = comp2NatTrans
  CopshWildCat .⋆IdL (α , _) = make2NatTransPath 
    (makeWNatTransPath
      refl 
      λ f → sym (lUnit (α .N-hom f))
    )
  CopshWildCat .⋆IdR (α , _) = make2NatTransPath
    (makeWNatTransPath
      refl
      λ f → (sym (rUnit (α .N-hom f)))
    )
  CopshWildCat .⋆Assoc (α , _) (β , _) (γ , _) = make2NatTransPath
    (makeWNatTransPath
      refl
      λ f → 
        cong (_∙ cong (α .N-ob _ » β .N-ob _ »_) (γ .N-hom f)) (cong-∙ (_» γ .N-ob _) _ _)
        ∙ sym (assoc _ _ _)
    )
    where open import Prelude

module _ (C : Prebicategory ℓC ℓC′) where
  open import Cubical.WildCat.Base
  open IsPrebicategory

  private 
    CopshC = CopshWildCat C

  open WildCat CopshC
  open Whiskering CopshC

  open import Cubical.WildCat.Functor
  open Prebicategory C using () renaming (str to ⟨C⟩)
  open Prebicategory GPD using () renaming (str to ⟨GPD⟩)
  open import Cubical.WildCat.Instances.WildCopresheaf ℓ
  module WG = WildCat (WildCopshCat ⟨C⟩)
  module WW = Whiskering (WildCopshCat ⟨C⟩)

  module _ where
    open WildFunctor
    open import Cubical.Prebicategory.Instances.Groupoids ℓ
    open import Cubical.WildCat.NaturalTransformation.Base
    ForgetGpdCopsh : WildFunctor ⟨C⟩ ⟨GPD⟩ → WildFunctor ⟨C⟩ TYPE
    ForgetGpdCopsh F = comp-WildFunctor F ForgetGpd

    ForgetGpdNT : {F G : WildFunctor ⟨C⟩ ⟨GPD⟩}
      → WildNatTrans _ _ F G
      → WildNatTrans _ _ (ForgetGpdCopsh F) (ForgetGpdCopsh G)
    ForgetGpdNT α = whiskerR-natTrans α ForgetGpd

  -- open Copresheaf using () renaming (str to ⟨_⟩)
  -- lemma : ∀ {F G H : Copresheaf C} 
  --   {α : 2NatTrans {C = C} ⟨ F ⟩ ⟨ G ⟩}
  --   {β : 2NatTrans {C = C} ⟨ G ⟩ ⟨ H ⟩}
  --   → let
  --       α′ = ForgetGpdNT (fst α)
  --       β′ = ForgetGpdNT (fst β)
  --     in WG.⋆Assoc α′ WG.id β′ ∙ α′ WW.◃ WG.⋆IdL β′ ≡ WG.⋆IdR α′ WW.▹ β′
  --   → ⋆Assoc α id β ∙ α ◃ ⋆IdL {G} {H} β ≡ ⋆IdR {F} {G} α ▹ β
  -- lemma = {! !}

  isPrebicatCopsh : IsPrebicategory CopshC
  isPrebicatCopsh .triangle {F} {G} {H} α β = lemma
    ( 
      makeNatTransPath refl (λ f → ? ∙ ?) 
        ∙ cong (α′ WG.⋆_) (WG.⋆IdL β′)
    ≡⟨ {! !} ⟩
      {! !}
    ∎)
    where 
    open import Cubical.WildCat.NaturalTransformation.Base
    open import Cubical.Foundations.GroupoidLaws
    open import Cubical.Data.Sigma
    α′ = ForgetGpdNT (fst α)
    β′ = ForgetGpdNT (fst β)
    lemma : WG.⋆Assoc α′ WG.id β′ ∙ α′ WW.◃ WG.⋆IdL β′ ≡ WG.⋆IdR α′ WW.▹ β′
      → ⋆Assoc α (id {G}) β ∙ α ◃ ⋆IdL β ≡ ⋆IdR α ▹ β
    lemma = {! !}
  isPrebicatCopsh .pentagon = {! !}
  isPrebicatCopsh .isGpdHom = {! !}
