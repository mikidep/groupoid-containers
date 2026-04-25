{-# OPTIONS --allow-unsolved-metas #-}
open import Cubical.Foundations.Prelude

module Cubical.Prebicategory.Instances.Copresheaf (ℓ : Level) where

open import Cubical.Prebicategory.Base
open import Cubical.Prebicategory.Copresheaf ℓ
open import Cubical.Foundations.GroupoidLaws

private
  variable
    ℓC ℓC′ : Level

module _ (C : Prebicategory ℓC ℓC′) where
  open import Cubical.WildCat.Base
  open import Cubical.WildCat.NaturalTransformation.Base
    using () renaming (makeNatTransPath to WNatTrans≡)
  open import Cubical.WildCat.Functor
  open WildCat
  open WildNatTrans

  private module C = Prebicategory C
  
  CopshWildCat : WildCat _ _
  CopshWildCat .ob = Copresheaf C
  CopshWildCat .Hom[_,_] F G = 2NatTrans F G
  CopshWildCat .id = id2NatTrans _
  CopshWildCat ._⋆_ α@(⟨α⟩ , _) β@(⟨β⟩ , _) = comp2NatTrans α β
  CopshWildCat .⋆IdL (α , _) = 2NatTrans≡ 
    (WNatTrans≡
      refl 
      λ f → sym (lUnit (α .N-hom f))
    )
  CopshWildCat .⋆IdR (α , _) = 2NatTrans≡ (WNatTrans≡ refl idr) where
    idr : ∀ {x y} → (f : C.Hom[ x , y ]) → α .N-hom f ∙ refl ≡ α .N-hom f
    idr f = sym (rUnit (α .N-hom f))
  CopshWildCat .⋆Assoc (α , _) (β , _) (γ , _) = 2NatTrans≡
    (WNatTrans≡
      refl
      λ f → 
        cong (_∙ cong (α .N-ob _ » β .N-ob _ »_) (γ .N-hom f)) (cong-∙ (_» γ .N-ob _) _ _)
        ∙ sym (assoc _ _ _)
    )
    where open import Prelude

  open Prebicategory
  CopshPrebicat : Prebicategory _ _
  CopshPrebicat .str = CopshWildCat
  CopshPrebicat .isPrebicat = {! !}
