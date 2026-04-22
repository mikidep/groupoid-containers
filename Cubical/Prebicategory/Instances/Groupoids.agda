open import Prelude

module Cubical.Prebicategory.Instances.Groupoids (ℓ : Level) where

open import Cubical.Prebicategory.Base
open import Cubical.WildCat.Base
open import Cubical.WildCat.Functor
open import Cubical.WildCat.Instances.Types
open import Cubical.WildCat.WithPred

open IsPrebicategory
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.HLevels

open import Cubical.Foundations.Powerset

module _ where
  open WildCat
  open import Cubical.Foundations.Structure

  GpdWildCat : WildCat (ℓ-suc ℓ) ℓ
  GpdWildCat .ob = TypeWithStr ℓ isGroupoid
  GpdWildCat .Hom[_,_] X Y = ⟨ X ⟩ → ⟨ Y ⟩
  GpdWildCat .id = idfun _
  GpdWildCat ._⋆_ f g = f » g
  GpdWildCat .⋆IdL _ = refl
  GpdWildCat .⋆IdR _ = refl
  GpdWildCat .⋆Assoc _ _ _ = refl
  
isPrebicategory-Gpd : IsPrebicategory GpdWildCat
isPrebicategory-Gpd .triangle f g = sym (lUnit _)
isPrebicategory-Gpd .pentagon f g h k = cong (refl ∙_) (sym (lUnit _))
isPrebicategory-Gpd .isGpdHom {b = b} = isGroupoidΠ λ _ → b .snd

module _ where
  open Prebicategory
  GpdPrebicat : Prebicategory (ℓ-suc ℓ) ℓ
  GpdPrebicat .str = GpdWildCat
  GpdPrebicat .isPrebicat = isPrebicategory-Gpd
