open import Prelude

module Cubical.Bicategory.Instances.Groupoids (ℓ : Level) where

open import Cubical.Bicategory.Base
open import Cubical.WildCat.Base
open import Cubical.WildCat.Functor
open import Cubical.WildCat.Instances.Types
open import Cubical.WildCat.WithPred

open IsBicategory
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.HLevels

open import Cubical.Foundations.Powerset

module _ where
  open WildCat
  open import Cubical.Foundations.Structure

  GpdWildCat : WildCat (ℓ-suc ℓ) ℓ
  GpdWildCat .ob = hGroupoid ℓ
  GpdWildCat .Hom[_,_] X Y = ⟨ X ⟩ → ⟨ Y ⟩
  GpdWildCat .id = idfun _
  GpdWildCat ._⋆_ f g = f » g
  GpdWildCat .⋆IdL _ = refl
  GpdWildCat .⋆IdR _ = refl
  GpdWildCat .⋆Assoc _ _ _ = refl
  
isBicategory-Gpd : IsBicategory GpdWildCat
isBicategory-Gpd .triangle f g = sym (lUnit _)
isBicategory-Gpd .pentagon f g h k = cong (refl ∙_) (sym (lUnit _))
isBicategory-Gpd .isGpdHom {b = b} = isGroupoidΠ λ _ → b .snd

module _ where
  open Bicategory
  GpdBicat : Bicategory (ℓ-suc ℓ) ℓ
  GpdBicat .str = GpdWildCat
  GpdBicat .isBicat = isBicategory-Gpd
