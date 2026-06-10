open import Prelude

open import Cubical.WildCat.Base

open import Cubical.Container.Base
import Cubical.Container.Constructions as CC

module Cubical.WildCat.Instances.Container where

open WildCat

ContainerWildCat : WildCat _ _
ContainerWildCat .ob = Container
ContainerWildCat .Hom[_,_] = _⇒_
ContainerWildCat .id = CC.Morphisms.id
ContainerWildCat ._⋆_ = CC.Morphisms._⋆_
ContainerWildCat .⋆IdL _ = refl
ContainerWildCat .⋆IdR _ = refl
ContainerWildCat .⋆Assoc _ _ _ = refl

module Extent where
  open CC.Extent

  open import Cubical.WildCat.Functor
  open import Cubical.WildCat.NaturalTransformation.Base
  open import Cubical.WildCat.Instances.WildCopresheaf
  open import Cubical.WildCat.Instances.Types

  open WildFunctor
  open WildNatTrans

  TypeEndoCat : WildCat _ _
  TypeEndoCat = WildCopshCat ℓ-zero (TypeCat ℓ-zero)

  module _ (F : Container) where
    open Container F
    Ext-ob : WildFunctor (TypeCat ℓ-zero) (TypeCat ℓ-zero)
    Ext-ob .F-ob = ⟦ F ⟧₀
    Ext-ob .F-hom = ⟦ F ⟧₁
    Ext-ob .F-id = refl
    Ext-ob .F-seq α β = refl

  module _ {F G : Container} (α : F ⇒ G) where
    open Container F
    open Container G renaming
      (
        S to S′
      ; P to P′
      )
    open _⇒_ α

    Ext-hom : WildNatTrans _ _ (Ext-ob F) (Ext-ob G)
    Ext-hom .N-ob = Ext₁ α
    Ext-hom .N-hom f = refl

  Extent : WildFunctor ContainerWildCat TypeEndoCat
  Extent .F-ob = Ext-ob
  Extent .F-hom = Ext-hom
  Extent .F-id = makeNatTransPath refl (λ _ → refl)
  Extent .F-seq α β =
    makeNatTransPath refl (λ _ → lUnit refl)
    where
    open import Cubical.Foundations.GroupoidLaws
