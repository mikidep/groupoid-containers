open import Prelude

open import Cubical.WildCat.Base

open import Cubical.Container.Base

module Cubical.WildCat.Instances.Container where

open WildCat

ContainerWildCat : WildCat _ _
ContainerWildCat .ob = Container
ContainerWildCat .Hom[_,_] = _⇒_
ContainerWildCat .id = CMor (idfun _) (λ s → idfun _)
ContainerWildCat ._⋆_ (CMor σ π) (CMor σ′ π′) = CMor (σ » σ′) (λ s → π′ (σ s) » π s)
ContainerWildCat .⋆IdL _ = refl
ContainerWildCat .⋆IdR _ = refl
ContainerWildCat .⋆Assoc _ _ _ = refl

module Extent where
  open import Cubical.WildCat.Functor
  -- open import Cubical.WildCat.Instances.WildFunctor
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
    Ext-ob .F-ob X = Σ S (λ s → P s → X)
    Ext-ob .F-hom f (s , px) = s , px » f
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
    Ext-hom .N-ob X (s , px) = σ s , π s » px
    Ext-hom .N-hom f = refl
    
    module _ (X : Type) (s : S) (px : P s → X) where
      -- what′s going on here?
      _ : Ext-hom .N-ob X (s , px) ≡ Ext-ob G .F-hom px (σ s , π s)
      _ = refl

  Extent : WildFunctor ContainerWildCat TypeEndoCat
  Extent .F-ob = Ext-ob
  Extent .F-hom = Ext-hom
  Extent .F-id = makeNatTransPath refl (λ f → refl)
  Extent .F-seq {x = (S ⊲ P)} {y = (S′ ⊲ P′)} {z = (S″ ⊲ P″)} α β = 
    makeNatTransPath refl (λ _ → lUnit refl)
    where
    open import Cubical.Foundations.GroupoidLaws
    -- Second goal was:
    -- idfun 
    --   (refl ≡ 
    --     -- (cong (_» (Ext-hom β .N-ob Y)) (Ext-hom α .N-hom f)) ∙ refl
    --     -- God knows why the left path is refl
    --     refl ∙ refl
    --     )
    
    
  module _ {F G : Container} (α : F ⇒ G) where
    open Container F
    open Container G renaming 
      (
        S to S′
      ; P to P′
      )

    open import Cubical.Foundations.Equiv
    open isEquiv

    Ext-hom-equiv : isEquiv (Ext-hom {F} {G})
    Ext-hom-equiv = {! !}

    open import Cubical.Foundations.Isomorphism
    open Iso
    
    Ext-hom-inv : 
      WildNatTrans _ _ (Ext-ob F) (Ext-ob G)
      → F ⇒ G
    Ext-hom-inv α = CMor σ π
      where
      ⟦G⟧ : Type → Type
      ⟦G⟧ = Ext-ob G .F-ob
      米→ :
        (A : Type)
        → (∀ (X : Type) → (A → X) → ⟦G⟧ X)
        → ⟦G⟧ A
      米→ A nat = nat A (idfun _)
      goal : ∀ (s : S) → Σ S′ (λ σs → P′ σs → P s)
      goal s = 
        米→
          (P s)
          λ X FP→X → α .N-ob X (s , FP→X)
      σ = goal » fst
      π = goal » snd

    open import Cubical.Functions.FunExtEquiv
    open import Cubical.Data.Sigma
    open import Cubical.Foundations.Path
    Ext-hom-is-iso : isIso (Ext-hom {F} {G})
    Ext-hom-is-iso .fst = Ext-hom-inv
    Ext-hom-is-iso .snd .fst α = 
      makeNatTransPath 
        (funExt₂ λ {
          X (s , v) →
            let α□v = α .N-hom v
            in
              sym (funExt⁻ α□v (s , idfun _))
         }) 
        λ {X} {Y} f → {!  !}
    Ext-hom-is-iso .snd .snd (CMor σ π) = refl

