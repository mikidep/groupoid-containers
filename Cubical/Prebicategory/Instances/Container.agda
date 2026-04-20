open import Prelude

open import Cubical.Container.Base
open import Cubical.WildCat.Base
open import Cubical.Prebicategory.Base

module Cubical.Prebicategory.Instances.Container where

module _ (F : Container) where
  record IsGpdContainer : Type₁ where
    open Container F
    field
      isGpdS : isGroupoid S
      isGpdP : ∀ {s : S} → isGroupoid (P s)

  open IsGpdContainer
  open import Cubical.Foundations.HLevels
  isPropIsGpdContainer : isProp IsGpdContainer
  isPropIsGpdContainer Fis Gis i .isGpdS = isPropIsGroupoid (Fis .isGpdS) (Gis .isGpdS) i
  isPropIsGpdContainer Fis Gis i .isGpdP {s} = isPropIsGroupoid (Fis .isGpdP {s}) (Gis .isGpdP {s}) i

record GpdContainer : Type₁ where
  field
    str : Container
    isGpdContainer : IsGpdContainer str
  open Container str public
  open IsGpdContainer isGpdContainer public

module _ where
  open import Cubical.WildCat.Instances.Container
  open WildCat
  open GpdContainer renaming (str to ⟨_⟩)
  module W = WildCat ContainerWildCat
  
  GpdContWildCat : WildCat _ _
  GpdContWildCat .ob = GpdContainer
  GpdContWildCat .Hom[_,_] F G = ⟨ F ⟩ ⇒ ⟨ G ⟩
  GpdContWildCat .id     = W.id
  GpdContWildCat ._⋆_    = W._⋆_
  GpdContWildCat .⋆IdL   = W.⋆IdL  
  GpdContWildCat .⋆IdR   = W.⋆IdR  
  GpdContWildCat .⋆Assoc = W.⋆Assoc

module _ {F G : GpdContainer} where
  open GpdContainer F using (isGpdP)
    renaming (str to ⟨F⟩)
  open GpdContainer G using ()
    renaming (str to ⟨G⟩; isGpdS to isGpdS′)
  open import Cubical.Reflection.RecordEquiv
  open import Cubical.Foundations.Isomorphism
  open import Cubical.Foundations.Equiv
  open import Cubical.Foundations.HLevels

  isGroupoidGpdContHom : isGroupoid (⟨F⟩ ⇒ ⟨G⟩)
  isGroupoidGpdContHom = isOfHLevelRespectEquiv 3 
    (invEquiv ContHomEquivΣ) 
    (isGroupoidΣ (isGroupoidΠ λ _ → isGpdS′) 
      λ _ → isGroupoidΠ2 λ s _ → isGpdP {s}
    )
    where
    unquoteDecl ContHomIsoΣ = declareRecordIsoΣ ContHomIsoΣ (quote _⇒_)
    ContHomEquivΣ = isoToEquiv (ContHomIsoΣ {⟨F⟩} {⟨G⟩})

open Prebicategory
open IsPrebicategory
open import Cubical.Foundations.GroupoidLaws

isPrebicatGpdCont : IsPrebicategory GpdContWildCat
isPrebicatGpdCont .triangle _ _ = sym (lUnit _)
isPrebicatGpdCont .pentagon _ _ _ _ = cong (refl ∙_) (sym (lUnit _))
isPrebicatGpdCont .isGpdHom {F} {G} = isGroupoidGpdContHom {F} {G}

ContainerPrebicat : Prebicategory _ _
ContainerPrebicat .str = GpdContWildCat
ContainerPrebicat .isPrebicat = isPrebicatGpdCont

module Extent where
  open import Cubical.Prebicategory.Copresheaf

  GpdEndoCat : Prebicategory _ _
  GpdEndoCat = 
--   open import Cubical.WildCat.Functor
--   -- open import Cubical.WildCat.Instances.WildFunctor
--   open import Cubical.WildCat.NaturalTransformation.Base
--   open import Cubical.WildCat.Instances.WildCopresheaf
--   open import Cubical.WildCat.Instances.Types
--
--   open WildFunctor
--   open WildNatTrans
--
--   TypeEndoCat : WildCat _ _
--   TypeEndoCat = WildCopshCat ℓ-zero (TypeCat ℓ-zero)
--
--   module _ (F : Container) where
--     open Container F
--     Ext-ob : WildFunctor (TypeCat ℓ-zero) (TypeCat ℓ-zero)
--     Ext-ob .F-ob X = Σ S (λ s → P s → X)
--     Ext-ob .F-hom f (s , px) = s , px » f
--     Ext-ob .F-id = refl
--     Ext-ob .F-seq α β = refl
--
--   module _ {F G : Container} (α : F ⇒ G) where
--     open Container F
--     open Container G renaming 
--       (
--         S to S′
--       ; P to P′
--       )
--     open _⇒_ α
--
--     Ext-hom : WildNatTrans _ _ (Ext-ob F) (Ext-ob G)
--     Ext-hom .N-ob X (s , px) = σ s , π s » px
--     Ext-hom .N-hom f = refl
--
--     module _ where
--       private
--         G$ = Ext-ob G .F-hom
--       -- what′s going on here?
--       -- (S ⊲ P) ⇒ G ≃ Π(s : S) . ⟦G⟧ (P s)
--       _ : Ext-hom .N-ob  ≡ λ where
--         X (s , px) → G$ px (σ s , π s)
--       _ = refl
--
--   Extent : WildFunctor ContainerWildCat TypeEndoCat
--   Extent .F-ob = Ext-ob
--   Extent .F-hom = Ext-hom
--   Extent .F-id = makeNatTransPath refl (λ _ → refl)
--   Extent .F-seq α β = 
--     makeNatTransPath refl (λ _ → lUnit refl)
--     where
--     open import Cubical.Foundations.GroupoidLaws
--     -- Second goal was:
--     -- idfun 
--     --   (refl ≡ 
--     --     -- (cong (_» (Ext-hom β .N-ob Y)) (Ext-hom α .N-hom f)) ∙ refl
--     --     -- God knows why the left path is refl
--     --     refl ∙ refl
--     --     )
--
--
--   module _ {F G : Container} (α : F ⇒ G) where
--     open Container F
--     open Container G renaming 
--       (
--         S to S′
--       ; P to P′
--       )
--
--     open import Cubical.Foundations.Equiv
--     open isEquiv
--
--     Ext-hom-equiv : isEquiv (Ext-hom {F} {G})
--     Ext-hom-equiv = {!  !}
--
--     open import Cubical.Foundations.Isomorphism
--     open Iso
--
--     Ext-hom-inv : 
--       WildNatTrans _ _ (Ext-ob F) (Ext-ob G)
--       → F ⇒ G
--     Ext-hom-inv α = CMor σ π
--       where
--       ⟦G⟧ : Type → Type
--       ⟦G⟧ = Ext-ob G .F-ob
--       米→ :
--         (A : Type)
--         → (∀ (X : Type) → (A → X) → ⟦G⟧ X)
--         → ⟦G⟧ A
--       米→ A nat = nat A (idfun _)
--       goal : ∀ (s : S) → Σ S′ (λ σs → P′ σs → P s)
--       goal s = 
--         米→
--           (P s)
--           λ X FP→X → α .N-ob X (s , FP→X)
--       σ = goal » fst
--       π = goal » snd
--
--     open import Cubical.Functions.FunExtEquiv
--     open import Cubical.Data.Sigma
--     open import Cubical.Foundations.Path
--     Ext-hom-is-iso : isIso (Ext-hom {F} {G})
--     Ext-hom-is-iso .fst = Ext-hom-inv
--     Ext-hom-is-iso .snd .fst α = 
--       makeNatTransPath 
--         (funExt₂ λ {
--           X (s , v) →
--             sym (funExt⁻ (α□ v) (s , idfun _))
--         }) 
--         λ {X} {Y} f → 
--           funExtSquare λ {
--             (s , v) → compPath→Square (
--               idfun ( 
--                 (sym (α□ (v » f))               ≡$ (s , idfun (P s))) 
--                 ∙ (cong (F$ v »_) (α□ f)        ≡$ (s , idfun (P s))) 
--                 ≡ refl 
--                 ∙ (sym (cong (_» G$ f) (α□ v))  ≡$ (s , idfun (P s)))
--                 )
--                 {! !}
--               )
--           }
--           where
--           open import Cubical.Foundations.Transport
--           F$ = Ext-ob F .F-hom
--           G$ = Ext-ob G .F-hom
--           α₀ = α .N-ob
--           α□ = α .N-hom
--     Ext-hom-is-iso .snd .snd (CMor σ π) = refl
--
