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
isPrebicatGpdCont .isGpdHom {a = F} {b = G} = isGroupoidGpdContHom {F} {G}

ContainerPrebicat : Prebicategory _ _
ContainerPrebicat .str = GpdContWildCat
ContainerPrebicat .isPrebicat = isPrebicatGpdCont

module Extent where
  open import Cubical.Prebicategory.Copresheaf ℓ-zero
  open import Cubical.Prebicategory.Instances.Copresheaf ℓ-zero

  GpdEndoCat : Prebicategory _ _
  GpdEndoCat = CopshPrebicat GPD

  module _ (F : GpdContainer) where
    open GpdContainer F

    open import Cubical.WildCat.Functor
    open import Cubical.Foundations.HLevels

    open WildFunctor
    open Is2Copresheaf
    open Copresheaf using (str; is2Copresheaf)

    Ext-ob : Copresheaf GPD
    Ext-ob .str .F-ob (X , isGpdX) = Σ S (λ s → P s → X) 
      , isGroupoidΣ isGpdS λ _ → isGroupoidΠ λ _ → isGpdX
    Ext-ob .str .F-hom f (s , px) = s , px » f
    Ext-ob .str .F-id = refl
    Ext-ob .str .F-seq _ _ = refl
    Ext-ob .is2Copresheaf .F-IdL = sym (lUnit _)
    Ext-ob .is2Copresheaf .F-IdR = sym (rUnit _)
    Ext-ob .is2Copresheaf .F-Assoc = cong (refl ∙_) (lUnit _)

  open Prebicategory ContainerPrebicat using ()
    renaming (Hom[_,_] to GC[_,_])
  module _ {F G : GpdContainer} (α : GC[ F , G ]) where
    open GpdContainer F
    open GpdContainer G renaming 
      (
        S to S′
      ; P to P′
      )
    open _⇒_ α

    open import Cubical.WildCat.Functor

    open WildNatTrans
    open Is2NatTrans
    Ext-hom : 2NatTrans (Ext-ob F) (Ext-ob G)
    Ext-hom .fst .N-ob (X , _) (s , px) = σ s , π s » px
    Ext-hom .fst .N-hom f = refl
    Ext-hom .snd .N-hom-nat f g f≡g = sym (lUnit _) ∙ rUnit _
    Ext-hom .snd .N-hom-id = sym (lUnit _)
    Ext-hom .snd .N-hom-seq f g = cong (refl ∙_) (lUnit _)

  open import Cubical.Prebicategory.Functor
  open Functor using (str; is2Functor)
  open import Cubical.WildCat.Functor using (WildFunctor)
  open import Cubical.WildCat.NaturalTransformation.Base
    using () renaming (makeNatTransPath to WNatTrans≡)
  open WildFunctor
  open Is2Functor
  open import Cubical.Foundations.Path

  Extent : Functor ContainerPrebicat GpdEndoCat
  Extent .str .F-ob = Ext-ob
  Extent .str .F-hom = Ext-hom
  Extent .str .F-id = 2NatTrans≡ (WNatTrans≡ refl (λ _ → refl))
  Extent .str .F-seq _ _ = 2NatTrans≡ (WNatTrans≡ refl (λ _ → lUnit refl))
  Extent .is2Functor .F-IdL = PathP→compPathL (2NatTrans□ (funExtSquare λ X → funExtSquare λ x → refl))
  Extent .is2Functor .F-IdR = PathP→compPathL (2NatTrans□ (funExtSquare λ X → funExtSquare λ x → refl))
  Extent .is2Functor .F-Assoc = PathP→compPathL (2NatTrans□ (funExtSquare λ X → funExtSquare λ x → {! !}))

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
