open import Prelude
open import Cubical.Container.Base as WC using (CMor)
open import Cubical.WildCat.Base
open import Cubical.Prebicategory.Base

module Cubical.Prebicategory.Instances.Container where

open import Cubical.Foundations.GroupoidLaws

module _ (F : WC.Container) where
  record IsGpdContainer : Type₁ where
    open WC.Container F
    field
      isGpdS : isGroupoid S
      isGpdP : ∀ {s : S} → isGroupoid (P s)

  open IsGpdContainer
  open import Cubical.Foundations.HLevels
  isPropIsGpdContainer : isProp IsGpdContainer
  isPropIsGpdContainer Fis Gis i .isGpdS = isPropIsGroupoid (Fis .isGpdS) (Gis .isGpdS) i
  isPropIsGpdContainer Fis Gis i .isGpdP {s} = isPropIsGroupoid (Fis .isGpdP {s}) (Gis .isGpdP {s}) i

record Container : Type₁ where
  field
    str : WC.Container
    isGpdContainer : IsGpdContainer str
  open WC.Container str public
  open IsGpdContainer isGpdContainer public

module _ (F G : Container) where
  open Container F using ()
    renaming (str to ⟨F⟩)
  open Container G using ()
    renaming (str to ⟨G⟩)

  infixr 18 _⇒_ 
  _⇒_ : Type
  _⇒_ = ⟨F⟩ WC.⇒ ⟨G⟩

module _ where
  open import Cubical.WildCat.Instances.Container
  open WildCat
  module W = WildCat ContainerWildCat
  
  GpdContWildCat : WildCat _ _
  GpdContWildCat .ob = Container
  GpdContWildCat .Hom[_,_] = _⇒_ 
  GpdContWildCat .id     = W.id
  GpdContWildCat ._⋆_    = W._⋆_
  GpdContWildCat .⋆IdL   = W.⋆IdL  
  GpdContWildCat .⋆IdR   = W.⋆IdR  
  GpdContWildCat .⋆Assoc = W.⋆Assoc

module _ {F G : Container} where
  open Container F using (isGpdP)
    renaming (str to ⟨F⟩)
  open Container G using ()
    renaming (str to ⟨G⟩; isGpdS to isGpdS′)
  open import Cubical.Reflection.RecordEquiv
  open import Cubical.Foundations.Isomorphism
  open import Cubical.Foundations.Equiv
  open import Cubical.Foundations.HLevels

  isGroupoidGpdContHom : isGroupoid (F ⇒ G)
  isGroupoidGpdContHom = isOfHLevelRespectEquiv 3 
    (invEquiv ContHomEquivΣ) 
    (isGroupoidΣ (isGroupoidΠ λ _ → isGpdS′) 
      λ _ → isGroupoidΠ2 λ s _ → isGpdP {s}
    )
    where
    unquoteDecl ContHomIsoΣ = declareRecordIsoΣ ContHomIsoΣ (quote WC._⇒_)
    ContHomEquivΣ = isoToEquiv (ContHomIsoΣ {⟨F⟩} {⟨G⟩})

module _ where
  open Prebicategory
  open IsPrebicategory

  isPrebicatGpdCont : IsPrebicategory GpdContWildCat
  isPrebicatGpdCont .triangle _ _ = sym (lUnit _)
  isPrebicatGpdCont .pentagon _ _ _ _ = cong (refl ∙_) (sym (lUnit _))
  isPrebicatGpdCont .isGpdHom {a = F} {b = G} = isGroupoidGpdContHom {F} {G}

  ContainerPrebicat : Prebicategory _ _
  ContainerPrebicat .str = GpdContWildCat
  ContainerPrebicat .isPrebicat = isPrebicatGpdCont

module Extent where
  open import Cubical.Prebicategory.Copresheaf ℓ-zero as CPsh
    using (Copresheaf; GPD; Is2Copresheaf)
  open import Cubical.Prebicategory.Instances.Copresheaf ℓ-zero

  GpdEndoCat : Prebicategory _ _
  GpdEndoCat = CopshPrebicat GPD

  module _ (F : Container) where
    open Container F

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

  module _ {F G : Container} (α : F ⇒ G) where
    open Container F using (isGpdP)
    open Container G using () 
      renaming (
        S to S′
      ; P to P′
      )
    open WC._⇒_ α

    open import Cubical.WildCat.Functor

    open WildNatTrans
    open CPsh.Is2NatTrans
    Ext-hom : CPsh.2NatTrans (Ext-ob F) (Ext-ob G)
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
  Extent .str .F-id = CPsh.2NatTrans≡ (WNatTrans≡ refl (λ _ → refl))
  Extent .str .F-seq _ _ = CPsh.2NatTrans≡ (WNatTrans≡ refl (λ _ → lUnit refl))
  Extent .is2Functor .F-IdL = PathP→compPathL (CPsh.2NatTrans□ (funExtSquare λ X → funExtSquare λ x → refl))
  Extent .is2Functor .F-IdR = PathP→compPathL (CPsh.2NatTrans□ (funExtSquare λ X → funExtSquare λ x → refl))
  Extent .is2Functor .F-Assoc = CPsh.2NatTrans□ (funExtSquare λ X → funExtSquare λ x → refl)

  module _ {F G : Container} (α : F ⇒ G) where
    open Container F
    open Container G using ()
      renaming (
        S to S′
      ; P to P′
      )

    open import Cubical.Foundations.Isomorphism
    open import Cubical.WildCat.Functor using (WildNatTrans)
    open Iso
    open WildNatTrans
    open import Cubical.Foundations.HLevels
    open import Cubical.Foundations.Structure using (⟨_⟩)

    open Copresheaf (Ext-ob F)
      using ()
      renaming (
        F₀ to ⟦F⟧;
        F₁ to ⟦F⟧₁
      )
    open Copresheaf (Ext-ob G)
      using ()
      renaming (
        F₀ to ⟦G⟧;
        F₁ to ⟦G⟧₁
      )

    Ext-hom-inv : 
      CPsh.2NatTrans (Ext-ob F) (Ext-ob G)
      → F ⇒ G
    Ext-hom-inv α = CMor σ π
      where
      module GPD = Prebicategory GPD
      米→ :
        (A : GPD.ob)
        → (∀ (X : GPD.ob) → (GPD.Hom[ A , X ]) → ⟨ ⟦G⟧ X ⟩)
        → ⟨ ⟦G⟧ A ⟩
      米→ A nat = nat A (idfun _)
      goal : ∀ (s : S) → Σ S′ (λ σs → P′ σs → P s)
      goal s = 
        米→
          (P s , isGpdP)
          λ X FP→X → α .fst .N-ob X (s , FP→X)
      σ = goal » fst
      π = goal » snd

    open import Cubical.Functions.FunExtEquiv
    open import Cubical.Data.Sigma
    open import Cubical.Foundations.Path
    isIso-Ext-hom : isIso (Ext-hom {F} {G})
    isIso-Ext-hom .fst = Ext-hom-inv
    isIso-Ext-hom .snd .fst α = 
      CPsh.2NatTrans≡ (WNatTrans≡ 
        (funExt₂ λ {
          X (s , v) →
            sym (funExt⁻ (α□ v) (s , idfun _))
        }) 
        λ {X} {Y} f → 
          funExtSquare λ {
            (s , v) → 
              let
                Ps : hGroupoid _
                Ps = P s , isGpdP
                F₁v = ⟦F⟧₁ {x = Ps} {y = X} v
                goal : α□ (v » f) ≡ 
                  F₁v ◃ α□ f ∙ α□ v ▹ ⟦G⟧₁ f
                goal = 
                    α□ (v » f) 
                  ≡⟨ rUnit _ ⟩
                    α□ (v » f) ∙ refl
                  ≡⟨ α .snd .N-hom-seq v f ⟩
                    refl ∙ F₁v ◃ α□ f ∙ α□ v ▹ ⟦G⟧₁ f
                  ≡⟨ sym (lUnit _ ) ⟩
                    F₁v ◃ α□ f ∙ α□ v ▹ ⟦G⟧₁ f
                  ∎
              in flipSquare (compPathR→PathP∙∙ (
                sym (α□ (v » f)) ≡$ (s , idfun (P s))
              ≡⟨ cong (λ p → sym p ≡$ (s , idfun (P s))) goal ⟩
                sym (F₁v ◃ α□ f ∙ α□ v ▹ ⟦G⟧₁ f) 
                  ≡$ (s , idfun (P s))
              ≡⟨ cong sym (congFunct (λ f → f (s , idfun (P s)))
                  (F₁v ◃ α□ f) (α□ v ▹ ⟦G⟧₁ f)) ⟩
                sym (
                  (F₁v ◃ α□ f ≡$ (s , idfun (P s)))
                  ∙ (α□ v ▹ ⟦G⟧₁ f ≡$ (s , idfun (P s)))
                )
              ≡⟨ symDistr _ _ ⟩
                sym (α□ v ▹ ⟦G⟧₁ f ≡$ (s , idfun (P s))) 
                ∙ sym (F₁v ◃ α□ f ≡$ (s , idfun (P s)))
              ∎
            ))
          }
        )
      where
      open import Cubical.Foundations.Path
      open Prebicategory GPD
        using (_◃_; _▹_)
      open CPsh.Is2NatTrans
      α₀ = α .fst .N-ob
      α□ = α .fst .N-hom
    isIso-Ext-hom .snd .snd (CMor σ π) = refl

    open import Cubical.Foundations.Equiv
    open isEquiv

    Ext-hom-equiv : isEquiv (Ext-hom {F} {G})
    Ext-hom-equiv = isIsoToIsEquiv isIso-Ext-hom
