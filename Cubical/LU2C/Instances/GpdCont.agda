open import Prelude
open import Cubical.Container.Base
open import Cubical.Container.GpdCont
open import Cubical.LU2C.Base

open import Cubical.WildCat.Instances.GpdCont

module Cubical.LU2C.Instances.GpdCont where

open import Cubical.Foundations.GroupoidLaws

open LU2CSyntax {{...}}

module _ where
  open IsLU2C

  isLU2CGpdCont : IsLU2C GpdContWildCat
  isLU2CGpdCont .triangle _ _ = sym (lUnit _)
  isLU2CGpdCont .pentagon _ _ _ _ = cong (refl ∙_) (sym (lUnit _))
  isLU2CGpdCont .isGpdHom {a = (F , isGpdF)} {b = (G , isGpdG)} = isGpd⇒ isGpdF isGpdG

  GpContLU2C : LU2C _ _
  GpContLU2C = record where
    str = GpdContWildCat
    isLU2C = isLU2CGpdCont

-- module Extent where
--   open import Cubical.LU2C.Copresheaf ℓ-zero as CPsh
--     using (Copresheaf; HGpd; Is2Copresheaf)
--   open import Cubical.LU2C.Instances.Copresheaf ℓ-zero
--
--   open LU2CSyn2C HGpd
--   private module HGpd = LU2C HGpd
--
--   GpdEndoCat : LU2C _ _
--   GpdEndoCat = CopshLU2C HGpd
--
--   module _ (F : Container) where
--     open Container F
--
--     open import Cubical.WildCat.Functor
--     open import Cubical.Foundations.HLevels
--
--     open WildFunctor
--     open Is2Copresheaf
--     open Copresheaf using (str; is2Copresheaf)
--
--     Ext-ob : Copresheaf HGpd
--     Ext-ob .str .F-ob (X , isGpdX) = Σ S (λ s → P s → X)
--       , isGroupoidΣ isGpdS λ _ → isGroupoidΠ λ _ → isGpdX
--     Ext-ob .str .F-hom f (s , px) = s , px » f
--     Ext-ob .str .F-id = refl
--     Ext-ob .str .F-seq _ _ = refl
--     Ext-ob .is2Copresheaf .F-IdL _ = sym (lUnit _)
--     Ext-ob .is2Copresheaf .F-IdR _ = sym (rUnit _)
--     Ext-ob .is2Copresheaf .F-Assoc _ _ _ = cong (refl ∙_) (lUnit _)
--
--   module _ {F G : Container} (α : F ⇒ G) where
--     open Container F using (isGpdP)
--     open Container G using ()
--       renaming (
--         S to S′
--       ; P to P′
--       )
--     open WC._⇒_ α
--
--     open import Cubical.WildCat.Functor
--
--     open WildNatTrans
--     open CPsh.IsPseudonat
--     Ext-hom : CPsh.PseudonatTrans (Ext-ob F) (Ext-ob G)
--     Ext-hom .fst .N-ob (X , _) (s , px) = σ s , π s » px
--     Ext-hom .fst .N-hom f = refl
--     Ext-hom .snd .N-hom-id = sym (lUnit _)
--     Ext-hom .snd .N-hom-seq f g = cong (refl ∙_) (lUnit _)
--
--   open import Cubical.LU2C.Pseudofunctor
--   open Pseudofunctor using (str; isPseudofunctor)
--   open import Cubical.WildCat.Functor using (WildFunctor)
--   open import Cubical.WildCat.NaturalTransformation.Base
--     using () renaming (makeNatTransPath to WNatTrans≡)
--   open WildFunctor
--   open IsPseudofunctor
--   open import Cubical.Foundations.Path
--
--   Extent : Pseudofunctor ContainerLU2C GpdEndoCat
--   Extent .str .F-ob = Ext-ob
--   Extent .str .F-hom = Ext-hom
--   Extent .str .F-id = CPsh.PseudonatTrans≡ (WNatTrans≡ refl (λ _ → refl))
--   Extent .str .F-seq _ _ = CPsh.PseudonatTrans≡ (WNatTrans≡ refl (λ _ → lUnit refl))
--   Extent .isPseudofunctor .F-IdL = PathP→compPathL (CPsh.PseudonatTrans□ (funExtSquare λ X → funExtSquare λ x → refl))
--   Extent .isPseudofunctor .F-IdR = PathP→compPathL (CPsh.PseudonatTrans□ (funExtSquare λ X → funExtSquare λ x → refl))
--   Extent .isPseudofunctor .F-Assoc = CPsh.PseudonatTrans□ (funExtSquare λ X → funExtSquare λ x → refl)
--
--   module _ {F G : Container} (α : F ⇒ G) where
--     open Container F
--     open Container G using ()
--       renaming (
--         S to S′
--       ; P to P′
--       )
--
--     open import Cubical.Foundations.Isomorphism
--     open import Cubical.WildCat.Functor using (WildNatTrans)
--     open Iso
--     open WildNatTrans
--     open import Cubical.Foundations.HLevels
--     open import Cubical.Foundations.Structure using (⟨_⟩)
--
--     open Copresheaf (Ext-ob F)
--       using ()
--       renaming (
--         F₀ to ⟦F⟧;
--         F₁ to ⟦F⟧₁
--       )
--     open Copresheaf (Ext-ob G)
--       using ()
--       renaming (
--         F₀ to ⟦G⟧;
--         F₁ to ⟦G⟧₁
--       )
--
--     Ext-hom-inv :
--       CPsh.PseudonatTrans (Ext-ob F) (Ext-ob G)
--       → F ⇒ G
--     Ext-hom-inv α = CMor σ π
--       where
--       米→ :
--         (A : HGpd.ob)
--         → (∀ (X : HGpd.ob) → (HGpd.Hom[ A , X ]) → ⟨ ⟦G⟧ X ⟩)
--         → ⟨ ⟦G⟧ A ⟩
--       米→ A nat = nat A (idfun _)
--       goal : ∀ (s : S) → Σ S′ (λ σs → P′ σs → P s)
--       goal s =
--         米→
--           (P s , isGpdP)
--           λ X FP→X → α .fst .N-ob X (s , FP→X)
--       σ = goal » fst
--       π = goal » snd
--
--     open import Cubical.Functions.FunExtEquiv
--     open import Cubical.Data.Sigma
--     open import Cubical.Foundations.Path
--     isIso-Ext-hom : isIso (Ext-hom {F} {G})
--     isIso-Ext-hom .fst = Ext-hom-inv
--     isIso-Ext-hom .snd .fst α =
--       CPsh.PseudonatTrans≡ (WNatTrans≡
--         (funExt₂ λ {
--           X (s , v) →
--             sym (α□ v ≡$ (s , idfun _))
--         })
--         λ {X} {Y} f →
--           funExtSquare λ {
--             (s , v) →
--               let
--                 Ps : hGroupoid _
--                 Ps = P s , isGpdP
--                 F₁v = ⟦F⟧₁ {x = Ps} {y = X} v
--                 goal : α□ (v » f) ≡
--                   F₁v ◃ α□ f ∙ α□ v ▹ ⟦G⟧₁ f
--                 goal =
--                     α□ (v » f)
--                   ≡⟨ rUnit _ ⟩
--                     α□ (v » f) ∙ refl
--                   ≡⟨ α .snd .N-hom-seq v f ⟩
--                     refl ∙ F₁v ◃ α□ f ∙ α□ v ▹ ⟦G⟧₁ f
--                   ≡⟨ sym (lUnit _ ) ⟩
--                     F₁v ◃ α□ f ∙ α□ v ▹ ⟦G⟧₁ f
--                   ∎
--               in flipSquare 
--                 {a₀₁ = α₀ Y (s , v » f)}
--                 (compPathR→PathP∙∙ (
--                 sym (α□ (v » f)) ≡$ (s , idfun (P s))
--               ≡⟨ cong (λ p → sym p ≡$ (s , idfun (P s))) goal ⟩
--                 sym (F₁v ◃ α□ f ∙ α□ v ▹ ⟦G⟧₁ f)
--                   ≡$ (s , idfun (P s))
--               ≡⟨ cong sym (congFunct (λ f → f (s , idfun (P s)))
--                   (F₁v ◃ α□ f) (α□ v ▹ ⟦G⟧₁ f)) ⟩
--                 sym (
--                   (F₁v ◃ α□ f ≡$ (s , idfun (P s)))
--                   ∙ (α□ v ▹ ⟦G⟧₁ f ≡$ (s , idfun (P s)))
--                 )
--               ≡⟨ symDistr _ _ ⟩
--                 sym (α□ v ▹ ⟦G⟧₁ f ≡$ (s , idfun (P s)))
--                 ∙ sym (F₁v ◃ α□ f ≡$ (s , idfun (P s)))
--               ∎
--             ))
--           }
--         )
--       where
--       open import Cubical.Foundations.Path
--       open CPsh.IsPseudonat
--       α₀ = α .fst .N-ob
--       α□ = α .fst .N-hom
--     isIso-Ext-hom .snd .snd (CMor σ π) = refl
--
--     open import Cubical.Foundations.Equiv
--
--     Ext-hom-equiv : isEquiv (Ext-hom {F} {G})
--     Ext-hom-equiv = isIsoToIsEquiv isIso-Ext-hom
