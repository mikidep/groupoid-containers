open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Path
open import Cubical.Functions.FunExtEquiv

open import Cubical.WildCat.Base hiding (_[_,_])
open import Cubical.WildCat.Functor hiding (_$_)
open import Cubical.WildCat.NaturalTransformation.Base
open import Cubical.WildCat.Functor.Instances.GpdEndoComp using (compWild)

module Cubical.WildCat.Monoidal.Instances.GpdEndo.LUnit 
  (ℓ : Level) where

open import Cubical.LU2C.Base
open import Cubical.LU2C.Pseudofunctor.NatTrans.Base
open import Cubical.LU2C.Instances.Groupoids ℓ-zero 
open import Cubical.WildCat.Instances.GpdEndo 
  renaming (GpdEndo to GpdEndoWC)
open import Cubical.LU2C.GpdEndo.Base {ℓ-zero}
open import Cubical.LU2C.GpdEndo.Constructions {ℓ-zero}
open import Cubical.LU2C.GpdEndo.NatTrans.Base {ℓ-zero}
open import Cubical.LU2C.GpdEndo.NatTrans.Constructions {ℓ-zero}

open import Cubical.WildCat.AsLU2C.Instances
open import Prelude.Reassoc
open import Reflection.Reassoc
open import Prelude.ExtraGpdLaws

module _ (F : GpdEndo) where
  open WildNatTrans
  open IsGpdEndoTrans
  open GpdEndoTransConv

  private module F = GpdEndo F

  iMG-lUnit-ob : GpdEndoTrans (Id ⨾₀ F) F
  iMG-lUnit-ob .fst .N-ob X = idfun _
  iMG-lUnit-ob .fst .N-hom f = refl
  iMG-lUnit-ob .snd = fromStrict {F = Id ⨾₀ F} {F} strictGoal
    where
    strictGoal : _
    strictGoal .N-hom-id {x} = reassoc!
    strictGoal .N-hom-seq f g = reassoc!

module _ {F G : GpdEndo} (α : GpdEndoTrans F G) where
  open GpdEndoTrans {F = F} {G} α using ()
    renaming (N-ob to α₀; N-hom to α□)

  private
    λ₀ = iMG-lUnit-ob
    module F = GpdEndo F
    module G = GpdEndo G

  open NotHGpd
  open NotWC GpdEndoWC

  iMG-lUnit-hom : 
    _⋆_ {x = Id ⨾₀ F} {Id ⨾₀ G} {G} 
      (_⨾₁_ {F = Id} {Id} {F} {G} (idPseudonatTrans Id) α) 
      (λ₀ G) 
    ≡ _⋆_ {x = Id ⨾₀ F} {F} {G} (λ₀ F) α
  iMG-lUnit-hom = GpdEndoTrans≡ {F = Id ⨾₀ F} {G} 
    (funExt λ x → F.F-id ▹ α₀ x) 
    λ f → compPath→Square (aux f)
    where
    aux : ∀ {x y} (f : HGpd [ x , y ]) → _
    aux {x} {y} f =
      F.F₁ f ◃ F.F-id ▹ α₀ y
      ∙ refl ∙ α□ f
          ≡⟨ ∙r cong (_▹ α₀ y) (F.F-IdR f) ⟩
      sym (F.F-seq f id) ▹ α₀ y
      ∙ refl ∙ α□ f
          ≡⟨ ∙l ∙r sym (rCancel (F.F-seq id f ▹ α₀ y)) ⟩
      sym (F.F-seq f id) ▹ α₀ y
      ∙ (F.F-seq id f ▹ α₀ y
        ∙ sym (F.F-seq id f) ▹ α₀ y)
      ∙ α□ f
          ≡⟨ ∙l ∙r ∙l cong (_▹ α₀ y) (sym (F.F-IdL f)) ⟩
      sym (F.F-seq f id) ▹ α₀ y
      ∙ (F.F-seq id f ▹ α₀ y
        ∙ F.F-id ▹ F.F₁ f ▹ α₀ y)
      ∙ α□ f
          ≡⟨ reassoc! ⟩
      sym (F.F-seq f id) ▹ α₀ y
      ∙ F.F-seq id f ▹ α₀ y
      ∙ (F.F-id ▹ F.F₁ f ▹ α₀ y
        ∙ α□ f)
          ≡⟨ ∙l ∙l sym (whisk-interchange (F.F-id {x = x .fst}) (α□ f)) ⟩
      sym (F.F-seq f id) ▹ α₀ y
      ∙ F.F-seq id f ▹ α₀ y
      ∙ (F.F₁ id ◃ α□ f
        ∙ F.F-id ▹ α₀ x ▹ G.F₁ f)
          ≡⟨ reassoc! ⟩
      ((sym (F.F-seq f id) ▹ α₀ y
        ∙ refl
        ∙ F.F-seq id f ▹ α₀ y
        ∙ F.F₁ id ◃ α□ f)
        ∙ refl)
      ∙ F.F-id ▹ α₀ x ▹ G.F₁ f
          ∎

module _ (F : GpdEndo) where
  open WildNatTrans
  open IsGpdEndoTrans
  open GpdEndoTransConv
  open wildIsIso

  private module F = GpdEndo F

  iMG-lUnit-isIs : wildIsIso {C = GpdEndoWC}
    {x = Id ⨾₀ F} {y = F} (iMG-lUnit-ob F)
  iMG-lUnit-isIs .inv' .fst .N-ob _ = idfun _
  iMG-lUnit-isIs .inv' .fst .N-hom _ = refl
  iMG-lUnit-isIs .inv' .snd = fromStrict {F = F} {Id ⨾₀ F} strictGoal
    where
    strictGoal : _
    strictGoal .N-hom-id {x} = reassoc!
    strictGoal .N-hom-seq f g = reassoc!
  iMG-lUnit-isIs .sect = GpdEndoTrans≡ {F = F} {G = F}
    refl λ f → reassoc!
  iMG-lUnit-isIs .retr = GpdEndoTrans≡ {F = Id ⨾₀ F} {G = Id ⨾₀ F}
    refl λ f → reassoc!

iMG-lUnit : WildNatIso GpdEndoWC GpdEndoWC
  (restrFunctorₗ compWild Id)
  (idWildFunctor GpdEndoWC)
iMG-lUnit = record where
  trans = record where
    N-ob = iMG-lUnit-ob
    N-hom = iMG-lUnit-hom
  isIs = iMG-lUnit-isIs
