open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Path
open import Cubical.Functions.FunExtEquiv

open import Cubical.WildCat.Base hiding (_[_,_])
open import Cubical.WildCat.Functor hiding (_$_)
open import Cubical.WildCat.NaturalTransformation.Base
open import Cubical.WildCat.Functor.Instances.GpdEndoComp using (compWild)

module Cubical.WildCat.Monoidal.Instances.GpdEndo.RUnit 
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

  iMG-rUnit-ob : GpdEndoTrans (F ⨾₀ Id) F
  iMG-rUnit-ob .fst .N-ob X = idfun _
  iMG-rUnit-ob .fst .N-hom f = refl
  iMG-rUnit-ob .snd = fromStrict {F = F ⨾₀ Id} {F} strictGoal
    where
    strictGoal : _
    strictGoal .N-hom-id {x} = reassoc!
    strictGoal .N-hom-seq f g = reassoc!

module _ {F G : GpdEndo} (α : GpdEndoTrans F G) where
  open GpdEndoTrans {F = F} {G} α using ()
    renaming (N-ob to α₀; N-hom to α□)

  private
    ρ₀ = iMG-rUnit-ob
    module F = GpdEndo F
    module G = GpdEndo G

  open NotHGpd
  open NotWC GpdEndoWC

  iMG-rUnit-hom :
    _⋆_ {x = F ⨾₀ Id} {G ⨾₀ Id} {G}
      (_⨾₁_ {F = F} {G} {Id} {Id} α (idPseudonatTrans Id))
      (ρ₀ G)
    ≡ _⋆_ {x = F ⨾₀ Id} {F} {G} (ρ₀ F) α
  iMG-rUnit-hom = GpdEndoTrans≡ {F = F ⨾₀ Id} {G}
    refl λ f → reassoc
      ((refl′ ∙′ ↑ α□ f ∙′ refl′ ∙′ refl′) ∙′ refl′)
      (refl′ ∙′ ↑ α□ f)
      refl

module _ (F : GpdEndo) where
  open WildNatTrans
  open IsGpdEndoTrans
  open GpdEndoTransConv
  open wildIsIso

  private module F = GpdEndo F

  iMG-rUnit-isIs : wildIsIso {C = GpdEndoWC}
    {x = F ⨾₀ Id} {y = F} (iMG-rUnit-ob F)
  iMG-rUnit-isIs .inv' .fst .N-ob _ = idfun _
  iMG-rUnit-isIs .inv' .fst .N-hom _ = refl
  iMG-rUnit-isIs .inv' .snd = fromStrict {F = F} {F ⨾₀ Id} strictGoal
    where
    strictGoal : _
    strictGoal .N-hom-id {x} = reassoc!
    strictGoal .N-hom-seq f g = reassoc!
  iMG-rUnit-isIs .sect = GpdEndoTrans≡ {F = F} {G = F}
    refl λ f → reassoc!
  iMG-rUnit-isIs .retr = GpdEndoTrans≡ {F = F ⨾₀ Id} {G = F ⨾₀ Id}
    refl λ f → reassoc!

iMG-rUnit : WildNatIso GpdEndoWC GpdEndoWC
  (restrFunctorᵣ compWild Id)
  (idWildFunctor GpdEndoWC)
iMG-rUnit = record where
  trans = record where
    N-ob = iMG-rUnit-ob
    N-hom = iMG-rUnit-hom
  isIs = iMG-rUnit-isIs
