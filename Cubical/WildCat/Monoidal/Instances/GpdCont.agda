open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Unit

open import Cubical.Container.Base as WC using (CMor)
open import Cubical.Bicategory.Copresheaf ℓ-zero
open import Cubical.Bicategory.Instances.Container

open import Cubical.WildCat.Base 
open import Cubical.WildCat.Functor 
open import Cubical.WildCat.Product 
open import Cubical.WildCat.BraidedSymmetricMonoidal

open import Cubical.WildCat.Monoidal.Instances.Container as MW
  using ()

module Cubical.WildCat.Monoidal.Instances.GpdCont where

open Container
open IsGpdContainer

module _ where
  iMC-𝟙 : Container
  iMC-𝟙 .str = MW.iMC-𝟙
  iMC-𝟙 .isGpdContainer .isGpdS = isSet→isGroupoid isSetUnit
  iMC-𝟙 .isGpdContainer .isGpdP = isSet→isGroupoid isSetUnit

open Extent using ()
  renaming (Ext-ob to ⟦_⟧)

module _ (F G : Container) where
  open Copresheaf (⟦ G ⟧) using ()
    renaming (F₀ to ⟦G⟧)

  iMC-⊗₀ : Container
  iMC-⊗₀ .str = MW.iMC-⊗₀ (F .str) (G .str)
  iMC-⊗₀ .isGpdContainer .isGpdS = ⟦G⟧ (F .S , F .isGpdS) .snd
  iMC-⊗₀ .isGpdContainer .isGpdP = isGroupoidΣ 
    (G .isGpdP) 
    λ _ → F .isGpdP

open WildFunctor
open import Cubical.Foundations.Function

iMC-⊗ : WildFunctor
  (GpdContWildCat × GpdContWildCat)
  GpdContWildCat
iMC-⊗ .F-ob = uncurry iMC-⊗₀
iMC-⊗ .F-hom = uncurry MW.iMC-⊗₁
iMC-⊗ .F-id = refl
iMC-⊗ .F-seq _ _ = refl

open WildNatTrans
open WildNatIso
open wildIsIso

open import Prelude

iMC-⊗lUnit : WildNatIso _ _ (restrFunctorₗ iMC-⊗ iMC-𝟙) (idWildFunctor GpdContWildCat)
iMC-⊗lUnit .trans .N-ob _ = CMor fst λ _ p → p , _
iMC-⊗lUnit .trans .N-hom f = refl
iMC-⊗lUnit .isIs _ .inv' = CMor (λ s → s , _) λ _ → fst
iMC-⊗lUnit .isIs _ .sect = refl
iMC-⊗lUnit .isIs _ .retr = refl

iMC-⊗rUnit : WildNatIso _ _ (restrFunctorᵣ iMC-⊗ iMC-𝟙) (idWildFunctor GpdContWildCat)
iMC-⊗rUnit .trans .N-ob _ = CMor (λ x → snd x _) λ _ p → _ , p
iMC-⊗rUnit .trans .N-hom f = refl
iMC-⊗rUnit .isIs _ .inv' = CMor (λ s → _ , (λ _ → s)) λ s p → p .snd
iMC-⊗rUnit .isIs _ .sect = refl
iMC-⊗rUnit .isIs _ .retr = refl

iMC-⊗assoc : WildNatIso _ _ (assocₗ iMC-⊗) (assocᵣ iMC-⊗)
iMC-⊗assoc .trans .N-ob _ = CMor σ π
  where
  σ : _
  σ ((s″ , op″) , op′) = s″ , λ p″ → op″ p″ , λ p′ → op′ (p″ , p′)
  π : _
  π ((s″ , op″) , op′) ((p″ , (p′ , p))) = (p″ , p′) , p
iMC-⊗assoc .trans .N-hom f = refl
iMC-⊗assoc .isIs _ .inv' = CMor σ π
  where
  σ : _
  σ (s″ , op) .fst = (s″ , op » fst)
  σ (s″ , op) .snd (p″ , p′) = op p″ .snd p′
  π : _
  π (s″ , op) ((p″ , p′) , p) = p″ , (p′ , p)
iMC-⊗assoc .isIs _ .sect = refl
iMC-⊗assoc .isIs _ .retr = refl

open isMonoidalWildCat

isMonoidalGpdCont : isMonoidalWildCat GpdContWildCat
isMonoidalGpdCont ._⊗_ = iMC-⊗
isMonoidalGpdCont .𝟙 = iMC-𝟙
isMonoidalGpdCont .⊗assoc = iMC-⊗assoc
isMonoidalGpdCont .⊗lUnit = iMC-⊗lUnit
isMonoidalGpdCont .⊗rUnit = iMC-⊗rUnit
isMonoidalGpdCont .triang _ _ = refl
isMonoidalGpdCont .⊗pentagon _ _ _ _ = refl
