open import Cubical.Foundations.Prelude
open import Cubical.Data.Unit

open import Cubical.WildCat.Base
open import Cubical.WildCat.BraidedSymmetricMonoidal
open import Cubical.WildCat.Functor
open import Cubical.WildCat.Product renaming (_×_ to ProdCat)
open import Cubical.Data.Sigma

open import Cubical.Container.Base
open import Cubical.WildCat.Instances.Container

module Cubical.WildCat.Monoidal.Instances.Container where

module _ where
  open Container

  iMC-𝟙 : Container
  iMC-𝟙 .S = Unit
  iMC-𝟙 .P _ = Unit

open Extent using ()
  renaming (Ext-ob to ⟦_⟧)

module _ (F G : Container) where
  open Container F
  open Container G using ()
    renaming (S to S′; P to P′)

  open WildFunctor (⟦ G ⟧) using ()
    renaming (F-ob to ⟦G⟧)

  iMC-⊗₀ : Container
  iMC-⊗₀ .Container.S = ⟦G⟧ S
  iMC-⊗₀ .Container.P (s′ , v′) = Σ[ p′ ∈ P′ s′ ] P (v′ p′)

module _ {F G H K : Container} (α : F ⇒ H) (β : G ⇒ K) where

  open Container F renaming (S to Sꟳ; P to Pꟳ)
  open Container G renaming (S to Sᴳ; P to Pᴳ)
  open Container H renaming (S to Sᴴ; P to Pᴴ)

  open _⇒_ α
  open _⇒_ β renaming (σ to σ′; π to π′)

  open WildFunctor (Extent.Ext-ob G) using ()
    renaming (F-hom to ⟦G⟧₁)

  open WildNatTrans (Extent.Ext-hom β) using ()
    renaming (N-ob to ⟦β⟧)

  open import Prelude

  iMC-⊗₁ : iMC-⊗₀ F G ⇒ iMC-⊗₀ H K
  iMC-⊗₁ ._⇒_.σ = ⟦G⟧₁ σ » ⟦β⟧ Sᴴ
    -- σ′ sᴳ , (π′ sᴳ » Pᴳ→Sꟳ » σ)
  iMC-⊗₁ ._⇒_.π x@(sᴳ , Pᴳ→Sꟳ) (pᴷ , pᴴ) = goal
    where
    goal = π′ sᴳ pᴷ , π (Pᴳ→Sꟳ (π′ sᴳ pᴷ)) pᴴ

module _ where
  open WildFunctor
  open import Cubical.Foundations.Function

  iMC-⊗ : WildFunctor
    (ProdCat ContainerWildCat ContainerWildCat) 
    ContainerWildCat
  iMC-⊗ .F-ob = uncurry iMC-⊗₀
  iMC-⊗ .F-hom = uncurry iMC-⊗₁
  iMC-⊗ .F-id = refl
  iMC-⊗ .F-seq _ _ = refl

module _ where
  open isMonoidalWildCat
  open WildNatTrans
  open WildNatIso
  open wildIsIso

  open import Prelude

  iMC-⊗lUnit : WildNatIso _ _ (restrFunctorₗ iMC-⊗ iMC-𝟙) (idWildFunctor ContainerWildCat)
  iMC-⊗lUnit .trans .N-ob _ = CMor fst λ _ p → p , _
  iMC-⊗lUnit .trans .N-hom f = refl
  iMC-⊗lUnit .isIs _ .inv' = CMor (λ s → s , _) λ _ → fst
  iMC-⊗lUnit .isIs _ .sect = refl
  iMC-⊗lUnit .isIs _ .retr = refl

  iMC-⊗rUnit : WildNatIso _ _ (restrFunctorᵣ iMC-⊗ iMC-𝟙) (idWildFunctor ContainerWildCat)
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

  isMonoidalContainer : isMonoidalWildCat ContainerWildCat
  isMonoidalContainer ._⊗_ = iMC-⊗
  isMonoidalContainer .𝟙 = iMC-𝟙
  isMonoidalContainer .⊗assoc = iMC-⊗assoc
  isMonoidalContainer .⊗lUnit = iMC-⊗lUnit
  isMonoidalContainer .⊗rUnit = iMC-⊗rUnit
  isMonoidalContainer .triang _ _ = refl
  isMonoidalContainer .⊗pentagon _ _ _ _ = refl
