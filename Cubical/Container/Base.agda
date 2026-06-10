open import Prelude

module Cubical.Container.Base where

record Container : Type₁ where
  constructor _⊲_
  field
    S : Type
    P : S → Type

-- Type of container morphisms
module _ (F G : Container) where
  open Container F
  open Container G renaming
    (
      S to S′
    ; P to P′
    )

  infixr 18 _⇒_
  record _⇒_ : Type where
    constructor CMor
    field
      σ : S → S′
      π : (s : S) → P′ (σ s) → P s

  is-Cartesian : _⇒_ → Type
  is-Cartesian (CMor σ π) = ∀ (s : S) → isEquiv (π s)
    where
    open import Cubical.Foundations.Equiv.Base

  -- Type of Cartesian morphisms
  _⇒ᶜ_ : Type
  _⇒ᶜ_ = Σ _⇒_ is-Cartesian

  CMor′ : (∀ s → Σ S′ (λ s′ → P′ s′ → P s)) → _⇒_
  CMor′ σπ = CMor (σπ » fst) (σπ » snd)
  
  CMor′⁻ : _⇒_ → (∀ s → Σ S′ (λ s′ → P′ s′ → P s)) 
  CMor′⁻ (CMor σ π) s = σ s , π s

  open import Cubical.Reflection.StrictEquiv
  unquoteDecl CMor′≃CMor = declStrictEquiv CMor′≃CMor CMor′ CMor′⁻

module _ {F G : Container} {α β : F ⇒ G} where
  open Container F
  open Container G renaming
    (
      S to S′
    ; P to P′
    )
  open _⇒_ α
  open _⇒_ β renaming
    (
      σ to σ′
    ; π to π′
    )

  open import Cubical.Foundations.Equiv
  open import Cubical.Foundations.Equiv.Properties

  CMor≡′ : (∀ (s : S) → _,_ {B = λ s′ → P′ s′ → P s} (σ s) (π s) ≡ (σ′ s , π′ s))
    → α ≡ β
  CMor≡′ htpy = equivFun (congEquiv (CMor′≃CMor F G)) (funExt htpy)

