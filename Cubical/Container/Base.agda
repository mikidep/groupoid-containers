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

module _ {F G : Container} where
  open Container F
  open Container G renaming
    (
      S to S′
    ; P to P′
    )

  CMor′ : (∀ s → Σ S′ (λ s′ → P′ s′ → P s)) → F ⇒ G
  CMor′ σπ = CMor (σπ » fst) (σπ » snd)
  
  CMor′⁻ : F ⇒ G → (∀ s → Σ S′ (λ s′ → P′ s′ → P s)) 
  CMor′⁻ (CMor σ π) s = σ s , π s

  open import Cubical.Reflection.StrictEquiv
  unquoteDecl CMor′≃CMor = declStrictEquiv CMor′≃CMor CMor′ CMor′⁻

