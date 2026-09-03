open import Cubical.Foundations.Prelude

open import Cubical.Foundations.Function
open import Cubical.Data.Unit

open import Cubical.Container.Base

module Cubical.Container.Monoid.Free_ (T : Container) where

open Container T

data S* : Type where
  unit : S*
  sup : (s : S) → (ps* : P s → S*) → S*

module _ 
  {ℓ : Level}
  (B : S* → Type ℓ)
  (unit′ : B unit)
  (sup′ : {s : S} {ps* : P s → S*} 
    (ps*′ : (p : P s) → B (ps* p)) → B (sup s ps*))
  where

  S*-elim : ∀ s* → B s*
  S*-elim unit = unit′
  S*-elim (sup s ps*) = sup′ λ p → S*-elim (ps* p)

P* : S* → Type
P* unit = Unit
P* (sup s ps*) = Σ (P s) (λ p → P* (ps* p))

-- S* := W λ X → Unit + T X
-- cf. T-uncurry

P*′ : S* → Type
P*′ = S*-elim _ Unit (Σ _)

T* = S* ⊲ P*

-- T* ≃ Id + T ⊗ T*

-- S* is fix (1 + T)
-- P* is S*-elim 1 Σ
-- T* is fix (Id + T ⊗ _)
-- So what's going on here?

open import Cubical.Container.Monoid.Definition T*

private module Free where
  import Cubical.Container.Constructions as CC
  open CC.Morphisms using (id; _⋆_)
  open CC.Monoidal using (𝟙; _⊗₀_; _⊗₁_)
  open import Cubical.Container.Path
  
  η : 𝟙 ⇒ T*
  η = CMor′ λ _ → unit , _

  μ : T* ⊗₀ T* ⇒ T*
  μ = CMor′ (uncurry μ′)
    where
    μ′ : _
    μ′ unit s′ = s′ tt , λ p → _ , p
    μ′ (sup s ps*) s′ = μ-sup-σ , μ-sup-π
      where
      ind : (p : P s) → _
      ind p = μ′ (ps* p) (curry s′ p)
      μ-sup-σ = sup s λ p → ind p .fst
      μ-sup-π : _
      μ-sup-π (p , p*) = (p , ind p .snd p* .fst) , ind p .snd p* .snd

  lUnit : η ⊗₁ id ⋆ μ ≡ LUnit
  lUnit = CMor≡′ (uncurry lUnit′)
    where
    lUnit′ : _
    lUnit′ unit _ = refl
    lUnit′ (sup s ps*) _ = goal
      where
      ind : (p : P s) → _
      ind p = lUnit′ (ps* p) _
      goal : _
      goal i .fst = sup s λ p → ind p i .fst
      goal i .snd (p , p*) = (p , ind p i .snd p* .fst) , ind p i .snd p* .snd

  assoc : Assoc ⋆ μ ⊗₁ id ⋆ μ ≡ id ⊗₁ μ ⋆ μ
  assoc = CMor≡′ (uncurry (uncurry assoc′))
    where
    assoc′ : _
    assoc′ unit s′ unc-s″ = assoc′-unit (s′ tt) (curry unc-s″ tt)
      where
      assoc′-unit : (s′ : S*) (s″ : P* s′ → S*) 
        → _
      assoc′-unit s′ s″ = {! !}
      
    assoc′ (sup s ps*) s′ Σs″ = {! !}
      where
      s″ = curry Σs″

open Pseudomonoid
open _⇒_
open import Cubical.Container.Path
open import Cubical.Data.Sigma using (ΣPathP)

Free : Pseudomonoid
Free .η = CMor′ λ _ → unit , _
Free .μ = Free.μ
Free .lUnit = Free.lUnit
Free .rUnit = CMor≡′ λ _ → refl
Free .assoc = Free.assoc
Free .assoc-coh = {! !}
Free .lrUnit-coh = {! !}

