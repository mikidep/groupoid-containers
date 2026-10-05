open import Cubical.Foundations.Prelude

open import Cubical.WildCat.Base

module Cubical.WildCat.Monoidal.Base where

open import Cubical.Data.Sigma renaming (_×_ to _×'_)

open import Cubical.WildCat.Base
open import Cubical.WildCat.Product
open import Cubical.WildCat.Functor

private
  variable
    ℓ ℓ' : Level

open WildCat

open WildFunctor
open WildNatTrans
open WildNatIso
open wildIsIso

module _ (M : WildCat ℓ ℓ') where
  record isMonoidalWildCat : Type (ℓ-max ℓ ℓ') where
    field
      _⊗_ : WildFunctor (M × M) M
      𝟙 : ob M

      ⊗assoc : WildNatIso (M × (M × M)) M (assocₗ _⊗_) (assocᵣ _⊗_)

      ⊗lUnit : WildNatIso M M (restrFunctorₗ _⊗_ 𝟙) (idWildFunctor M)
      ⊗rUnit : WildNatIso M M (restrFunctorᵣ _⊗_ 𝟙) (idWildFunctor M)

    private
      α = N-ob (trans ⊗assoc)
      α⁻ : (c : ob M ×' ob M ×' ob M) → M [ _ , _ ]
      α⁻ c = wildIsIso.inv' (isIs ⊗assoc c)
      rId = N-ob (trans ⊗rUnit)
      lId = N-ob (trans ⊗lUnit)

    field
      -- Note: associators are on the form x ⊗ (y ⊗ z) → (x ⊗ y) ⊗ z
      -- TODO: change to paths between nat trans.
      ⊗triangle : (a b : M .ob)
        → α (a , 𝟙 , b) ⋆⟨ M ⟩ (F-hom _⊗_ ((rId a) , id M))
          ≡ F-hom _⊗_ ((id M) , lId b)

      ⊗pentagon : (a b c d : M .ob)
        → (F-hom _⊗_ (id M , α (b , c , d)))
           ⋆⟨ M ⟩ ((α (a , (_⊗_ .F-ob (b , c)) , d))
           ⋆⟨ M ⟩ (F-hom _⊗_ (α (a , b , c) , id M)))
        ≡  (α (a , b , (F-ob _⊗_ (c , d))))
           ⋆⟨ M ⟩ (α((F-ob _⊗_ (a , b)) , c , d))

MonoidalWildCat : (ℓ ℓ' : Level) → Type (ℓ-suc (ℓ-max ℓ ℓ'))
MonoidalWildCat ℓ ℓ' =
  Σ[ C ∈ WildCat ℓ ℓ' ] isMonoidalWildCat C
