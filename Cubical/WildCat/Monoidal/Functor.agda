
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Unit

open import Cubical.WildCat.Base
open import Cubical.WildCat.BraidedSymmetricMonoidal
open import Cubical.WildCat.Functor
open import Cubical.WildCat.Product
open import Cubical.Data.Sigma renaming (_×_ to _×'_)
open import Cubical.WildCat.Product.Functor

module Cubical.WildCat.Monoidal.Functor
  {ℓC ℓC' ℓD ℓD' : Level} 
  (C : WildCat ℓC ℓC')
  (D : WildCat ℓD ℓD')
  (isMonCatC : isMonoidalWildCat C)
  (isMonCatD : isMonoidalWildCat D)
  where

open WildCat D using ()
  renaming (Hom[_,_] to D[_,_])
open isMonoidalWildCat isMonCatC using ()
  renaming (𝟙 to 𝟙ᶜ; _⊗_ to _⊗ᶜ_)
open isMonoidalWildCat isMonCatD using ()
  renaming (𝟙 to 𝟙ᵈ; _⊗_ to _⊗ᵈ_)

private
  _⊗ᵈ₀_ = curry (_⊗ᵈ_ .WildFunctor.F-ob)
  _⊗ᵈ₁_ = λ {x y} → curry (_⊗ᵈ_ .WildFunctor.F-hom {x} {y})

-- stricter defitinitions for more succint compositions

module ⊗CohSides (F : WildFunctor C D) where
  open WildFunctor

--   private module F = WildFunctor F
--   open F using () 
--     renaming (F-ob to F₀; F-hom to F₁)

  F[-]⊗F[-] F[-⊗-] : WildFunctor (C × C) D
  
  F[-]⊗F[-] = comp-WildFunctor (ProdFunctor F F) _⊗ᵈ_
  F[-⊗-] = comp-WildFunctor _⊗ᶜ_ F

record IsMonoidalFunctor (F : WildFunctor C D) 
  : Type (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓD ℓD')) where
  open WildFunctor F using () renaming (F-ob to F₀)
  open ⊗CohSides F
  field
    F-𝟙 : D[ 𝟙ᵈ , F₀ 𝟙ᶜ ]
    F-⊗ : WildNatTrans _ _ F[-]⊗F[-] F[-⊗-]
    -- coherences here should be modifications, as should 
    -- be triangle and pentagon in MonoidalWildCat, 
    -- cf. Johnson Yau, Motivation 11.2.3.
