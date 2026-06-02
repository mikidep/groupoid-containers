
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

private
  module C = WildCat C
  module D = WildCat D
  module iMC = isMonoidalWildCat isMonCatC
  module iMD = isMonoidalWildCat isMonCatD

open C using ()
  renaming (ob to C₀; Hom[_,_] to C[_,_]; _⋆_ to _⋆ᶜ_)
open D using ()
  renaming (Hom[_,_] to D[_,_]; _⋆_ to _⋆ᵈ_)
open isMonoidalWildCat isMonCatC using ()
  renaming (
    𝟙 to 𝟙ᶜ; 
    _⊗_ to _⊗ᶜ_;
    ⊗lUnit to ⊗lUnitᶜ;
    ⊗rUnit to ⊗rUnitᶜ;
    ⊗assoc to ⊗assocᶜ
  )
open isMonoidalWildCat isMonCatD using ()
  renaming (
    𝟙 to 𝟙ᵈ; 
    _⊗_ to _⊗ᵈ_;
    ⊗lUnit to ⊗lUnitᵈ;
    ⊗rUnit to ⊗rUnitᵈ;
    ⊗assoc to ⊗assocᵈ
  )

open WildNatTrans (WildNatIso.trans ⊗lUnitᶜ) using ()
  renaming (N-ob to ⊗lUnitᶜ₀)
open WildNatTrans (WildNatIso.trans ⊗lUnitᵈ) using ()
  renaming (N-ob to ⊗lUnitᵈ₀)
open WildNatTrans (WildNatIso.trans ⊗rUnitᶜ) using ()
  renaming (N-ob to ⊗rUnitᶜ₀)
open WildNatTrans (WildNatIso.trans ⊗rUnitᵈ) using ()
  renaming (N-ob to ⊗rUnitᵈ₀)
open WildNatTrans (WildNatIso.trans ⊗assocᶜ) using ()
  renaming (N-ob to ⊗assocᶜ₀)
open WildNatTrans (WildNatIso.trans ⊗assocᵈ) using ()
  renaming (N-ob to ⊗assocᵈ₀)

open WildNatTrans

private
  _⊗ᶜ₀_ = curry (_⊗ᶜ_ .WildFunctor.F-ob)
  _⊗ᶜ₁_ = λ {x y} → curry (_⊗ᶜ_ .WildFunctor.F-hom {x} {y})
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

record IsMonoidal (F : WildFunctor C D) 
  : Type (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓD ℓD')) where
  open WildFunctor F using () 
    renaming (F-ob to F₀; F-hom to F₁)
  open ⊗CohSides F
  field
    F-𝟙 : D[ 𝟙ᵈ , F₀ 𝟙ᶜ ]
    F-⊗ : WildNatTrans _ _ F[-]⊗F[-] F[-⊗-]
  private F-⊗₀ = F-⊗ .N-ob
  field
    -- coherences here should be modifications, as should 
    -- be triangle and pentagon in MonoidalWildCat, 
    -- cf. Johnson Yau, Motivation 11.2.3.
    F-⊗lUnit : ∀ {x : C₀}
      → (F-𝟙 ⊗ᵈ₁ D.id) ⋆ᵈ (F-⊗₀ (𝟙ᶜ , x) ⋆ᵈ F₁ (⊗lUnitᶜ₀ x)) 
        ≡ ⊗lUnitᵈ₀ (F₀ x)
    F-⊗rUnit : ∀ {x : C₀}
      → (D.id ⊗ᵈ₁ F-𝟙) ⋆ᵈ (F-⊗₀ (x , 𝟙ᶜ) ⋆ᵈ F₁ (⊗rUnitᶜ₀ x)) 
        ≡ ⊗rUnitᵈ₀ (F₀ x)
    F-⊗assoc : ∀ {x y z : C₀}
      → ⊗assocᵈ₀ (F₀ x , F₀ y , F₀ z)
        ⋆ᵈ ((F-⊗₀ (x , y) ⊗ᵈ₁ D.id)
          ⋆ᵈ F-⊗₀ (x ⊗ᶜ₀ y , z))
        ≡ (D.id ⊗ᵈ₁ F-⊗₀ (y , z))
        ⋆ᵈ (F-⊗₀ (x , y ⊗ᶜ₀ z)
          ⋆ᵈ F₁ (⊗assocᶜ₀ (x , y , z)))

record IsStrongMonoidal (F : WildFunctor C D) 
  : Type (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓD ℓD')) where
  field
    isMonoidal : IsMonoidal F
  open IsMonoidal isMonoidal public
  field
    isIsoF-𝟙 : wildIsIso {C = D} F-𝟙
    isIsoF-⊗ : (x y : C₀) → wildIsIso {C = D} (F-⊗ .N-ob (x , y))

MonoidalFunctor = Σ (WildFunctor C D) IsMonoidal
StrongMonoidalFunctor = Σ (WildFunctor C D) IsStrongMonoidal
