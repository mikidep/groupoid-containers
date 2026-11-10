open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Sigma renaming (_×_ to _×'_)
open import Cubical.WildCat.Base
open import Cubical.WildCat.Monoidal.Definition.Structure
open import Cubical.WildCat.Product
open import Cubical.WildCat.Functor
open import Cubical.WildCat.Product.Functor

open import Cubical.WildCat.AsLU2C.Instances

module Cubical.WildCat.Monoidal.Definition.Endpoints
  {ℓ ℓ' : Level} {M : WildCat ℓ ℓ'} 
  (mStr : MonoidalStr M) where

open WildCat M using (ob)
open NotWC M
open MonoidalStr mStr
open WildNatTrans
open WildNatIso

private
  module ⊗ = WildFunctor _⊗_
  𝟙⊗_ = restrFunctorₗ _⊗_ 𝟙
  idF = idWildFunctor
  _⨾_ = comp-WildFunctor
  _⊗₀_ = curry (_⊗_ .WildFunctor.F-ob)
  infix 50 _⊗₁_
  infix 50 _⊗₂_
  _⊗₁_ = λ {x y} → curry (_⊗_ .WildFunctor.F-hom {x} {y})
  _⊗₂_ = λ {x y : ob ×' ob} {f g : (M × M) [ x , y ]} 
    (p : f .fst ≡ g .fst)
    (q : f .snd ≡ g .snd) → cong ⊗.F-hom (≡-× p q)

open WildNatTrans (trans ⊗lUnit)
  renaming (N-ob to ⊗lU₀; N-hom to ⊗lU□)
open WildNatTrans (trans ⊗rUnit)
  renaming (N-ob to ⊗rU₀; N-hom to ⊗rU□)
open WildNatTrans (trans ⊗assoc)
  renaming (N-ob to ⊗as₀; N-hom to ⊗as□)

⊗as₀⁻ : (c : ob ×' ob ×' ob) → M [ _ , _ ]
⊗as₀⁻ c = wildIsIso.inv' (isIs ⊗assoc c)

-- In the schematic composites below, 1_F is the 
-- identity natural transformation on F.

-- (E ◃ ⊗assoc) ⋆ ((⊗rUnit ×₂ 1_(idF M)) ▹ _⊗_)
-- where E(a , b) = (a , 𝟙 , b) and E(f , g) = (f , id , g).
⊗triangleₗ : WildNatTrans (M × M) M ((idF M ×₁ 𝟙⊗_) ⨾ _⊗_) _⊗_
⊗triangleₗ .N-ob (a , b) = ⊗as₀ (a , 𝟙 , b) ⋆ ⊗rU₀ a ⊗₁ id
⊗triangleₗ .N-hom {(a , b)} {(a′ , b′)} (f , g) =
  sym (⋆Assoc _ _ _)
  ∙ ⊗as□ (f , id , g) ▹ ⊗rU₀ a′ ⊗₁ id
  ∙ ⋆Assoc _ _ _
  ∙ ⊗as₀ (a , 𝟙 , b) ◃ (sym (⊗.F-seq (f ⊗₁ id , g) (⊗rU₀ a′ , id))
    -- that's a whiskering below
    ∙ refl ⊗₂ ⋆IdR g
    ∙ ⊗rU□ f ⊗₂ sym (⋆IdL g)
    ∙ ⊗.F-seq (⊗rU₀ a , id) (f , g))
  ∙ sym (⋆Assoc _ _ _)


-- (1_(idF M) ×₂ ⊗lUnit) ▹ _⊗_
-- Except that Id ×₁ Id ⨾ _⊗_ is not def. _⊗_
⊗triangleᵣ : WildNatTrans (M × M) M ((idF M ×₁ 𝟙⊗_) ⨾ _⊗_) _⊗_
⊗triangleᵣ .N-ob (a , b) = id ⊗₁ ⊗lU₀ b
⊗triangleᵣ .N-hom {(a , b)} {(a′ , b′)} (f , g) =
  sym (⊗.F-seq (f , id ⊗₁ g) (id , ⊗lU₀ b′))
  ∙ ⋆IdR f ⊗₂ refl 
  ∙ sym (⋆IdL f) ⊗₂ ⊗lU□ g
  ∙ ⊗.F-seq (id , ⊗lU₀ b) (f , g)
  

M⁴ = M × (M × (M × M))

⊗pentagon-source : WildFunctor M⁴ M
⊗pentagon-source = (idF M ×₁ assocₗ _⊗_) ⨾ _⊗_

⊗pentagon-target : WildFunctor M⁴ M
⊗pentagon-target = (ProdAssoc ⨾ (_⊗_ ×₁ idF (M × M))) ⨾ assocᵣ _⊗_

-- ((1_(idF M) ×₂ ⊗assoc) ▹ _⊗_)
--   ⋆ ((P ◃ ⊗assoc) ⋆ (Q ◃ ((⊗assoc ×₂ 1_(idF M)) ▹ _⊗_)))
-- where P = idF M ×₁ (ProdAssoc ⨾ (_⊗_ ×₁ idF M)),
--       P(a , b , c , d) = (a , b ⊗ c , d),
-- and Q just regroups (a , b , c , d) as ((a , b , c) , d)
-- on both objects and morphisms.
⊗pentagonₗ : WildNatTrans M⁴ M ⊗pentagon-source ⊗pentagon-target
⊗pentagonₗ .N-ob (a , b , c , d) =
  id ⊗₁ ⊗as₀ (b , c , d) ⋆
    (⊗as₀ (a , b ⊗₀ c , d) ⋆
      ⊗as₀ (a , b , c) ⊗₁ id)
⊗pentagonₗ .N-hom {(a , b , c , d)} {(a′ , b′ , c′ , d′)} (f , g , h , k) =
  sym (⋆Assoc _ _ _)
  ∙ (sym (⊗.F-seq (f , g ⊗₁ (h ⊗₁ k)) (id , ⊗as₀ (b′ , c′ , d′)))
    ∙ ⋆IdR f ⊗₂ refl
    ∙ sym (⋆IdL f) ⊗₂ ⊗as□ (g , h , k)
    ∙ ⊗.F-seq (id , ⊗as₀ (b , c , d)) (f , (g ⊗₁ h) ⊗₁ k))
    ▹ (⊗as₀ (a′ , b′ ⊗₀ c′ , d′) ⋆ ⊗as₀ (a′ , b′ , c′) ⊗₁ id)
  ∙ ⋆Assoc _ _ _
  ∙ id ⊗₁ ⊗as₀ (b , c , d) ◃ (sym (⋆Assoc _ _ _)
    ∙ ⊗as□ (f , g ⊗₁ h , k) ▹ ⊗as₀ (a′ , b′ , c′) ⊗₁ id
    ∙ ⋆Assoc _ _ _
    ∙ ⊗as₀ (a , b ⊗₀ c , d) ◃ (sym (⊗.F-seq (f ⊗₁ (g ⊗₁ h) , k) (⊗as₀ (a′ , b′ , c′) , id))
      ∙ refl ⊗₂ ⋆IdR k
      ∙ ⊗as□ (f , g , h) ⊗₂ sym (⋆IdL k)
      ∙ ⊗.F-seq (⊗as₀ (a , b , c) , id) ((f ⊗₁ g) ⊗₁ h , k))
    ∙ sym (⋆Assoc _ _ _))
  ∙ sym (⋆Assoc _ _ _)


-- ((idF M ×₁ (idF M ×₁ _⊗_)) ◃ ⊗assoc)
--   ⋆ ((ProdAssoc ⨾ (_⊗_ ×₁ idF (M × M))) ◃ ⊗assoc)
⊗pentagonᵣ : WildNatTrans M⁴ M ⊗pentagon-source ⊗pentagon-target
⊗pentagonᵣ .N-ob (a , b , c , d) =
  ⊗as₀ (a , b , c ⊗₀ d) ⋆ ⊗as₀ (a ⊗₀ b , c , d)
⊗pentagonᵣ .N-hom {(a , b , c , d)} {(a′ , b′ , c′ , d′)} (f , g , h , k) =
  sym (⋆Assoc _ _ _)
  ∙ ⊗as□ (f , g , h ⊗₁ k) ▹ ⊗as₀ (a′ ⊗₀ b′ , c′ , d′)
  ∙ ⋆Assoc _ _ _
  ∙ ⊗as₀ (a , b , c ⊗₀ d) ◃ ⊗as□ (f ⊗₁ g , h , k)
  ∙ sym (⋆Assoc _ _ _)
  
