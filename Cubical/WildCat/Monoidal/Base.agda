open import Cubical.Foundations.Prelude

open import Cubical.WildCat.Base

module Cubical.WildCat.Monoidal.Base where

open import Cubical.Data.Sigma renaming (_×_ to _×'_)

open import Cubical.WildCat.Base
open import Cubical.WildCat.Product
open import Cubical.WildCat.Functor
open import Cubical.WildCat.Product.Functor

private
  variable
    ℓ ℓ' : Level

open WildFunctor
open WildNatTrans
open WildNatIso
open wildIsIso

module _ (M : WildCat ℓ ℓ') where
  record isMonoidalWildCat : Type (ℓ-max ℓ ℓ') where
    open WildCat M
    field
      _⊗_ : WildFunctor (M × M) M
      𝟙 : ob

      ⊗assoc : WildNatIso (M × (M × M)) M (assocₗ _⊗_) (assocᵣ _⊗_)

      ⊗lUnit : WildNatIso M M (restrFunctorₗ _⊗_ 𝟙) (idWildFunctor M)
      ⊗rUnit : WildNatIso M M (restrFunctorᵣ _⊗_ 𝟙) (idWildFunctor M)

    private
      𝟙⊗_ = restrFunctorₗ _⊗_ 𝟙
      idF = idWildFunctor
      _⨾_ = comp-WildFunctor

    open WildNatTrans (trans ⊗lUnit)
      renaming (N-ob to ⊗lU₀; N-hom to ⊗lU□)
    open WildNatTrans (trans ⊗rUnit)
      renaming (N-ob to ⊗rU₀; N-hom to ⊗rU□)
    open WildNatTrans (trans ⊗assoc)
      renaming (N-ob to ⊗as₀; N-hom to ⊗as□)
    
    private
      ⊗as₀⁻ : (c : ob ×' ob ×' ob) → M [ _ , _ ]
      ⊗as₀⁻ c = wildIsIso.inv' (isIs ⊗assoc c)

      -- In the schematic composites below, 1_F is the identity natural transformation on F.

      -- (E ◃ ⊗assoc) ⋆ ((⊗rUnit ×₂ 1_(idF M)) ▹ _⊗_)
      -- where E(a , b) = (a , 𝟙 , b) and E(f , g) = (f , id , g).
      ⊗triangleₗ : WildNatTrans (M × M) M ((idF M ×₁ 𝟙⊗_) ⨾ _⊗_) _⊗_
      ⊗triangleₗ = record 
        { N-ob = λ where
          (a , b) → ⊗as₀ (a , 𝟙 , b) ⋆ (F-hom _⊗_ ((⊗rU₀ a) , id))
        ; N-hom = λ where
          {(a , b)} {(a′ , b′)} (f , g) →
            sym (⋆Assoc _ _ _)
            ∙ cong (λ h → h ⋆ F-hom _⊗_ (⊗rU₀ a′ , id)) (⊗as□ (f , id , g))
            ∙ ⋆Assoc _ _ _
            ∙ cong (λ h → ⊗as₀ (a , 𝟙 , b) ⋆ h)
              (sym (F-seq _⊗_ (F-hom _⊗_ (f , id) , g) (⊗rU₀ a′ , id)))
            ∙ cong (λ h → ⊗as₀ (a , 𝟙 , b) ⋆ F-hom _⊗_ h)
              (≡-× refl (⋆IdR g))
            ∙ cong (λ h → ⊗as₀ (a , 𝟙 , b) ⋆ F-hom _⊗_ h)
              (≡-× (⊗rU□ f) (sym (⋆IdL g)))
            ∙ cong (λ h → ⊗as₀ (a , 𝟙 , b) ⋆ h)
              (F-seq _⊗_ (⊗rU₀ a , id) (f , g))
            ∙ sym (⋆Assoc _ _ _)
        }

      -- (1_(idF M) ×₂ ⊗lUnit) ▹ _⊗_
      ⊗triangleᵣ : WildNatTrans (M × M) M ((idF M ×₁ 𝟙⊗_) ⨾ _⊗_) _⊗_
      ⊗triangleᵣ = record
        { N-ob = λ where
          (a , b) → F-hom _⊗_ (id , ⊗lU₀ b)
        ; N-hom = λ where
          {(a , b)} {(a′ , b′)} (f , g) →
            sym (F-seq _⊗_ (f , F-hom _⊗_ (id , g)) (id , ⊗lU₀ b′))
            ∙ cong (F-hom _⊗_) (≡-× (⋆IdR f) refl) 
            ∙ cong (F-hom _⊗_) (≡-× (sym (⋆IdL f)) (⊗lU□ g))
            ∙ F-seq _⊗_ (id , ⊗lU₀ b) (f , g)
        }

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
      ⊗pentagonₗ = record
        { N-ob = λ where
          (a , b , c , d) →
            F-hom _⊗_ (id , ⊗as₀ (b , c , d)) ⋆
              (⊗as₀ (a , F-ob _⊗_ (b , c) , d) ⋆
                F-hom _⊗_ (⊗as₀ (a , b , c) , id))
        ; N-hom = λ where
          {(a , b , c , d)} {(a′ , b′ , c′ , d′)} (f , g , h , k) →
            sym (⋆Assoc _ _ _)
            ∙ cong (λ q → q ⋆
                (⊗as₀ (a′ , F-ob _⊗_ (b′ , c′) , d′) ⋆
                  F-hom _⊗_ (⊗as₀ (a′ , b′ , c′) , id)))
              (sym (F-seq _⊗_ (f , F-hom _⊗_ (g , F-hom _⊗_ (h , k)))
                (id , ⊗as₀ (b′ , c′ , d′))))
            ∙ cong (λ q → F-hom _⊗_ q ⋆
                (⊗as₀ (a′ , F-ob _⊗_ (b′ , c′) , d′) ⋆
                  F-hom _⊗_ (⊗as₀ (a′ , b′ , c′) , id)))
              (≡-× (⋆IdR f) refl)
            ∙ cong (λ q → F-hom _⊗_ q ⋆
                (⊗as₀ (a′ , F-ob _⊗_ (b′ , c′) , d′) ⋆
                  F-hom _⊗_ (⊗as₀ (a′ , b′ , c′) , id)))
              (≡-× (sym (⋆IdL f)) (⊗as□ (g , h , k)))
            ∙ cong (λ q → q ⋆
                (⊗as₀ (a′ , F-ob _⊗_ (b′ , c′) , d′) ⋆
                  F-hom _⊗_ (⊗as₀ (a′ , b′ , c′) , id)))
              (F-seq _⊗_ (id , ⊗as₀ (b , c , d))
                (f , F-hom _⊗_ (F-hom _⊗_ (g , h) , k)))
            ∙ ⋆Assoc _ _ _
            ∙ cong (λ q → F-hom _⊗_ (id , ⊗as₀ (b , c , d)) ⋆ q)
              (sym (⋆Assoc _ _ _))
            ∙ cong (λ q → F-hom _⊗_ (id , ⊗as₀ (b , c , d)) ⋆
                (q ⋆ F-hom _⊗_ (⊗as₀ (a′ , b′ , c′) , id)))
              (⊗as□ (f , F-hom _⊗_ (g , h) , k))
            ∙ cong (λ q → F-hom _⊗_ (id , ⊗as₀ (b , c , d)) ⋆ q)
              (⋆Assoc _ _ _)
            ∙ cong (λ q → F-hom _⊗_ (id , ⊗as₀ (b , c , d)) ⋆
                (⊗as₀ (a , F-ob _⊗_ (b , c) , d) ⋆ q))
              (sym (F-seq _⊗_ (F-hom _⊗_ (f , F-hom _⊗_ (g , h)) , k)
                (⊗as₀ (a′ , b′ , c′) , id)))
            ∙ cong (λ q → F-hom _⊗_ (id , ⊗as₀ (b , c , d)) ⋆
                (⊗as₀ (a , F-ob _⊗_ (b , c) , d) ⋆ F-hom _⊗_ q))
              (≡-× refl (⋆IdR k))
            ∙ cong (λ q → F-hom _⊗_ (id , ⊗as₀ (b , c , d)) ⋆
                (⊗as₀ (a , F-ob _⊗_ (b , c) , d) ⋆ F-hom _⊗_ q))
              (≡-× (⊗as□ (f , g , h)) (sym (⋆IdL k)))
            ∙ cong (λ q → F-hom _⊗_ (id , ⊗as₀ (b , c , d)) ⋆
                (⊗as₀ (a , F-ob _⊗_ (b , c) , d) ⋆ q))
              (F-seq _⊗_ (⊗as₀ (a , b , c) , id)
                (F-hom _⊗_ (F-hom _⊗_ (f , g) , h) , k))
            ∙ cong (λ q → F-hom _⊗_ (id , ⊗as₀ (b , c , d)) ⋆ q)
              (sym (⋆Assoc _ _ _))
            ∙ sym (⋆Assoc _ _ _)
        }

      -- ((idF M ×₁ (idF M ×₁ _⊗_)) ◃ ⊗assoc)
      --   ⋆ ((ProdAssoc ⨾ (_⊗_ ×₁ idF (M × M))) ◃ ⊗assoc)
      ⊗pentagonᵣ : WildNatTrans M⁴ M ⊗pentagon-source ⊗pentagon-target
      ⊗pentagonᵣ = record
        { N-ob = λ where
          (a , b , c , d) →
            ⊗as₀ (a , b , F-ob _⊗_ (c , d)) ⋆
              ⊗as₀ (F-ob _⊗_ (a , b) , c , d)
        ; N-hom = λ where
          {(a , b , c , d)} {(a′ , b′ , c′ , d′)} (f , g , h , k) →
            sym (⋆Assoc _ _ _)
            ∙ cong (λ q → q ⋆ ⊗as₀ (F-ob _⊗_ (a′ , b′) , c′ , d′))
              (⊗as□ (f , g , F-hom _⊗_ (h , k)))
            ∙ ⋆Assoc _ _ _
            ∙ cong (λ q → ⊗as₀ (a , b , F-ob _⊗_ (c , d)) ⋆ q)
              (⊗as□ (F-hom _⊗_ (f , g) , h , k))
            ∙ sym (⋆Assoc _ _ _)
        }

    field
      ⊗triangle : ⊗triangleₗ ≡ ⊗triangleᵣ
      ⊗pentagon : ⊗pentagonₗ ≡ ⊗pentagonᵣ

MonoidalWildCat : (ℓ ℓ' : Level) → Type (ℓ-suc (ℓ-max ℓ ℓ'))
MonoidalWildCat ℓ ℓ' =
  Σ[ C ∈ WildCat ℓ ℓ' ] isMonoidalWildCat C
