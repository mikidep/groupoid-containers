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

      α = N-ob (trans ⊗assoc)
      α⁻ : (c : ob ×' ob ×' ob) → M [ _ , _ ]
      α⁻ c = wildIsIso.inv' (isIs ⊗assoc c)
      rId = N-ob (trans ⊗rUnit)
      lId = N-ob (trans ⊗lUnit)

      -- In the schematic composites below, 1_F is the identity natural transformation on F.

      -- (E ◃ ⊗assoc) ⋆ ((⊗rUnit ×₂ 1_(idF M)) ▹ _⊗_)
      -- where E(a , b) = (a , 𝟙 , b) and E(f , g) = (f , id , g).
      ⊗triangleₗ : WildNatTrans (M × M) M ((idF M ×₁ 𝟙⊗_) ⨾ _⊗_) _⊗_
      ⊗triangleₗ = record 
        { N-ob = λ where
          (a , b) → α (a , 𝟙 , b) ⋆ (F-hom _⊗_ ((rId a) , id))
        ; N-hom = λ where
          {(a , b)} {(a′ , b′)} (f , g) → 
            ((F-hom _⊗_ (f , F-hom _⊗_ (id , g)))) 
              ⋆ (α (a′ , 𝟙 , b′) ⋆ (F-hom _⊗_ ((rId a′) , id)))
                ≡⟨ sym (⋆Assoc _ _ _) ⟩
            (F-hom _⊗_ (f , F-hom _⊗_ (id , g))
              ⋆ α (a′ , 𝟙 , b′))
              ⋆ F-hom _⊗_ (rId a′ , id)
                ≡⟨ cong (λ h → h ⋆ F-hom _⊗_ (rId a′ , id))
                    (N-hom (trans ⊗assoc) (f , id , g)) ⟩
            (α (a , 𝟙 , b) ⋆ F-hom _⊗_ (F-hom _⊗_ (f , id) , g))
              ⋆ F-hom _⊗_ (rId a′ , id)
                ≡⟨ ⋆Assoc _ _ _ ⟩
            α (a , 𝟙 , b) ⋆
              (F-hom _⊗_ (F-hom _⊗_ (f , id) , g)
                ⋆ F-hom _⊗_ (rId a′ , id))
                ≡⟨ cong (λ h → α (a , 𝟙 , b) ⋆ h)
                    (sym (F-seq _⊗_ (F-hom _⊗_ (f , id) , g) (rId a′ , id))) ⟩
            α (a , 𝟙 , b) ⋆
              F-hom _⊗_ (F-hom _⊗_ (f , id) ⋆ rId a′ , g ⋆ id)
                ≡⟨ cong (λ h → α (a , 𝟙 , b) ⋆ F-hom _⊗_ h)
                    (≡-× (N-hom (trans ⊗rUnit) f) (⋆IdR g ∙ sym (⋆IdL g))) ⟩
            α (a , 𝟙 , b) ⋆
              F-hom _⊗_ (rId a ⋆ f , id ⋆ g)
                ≡⟨ cong (λ h → α (a , 𝟙 , b) ⋆ h)
                    (F-seq _⊗_ (rId a , id) (f , g)) ⟩
            α (a , 𝟙 , b) ⋆
              (F-hom _⊗_ (rId a , id) ⋆ F-hom _⊗_ (f , g))
                ≡⟨ sym (⋆Assoc _ _ _) ⟩
            (α (a , 𝟙 , b) ⋆ (F-hom _⊗_ ((rId a) , id))) 
              ⋆ (F-hom _⊗_ (f , g))
                ∎
        }

      -- (1_(idF M) ×₂ ⊗lUnit) ▹ _⊗_
      ⊗triangleᵣ : WildNatTrans (M × M) M ((idF M ×₁ 𝟙⊗_) ⨾ _⊗_) _⊗_
      ⊗triangleᵣ = record
        { N-ob = λ where
          (a , b) → F-hom _⊗_ (id , lId b)
        ; N-hom = λ where
          {(a , b)} {(a′ , b′)} (f , g) →
            F-hom _⊗_ (f , F-hom _⊗_ (id , g))
              ⋆ F-hom _⊗_ (id , lId b′)
                ≡⟨ sym (F-seq _⊗_ (f , F-hom _⊗_ (id , g)) (id , lId b′)) ⟩
            F-hom _⊗_ (f ⋆ id , F-hom _⊗_ (id , g) ⋆ lId b′)
                ≡⟨ cong (F-hom _⊗_)
                    (≡-× (⋆IdR f ∙ sym (⋆IdL f)) (N-hom (trans ⊗lUnit) g)) ⟩
            F-hom _⊗_ (id ⋆ f , lId b ⋆ g)
                ≡⟨ F-seq _⊗_ (id , lId b) (f , g) ⟩
            F-hom _⊗_ (id , lId b) ⋆ F-hom _⊗_ (f , g)
                ∎
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
            F-hom _⊗_ (id , α (b , c , d)) ⋆
              (α (a , F-ob _⊗_ (b , c) , d) ⋆
                F-hom _⊗_ (α (a , b , c) , id))
        ; N-hom = λ where
          {(a , b , c , d)} {(a′ , b′ , c′ , d′)} (f , g , h , k) →
            sym (⋆Assoc _ _ _)
            ∙ cong (λ q → q ⋆
                (α (a′ , F-ob _⊗_ (b′ , c′) , d′) ⋆
                  F-hom _⊗_ (α (a′ , b′ , c′) , id)))
              (sym (F-seq _⊗_ (f , F-hom _⊗_ (g , F-hom _⊗_ (h , k)))
                  (id , α (b′ , c′ , d′)))
                ∙ cong (F-hom _⊗_)
                  (≡-× (⋆IdR f ∙ sym (⋆IdL f)) (N-hom (trans ⊗assoc) (g , h , k)))
                ∙ F-seq _⊗_ (id , α (b , c , d))
                  (f , F-hom _⊗_ (F-hom _⊗_ (g , h) , k)))
            ∙ ⋆Assoc _ _ _
            ∙ cong (λ q → F-hom _⊗_ (id , α (b , c , d)) ⋆ q)
              (sym (⋆Assoc _ _ _)
                ∙ cong (λ q → q ⋆ F-hom _⊗_ (α (a′ , b′ , c′) , id))
                  (N-hom (trans ⊗assoc) (f , F-hom _⊗_ (g , h) , k))
                ∙ ⋆Assoc _ _ _
                ∙ cong (λ q → α (a , F-ob _⊗_ (b , c) , d) ⋆ q)
                  (sym (F-seq _⊗_ (F-hom _⊗_ (f , F-hom _⊗_ (g , h)) , k)
                      (α (a′ , b′ , c′) , id))
                    ∙ cong (F-hom _⊗_)
                      (≡-× (N-hom (trans ⊗assoc) (f , g , h)) (⋆IdR k ∙ sym (⋆IdL k)))
                    ∙ F-seq _⊗_ (α (a , b , c) , id)
                      (F-hom _⊗_ (F-hom _⊗_ (f , g) , h) , k))
                ∙ sym (⋆Assoc _ _ _))
            ∙ sym (⋆Assoc _ _ _)
        }

      -- ((idF M ×₁ (idF M ×₁ _⊗_)) ◃ ⊗assoc)
      --   ⋆ ((ProdAssoc ⨾ (_⊗_ ×₁ idF (M × M))) ◃ ⊗assoc)
      ⊗pentagonᵣ : WildNatTrans M⁴ M ⊗pentagon-source ⊗pentagon-target
      ⊗pentagonᵣ = record
        { N-ob = λ where
          (a , b , c , d) →
            α (a , b , F-ob _⊗_ (c , d)) ⋆
              α (F-ob _⊗_ (a , b) , c , d)
        ; N-hom = λ where
          {(a , b , c , d)} {(a′ , b′ , c′ , d′)} (f , g , h , k) →
            sym (⋆Assoc _ _ _)
            ∙ cong (λ q → q ⋆ α (F-ob _⊗_ (a′ , b′) , c′ , d′))
              (N-hom (trans ⊗assoc) (f , g , F-hom _⊗_ (h , k)))
            ∙ ⋆Assoc _ _ _
            ∙ cong (λ q → α (a , b , F-ob _⊗_ (c , d)) ⋆ q)
              (N-hom (trans ⊗assoc) (F-hom _⊗_ (f , g) , h , k))
            ∙ sym (⋆Assoc _ _ _)
        }

    field
      -- Note: associators are on the form x ⊗ (y ⊗ z) → (x ⊗ y) ⊗ z
      -- TODO: change to paths between nat trans.
      ⊗triangle : ⊗triangleₗ ≡ ⊗triangleᵣ

      ⊗pentagon : (a b c d : ob)
        → (F-hom _⊗_ (id , α (b , c , d)))
           ⋆ ((α (a , (_⊗_ .F-ob (b , c)) , d))
           ⋆ (F-hom _⊗_ (α (a , b , c) , id)))
          ≡ (α (a , b , (F-ob _⊗_ (c , d))))
             ⋆ (α((F-ob _⊗_ (a , b)) , c , d))


MonoidalWildCat : (ℓ ℓ' : Level) → Type (ℓ-suc (ℓ-max ℓ ℓ'))
MonoidalWildCat ℓ ℓ' =
  Σ[ C ∈ WildCat ℓ ℓ' ] isMonoidalWildCat C
