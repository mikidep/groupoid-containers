module Cubical.WildCat.NaturalTransformation.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.WildCat.Base
open import Cubical.WildCat.Functor

private
  variable
    ℓC ℓC' ℓD ℓD' ℓE ℓE' : Level

module _ {C : WildCat ℓC ℓC'} {D : WildCat ℓD ℓD'} where
  module _ {F G : WildFunctor C D} where

    open WildCat
    open WildFunctor
    open WildNatTrans
    open import Cubical.Foundations.Isomorphism
    
    WNTΣ : Type (ℓ-max (ℓ-max ℓC ℓC') ℓD')
    WNTΣ = Σ ((x : C .ob) → D [ F .F-ob x , G .F-ob x ]) 
      (λ N-ob' 
        → {x y : C .ob} (f : C [ x , y ]) 
        → (F .F-hom f) ⋆⟨ D ⟩ (N-ob' y) 
          ≡ (N-ob' x) ⋆⟨ D ⟩ (G .F-hom f))

    WildNatTrans→Σ : WildNatTrans _ _ F G → WNTΣ
    WildNatTrans→Σ α .fst = α .N-ob
    WildNatTrans→Σ α .snd = α .N-hom

    Σ→WildNatTrans : WNTΣ → WildNatTrans _ _ F G
    Σ→WildNatTrans α .N-ob  = α .fst
    Σ→WildNatTrans α .N-hom = α .snd

    open import Cubical.Foundations.Isomorphism
    open Iso
    WildNatTransIsoΣ : Iso (WildNatTrans _ _ F G) WNTΣ
    WildNatTransIsoΣ .fun = WildNatTrans→Σ
    WildNatTransIsoΣ .inv = Σ→WildNatTrans
    WildNatTransIsoΣ .rightInv x = refl
    WildNatTransIsoΣ .leftInv x i .N-ob = x .N-ob
    WildNatTransIsoΣ .leftInv x i .N-hom = x .N-hom

    WildNatTransEquivΣ = isoToEquiv WildNatTransIsoΣ

  module _ {F G : WildFunctor C D} {α β : WildNatTrans _ _ F G} where
    open WildCat
    open WildFunctor
    open WildNatTrans

    makeNatTransPath : 
      (p : α .N-ob ≡ β .N-ob)
      → (∀ {x y} f → PathP (λ i → (F .F-hom {x} {y} f) ⋆⟨ D ⟩ (p i _) ≡ (p i _) ⋆⟨ D ⟩ (G .F-hom f))
          (α .N-hom f) (β .N-hom f))
      → α ≡ β
    makeNatTransPath p q i .N-ob = p i
    makeNatTransPath p q i .N-hom f = q f i

  module _ {F G : WildFunctor C D} {α β γ δ : WildNatTrans _ _ F G} where
    open WildCat
    open WildFunctor
    open WildNatTrans

    makeNatTransSquare :
      ∀ {p : α ≡ β}
      → {q : γ ≡ δ}
      → {r : α ≡ γ}
      → {s : β ≡ δ}
      → (ob-□ : Square (cong N-ob p) (cong N-ob q) (cong N-ob r) (cong N-ob s))
      → (hom-□ : SquareP
          (λ i j → ∀ {x y} (f : C [ x , y ])
            → (F .F-hom {x} {y} f) ⋆⟨ D ⟩ ob-□ i j y ≡ ob-□ i j x ⋆⟨ D ⟩ (G .F-hom f)
          )
          (cong N-hom p)
          (cong N-hom q)
          (cong N-hom r)
          (cong N-hom s)
        )
      → Square p q r s
    makeNatTransSquare ob-□ hom-□ i j .N-ob = ob-□ i j
    makeNatTransSquare ob-□ hom-□ i j .N-hom = hom-□ i j

module _ {C : WildCat ℓC ℓC'} {D : WildCat ℓD ℓD'} {E : WildCat ℓE ℓE'} where
  module _ {F G : WildFunctor C D} (α : WildNatTrans _ _ F G) (H : WildFunctor D E) where
    open WildNatTrans
    open WildNatTrans α using () renaming (N-ob to α₀)
    open WildFunctor 
    open WildFunctor F using () renaming (F-hom to F₁)
    open WildFunctor G using () renaming (F-hom to G₁)
    open WildFunctor H using () renaming (F-hom to H₁)
    open WildCat D renaming (Hom[_,_] to E[_,_]; _⋆_ to _⋆ᵈ_)
    open WildCat E using (_⋆_) renaming (Hom[_,_] to E[_,_])

    private
      _⋆F_ = comp-WildFunctor {C = C} {D} {E}

    whiskerR-natTrans : WildNatTrans _ _ (F ⋆F H) (G ⋆F H)
    whiskerR-natTrans .N-ob X = H .F-hom (α .N-ob X)
    whiskerR-natTrans .N-hom f = 
      sym (H .F-seq _ _) 
      ∙ cong H₁ (α .N-hom f) 
      ∙ H .F-seq _ _ 
      --   H₁ (F₁ f) ⋆ H₁ (α₀ Y) 
      -- ≡⟨ sym (H .F-seq _ _) ⟩ 
      --   H₁ (F₁ f ⋆ᵈ α₀ Y) 
      -- ≡⟨ cong H₁ (α .N-hom f)⟩ 
      --   H₁ (α₀ X ⋆ᵈ G₁ f) 
      -- ≡⟨ H .F-seq _ _ ⟩ 
      --   H₁ (α₀ X) ⋆ H₁ (G₁ f)
      -- ∎
