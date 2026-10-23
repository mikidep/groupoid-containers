open import Cubical.Foundations.Prelude

module Cubical.LU2C.Instances.Copresheaf (ℓ : Level) where

open import Cubical.LU2C.Base
open import Cubical.LU2C.Instances.Groupoids ℓ
open import Cubical.LU2C.Copresheaf ℓ
open import Cubical.Foundations.GroupoidLaws
open import Prelude.ExtraGpdLaws

open import Cubical.WildCat.FullSub.Notation

open Not2C HGpd

private
  variable
    ℓC ℓC' : Level

module _ (C : LU2C ℓC ℓC') where
  open import Cubical.WildCat.Base
  open import Cubical.WildCat.NaturalTransformation.Base
    using () renaming (makeNatTransPath to WNatTrans≡)
  open import Cubical.WildCat.Functor

  module _ where
    private module W = WildCat
    open WildNatTrans
    open import Prelude.Reassoc
    open LU2C HGpd using () renaming (str to ⟨HGpd⟩)
    open LU2CReassoc ⟨HGpd⟩

    CopshWildCat : WildCat _ _
    CopshWildCat .W.ob = Copresheaf C
    CopshWildCat .W.Hom[_,_] F G = PseudonatTrans F G
    CopshWildCat .W.id = idPseudonatTrans _
    CopshWildCat .W._⋆_ = compPseudonatTrans
    CopshWildCat .W.⋆IdL (α , _) = PseudonatTrans≡
      (WNatTrans≡
        refl
        λ f → sym (lUnit (α .N-hom f))
      )
    CopshWildCat .W.⋆IdR (α , _) = PseudonatTrans≡
      (WNatTrans≡
        refl
        λ f → sym (rUnit (α .N-hom f))
      )
    CopshWildCat .W.⋆Assoc α β γ = PseudonatTrans≡
      (WNatTrans≡
        refl
        λ {x} {y} f → 
          let
            α₀ = α .fst .N-ob
            β₀ = β .fst .N-ob
            γ₀ = γ .fst .N-ob
            α□ = α .fst .N-hom
            β□ = β .fst .N-hom
            γ□ = γ .fst .N-hom
          in reassoc
            ((↑ α□ f ▹′ β₀ y 
              ∙′ α₀ x ◃′ ↑ β□ f) ▹′ γ₀ y 
            ∙′ α₀ x ◃′ β₀ x ◃′ ↑ γ□ f)
            (↑ α□ f ▹′ β₀ y ▹′ γ₀ y
            ∙′ α₀ x ◃′ ↑ β□ f ▹′ γ₀ y
            ∙′ α₀ x ◃′ β₀ x ◃′ ↑ γ□ f)
            refl
      )

  module _ where
    open IsLU2C
    
    open NotWC CopshWildCat
    
    open import Cubical.Foundations.Path
    open import Prelude.Square

    isLU2CCopsh : IsLU2C CopshWildCat
    isLU2CCopsh .triangle α β = sym (PathP→compPathR∙∙
        (PseudonatTrans□ (funExtSquare λ X → funExtSquare λ x → refl)) )
    isLU2CCopsh .pentagon α β γ δ = PseudonatTrans□ goal
      where
      open WildNatTrans
      open import Prelude
      N₀ : ∀ {a b : Copresheaf C} → PseudonatTrans a b → _
      N₀ = fst » N-ob
      midpath : N₀ (((α ⋆ β) ⋆ γ) ⋆ δ) ≡ N₀ (α ⋆ (β ⋆ (γ ⋆ δ)))
      midpath = refl
      goal =
          cong N₀ (⋆Assoc α β γ ▹ δ ∙ ⋆Assoc α (β ⋆ γ) δ ∙ α ◃ ⋆Assoc β γ δ)
        ≡⟨ congFunct N₀ (⋆Assoc α β γ ▹ δ) _ ⟩
          cong N₀ (⋆Assoc α β γ ▹ δ) ∙ cong N₀ (⋆Assoc α (β ⋆ γ) δ ∙ α ◃ ⋆Assoc β γ δ)
        ≡⟨ cong (cong N₀ (⋆Assoc α β γ ▹ δ) ∙_) (congFunct N₀ (⋆Assoc α (β ⋆ γ) δ) _) ⟩
          cong N₀ (⋆Assoc α β γ ▹ δ) ∙ cong N₀ (⋆Assoc α (β ⋆ γ) δ) ∙ cong N₀ (α ◃ ⋆Assoc β γ δ)
        ≡⟨ PathP→compPathL refl ⟩
          midpath
        ≡⟨ PathP→compPathR∙∙ refl ⟩
          cong N₀ (⋆Assoc (α ⋆ β) γ δ) ∙ cong N₀ (⋆Assoc α β (γ ⋆ δ))
        ≡⟨ sym (congFunct N₀ (⋆Assoc (α ⋆ β) γ δ) _) ⟩
          cong N₀ (⋆Assoc (α ⋆ β) γ δ ∙ ⋆Assoc α β (γ ⋆ δ))
        ∎
    isLU2CCopsh .isGpdHom = isGroupoidPseudonatTrans

  open LU2C
  CopshLU2C : LU2C _ _
  CopshLU2C .str = CopshWildCat
  CopshLU2C .isLU2C = isLU2CCopsh
