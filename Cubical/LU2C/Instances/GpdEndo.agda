open import Cubical.Foundations.Prelude

module Cubical.LU2C.Instances.GpdEndo (ℓ : Level) where

open import Cubical.LU2C.Base
open import Cubical.LU2C.Instances.Groupoids ℓ-zero
open import Cubical.LU2C.GpdEndo.Base {ℓ-zero}
open import Cubical.LU2C.GpdEndo.NatTrans.Base {ℓ-zero}

open import Cubical.Foundations.GroupoidLaws
open import Prelude.ExtraGpdLaws

open import Cubical.WildCat.Instances.GpdEndo

open import Cubical.WildCat.AsLU2C.Instances

open NotHGpd

-- open import Cubical.WildCat.Base
open import Cubical.WildCat.Functor

module _ where
  open IsLU2C
  
  open NotWC GpdEndoWildCat
  
  open import Cubical.Foundations.Path
  open import Prelude.Square

  isLU2CGpdEndo : IsLU2C GpdEndoWildCat
  isLU2CGpdEndo .triangle {a = F} {c = G} α β = 
    sym (PathP→compPathR∙∙
      (GpdEndoTrans□ {F = F} {G} 
        (funExtSquare λ X → funExtSquare λ x → refl)))
  isLU2CGpdEndo .pentagon {a = F} {e = G} α β γ δ = 
    GpdEndoTrans□ {F = F} {G} goal
    where
    open WildNatTrans
    open import Prelude
    N₀ : GpdEndoTrans F G → _
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
  isLU2CGpdEndo .isGpdHom {a = F} {b = G} = isGroupoidGpdEndoTrans {F = F} {G}

-- TODO: this should be refined from WildFunctorLU2C
GpdEndoLU2C : LU2C _ _
GpdEndoLU2C = record where
  str = GpdEndoWildCat
  isLU2C = isLU2CGpdEndo
