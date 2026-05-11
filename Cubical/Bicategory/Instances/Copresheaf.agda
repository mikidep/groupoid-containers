open import Cubical.Foundations.Prelude

module Cubical.Bicategory.Instances.Copresheaf (ℓ : Level) where

open import Cubical.Bicategory.Base
open import Cubical.Bicategory.Copresheaf ℓ
open import Cubical.Foundations.GroupoidLaws
open import Prelude.ExtraGpdLaws

private
  variable
    ℓC ℓC' : Level

module _ (C : Bicategory ℓC ℓC') where
  open import Cubical.WildCat.Base
  open import Cubical.WildCat.NaturalTransformation.Base
    using () renaming (makeNatTransPath to WNatTrans≡)
  open import Cubical.WildCat.Functor

  module _ where
    open WildCat
    open WildNatTrans
    
    CopshWildCat : WildCat _ _
    CopshWildCat .ob = Copresheaf C
    CopshWildCat .Hom[_,_] F G = 2NatTrans F G
    CopshWildCat .id = id2NatTrans _
    CopshWildCat ._⋆_ = comp2NatTrans
    CopshWildCat .⋆IdL (α , _) = 2NatTrans≡ 
      (WNatTrans≡
        refl 
        λ f → sym (lUnit (α .N-hom f))
      )
    CopshWildCat .⋆IdR (α , _) = 2NatTrans≡ 
      (WNatTrans≡ 
        refl 
        λ f → sym (rUnit (α .N-hom f))
      ) 
    CopshWildCat .⋆Assoc (α , _) (β , _) (γ , _) = 2NatTrans≡
      (WNatTrans≡
        refl
        λ f → 
          cong (_∙ cong (α .N-ob _ » β .N-ob _ »_) (γ .N-hom f)) (cong-∙ (_» γ .N-ob _) _ _)
          ∙ sym assoc-inf
      )
      where open import Prelude

  module _ where
    open IsBicategory

    open WildCat CopshWildCat
    open Whiskering CopshWildCat

    open import Cubical.Foundations.Path
    open import Prelude.Square

    isBicatCopsh : IsBicategory CopshWildCat
    isBicatCopsh .triangle α β = sym (PathP→compPathR∙∙ 
        (2NatTrans□ (funExtSquare λ X → funExtSquare λ x → refl)) )
    isBicatCopsh .pentagon α β γ δ = 2NatTrans□ goal
      where
      open WildNatTrans
      open import Prelude
      N₀ : ∀ {a b : Copresheaf C} → 2NatTrans a b → _
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
    isBicatCopsh .isGpdHom = isGroupoid2NatTrans

  open Bicategory
  CopshBicat : Bicategory _ _
  CopshBicat .str = CopshWildCat
  CopshBicat .isBicat = isBicatCopsh
