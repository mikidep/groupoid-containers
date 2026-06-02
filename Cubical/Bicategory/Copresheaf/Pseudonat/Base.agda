open import Cubical.Foundations.Prelude

-- TODO: Prove these notions are equivalent
-- to those in Cubical.Bicategory.Functor

module Cubical.Bicategory.Copresheaf.Pseudonat.Base (ℓ : Level) where

open import Prelude.Square using (ΣSquareProp)

open import Cubical.WildCat.Functor using (WildNatTrans)
open import Cubical.WildCat.Instances.WildCopresheaf as WC

open import Cubical.Bicategory.Base
open import Cubical.Bicategory.Copresheaf.Base ℓ
open import Cubical.WildCat.NaturalTransformation.Base
  using (makeNatTransSquare)

private
  variable
    ℓC ℓC' : Level

open Bicategory GPD using ()
  renaming (
    str to ⟨GPD⟩;
    Hom[_,_] to D[_,_];
    _⋆_ to _⋆ᵈ_;
    id to idᵈ;
    isGpdHom to isGpdHomGPD;
    ⋆IdL to D-⋆IdL;
    ⋆IdR to D-⋆IdR;
    ⋆Assoc to D-⋆Assoc
  )
open Whiskering ⟨GPD⟩
open 2CellLaws ⟨GPD⟩

module _ {C : Bicategory ℓC ℓC'} where
  private module C = Bicategory C
  open C using ()
    renaming (
      str to ⟨C⟩;
      Hom[_,_] to C[_,_];
      id to idᶜ;
      _⋆_ to _⋆ᶜ_
    )

  open Copresheaf using () renaming (str to ⟨_⟩)

  module _ {F G : Copresheaf C}
    (α : WildNatTrans _ _ ⟨ F ⟩ ⟨ G ⟩) where

    open import Cubical.Foundations.GroupoidLaws

    open WildNatTrans α using ()
      renaming (N-ob to α₀; N-hom to α□)
    open Copresheaf F using (F-id; F-seq; F₁; F₂)
    open Copresheaf G using ()
      renaming (
        F₁ to G₁;
        F-id to G-id;
        F-seq to G-seq;
        F₂ to G₂
      )

    record IsPseudonat : Type (ℓ-max (ℓ-max ℓC ℓC') (ℓ-suc ℓ)) where
      field
        N-hom-id :
          ∀ {X}
          →   α□ (idᶜ {X})
              ∙ α₀ X ◃ G-id
            ≡ F-id ▹ α₀ X
        N-hom-seq :
          ∀ {X} {Y} {Z} (f : C[ X , Y ]) (g : C[ Y , Z ])
          →   α□ (f ⋆ᶜ g)
              ∙ α₀ X ◃ G-seq f g
            ≡ F-seq f g ▹ α₀ Z
              ∙ F₁ f ◃ α□ g
              ∙ α□ f ▹ G₁ g

    open import Cubical.Foundations.HLevels
    open IsPseudonat
    isPropIsPseudonat : isProp IsPseudonat
    isPropIsPseudonat αis βis i .N-hom-id {X} = aux i
      where
      aux : αis .N-hom-id {X} ≡ βis .N-hom-id
      aux = isGpdHomGPD _ _ _ _ (αis .N-hom-id) (βis .N-hom-id)
    isPropIsPseudonat αis βis i .N-hom-seq f g = aux i
      where
      aux : αis .N-hom-seq f g ≡ βis .N-hom-seq f g
      aux = isGpdHomGPD _ _ _ _ (αis .N-hom-seq f g) (βis .N-hom-seq f g)

  module _ (F G : Copresheaf C) where
    open Copresheaf using () renaming (str to ⟨_⟩)
    PseudonatTrans = Σ (WildNatTrans _ _ ⟨ F ⟩ ⟨ G ⟩) (IsPseudonat {F} {G})

  module _ {F G : Copresheaf C}
    {α β : PseudonatTrans F G} where
    open Copresheaf F using (F₁)
    open Copresheaf G using ()
      renaming (F₁ to G₁)

    open import Cubical.Foundations.HLevels
    open import Cubical.Data.Sigma.Properties
    open import Cubical.Foundations.Equiv

    PseudonatTrans≡Equiv :
      (α .fst ≡ β .fst) ≃ (α ≡ β)
    PseudonatTrans≡Equiv = Σ≡PropEquiv isPropIsPseudonat

    PseudonatTrans≡ :
      α .fst ≡ β .fst → α ≡ β
    PseudonatTrans≡ = equivFun PseudonatTrans≡Equiv

    private
      open WildNatTrans
      open import Prelude
      N₀ : PseudonatTrans F G → _
      N₀ = fst » N-ob
      N₁ : ∀ (ξ : PseudonatTrans F G) {x y} (f : C[ x , y ])
        → F₁ f ⋆ᵈ N₀ ξ y ≡ N₀ ξ x ⋆ᵈ G₁ f
      N₁ ξ f = ξ .fst .N-hom f

    PseudonatTransPath≡ :
      ∀ {p q : α ≡ β}
      → cong N₀ p ≡ cong N₀ q
      → p ≡ q
    PseudonatTransPath≡ {p} {q} N₀≡ = ΣSquareProp isPropIsPseudonat aux
      where
      aux : cong fst p ≡ cong fst q
      aux = makeNatTransSquare N₀≡
        (isSet→SquareP
          (λ i j → isSetImplicitΠ2 λ x y → isSetΠ
            λ (f : C[ x , y ]) → isGpdHomGPD (F₁ f ⋆ᵈ N₀≡ i j y) (N₀≡ i j x ⋆ᵈ G₁ f))
          (cong N₁ p) (cong N₁ q) refl refl
        )

  module _ {F G : Copresheaf C}
    {α β γ δ : PseudonatTrans F G} where
    open Copresheaf F using (F₁)
    open Copresheaf G using ()
      renaming (F₁ to G₁)

    private
      open WildNatTrans
      open import Prelude
      N₀ : PseudonatTrans F G → _
      N₀ = fst » N-ob
      N₁ : ∀ (ξ : PseudonatTrans F G) {x y} (f : C[ x , y ])
        → F₁ f ⋆ᵈ N₀ ξ y ≡ N₀ ξ x ⋆ᵈ G₁ f
      N₁ ξ f = ξ .fst .N-hom f

    open import Cubical.Foundations.HLevels

    PseudonatTrans□ :
      ∀ {p : α ≡ β}
      → {q : γ ≡ δ}
      → {r : α ≡ γ}
      → {s : β ≡ δ}
      → (ob-□ : Square (cong N₀ p) (cong N₀ q) (cong N₀ r) (cong N₀ s))
      → Square p q r s
    PseudonatTrans□ {p} {q} {r} {s} ob-□ = ΣSquareProp isPropIsPseudonat snd□
      where
      open import Prelude.Square
      snd□ : Square (cong fst p) (cong fst q) (cong fst r) (cong fst s)
      snd□ = makeNatTransSquare
        ob-□
        (isSet→SquareP
          (λ i j → isSetImplicitΠ2 λ x y → isSetΠ
            λ (f : C[ x , y ]) → isGpdHomGPD (F₁ f ⋆ᵈ ob-□ i j y) (ob-□ i j x ⋆ᵈ G₁ f))
          (cong N₁ p) (cong N₁ q) (cong N₁ r) (cong N₁ s)
        )

  module _ {F G : Copresheaf C} where
    open Copresheaf F using ()
      renaming (str to ⟨F⟩)
    open Copresheaf G using ()
      renaming (str to ⟨G⟩)

    open import Cubical.Foundations.HLevels

    isGroupoidWildNatTrans : isGroupoid (WildNatTrans _ _ ⟨F⟩ ⟨G⟩)
    isGroupoidWildNatTrans = isOfHLevelRespectEquiv 3 (invEquiv WildNatTransEquivΣ)
      (isGroupoidΣ (isGroupoidΠ λ _ → isGpdHomGPD)
        λ x → isSet→isGroupoid (isSetImplicitΠ2
          λ _ _ → isSetΠ λ f → isGpdHomGPD _ _
        )
      )
      where
      open import Cubical.Foundations.Equiv
      open import Cubical.WildCat.NaturalTransformation.Base

    isGroupoidPseudonatTrans : isGroupoid (PseudonatTrans F G)
    isGroupoidPseudonatTrans = isGroupoidΣ
      isGroupoidWildNatTrans
      λ _ → isProp→isOfHLevelSuc 2 (isPropIsPseudonat _)

