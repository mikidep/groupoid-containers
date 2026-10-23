open import Cubical.Foundations.Prelude

open import Cubical.LU2C.Base
open import Cubical.WildCat.Base
open import Cubical.WildCat.Functor
open import CubicalCompat.WildCat.Functor
open import Cubical.WildCat.AsLU2C.Instances
open import Cubical.WildCat.NaturalTransformation.Base
import Cubical.WildCat.AsLU2C.Functor.Notation as NotF
open import Prelude.ExtraGpdLaws
open import Cubical.Foundations.GroupoidLaws

module Cubical.WildCat.Instances.WildFunctLU2C where

private
  variable
    ℓC ℓC' ℓD ℓD' : Level

module _ (C : WildCat ℓC ℓC') (D : LU2C ℓD ℓD') where
  private 
    module W = WildCat
    module L = LU2C
    module C = WildCat C
    module D = LU2C D

  open NotWC C
  open Not2C D

  open WildNatTrans
  open import Cubical.Foundations.Path
  open import Prelude.Reassoc
  open LU2CReassoc D.str

  open import Cubical.LU2C.Properties
    using (⋆IdL-nat; ⋆IdL-⋆; ⋆IdR-nat; ⋆IdR-⋆; ⋆Assoc-nat)

  -- TODO: check vibe obligations
  WildFunctWC : WildCat _ _
  WildFunctWC .W.ob = WildFunctor C (D.str)
  WildFunctWC .W.Hom[_,_] F G = WildNatTrans _ _ F G
  WildFunctWC .W.id = idWildNatTrans
  WildFunctWC .W._⋆_ α β = compWildNatTrans _ _ _ α β
  WildFunctWC .W.⋆IdL {x = F} {y = G} α = makeNatTransPath
    (funExt λ x → D.⋆IdL (α₀ x))
    λ f → compPath→Square (aux f)
    where
    open import Cubical.LU2C.Pseudofunctor
    open WildNatTrans α renaming (N-ob to α₀; N-hom to α□)
    open NotF F
    open NotF G renaming (F₁ to G₁)
    aux : ∀ {x} {y} (f : C.Hom[ x , y ]) → _
    aux {x} {y} f =
      F₁ f ◃ D.⋆IdL (α₀ y) ∙ α□ f
        ≡⟨ ∙r (sym (shuffleSymL (sym (D.triangle (F₁ f) (α₀ y))))) ⟩
      (sym (D.⋆Assoc (F₁ f) D.id (α₀ y)) 
        ∙ D.⋆IdR (F₁ f) ▹ α₀ y)
      ∙ α□ f
        ≡⟨ reass₁ ⟩
      sym (D.⋆Assoc (F₁ f) D.id (α₀ y))
      ∙ (D.⋆IdR (F₁ f) ∙ sym (D.⋆IdL (F₁ f))) ▹ α₀ y
      ∙ D.⋆IdL (F₁ f) ▹ α₀ y
      ∙ α□ f
        ≡⟨ ∙l ∙l ∙r (sym (⋆IdL-⋆ D (F₁ f) (α₀ y))) ⟩
      sym (D.⋆Assoc (F₁ f) D.id (α₀ y))
      ∙ (D.⋆IdR (F₁ f) ∙ sym (D.⋆IdL (F₁ f))) ▹ α₀ y
      ∙ ((D.⋆Assoc D.id (F₁ f) (α₀ y) ∙ D.⋆IdL (F₁ f ⋆ α₀ y)) ∙ α□ f)
        ≡⟨ ∙l ∙l (sym (assoc _ _ _)) ⟩
      sym (D.⋆Assoc (F₁ f) D.id (α₀ y))
      ∙ (D.⋆IdR (F₁ f) ∙ sym (D.⋆IdL (F₁ f))) ▹ α₀ y
      ∙ D.⋆Assoc D.id (F₁ f) (α₀ y)
      ∙ D.⋆IdL (F₁ f ⋆ α₀ y) ∙ α□ f
        ≡⟨ ∙l ∙l ∙l (⋆IdL-nat D (α□ f)) ⟩
      sym (D.⋆Assoc (F₁ f) D.id (α₀ y))
      ∙ (D.⋆IdR (F₁ f) ∙ sym (D.⋆IdL (F₁ f))) ▹ α₀ y
      ∙ D.⋆Assoc D.id (F₁ f) (α₀ y)
      ∙ D.id ◃ α□ f ∙ D.⋆IdL (α₀ x ⋆ G₁ f)
        ≡⟨ ∙l ∙l ∙l ∙l (sym (shuffleSymL (sym (⋆IdL-⋆ D (α₀ x) (G₁ f))))) ⟩
      sym (D.⋆Assoc (F₁ f) D.id (α₀ y))
      ∙ (D.⋆IdR (F₁ f) ∙ sym (D.⋆IdL (F₁ f))) ▹ α₀ y
      ∙ D.⋆Assoc D.id (F₁ f) (α₀ y)
      ∙ D.id ◃ α□ f
      ∙ (sym (D.⋆Assoc D.id (α₀ x) (G₁ f)) ∙ D.⋆IdL (α₀ x) ▹ G₁ f)
        ≡⟨ reass₂ ⟩
      (sym (D.⋆Assoc (F₁ f) D.id (α₀ y))
        ∙ (D.⋆IdR (F₁ f)
          ∙ sym (D.⋆IdL (F₁ f))) ▹ α₀ y
        ∙ D.⋆Assoc D.id (F₁ f) (α₀ y)
        ∙ D.id ◃ α□ f
        ∙ sym (D.⋆Assoc D.id (α₀ x) (G₁ f)))
      ∙ D.⋆IdL (α₀ x) ▹ G₁ f
        ∎
      where
      reass₁ = reassoc
        ((↑ (sym (D.⋆Assoc (F₁ f) D.id (α₀ y)))
          ∙′ ↑ (D.⋆IdR (F₁ f)) ▹′ α₀ y) ∙′ ↑ (α□ f))
        (↑ (sym (D.⋆Assoc (F₁ f) D.id (α₀ y)))
          ∙′ (↑ (D.⋆IdR (F₁ f)) ∙′ ↑ (sym (D.⋆IdL (F₁ f)))) ▹′ α₀ y
          ∙′ ↑ (D.⋆IdL (F₁ f)) ▹′ α₀ y ∙′ ↑ (α□ f))
        (∙l ∙l (sym (shuffleSymL {q = D.⋆IdL (F₁ f) ▹ α₀ y} refl)))
      reass₂ = reassoc
        (↑ (sym (D.⋆Assoc (F₁ f) D.id (α₀ y)))
          ∙′ (↑ (D.⋆IdR (F₁ f)) ∙′ ↑ (sym (D.⋆IdL (F₁ f)))) ▹′ α₀ y
          ∙′ ↑ (D.⋆Assoc D.id (F₁ f) (α₀ y))
          ∙′ D.id ◃′ ↑ (α□ f)
          ∙′ (↑ (sym (D.⋆Assoc D.id (α₀ x) (G₁ f)))
            ∙′ ↑ (D.⋆IdL (α₀ x)) ▹′ G₁ f))
        ((↑ (sym (D.⋆Assoc (F₁ f) D.id (α₀ y)))
          ∙′ (↑ (D.⋆IdR (F₁ f)) ∙′ ↑ (sym (D.⋆IdL (F₁ f)))) ▹′ α₀ y
          ∙′ ↑ (D.⋆Assoc D.id (F₁ f) (α₀ y))
          ∙′ D.id ◃′ ↑ (α□ f)
          ∙′ ↑ (sym (D.⋆Assoc D.id (α₀ x) (G₁ f))))
          ∙′ ↑ (D.⋆IdL (α₀ x)) ▹′ G₁ f)
        refl
  WildFunctWC .W.⋆IdR {x = F} {y = G} α = makeNatTransPath
    (funExt λ x → D.⋆IdR (α₀ x))
    λ f → compPath→Square (aux f)
    where
    open import Cubical.LU2C.Pseudofunctor
    open WildNatTrans α renaming (N-ob to α₀; N-hom to α□)
    open NotF F
    open NotF G renaming (F₁ to G₁)
    aux : ∀ {x} {y} (f : C.Hom[ x , y ]) → _
    aux {x} {y} f =
      F₁ f ◃ D.⋆IdR (α₀ y) ∙ α□ f
        ≡⟨ ∙r (sym (shuffleSymL (sym (⋆IdR-⋆ D (F₁ f) (α₀ y))))) ⟩
      (sym (D.⋆Assoc (F₁ f) (α₀ y) D.id) ∙ D.⋆IdR (F₁ f ⋆ α₀ y))
      ∙ α□ f
        ≡⟨ sym (assoc _ _ _) ⟩
      sym (D.⋆Assoc (F₁ f) (α₀ y) D.id)
      ∙ D.⋆IdR (F₁ f ⋆ α₀ y) ∙ α□ f
        ≡⟨ ∙l (⋆IdR-nat D (α□ f)) ⟩
      sym (D.⋆Assoc (F₁ f) (α₀ y) D.id)
      ∙ α□ f ▹ D.id ∙ D.⋆IdR (α₀ x ⋆ G₁ f)
        ≡⟨ ∙l ∙l (sym (⋆IdR-⋆ D (α₀ x) (G₁ f))) ⟩
      sym (D.⋆Assoc (F₁ f) (α₀ y) D.id)
      ∙ α□ f ▹ D.id
      ∙ D.⋆Assoc (α₀ x) (G₁ f) D.id
      ∙ α₀ x ◃ D.⋆IdR (G₁ f)
        ≡⟨ reass₁ ⟩
      sym (D.⋆Assoc (F₁ f) (α₀ y) D.id)
      ∙ α□ f ▹ D.id
      ∙ D.⋆Assoc (α₀ x) (G₁ f) D.id
      ∙ α₀ x ◃ (D.⋆IdR (G₁ f) ∙ sym (D.⋆IdL (G₁ f)))
      ∙ α₀ x ◃ D.⋆IdL (G₁ f)
        ≡⟨ ∙l ∙l ∙l ∙l (sym (shuffleSymL (sym (D.triangle (α₀ x) (G₁ f))))) ⟩
      sym (D.⋆Assoc (F₁ f) (α₀ y) D.id)
      ∙ α□ f ▹ D.id
      ∙ D.⋆Assoc (α₀ x) (G₁ f) D.id
      ∙ α₀ x ◃ (D.⋆IdR (G₁ f) ∙ sym (D.⋆IdL (G₁ f)))
      ∙ (sym (D.⋆Assoc (α₀ x) D.id (G₁ f)) ∙ D.⋆IdR (α₀ x) ▹ G₁ f)
        ≡⟨ reass₂ ⟩
      (sym (D.⋆Assoc (F₁ f) (α₀ y) D.id)
        ∙ α□ f ▹ D.id
        ∙ D.⋆Assoc (α₀ x) (G₁ f) D.id
        ∙ α₀ x ◃ (D.⋆IdR (G₁ f) ∙ sym (D.⋆IdL (G₁ f)))
        ∙ sym (D.⋆Assoc (α₀ x) D.id (G₁ f)))
      ∙ D.⋆IdR (α₀ x) ▹ G₁ f
        ∎
      where
      reass₁ = reassoc
        (↑ (sym (D.⋆Assoc (F₁ f) (α₀ y) D.id))
          ∙′ ↑ (α□ f) ▹′ D.id
          ∙′ ↑ (D.⋆Assoc (α₀ x) (G₁ f) D.id)
          ∙′ α₀ x ◃′ ↑ (D.⋆IdR (G₁ f)))
        (↑ (sym (D.⋆Assoc (F₁ f) (α₀ y) D.id))
          ∙′ ↑ (α□ f) ▹′ D.id
          ∙′ ↑ (D.⋆Assoc (α₀ x) (G₁ f) D.id)
          ∙′ α₀ x ◃′ (↑ (D.⋆IdR (G₁ f)) ∙′ ↑ (sym (D.⋆IdL (G₁ f))))
          ∙′ α₀ x ◃′ ↑ (D.⋆IdL (G₁ f)))
        (∙l ∙l ∙l ∙l (sym (shuffleSymL {q = α₀ x ◃ D.⋆IdL (G₁ f)} refl)))
      reass₂ = reassoc
        (↑ (sym (D.⋆Assoc (F₁ f) (α₀ y) D.id))
          ∙′ ↑ (α□ f) ▹′ D.id
          ∙′ ↑ (D.⋆Assoc (α₀ x) (G₁ f) D.id)
          ∙′ α₀ x ◃′ (↑ (D.⋆IdR (G₁ f)) ∙′ ↑ (sym (D.⋆IdL (G₁ f))))
          ∙′ (↑ (sym (D.⋆Assoc (α₀ x) D.id (G₁ f)))
            ∙′ ↑ (D.⋆IdR (α₀ x)) ▹′ G₁ f))
        ((↑ (sym (D.⋆Assoc (F₁ f) (α₀ y) D.id))
          ∙′ ↑ (α□ f) ▹′ D.id
          ∙′ ↑ (D.⋆Assoc (α₀ x) (G₁ f) D.id)
          ∙′ α₀ x ◃′ (↑ (D.⋆IdR (G₁ f)) ∙′ ↑ (sym (D.⋆IdL (G₁ f))))
          ∙′ ↑ (sym (D.⋆Assoc (α₀ x) D.id (G₁ f))))
          ∙′ ↑ (D.⋆IdR (α₀ x)) ▹′ G₁ f)
        refl
  WildFunctWC .W.⋆Assoc {u = F} {v = G} {w = H} {x = K} α β γ = makeNatTransPath
    (funExt λ x → D.⋆Assoc (α₀ x) (β₀ x) (γ₀ x))
    λ f → compPath→Square (aux f)
    where
    open import Cubical.LU2C.Pseudofunctor
    open WildNatTrans α renaming (N-ob to α₀; N-hom to α□)
    open WildNatTrans β renaming (N-ob to β₀; N-hom to β□)
    open WildNatTrans γ renaming (N-ob to γ₀; N-hom to γ□)
    open NotF F
    open NotF G renaming (F₁ to G₁)
    open NotF H renaming (F₁ to H₁)
    open NotF K renaming (F₁ to K₁)
    aux : ∀ {x} {y} (f : C.Hom[ x , y ]) → _
    aux {x} {y} f = lCancelEq (lCancelEq goal)
      where
      -- Paste the four pentagons and the three naturality squares,
      -- then cancel the two associators prefixed to both sides.
      goal =
        D.⋆Assoc (F₁ f) (α₀ y) (β₀ y) ▹ γ₀ y
        ∙ D.⋆Assoc (F₁ f) (α₀ y ⋆ β₀ y) (γ₀ y)
        ∙ (F₁ f ◃ D.⋆Assoc (α₀ y) (β₀ y) (γ₀ y)
          ∙ (sym (D.⋆Assoc (F₁ f) (α₀ y) (β₀ y ⋆ γ₀ y))
            ∙ α□ f ▹ (β₀ y ⋆ γ₀ y)
            ∙ D.⋆Assoc (α₀ x) (G₁ f) (β₀ y ⋆ γ₀ y)
            ∙ α₀ x ◃ (sym (D.⋆Assoc (G₁ f) (β₀ y) (γ₀ y))
              ∙ β□ f ▹ γ₀ y
              ∙ D.⋆Assoc (β₀ x) (H₁ f) (γ₀ y)
              ∙ β₀ x ◃ γ□ f
              ∙ sym (D.⋆Assoc (β₀ x) (γ₀ x) (K₁ f)))
            ∙ sym (D.⋆Assoc (α₀ x) (β₀ x ⋆ γ₀ x) (K₁ f))))
          ≡⟨ reass₁ ⟩
        (D.⋆Assoc (F₁ f) (α₀ y) (β₀ y) ▹ γ₀ y
          ∙ D.⋆Assoc (F₁ f) (α₀ y ⋆ β₀ y) (γ₀ y)
          ∙ F₁ f ◃ D.⋆Assoc (α₀ y) (β₀ y) (γ₀ y))
        ∙ sym (D.⋆Assoc (F₁ f) (α₀ y) (β₀ y ⋆ γ₀ y))
        ∙ α□ f ▹ (β₀ y ⋆ γ₀ y)
        ∙ D.⋆Assoc (α₀ x) (G₁ f) (β₀ y ⋆ γ₀ y)
        ∙ α₀ x ◃ (sym (D.⋆Assoc (G₁ f) (β₀ y) (γ₀ y))
          ∙ β□ f ▹ γ₀ y
          ∙ D.⋆Assoc (β₀ x) (H₁ f) (γ₀ y)
          ∙ β₀ x ◃ γ□ f
          ∙ sym (D.⋆Assoc (β₀ x) (γ₀ x) (K₁ f)))
        ∙ sym (D.⋆Assoc (α₀ x) (β₀ x ⋆ γ₀ x) (K₁ f))
          ≡⟨ ∙r (D.pentagon (F₁ f) (α₀ y) (β₀ y) (γ₀ y)) ⟩
        (D.⋆Assoc (F₁ f ⋆ α₀ y) (β₀ y) (γ₀ y)
          ∙ D.⋆Assoc (F₁ f) (α₀ y) (β₀ y ⋆ γ₀ y))
        ∙ sym (D.⋆Assoc (F₁ f) (α₀ y) (β₀ y ⋆ γ₀ y))
        ∙ α□ f ▹ (β₀ y ⋆ γ₀ y)
        ∙ D.⋆Assoc (α₀ x) (G₁ f) (β₀ y ⋆ γ₀ y)
        ∙ α₀ x ◃ (sym (D.⋆Assoc (G₁ f) (β₀ y) (γ₀ y))
          ∙ β□ f ▹ γ₀ y
          ∙ D.⋆Assoc (β₀ x) (H₁ f) (γ₀ y)
          ∙ β₀ x ◃ γ□ f
          ∙ sym (D.⋆Assoc (β₀ x) (γ₀ x) (K₁ f)))
        ∙ sym (D.⋆Assoc (α₀ x) (β₀ x ⋆ γ₀ x) (K₁ f))
          ≡⟨ reass₂ ⟩
        (D.⋆Assoc (F₁ f ⋆ α₀ y) (β₀ y) (γ₀ y)
          ∙ α□ f ▹ (β₀ y ⋆ γ₀ y))
        ∙ D.⋆Assoc (α₀ x) (G₁ f) (β₀ y ⋆ γ₀ y)
        ∙ α₀ x ◃ (sym (D.⋆Assoc (G₁ f) (β₀ y) (γ₀ y))
          ∙ β□ f ▹ γ₀ y
          ∙ D.⋆Assoc (β₀ x) (H₁ f) (γ₀ y)
          ∙ β₀ x ◃ γ□ f
          ∙ sym (D.⋆Assoc (β₀ x) (γ₀ x) (K₁ f)))
        ∙ sym (D.⋆Assoc (α₀ x) (β₀ x ⋆ γ₀ x) (K₁ f))
          ≡⟨ ∙r (⋆Assoc-nat D (α□ f) refl refl) ⟩
        (α□ f ▹ β₀ y ▹ γ₀ y
          ∙ D.⋆Assoc (α₀ x ⋆ G₁ f) (β₀ y) (γ₀ y))
        ∙ D.⋆Assoc (α₀ x) (G₁ f) (β₀ y ⋆ γ₀ y)
        ∙ α₀ x ◃ (sym (D.⋆Assoc (G₁ f) (β₀ y) (γ₀ y))
          ∙ β□ f ▹ γ₀ y
          ∙ D.⋆Assoc (β₀ x) (H₁ f) (γ₀ y)
          ∙ β₀ x ◃ γ□ f
          ∙ sym (D.⋆Assoc (β₀ x) (γ₀ x) (K₁ f)))
        ∙ sym (D.⋆Assoc (α₀ x) (β₀ x ⋆ γ₀ x) (K₁ f))
          ≡⟨ reass₃ ⟩
        α□ f ▹ β₀ y ▹ γ₀ y
        ∙ (D.⋆Assoc (α₀ x ⋆ G₁ f) (β₀ y) (γ₀ y)
          ∙ D.⋆Assoc (α₀ x) (G₁ f) (β₀ y ⋆ γ₀ y))
        ∙ α₀ x ◃ (sym (D.⋆Assoc (G₁ f) (β₀ y) (γ₀ y))
          ∙ β□ f ▹ γ₀ y
          ∙ D.⋆Assoc (β₀ x) (H₁ f) (γ₀ y)
          ∙ β₀ x ◃ γ□ f
          ∙ sym (D.⋆Assoc (β₀ x) (γ₀ x) (K₁ f)))
        ∙ sym (D.⋆Assoc (α₀ x) (β₀ x ⋆ γ₀ x) (K₁ f))
          ≡⟨ ∙l ∙r (sym (D.pentagon (α₀ x) (G₁ f) (β₀ y) (γ₀ y))) ⟩
        α□ f ▹ β₀ y ▹ γ₀ y
        ∙ (D.⋆Assoc (α₀ x) (G₁ f) (β₀ y) ▹ γ₀ y
          ∙ D.⋆Assoc (α₀ x) (G₁ f ⋆ β₀ y) (γ₀ y)
          ∙ α₀ x ◃ D.⋆Assoc (G₁ f) (β₀ y) (γ₀ y))
        ∙ α₀ x ◃ (sym (D.⋆Assoc (G₁ f) (β₀ y) (γ₀ y))
          ∙ β□ f ▹ γ₀ y
          ∙ D.⋆Assoc (β₀ x) (H₁ f) (γ₀ y)
          ∙ β₀ x ◃ γ□ f
          ∙ sym (D.⋆Assoc (β₀ x) (γ₀ x) (K₁ f)))
        ∙ sym (D.⋆Assoc (α₀ x) (β₀ x ⋆ γ₀ x) (K₁ f))
          ≡⟨ reass₄ ⟩
        α□ f ▹ β₀ y ▹ γ₀ y
        ∙ D.⋆Assoc (α₀ x) (G₁ f) (β₀ y) ▹ γ₀ y
        ∙ (D.⋆Assoc (α₀ x) (G₁ f ⋆ β₀ y) (γ₀ y)
          ∙ α₀ x ◃ (β□ f ▹ γ₀ y))
        ∙ α₀ x ◃ D.⋆Assoc (β₀ x) (H₁ f) (γ₀ y)
        ∙ α₀ x ◃ β₀ x ◃ γ□ f
        ∙ α₀ x ◃ sym (D.⋆Assoc (β₀ x) (γ₀ x) (K₁ f))
        ∙ sym (D.⋆Assoc (α₀ x) (β₀ x ⋆ γ₀ x) (K₁ f))
          ≡⟨ ∙l ∙l ∙r (⋆Assoc-nat D refl (β□ f) refl) ⟩
        α□ f ▹ β₀ y ▹ γ₀ y
        ∙ D.⋆Assoc (α₀ x) (G₁ f) (β₀ y) ▹ γ₀ y
        ∙ ((α₀ x ◃ β□ f) ▹ γ₀ y
          ∙ D.⋆Assoc (α₀ x) (β₀ x ⋆ H₁ f) (γ₀ y))
        ∙ α₀ x ◃ D.⋆Assoc (β₀ x) (H₁ f) (γ₀ y)
        ∙ α₀ x ◃ β₀ x ◃ γ□ f
        ∙ α₀ x ◃ sym (D.⋆Assoc (β₀ x) (γ₀ x) (K₁ f))
        ∙ sym (D.⋆Assoc (α₀ x) (β₀ x ⋆ γ₀ x) (K₁ f))
          ≡⟨ reass₅ ⟩
        α□ f ▹ β₀ y ▹ γ₀ y
        ∙ D.⋆Assoc (α₀ x) (G₁ f) (β₀ y) ▹ γ₀ y
        ∙ (α₀ x ◃ β□ f) ▹ γ₀ y
        ∙ (D.⋆Assoc (α₀ x) (β₀ x ⋆ H₁ f) (γ₀ y)
          ∙ α₀ x ◃ D.⋆Assoc (β₀ x) (H₁ f) (γ₀ y))
        ∙ α₀ x ◃ β₀ x ◃ γ□ f
        ∙ α₀ x ◃ sym (D.⋆Assoc (β₀ x) (γ₀ x) (K₁ f))
        ∙ sym (D.⋆Assoc (α₀ x) (β₀ x ⋆ γ₀ x) (K₁ f))
          ≡⟨ ∙l ∙l ∙l ∙r (sym (shuffleSymL (sym (D.pentagon (α₀ x) (β₀ x) (H₁ f) (γ₀ y))))) ⟩
        α□ f ▹ β₀ y ▹ γ₀ y
        ∙ D.⋆Assoc (α₀ x) (G₁ f) (β₀ y) ▹ γ₀ y
        ∙ (α₀ x ◃ β□ f) ▹ γ₀ y
        ∙ (sym (D.⋆Assoc (α₀ x) (β₀ x) (H₁ f) ▹ γ₀ y)
          ∙ D.⋆Assoc (α₀ x ⋆ β₀ x) (H₁ f) (γ₀ y)
          ∙ D.⋆Assoc (α₀ x) (β₀ x) (H₁ f ⋆ γ₀ y))
        ∙ α₀ x ◃ β₀ x ◃ γ□ f
        ∙ α₀ x ◃ sym (D.⋆Assoc (β₀ x) (γ₀ x) (K₁ f))
        ∙ sym (D.⋆Assoc (α₀ x) (β₀ x ⋆ γ₀ x) (K₁ f))
          ≡⟨ reass₆ ⟩
        α□ f ▹ β₀ y ▹ γ₀ y
        ∙ D.⋆Assoc (α₀ x) (G₁ f) (β₀ y) ▹ γ₀ y
        ∙ (α₀ x ◃ β□ f) ▹ γ₀ y
        ∙ sym (D.⋆Assoc (α₀ x) (β₀ x) (H₁ f) ▹ γ₀ y)
        ∙ D.⋆Assoc (α₀ x ⋆ β₀ x) (H₁ f) (γ₀ y)
        ∙ (D.⋆Assoc (α₀ x) (β₀ x) (H₁ f ⋆ γ₀ y)
          ∙ α₀ x ◃ β₀ x ◃ γ□ f)
        ∙ α₀ x ◃ sym (D.⋆Assoc (β₀ x) (γ₀ x) (K₁ f))
        ∙ sym (D.⋆Assoc (α₀ x) (β₀ x ⋆ γ₀ x) (K₁ f))
          ≡⟨ ∙l ∙l ∙l ∙l ∙l ∙r (⋆Assoc-nat D refl refl (γ□ f)) ⟩
        α□ f ▹ β₀ y ▹ γ₀ y
        ∙ D.⋆Assoc (α₀ x) (G₁ f) (β₀ y) ▹ γ₀ y
        ∙ (α₀ x ◃ β□ f) ▹ γ₀ y
        ∙ sym (D.⋆Assoc (α₀ x) (β₀ x) (H₁ f) ▹ γ₀ y)
        ∙ D.⋆Assoc (α₀ x ⋆ β₀ x) (H₁ f) (γ₀ y)
        ∙ ((α₀ x ⋆ β₀ x) ◃ γ□ f
          ∙ D.⋆Assoc (α₀ x) (β₀ x) (γ₀ x ⋆ K₁ f))
        ∙ α₀ x ◃ sym (D.⋆Assoc (β₀ x) (γ₀ x) (K₁ f))
        ∙ sym (D.⋆Assoc (α₀ x) (β₀ x ⋆ γ₀ x) (K₁ f))
          ≡⟨ ∙l ∙l ∙l ∙l ∙l ∙r ∙l (sym (shuffleSymL (D.pentagon (α₀ x) (β₀ x) (γ₀ x) (K₁ f)))) ⟩
        α□ f ▹ β₀ y ▹ γ₀ y
        ∙ D.⋆Assoc (α₀ x) (G₁ f) (β₀ y) ▹ γ₀ y
        ∙ (α₀ x ◃ β□ f) ▹ γ₀ y
        ∙ sym (D.⋆Assoc (α₀ x) (β₀ x) (H₁ f) ▹ γ₀ y)
        ∙ D.⋆Assoc (α₀ x ⋆ β₀ x) (H₁ f) (γ₀ y)
        ∙ ((α₀ x ⋆ β₀ x) ◃ γ□ f
          ∙ (sym (D.⋆Assoc (α₀ x ⋆ β₀ x) (γ₀ x) (K₁ f))
            ∙ D.⋆Assoc (α₀ x) (β₀ x) (γ₀ x) ▹ K₁ f
            ∙ D.⋆Assoc (α₀ x) (β₀ x ⋆ γ₀ x) (K₁ f)
            ∙ α₀ x ◃ D.⋆Assoc (β₀ x) (γ₀ x) (K₁ f)))
        ∙ α₀ x ◃ sym (D.⋆Assoc (β₀ x) (γ₀ x) (K₁ f))
        ∙ sym (D.⋆Assoc (α₀ x) (β₀ x ⋆ γ₀ x) (K₁ f))
          ≡⟨ reass₇ ⟩
        α□ f ▹ β₀ y ▹ γ₀ y
        ∙ D.⋆Assoc (α₀ x) (G₁ f) (β₀ y) ▹ γ₀ y
        ∙ (α₀ x ◃ β□ f) ▹ γ₀ y
        ∙ sym (D.⋆Assoc (α₀ x) (β₀ x) (H₁ f) ▹ γ₀ y)
        ∙ D.⋆Assoc (α₀ x ⋆ β₀ x) (H₁ f) (γ₀ y)
        ∙ (α₀ x ⋆ β₀ x) ◃ γ□ f
        ∙ sym (D.⋆Assoc (α₀ x ⋆ β₀ x) (γ₀ x) (K₁ f))
        ∙ D.⋆Assoc (α₀ x) (β₀ x) (γ₀ x) ▹ K₁ f
          ≡⟨ reass₈ ⟩
        D.⋆Assoc (F₁ f) (α₀ y) (β₀ y) ▹ γ₀ y
        ∙ D.⋆Assoc (F₁ f) (α₀ y ⋆ β₀ y) (γ₀ y)
        ∙ ((sym (D.⋆Assoc (F₁ f) (α₀ y ⋆ β₀ y) (γ₀ y))
            ∙ (sym (D.⋆Assoc (F₁ f) (α₀ y) (β₀ y))
              ∙ α□ f ▹ β₀ y
              ∙ D.⋆Assoc (α₀ x) (G₁ f) (β₀ y)
              ∙ α₀ x ◃ β□ f
              ∙ sym (D.⋆Assoc (α₀ x) (β₀ x) (H₁ f))) ▹ γ₀ y
            ∙ D.⋆Assoc (α₀ x ⋆ β₀ x) (H₁ f) (γ₀ y)
            ∙ (α₀ x ⋆ β₀ x) ◃ γ□ f
            ∙ sym (D.⋆Assoc (α₀ x ⋆ β₀ x) (γ₀ x) (K₁ f)))
          ∙ D.⋆Assoc (α₀ x) (β₀ x) (γ₀ x) ▹ K₁ f)
          ∎
        where
        reass₁ = reassoc
          (↑ (D.⋆Assoc (F₁ f) (α₀ y) (β₀ y)) ▹′ γ₀ y
            ∙′ ↑ (D.⋆Assoc (F₁ f) (α₀ y ⋆ β₀ y) (γ₀ y))
            ∙′ (F₁ f ◃′ ↑ (D.⋆Assoc (α₀ y) (β₀ y) (γ₀ y))
              ∙′ (↑ (sym (D.⋆Assoc (F₁ f) (α₀ y) (β₀ y ⋆ γ₀ y)))
                ∙′ ↑ (α□ f) ▹′ (β₀ y ⋆ γ₀ y)
                ∙′ ↑ (D.⋆Assoc (α₀ x) (G₁ f) (β₀ y ⋆ γ₀ y))
                ∙′ α₀ x ◃′ (↑ (sym (D.⋆Assoc (G₁ f) (β₀ y) (γ₀ y)))
                  ∙′ ↑ (β□ f) ▹′ γ₀ y
                  ∙′ ↑ (D.⋆Assoc (β₀ x) (H₁ f) (γ₀ y))
                  ∙′ β₀ x ◃′ ↑ (γ□ f)
                  ∙′ ↑ (sym (D.⋆Assoc (β₀ x) (γ₀ x) (K₁ f))))
                ∙′ ↑ (sym (D.⋆Assoc (α₀ x) (β₀ x ⋆ γ₀ x) (K₁ f))))))
          ((↑ (D.⋆Assoc (F₁ f) (α₀ y) (β₀ y)) ▹′ γ₀ y
              ∙′ ↑ (D.⋆Assoc (F₁ f) (α₀ y ⋆ β₀ y) (γ₀ y))
              ∙′ F₁ f ◃′ ↑ (D.⋆Assoc (α₀ y) (β₀ y) (γ₀ y)))
            ∙′ ↑ (sym (D.⋆Assoc (F₁ f) (α₀ y) (β₀ y ⋆ γ₀ y)))
            ∙′ ↑ (α□ f) ▹′ (β₀ y ⋆ γ₀ y)
            ∙′ ↑ (D.⋆Assoc (α₀ x) (G₁ f) (β₀ y ⋆ γ₀ y))
            ∙′ α₀ x ◃′ (↑ (sym (D.⋆Assoc (G₁ f) (β₀ y) (γ₀ y)))
              ∙′ ↑ (β□ f) ▹′ γ₀ y
              ∙′ ↑ (D.⋆Assoc (β₀ x) (H₁ f) (γ₀ y))
              ∙′ β₀ x ◃′ ↑ (γ□ f)
              ∙′ ↑ (sym (D.⋆Assoc (β₀ x) (γ₀ x) (K₁ f))))
            ∙′ ↑ (sym (D.⋆Assoc (α₀ x) (β₀ x ⋆ γ₀ x) (K₁ f))))
          refl
        reass₂ = reassoc
          ((↑ (D.⋆Assoc (F₁ f ⋆ α₀ y) (β₀ y) (γ₀ y))
              ∙′ ↑ (D.⋆Assoc (F₁ f) (α₀ y) (β₀ y ⋆ γ₀ y)))
            ∙′ ↑ (sym (D.⋆Assoc (F₁ f) (α₀ y) (β₀ y ⋆ γ₀ y)))
            ∙′ ↑ (α□ f) ▹′ (β₀ y ⋆ γ₀ y)
            ∙′ ↑ (D.⋆Assoc (α₀ x) (G₁ f) (β₀ y ⋆ γ₀ y))
            ∙′ α₀ x ◃′ (↑ (sym (D.⋆Assoc (G₁ f) (β₀ y) (γ₀ y)))
              ∙′ ↑ (β□ f) ▹′ γ₀ y
              ∙′ ↑ (D.⋆Assoc (β₀ x) (H₁ f) (γ₀ y))
              ∙′ β₀ x ◃′ ↑ (γ□ f)
              ∙′ ↑ (sym (D.⋆Assoc (β₀ x) (γ₀ x) (K₁ f))))
            ∙′ ↑ (sym (D.⋆Assoc (α₀ x) (β₀ x ⋆ γ₀ x) (K₁ f))))
          ((↑ (D.⋆Assoc (F₁ f ⋆ α₀ y) (β₀ y) (γ₀ y))
              ∙′ ↑ (α□ f) ▹′ (β₀ y ⋆ γ₀ y))
            ∙′ ↑ (D.⋆Assoc (α₀ x) (G₁ f) (β₀ y ⋆ γ₀ y))
            ∙′ α₀ x ◃′ (↑ (sym (D.⋆Assoc (G₁ f) (β₀ y) (γ₀ y)))
              ∙′ ↑ (β□ f) ▹′ γ₀ y
              ∙′ ↑ (D.⋆Assoc (β₀ x) (H₁ f) (γ₀ y))
              ∙′ β₀ x ◃′ ↑ (γ□ f)
              ∙′ ↑ (sym (D.⋆Assoc (β₀ x) (γ₀ x) (K₁ f))))
            ∙′ ↑ (sym (D.⋆Assoc (α₀ x) (β₀ x ⋆ γ₀ x) (K₁ f))))
          (∙l (shuffleSymL {q = sym (D.⋆Assoc (F₁ f) (α₀ y) (β₀ y ⋆ γ₀ y))} refl))
        reass₃ = reassoc
          ((↑ (α□ f) ▹′ β₀ y ▹′ γ₀ y
              ∙′ ↑ (D.⋆Assoc (α₀ x ⋆ G₁ f) (β₀ y) (γ₀ y)))
            ∙′ ↑ (D.⋆Assoc (α₀ x) (G₁ f) (β₀ y ⋆ γ₀ y))
            ∙′ α₀ x ◃′ (↑ (sym (D.⋆Assoc (G₁ f) (β₀ y) (γ₀ y)))
              ∙′ ↑ (β□ f) ▹′ γ₀ y
              ∙′ ↑ (D.⋆Assoc (β₀ x) (H₁ f) (γ₀ y))
              ∙′ β₀ x ◃′ ↑ (γ□ f)
              ∙′ ↑ (sym (D.⋆Assoc (β₀ x) (γ₀ x) (K₁ f))))
            ∙′ ↑ (sym (D.⋆Assoc (α₀ x) (β₀ x ⋆ γ₀ x) (K₁ f))))
          (↑ (α□ f) ▹′ β₀ y ▹′ γ₀ y
            ∙′ (↑ (D.⋆Assoc (α₀ x ⋆ G₁ f) (β₀ y) (γ₀ y))
              ∙′ ↑ (D.⋆Assoc (α₀ x) (G₁ f) (β₀ y ⋆ γ₀ y)))
            ∙′ α₀ x ◃′ (↑ (sym (D.⋆Assoc (G₁ f) (β₀ y) (γ₀ y)))
              ∙′ ↑ (β□ f) ▹′ γ₀ y
              ∙′ ↑ (D.⋆Assoc (β₀ x) (H₁ f) (γ₀ y))
              ∙′ β₀ x ◃′ ↑ (γ□ f)
              ∙′ ↑ (sym (D.⋆Assoc (β₀ x) (γ₀ x) (K₁ f))))
            ∙′ ↑ (sym (D.⋆Assoc (α₀ x) (β₀ x ⋆ γ₀ x) (K₁ f))))
          refl
        reass₄ = reassoc
          (↑ (α□ f) ▹′ β₀ y ▹′ γ₀ y
            ∙′ (↑ (D.⋆Assoc (α₀ x) (G₁ f) (β₀ y)) ▹′ γ₀ y
              ∙′ ↑ (D.⋆Assoc (α₀ x) (G₁ f ⋆ β₀ y) (γ₀ y))
              ∙′ α₀ x ◃′ ↑ (D.⋆Assoc (G₁ f) (β₀ y) (γ₀ y)))
            ∙′ α₀ x ◃′ (↑ (sym (D.⋆Assoc (G₁ f) (β₀ y) (γ₀ y)))
              ∙′ ↑ (β□ f) ▹′ γ₀ y
              ∙′ ↑ (D.⋆Assoc (β₀ x) (H₁ f) (γ₀ y))
              ∙′ β₀ x ◃′ ↑ (γ□ f)
              ∙′ ↑ (sym (D.⋆Assoc (β₀ x) (γ₀ x) (K₁ f))))
            ∙′ ↑ (sym (D.⋆Assoc (α₀ x) (β₀ x ⋆ γ₀ x) (K₁ f))))
          (↑ (α□ f) ▹′ β₀ y ▹′ γ₀ y
            ∙′ ↑ (D.⋆Assoc (α₀ x) (G₁ f) (β₀ y)) ▹′ γ₀ y
            ∙′ (↑ (D.⋆Assoc (α₀ x) (G₁ f ⋆ β₀ y) (γ₀ y))
              ∙′ α₀ x ◃′ (↑ (β□ f) ▹′ γ₀ y))
            ∙′ α₀ x ◃′ ↑ (D.⋆Assoc (β₀ x) (H₁ f) (γ₀ y))
            ∙′ α₀ x ◃′ β₀ x ◃′ ↑ (γ□ f)
            ∙′ α₀ x ◃′ ↑ (sym (D.⋆Assoc (β₀ x) (γ₀ x) (K₁ f)))
            ∙′ ↑ (sym (D.⋆Assoc (α₀ x) (β₀ x ⋆ γ₀ x) (K₁ f))))
          (∙l ∙l ∙l (shuffleSymL {q = sym (α₀ x ◃ D.⋆Assoc (G₁ f) (β₀ y) (γ₀ y))} refl))
        reass₅ = reassoc
          (↑ (α□ f) ▹′ β₀ y ▹′ γ₀ y
            ∙′ ↑ (D.⋆Assoc (α₀ x) (G₁ f) (β₀ y)) ▹′ γ₀ y
            ∙′ ((α₀ x ◃′ ↑ (β□ f)) ▹′ γ₀ y
              ∙′ ↑ (D.⋆Assoc (α₀ x) (β₀ x ⋆ H₁ f) (γ₀ y)))
            ∙′ α₀ x ◃′ ↑ (D.⋆Assoc (β₀ x) (H₁ f) (γ₀ y))
            ∙′ α₀ x ◃′ β₀ x ◃′ ↑ (γ□ f)
            ∙′ α₀ x ◃′ ↑ (sym (D.⋆Assoc (β₀ x) (γ₀ x) (K₁ f)))
            ∙′ ↑ (sym (D.⋆Assoc (α₀ x) (β₀ x ⋆ γ₀ x) (K₁ f))))
          (↑ (α□ f) ▹′ β₀ y ▹′ γ₀ y
            ∙′ ↑ (D.⋆Assoc (α₀ x) (G₁ f) (β₀ y)) ▹′ γ₀ y
            ∙′ (α₀ x ◃′ ↑ (β□ f)) ▹′ γ₀ y
            ∙′ (↑ (D.⋆Assoc (α₀ x) (β₀ x ⋆ H₁ f) (γ₀ y))
              ∙′ α₀ x ◃′ ↑ (D.⋆Assoc (β₀ x) (H₁ f) (γ₀ y)))
            ∙′ α₀ x ◃′ β₀ x ◃′ ↑ (γ□ f)
            ∙′ α₀ x ◃′ ↑ (sym (D.⋆Assoc (β₀ x) (γ₀ x) (K₁ f)))
            ∙′ ↑ (sym (D.⋆Assoc (α₀ x) (β₀ x ⋆ γ₀ x) (K₁ f))))
          refl
        reass₆ = reassoc
          (↑ (α□ f) ▹′ β₀ y ▹′ γ₀ y
            ∙′ ↑ (D.⋆Assoc (α₀ x) (G₁ f) (β₀ y)) ▹′ γ₀ y
            ∙′ (α₀ x ◃′ ↑ (β□ f)) ▹′ γ₀ y
            ∙′ (↑ (sym (D.⋆Assoc (α₀ x) (β₀ x) (H₁ f) ▹ γ₀ y))
              ∙′ ↑ (D.⋆Assoc (α₀ x ⋆ β₀ x) (H₁ f) (γ₀ y))
              ∙′ ↑ (D.⋆Assoc (α₀ x) (β₀ x) (H₁ f ⋆ γ₀ y)))
            ∙′ α₀ x ◃′ β₀ x ◃′ ↑ (γ□ f)
            ∙′ α₀ x ◃′ ↑ (sym (D.⋆Assoc (β₀ x) (γ₀ x) (K₁ f)))
            ∙′ ↑ (sym (D.⋆Assoc (α₀ x) (β₀ x ⋆ γ₀ x) (K₁ f))))
          (↑ (α□ f) ▹′ β₀ y ▹′ γ₀ y
            ∙′ ↑ (D.⋆Assoc (α₀ x) (G₁ f) (β₀ y)) ▹′ γ₀ y
            ∙′ (α₀ x ◃′ ↑ (β□ f)) ▹′ γ₀ y
            ∙′ ↑ (sym (D.⋆Assoc (α₀ x) (β₀ x) (H₁ f) ▹ γ₀ y))
            ∙′ ↑ (D.⋆Assoc (α₀ x ⋆ β₀ x) (H₁ f) (γ₀ y))
            ∙′ (↑ (D.⋆Assoc (α₀ x) (β₀ x) (H₁ f ⋆ γ₀ y))
              ∙′ α₀ x ◃′ β₀ x ◃′ ↑ (γ□ f))
            ∙′ α₀ x ◃′ ↑ (sym (D.⋆Assoc (β₀ x) (γ₀ x) (K₁ f)))
            ∙′ ↑ (sym (D.⋆Assoc (α₀ x) (β₀ x ⋆ γ₀ x) (K₁ f))))
          refl
        reass₇ = reassoc
          (↑ (α□ f) ▹′ β₀ y ▹′ γ₀ y
            ∙′ ↑ (D.⋆Assoc (α₀ x) (G₁ f) (β₀ y)) ▹′ γ₀ y
            ∙′ (α₀ x ◃′ ↑ (β□ f)) ▹′ γ₀ y
            ∙′ ↑ (sym (D.⋆Assoc (α₀ x) (β₀ x) (H₁ f) ▹ γ₀ y))
            ∙′ ↑ (D.⋆Assoc (α₀ x ⋆ β₀ x) (H₁ f) (γ₀ y))
            ∙′ ((α₀ x ⋆ β₀ x) ◃′ ↑ (γ□ f)
              ∙′ (↑ (sym (D.⋆Assoc (α₀ x ⋆ β₀ x) (γ₀ x) (K₁ f)))
                ∙′ ↑ (D.⋆Assoc (α₀ x) (β₀ x) (γ₀ x)) ▹′ K₁ f
                ∙′ ↑ (D.⋆Assoc (α₀ x) (β₀ x ⋆ γ₀ x) (K₁ f))
                ∙′ α₀ x ◃′ ↑ (D.⋆Assoc (β₀ x) (γ₀ x) (K₁ f))))
            ∙′ α₀ x ◃′ ↑ (sym (D.⋆Assoc (β₀ x) (γ₀ x) (K₁ f)))
            ∙′ ↑ (sym (D.⋆Assoc (α₀ x) (β₀ x ⋆ γ₀ x) (K₁ f))))
          (↑ (α□ f) ▹′ β₀ y ▹′ γ₀ y
            ∙′ ↑ (D.⋆Assoc (α₀ x) (G₁ f) (β₀ y)) ▹′ γ₀ y
            ∙′ (α₀ x ◃′ ↑ (β□ f)) ▹′ γ₀ y
            ∙′ ↑ (sym (D.⋆Assoc (α₀ x) (β₀ x) (H₁ f) ▹ γ₀ y))
            ∙′ ↑ (D.⋆Assoc (α₀ x ⋆ β₀ x) (H₁ f) (γ₀ y))
            ∙′ (α₀ x ⋆ β₀ x) ◃′ ↑ (γ□ f)
            ∙′ ↑ (sym (D.⋆Assoc (α₀ x ⋆ β₀ x) (γ₀ x) (K₁ f)))
            ∙′ ↑ (D.⋆Assoc (α₀ x) (β₀ x) (γ₀ x)) ▹′ K₁ f)
          (∙l ∙l ∙l ∙l ∙l ∙l ∙l ∙l
            (∙l (shuffleSymL {q = sym (α₀ x ◃ D.⋆Assoc (β₀ x) (γ₀ x) (K₁ f))} refl)
            ∙ shuffleSymL {q = sym (D.⋆Assoc (α₀ x) (β₀ x ⋆ γ₀ x) (K₁ f))} refl))
        reass₈ = reassoc
          (↑ (α□ f) ▹′ β₀ y ▹′ γ₀ y
            ∙′ ↑ (D.⋆Assoc (α₀ x) (G₁ f) (β₀ y)) ▹′ γ₀ y
            ∙′ (α₀ x ◃′ ↑ (β□ f)) ▹′ γ₀ y
            ∙′ ↑ (sym (D.⋆Assoc (α₀ x) (β₀ x) (H₁ f) ▹ γ₀ y))
            ∙′ ↑ (D.⋆Assoc (α₀ x ⋆ β₀ x) (H₁ f) (γ₀ y))
            ∙′ (α₀ x ⋆ β₀ x) ◃′ ↑ (γ□ f)
            ∙′ ↑ (sym (D.⋆Assoc (α₀ x ⋆ β₀ x) (γ₀ x) (K₁ f)))
            ∙′ ↑ (D.⋆Assoc (α₀ x) (β₀ x) (γ₀ x)) ▹′ K₁ f)
          (↑ (D.⋆Assoc (F₁ f) (α₀ y) (β₀ y)) ▹′ γ₀ y
            ∙′ ↑ (D.⋆Assoc (F₁ f) (α₀ y ⋆ β₀ y) (γ₀ y))
            ∙′ ((↑ (sym (D.⋆Assoc (F₁ f) (α₀ y ⋆ β₀ y) (γ₀ y)))
                ∙′ (↑ (sym (D.⋆Assoc (F₁ f) (α₀ y) (β₀ y)))
                  ∙′ ↑ (α□ f) ▹′ β₀ y
                  ∙′ ↑ (D.⋆Assoc (α₀ x) (G₁ f) (β₀ y))
                  ∙′ α₀ x ◃′ ↑ (β□ f)
                  ∙′ ↑ (sym (D.⋆Assoc (α₀ x) (β₀ x) (H₁ f)))) ▹′ γ₀ y
                ∙′ ↑ (D.⋆Assoc (α₀ x ⋆ β₀ x) (H₁ f) (γ₀ y))
                ∙′ (α₀ x ⋆ β₀ x) ◃′ ↑ (γ□ f)
                ∙′ ↑ (sym (D.⋆Assoc (α₀ x ⋆ β₀ x) (γ₀ x) (K₁ f))))
              ∙′ ↑ (D.⋆Assoc (α₀ x) (β₀ x) (γ₀ x)) ▹′ K₁ f))
          (sym (shuffleSymL {q = sym (D.⋆Assoc (F₁ f) (α₀ y) (β₀ y) ▹ γ₀ y)} refl)
          ∙ ∙l (sym (shuffleSymL {q = sym (D.⋆Assoc (F₁ f) (α₀ y ⋆ β₀ y) (γ₀ y))} refl)))
