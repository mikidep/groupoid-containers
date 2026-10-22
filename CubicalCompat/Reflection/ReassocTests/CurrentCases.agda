-- Regression cases copied from every existing Prelude.Reassoc call.
-- The paths and residual witnesses retain their original structure, with
-- quotation constructors replaced by ordinary path operations. Only the
-- surrounding data is abstracted: coherence fields are not used here.
module CubicalCompat.Reflection.ReassocTests.CurrentCases where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws
open import Cubical.WildCat.Base hiding (_[_,_])
open import Cubical.WildCat.Functor
open import Cubical.LU2C.Base
open import Cubical.WildCat.AsLU2C.Instances
import Cubical.WildCat.AsLU2C.Functor.Notation as NotF
open import Prelude.ExtraGpdLaws
open import CubicalCompat.Reflection.Reassoc

module Functors {ℓC ℓC′ ℓD ℓD′ : Level}
  (C : WildCat ℓC ℓC′) (D : LU2C ℓD ℓD′)
  {F G H K : WildFunctor C (LU2C.str D)}
  (α : WildNatTrans _ _ F G) (β : WildNatTrans _ _ G H) (γ : WildNatTrans _ _ H K)
  {x y : WildCat.ob C} (f : WildCat.Hom[_,_] C x y) where
  private module D = LU2C D
  open NotWC C
  open Not2C D
  open NotF F using (F₁)
  open NotF G using () renaming (F₁ to G₁)
  open NotF H using () renaming (F₁ to H₁)
  open NotF K using () renaming (F₁ to K₁)
  open WildNatTrans α using () renaming (N-ob to α₀; N-hom to α□)
  open WildNatTrans β using () renaming (N-ob to β₀; N-hom to β□)
  open WildNatTrans γ using () renaming (N-ob to γ₀; N-hom to γ□)
  -- Cubical/LU2C/Instances/WildFunctor.agda:95
  idl-1 :
    (((sym (D.⋆Assoc (F₁ f) D.id (α₀ y)))
    ∙ (D.⋆IdR (F₁ f)) ▹ α₀ y) ∙ (α□ f))
    ≡ ((sym (D.⋆Assoc (F₁ f) D.id (α₀ y)))
    ∙ ((D.⋆IdR (F₁ f)) ∙ (sym (D.⋆IdL (F₁ f)))) ▹ α₀ y
    ∙ (D.⋆IdL (F₁ f)) ▹ α₀ y ∙ (α□ f))
  idl-1 = reassoc-with (∙l ∙l (sym (shuffleSymL {q = D.⋆IdL (F₁ f) ▹ α₀ y} refl)))

  -- Cubical/LU2C/Instances/WildFunctor.agda:102
  idl-2 :
    ((sym (D.⋆Assoc (F₁ f) D.id (α₀ y)))
    ∙ ((D.⋆IdR (F₁ f)) ∙ (sym (D.⋆IdL (F₁ f)))) ▹ α₀ y
    ∙ (D.⋆Assoc D.id (F₁ f) (α₀ y))
    ∙ D.id ◃ (α□ f)
    ∙ ((sym (D.⋆Assoc D.id (α₀ x) (G₁ f)))
      ∙ (D.⋆IdL (α₀ x)) ▹ G₁ f))
    ≡ (((sym (D.⋆Assoc (F₁ f) D.id (α₀ y)))
    ∙ ((D.⋆IdR (F₁ f)) ∙ (sym (D.⋆IdL (F₁ f)))) ▹ α₀ y
    ∙ (D.⋆Assoc D.id (F₁ f) (α₀ y))
    ∙ D.id ◃ (α□ f)
    ∙ (sym (D.⋆Assoc D.id (α₀ x) (G₁ f))))
    ∙ (D.⋆IdL (α₀ x)) ▹ G₁ f)
  idl-2 = reassoc!

  -- Cubical/LU2C/Instances/WildFunctor.agda:162
  idr-1 :
    ((sym (D.⋆Assoc (F₁ f) (α₀ y) D.id))
    ∙ (α□ f) ▹ D.id
    ∙ (D.⋆Assoc (α₀ x) (G₁ f) D.id)
    ∙ α₀ x ◃ (D.⋆IdR (G₁ f)))
    ≡ ((sym (D.⋆Assoc (F₁ f) (α₀ y) D.id))
    ∙ (α□ f) ▹ D.id
    ∙ (D.⋆Assoc (α₀ x) (G₁ f) D.id)
    ∙ α₀ x ◃ ((D.⋆IdR (G₁ f)) ∙ (sym (D.⋆IdL (G₁ f))))
    ∙ α₀ x ◃ (D.⋆IdL (G₁ f)))
  idr-1 = reassoc-with (∙l ∙l ∙l ∙l (sym (shuffleSymL {q = α₀ x ◃ D.⋆IdL (G₁ f)} refl)))

  -- Cubical/LU2C/Instances/WildFunctor.agda:173
  idr-2 :
    ((sym (D.⋆Assoc (F₁ f) (α₀ y) D.id))
    ∙ (α□ f) ▹ D.id
    ∙ (D.⋆Assoc (α₀ x) (G₁ f) D.id)
    ∙ α₀ x ◃ ((D.⋆IdR (G₁ f)) ∙ (sym (D.⋆IdL (G₁ f))))
    ∙ ((sym (D.⋆Assoc (α₀ x) D.id (G₁ f)))
      ∙ (D.⋆IdR (α₀ x)) ▹ G₁ f))
    ≡ (((sym (D.⋆Assoc (F₁ f) (α₀ y) D.id))
    ∙ (α□ f) ▹ D.id
    ∙ (D.⋆Assoc (α₀ x) (G₁ f) D.id)
    ∙ α₀ x ◃ ((D.⋆IdR (G₁ f)) ∙ (sym (D.⋆IdL (G₁ f))))
    ∙ (sym (D.⋆Assoc (α₀ x) D.id (G₁ f))))
    ∙ (D.⋆IdR (α₀ x)) ▹ G₁ f)
  idr-2 = reassoc!

  -- Cubical/LU2C/Instances/WildFunctor.agda:377
  assoc-1 :
    ((D.⋆Assoc (F₁ f) (α₀ y) (β₀ y)) ▹ γ₀ y
    ∙ (D.⋆Assoc (F₁ f) (α₀ y ⋆ β₀ y) (γ₀ y))
    ∙ (F₁ f ◃ (D.⋆Assoc (α₀ y) (β₀ y) (γ₀ y))
      ∙ ((sym (D.⋆Assoc (F₁ f) (α₀ y) (β₀ y ⋆ γ₀ y)))
        ∙ (α□ f) ▹ (β₀ y ⋆ γ₀ y)
        ∙ (D.⋆Assoc (α₀ x) (G₁ f) (β₀ y ⋆ γ₀ y))
        ∙ α₀ x ◃ ((sym (D.⋆Assoc (G₁ f) (β₀ y) (γ₀ y)))
          ∙ (β□ f) ▹ γ₀ y
          ∙ (D.⋆Assoc (β₀ x) (H₁ f) (γ₀ y))
          ∙ β₀ x ◃ (γ□ f)
          ∙ (sym (D.⋆Assoc (β₀ x) (γ₀ x) (K₁ f))))
        ∙ (sym (D.⋆Assoc (α₀ x) (β₀ x ⋆ γ₀ x) (K₁ f))))))
    ≡ (((D.⋆Assoc (F₁ f) (α₀ y) (β₀ y)) ▹ γ₀ y
      ∙ (D.⋆Assoc (F₁ f) (α₀ y ⋆ β₀ y) (γ₀ y))
      ∙ F₁ f ◃ (D.⋆Assoc (α₀ y) (β₀ y) (γ₀ y)))
    ∙ (sym (D.⋆Assoc (F₁ f) (α₀ y) (β₀ y ⋆ γ₀ y)))
    ∙ (α□ f) ▹ (β₀ y ⋆ γ₀ y)
    ∙ (D.⋆Assoc (α₀ x) (G₁ f) (β₀ y ⋆ γ₀ y))
    ∙ α₀ x ◃ ((sym (D.⋆Assoc (G₁ f) (β₀ y) (γ₀ y)))
      ∙ (β□ f) ▹ γ₀ y
      ∙ (D.⋆Assoc (β₀ x) (H₁ f) (γ₀ y))
      ∙ β₀ x ◃ (γ□ f)
      ∙ (sym (D.⋆Assoc (β₀ x) (γ₀ x) (K₁ f))))
    ∙ (sym (D.⋆Assoc (α₀ x) (β₀ x ⋆ γ₀ x) (K₁ f))))
  assoc-1 = reassoc!

  -- Cubical/LU2C/Instances/WildFunctor.agda:403
  assoc-2 :
    (((D.⋆Assoc (F₁ f ⋆ α₀ y) (β₀ y) (γ₀ y))
      ∙ (D.⋆Assoc (F₁ f) (α₀ y) (β₀ y ⋆ γ₀ y)))
    ∙ (sym (D.⋆Assoc (F₁ f) (α₀ y) (β₀ y ⋆ γ₀ y)))
    ∙ (α□ f) ▹ (β₀ y ⋆ γ₀ y)
    ∙ (D.⋆Assoc (α₀ x) (G₁ f) (β₀ y ⋆ γ₀ y))
    ∙ α₀ x ◃ ((sym (D.⋆Assoc (G₁ f) (β₀ y) (γ₀ y)))
      ∙ (β□ f) ▹ γ₀ y
      ∙ (D.⋆Assoc (β₀ x) (H₁ f) (γ₀ y))
      ∙ β₀ x ◃ (γ□ f)
      ∙ (sym (D.⋆Assoc (β₀ x) (γ₀ x) (K₁ f))))
    ∙ (sym (D.⋆Assoc (α₀ x) (β₀ x ⋆ γ₀ x) (K₁ f))))
    ≡ (((D.⋆Assoc (F₁ f ⋆ α₀ y) (β₀ y) (γ₀ y))
      ∙ (α□ f) ▹ (β₀ y ⋆ γ₀ y))
    ∙ (D.⋆Assoc (α₀ x) (G₁ f) (β₀ y ⋆ γ₀ y))
    ∙ α₀ x ◃ ((sym (D.⋆Assoc (G₁ f) (β₀ y) (γ₀ y)))
      ∙ (β□ f) ▹ γ₀ y
      ∙ (D.⋆Assoc (β₀ x) (H₁ f) (γ₀ y))
      ∙ β₀ x ◃ (γ□ f)
      ∙ (sym (D.⋆Assoc (β₀ x) (γ₀ x) (K₁ f))))
    ∙ (sym (D.⋆Assoc (α₀ x) (β₀ x ⋆ γ₀ x) (K₁ f))))
  assoc-2 = reassoc-with (∙l (shuffleSymL {q = sym (D.⋆Assoc (F₁ f) (α₀ y) (β₀ y ⋆ γ₀ y))} refl))

  -- Cubical/LU2C/Instances/WildFunctor.agda:425
  assoc-3 :
    (((α□ f) ▹ β₀ y ▹ γ₀ y
      ∙ (D.⋆Assoc (α₀ x ⋆ G₁ f) (β₀ y) (γ₀ y)))
    ∙ (D.⋆Assoc (α₀ x) (G₁ f) (β₀ y ⋆ γ₀ y))
    ∙ α₀ x ◃ ((sym (D.⋆Assoc (G₁ f) (β₀ y) (γ₀ y)))
      ∙ (β□ f) ▹ γ₀ y
      ∙ (D.⋆Assoc (β₀ x) (H₁ f) (γ₀ y))
      ∙ β₀ x ◃ (γ□ f)
      ∙ (sym (D.⋆Assoc (β₀ x) (γ₀ x) (K₁ f))))
    ∙ (sym (D.⋆Assoc (α₀ x) (β₀ x ⋆ γ₀ x) (K₁ f))))
    ≡ ((α□ f) ▹ β₀ y ▹ γ₀ y
    ∙ ((D.⋆Assoc (α₀ x ⋆ G₁ f) (β₀ y) (γ₀ y))
      ∙ (D.⋆Assoc (α₀ x) (G₁ f) (β₀ y ⋆ γ₀ y)))
    ∙ α₀ x ◃ ((sym (D.⋆Assoc (G₁ f) (β₀ y) (γ₀ y)))
      ∙ (β□ f) ▹ γ₀ y
      ∙ (D.⋆Assoc (β₀ x) (H₁ f) (γ₀ y))
      ∙ β₀ x ◃ (γ□ f)
      ∙ (sym (D.⋆Assoc (β₀ x) (γ₀ x) (K₁ f))))
    ∙ (sym (D.⋆Assoc (α₀ x) (β₀ x ⋆ γ₀ x) (K₁ f))))
  assoc-3 = reassoc!

  -- Cubical/LU2C/Instances/WildFunctor.agda:445
  assoc-4 :
    ((α□ f) ▹ β₀ y ▹ γ₀ y
    ∙ ((D.⋆Assoc (α₀ x) (G₁ f) (β₀ y)) ▹ γ₀ y
      ∙ (D.⋆Assoc (α₀ x) (G₁ f ⋆ β₀ y) (γ₀ y))
      ∙ α₀ x ◃ (D.⋆Assoc (G₁ f) (β₀ y) (γ₀ y)))
    ∙ α₀ x ◃ ((sym (D.⋆Assoc (G₁ f) (β₀ y) (γ₀ y)))
      ∙ (β□ f) ▹ γ₀ y
      ∙ (D.⋆Assoc (β₀ x) (H₁ f) (γ₀ y))
      ∙ β₀ x ◃ (γ□ f)
      ∙ (sym (D.⋆Assoc (β₀ x) (γ₀ x) (K₁ f))))
    ∙ (sym (D.⋆Assoc (α₀ x) (β₀ x ⋆ γ₀ x) (K₁ f))))
    ≡ ((α□ f) ▹ β₀ y ▹ γ₀ y
    ∙ (D.⋆Assoc (α₀ x) (G₁ f) (β₀ y)) ▹ γ₀ y
    ∙ ((D.⋆Assoc (α₀ x) (G₁ f ⋆ β₀ y) (γ₀ y))
      ∙ α₀ x ◃ ((β□ f) ▹ γ₀ y))
    ∙ α₀ x ◃ (D.⋆Assoc (β₀ x) (H₁ f) (γ₀ y))
    ∙ α₀ x ◃ β₀ x ◃ (γ□ f)
    ∙ α₀ x ◃ (sym (D.⋆Assoc (β₀ x) (γ₀ x) (K₁ f)))
    ∙ (sym (D.⋆Assoc (α₀ x) (β₀ x ⋆ γ₀ x) (K₁ f))))
  assoc-4 = reassoc-with (∙l ∙l ∙l (shuffleSymL {q = sym (α₀ x ◃ D.⋆Assoc (G₁ f) (β₀ y) (γ₀ y))} refl))

  -- Cubical/LU2C/Instances/WildFunctor.agda:465
  assoc-5 :
    ((α□ f) ▹ β₀ y ▹ γ₀ y
    ∙ (D.⋆Assoc (α₀ x) (G₁ f) (β₀ y)) ▹ γ₀ y
    ∙ ((α₀ x ◃ (β□ f)) ▹ γ₀ y
      ∙ (D.⋆Assoc (α₀ x) (β₀ x ⋆ H₁ f) (γ₀ y)))
    ∙ α₀ x ◃ (D.⋆Assoc (β₀ x) (H₁ f) (γ₀ y))
    ∙ α₀ x ◃ β₀ x ◃ (γ□ f)
    ∙ α₀ x ◃ (sym (D.⋆Assoc (β₀ x) (γ₀ x) (K₁ f)))
    ∙ (sym (D.⋆Assoc (α₀ x) (β₀ x ⋆ γ₀ x) (K₁ f))))
    ≡ ((α□ f) ▹ β₀ y ▹ γ₀ y
    ∙ (D.⋆Assoc (α₀ x) (G₁ f) (β₀ y)) ▹ γ₀ y
    ∙ (α₀ x ◃ (β□ f)) ▹ γ₀ y
    ∙ ((D.⋆Assoc (α₀ x) (β₀ x ⋆ H₁ f) (γ₀ y))
      ∙ α₀ x ◃ (D.⋆Assoc (β₀ x) (H₁ f) (γ₀ y)))
    ∙ α₀ x ◃ β₀ x ◃ (γ□ f)
    ∙ α₀ x ◃ (sym (D.⋆Assoc (β₀ x) (γ₀ x) (K₁ f)))
    ∙ (sym (D.⋆Assoc (α₀ x) (β₀ x ⋆ γ₀ x) (K₁ f))))
  assoc-5 = reassoc!

  -- Cubical/LU2C/Instances/WildFunctor.agda:483
  assoc-6 :
    ((α□ f) ▹ β₀ y ▹ γ₀ y
    ∙ (D.⋆Assoc (α₀ x) (G₁ f) (β₀ y)) ▹ γ₀ y
    ∙ (α₀ x ◃ (β□ f)) ▹ γ₀ y
    ∙ ((sym (D.⋆Assoc (α₀ x) (β₀ x) (H₁ f) ▹ γ₀ y))
      ∙ (D.⋆Assoc (α₀ x ⋆ β₀ x) (H₁ f) (γ₀ y))
      ∙ (D.⋆Assoc (α₀ x) (β₀ x) (H₁ f ⋆ γ₀ y)))
    ∙ α₀ x ◃ β₀ x ◃ (γ□ f)
    ∙ α₀ x ◃ (sym (D.⋆Assoc (β₀ x) (γ₀ x) (K₁ f)))
    ∙ (sym (D.⋆Assoc (α₀ x) (β₀ x ⋆ γ₀ x) (K₁ f))))
    ≡ ((α□ f) ▹ β₀ y ▹ γ₀ y
    ∙ (D.⋆Assoc (α₀ x) (G₁ f) (β₀ y)) ▹ γ₀ y
    ∙ (α₀ x ◃ (β□ f)) ▹ γ₀ y
    ∙ (sym (D.⋆Assoc (α₀ x) (β₀ x) (H₁ f) ▹ γ₀ y))
    ∙ (D.⋆Assoc (α₀ x ⋆ β₀ x) (H₁ f) (γ₀ y))
    ∙ ((D.⋆Assoc (α₀ x) (β₀ x) (H₁ f ⋆ γ₀ y))
      ∙ α₀ x ◃ β₀ x ◃ (γ□ f))
    ∙ α₀ x ◃ (sym (D.⋆Assoc (β₀ x) (γ₀ x) (K₁ f)))
    ∙ (sym (D.⋆Assoc (α₀ x) (β₀ x ⋆ γ₀ x) (K₁ f))))
  assoc-6 = reassoc!

  -- Cubical/LU2C/Instances/WildFunctor.agda:503
  assoc-7 :
    ((α□ f) ▹ β₀ y ▹ γ₀ y
    ∙ (D.⋆Assoc (α₀ x) (G₁ f) (β₀ y)) ▹ γ₀ y
    ∙ (α₀ x ◃ (β□ f)) ▹ γ₀ y
    ∙ (sym (D.⋆Assoc (α₀ x) (β₀ x) (H₁ f) ▹ γ₀ y))
    ∙ (D.⋆Assoc (α₀ x ⋆ β₀ x) (H₁ f) (γ₀ y))
    ∙ ((α₀ x ⋆ β₀ x) ◃ (γ□ f)
      ∙ ((sym (D.⋆Assoc (α₀ x ⋆ β₀ x) (γ₀ x) (K₁ f)))
        ∙ (D.⋆Assoc (α₀ x) (β₀ x) (γ₀ x)) ▹ K₁ f
        ∙ (D.⋆Assoc (α₀ x) (β₀ x ⋆ γ₀ x) (K₁ f))
        ∙ α₀ x ◃ (D.⋆Assoc (β₀ x) (γ₀ x) (K₁ f))))
    ∙ α₀ x ◃ (sym (D.⋆Assoc (β₀ x) (γ₀ x) (K₁ f)))
    ∙ (sym (D.⋆Assoc (α₀ x) (β₀ x ⋆ γ₀ x) (K₁ f))))
    ≡ ((α□ f) ▹ β₀ y ▹ γ₀ y
    ∙ (D.⋆Assoc (α₀ x) (G₁ f) (β₀ y)) ▹ γ₀ y
    ∙ (α₀ x ◃ (β□ f)) ▹ γ₀ y
    ∙ (sym (D.⋆Assoc (α₀ x) (β₀ x) (H₁ f) ▹ γ₀ y))
    ∙ (D.⋆Assoc (α₀ x ⋆ β₀ x) (H₁ f) (γ₀ y))
    ∙ (α₀ x ⋆ β₀ x) ◃ (γ□ f)
    ∙ (sym (D.⋆Assoc (α₀ x ⋆ β₀ x) (γ₀ x) (K₁ f)))
    ∙ (D.⋆Assoc (α₀ x) (β₀ x) (γ₀ x)) ▹ K₁ f)
  assoc-7 = reassoc-with (∙l ∙l ∙l ∙l ∙l ∙l ∙l ∙l
    (∙l (shuffleSymL {q = sym (α₀ x ◃ D.⋆Assoc (β₀ x) (γ₀ x) (K₁ f))} refl)
    ∙ shuffleSymL {q = sym (D.⋆Assoc (α₀ x) (β₀ x ⋆ γ₀ x) (K₁ f))} refl))

  -- Cubical/LU2C/Instances/WildFunctor.agda:527
  assoc-8 :
    ((α□ f) ▹ β₀ y ▹ γ₀ y
    ∙ (D.⋆Assoc (α₀ x) (G₁ f) (β₀ y)) ▹ γ₀ y
    ∙ (α₀ x ◃ (β□ f)) ▹ γ₀ y
    ∙ (sym (D.⋆Assoc (α₀ x) (β₀ x) (H₁ f) ▹ γ₀ y))
    ∙ (D.⋆Assoc (α₀ x ⋆ β₀ x) (H₁ f) (γ₀ y))
    ∙ (α₀ x ⋆ β₀ x) ◃ (γ□ f)
    ∙ (sym (D.⋆Assoc (α₀ x ⋆ β₀ x) (γ₀ x) (K₁ f)))
    ∙ (D.⋆Assoc (α₀ x) (β₀ x) (γ₀ x)) ▹ K₁ f)
    ≡ ((D.⋆Assoc (F₁ f) (α₀ y) (β₀ y)) ▹ γ₀ y
    ∙ (D.⋆Assoc (F₁ f) (α₀ y ⋆ β₀ y) (γ₀ y))
    ∙ (((sym (D.⋆Assoc (F₁ f) (α₀ y ⋆ β₀ y) (γ₀ y)))
        ∙ ((sym (D.⋆Assoc (F₁ f) (α₀ y) (β₀ y)))
          ∙ (α□ f) ▹ β₀ y
          ∙ (D.⋆Assoc (α₀ x) (G₁ f) (β₀ y))
          ∙ α₀ x ◃ (β□ f)
          ∙ (sym (D.⋆Assoc (α₀ x) (β₀ x) (H₁ f)))) ▹ γ₀ y
        ∙ (D.⋆Assoc (α₀ x ⋆ β₀ x) (H₁ f) (γ₀ y))
        ∙ (α₀ x ⋆ β₀ x) ◃ (γ□ f)
        ∙ (sym (D.⋆Assoc (α₀ x ⋆ β₀ x) (γ₀ x) (K₁ f))))
      ∙ (D.⋆Assoc (α₀ x) (β₀ x) (γ₀ x)) ▹ K₁ f))
  assoc-8 = reassoc-with (sym (shuffleSymL {q = sym (D.⋆Assoc (F₁ f) (α₀ y) (β₀ y) ▹ γ₀ y)} refl)
    ∙ ∙l (sym (shuffleSymL {q = sym (D.⋆Assoc (F₁ f) (α₀ y ⋆ β₀ y) (γ₀ y))} refl)))

module Properties {ℓ ℓ′ : Level} (C : LU2C ℓ ℓ′)
  {x y z : LU2C.ob C} (f : C [ x , y ]) (g : C [ y , z ]) where
  open Not2C C
  -- Cubical/LU2C/Properties.agda:138
  idl-1 :
    ((⋆Assoc id id f ▹ g) ∙ (⋆Assoc id (id ⋆ f) g)
    ∙ id ◃ ((⋆Assoc id f g) ∙ (⋆IdL (f ⋆ g))))
    ≡ (((⋆Assoc id id f ▹ g) ∙ (⋆Assoc id (id ⋆ f) g)
    ∙ (id ◃ ⋆Assoc id f g)) ∙ (id ◃ ⋆IdL (f ⋆ g)))
  idl-1 = reassoc!

  -- Cubical/LU2C/Properties.agda:144
  idl-2 :
    (((⋆Assoc id id f) ∙ (id ◃ ⋆IdL f)) ▹ g ∙ (⋆Assoc id f g))
    ≡ ((⋆Assoc id id f ▹ g) ∙ ((id ◃ ⋆IdL f) ▹ g) ∙ (⋆Assoc id f g))
  idl-2 = reassoc!

  -- Cubical/LU2C/Properties.agda:187
  idr-1 :
    (((⋆Assoc f g id) ∙ (f ◃ ⋆IdR g)) ▹ id ∙ (⋆Assoc f g id))
    ≡ ((⋆Assoc f g id ▹ id) ∙ ((f ◃ ⋆IdR g) ▹ id) ∙ (⋆Assoc f g id))
  idr-1 = reassoc!

  -- Cubical/LU2C/Properties.agda:191
  idr-2 :
    ((⋆Assoc f g id ▹ id) ∙ (⋆Assoc f (g ⋆ id) id)
    ∙ f ◃ ((⋆Assoc g id id) ∙ (g ◃ ⋆IdL id)))
    ≡ (((⋆Assoc f g id ▹ id) ∙ (⋆Assoc f (g ⋆ id) id)
    ∙ (f ◃ ⋆Assoc g id id)) ∙ (f ◃ (g ◃ ⋆IdL id)))
  idr-2 = reassoc!

module Container {ℓ : Level} {A : Type ℓ} (x : A) where
  -- Cubical/WildCat/Monoidal/Instances/Container.agda:74
  triangle :
    (refl {x = x} ∙ refl ∙ refl ∙ refl
    ∙ refl ∙ refl ∙ refl ∙ refl)
    ≡ (refl ∙ refl ∙ refl ∙ refl)
  triangle = reassoc!

  -- Cubical/WildCat/Monoidal/Instances/Container.agda:82
  pentagon :
    (refl {x = x} ∙ refl ∙ refl ∙ refl
    ∙ refl ∙ refl ∙ refl ∙ refl
    ∙ refl ∙ refl ∙ refl ∙ refl
    ∙ refl ∙ refl ∙ refl)
    ≡ (refl ∙ refl ∙ refl ∙ refl ∙ refl)
  pentagon = reassoc!


-- Keep the carrier family abstract while checking these cases: a function's
-- type then determines its implicit objects. For actual groupoids, forgetting
-- their groupoid witnesses otherwise leaves metas in standalone signatures.
-- The specialization below has exactly the original groupoid category's fields.
functionCategory : ∀ {ℓ₀ ℓ} (O : Type ℓ₀) (El : O → Type ℓ) → WildCat ℓ₀ ℓ
functionCategory O El .WildCat.ob = O
functionCategory O El .WildCat.Hom[_,_] X Y = El X → El Y
functionCategory O El .WildCat.id x = x
functionCategory O El .WildCat._⋆_ f g x = g (f x)
functionCategory O El .WildCat.⋆IdL f = refl
functionCategory O El .WildCat.⋆IdR f = refl
functionCategory O El .WildCat.⋆Assoc f g h = refl

module FunctionCategories {ℓ₀ ℓ} (O : Type ℓ₀) (El : O → Type ℓ) where
  private
    HGpd = functionCategory O El
    module HGpd = WildCat HGpd
  open NotWC HGpd

  module Composite (F G : WildFunctor HGpd HGpd) where
    private
      module F = NotF F
      module G = NotF G
    open F using (F₁; F₂)
    open G using () renaming
      (F₁ to G₁; F₂ to G₂; F-id to G-id; F-seq to G-seq)

    module Units {X Y : HGpd.ob} (f : HGpd.Hom[ X , Y ]) where
      -- Cubical/LU2C/Copresheaf/EndoConstructions/Composite.agda:80
      idl-1 :
        ( (G₂ (F.F-seq id f) ∙ G-seq (F₁ id) (F₁ f))
        ∙ (G₂ F.F-id ∙ G-id) ▹ G₁ (F₁ f) )
        ≡ ( G₂ (F.F-seq id f)
        ∙ (G-seq (F₁ id) (F₁ f) ∙ G₂ F.F-id ▹ G₁ (F₁ f))
        ∙ G-id ▹ G₁ (F₁ f) )
      idl-1 = reassoc!

      -- Cubical/LU2C/Copresheaf/EndoConstructions/Composite.agda:87
      idl-2 :
        ( G₂ (F.F-seq id f)
        ∙ (G₂ (F.F-id ▹ F₁ f) ∙ G-seq id (F₁ f))
        ∙ G-id ▹ G₁ (F₁ f) )
        ≡ ( (G₂ (F.F-seq id f ∙ F.F-id ▹ F₁ f)
          ∙ G-seq id (F₁ f))
        ∙ G-id ▹ G₁ (F₁ f) )
      idl-2 = reassoc!

      -- Cubical/LU2C/Copresheaf/EndoConstructions/Composite.agda:122
      idr-1 :
        ( (G₂ (F.F-seq f id) ∙ G-seq (F₁ f) (F₁ id))
        ∙ G₁ (F₁ f) ◃ (G₂ (F.F-id) ∙ G-id) )
        ≡ ( (G₂ (F.F-seq f id)
          ∙ G-seq (F₁ f) (F₁ id)
          ∙ G₁ (F₁ f) ◃ G₂ (F.F-id))
        ∙ G₁ (F₁ f) ◃ G-id )
      idr-1 = reassoc!

      -- Cubical/LU2C/Copresheaf/EndoConstructions/Composite.agda:130
      idr-2 :
        ( (G₂ (F.F-seq f id)
          ∙ G₂ (F₁ f ◃ F.F-id)
          ∙ G-seq (F₁ f) id)
        ∙ G₁ (F₁ f) ◃ G-id )
        ≡ ( ((G₂ (F.F-seq f id ∙ F₁ f ◃ F.F-id))
          ∙ G-seq (F₁ f) id)
        ∙ G₁ (F₁ f) ◃ G-id )
      idr-2 = reassoc!

    module Associativity {W X Y Z : HGpd.ob}
      (f : HGpd.Hom[ W , X ]) (g : HGpd.Hom[ X , Y ]) (h : HGpd.Hom[ Y , Z ]) where
      -- Cubical/LU2C/Copresheaf/EndoConstructions/Composite.agda:195
      assoc-1 :
        ( (G₂ (F.F-seq (f ⋆ g) h)
          ∙ G-seq (F₁ (f ⋆ g)) (F₁ h))
        ∙ (G₂ (F.F-seq f g)
          ∙ G-seq (F₁ f) (F₁ g)) ▹ G₁ (F₁ h) )
        ≡ ( G₂ (F.F-seq (f ⋆ g) h)
        ∙ (G-seq (F₁ (f ⋆ g)) (F₁ h)
          ∙ G₂ (F.F-seq f g) ▹ G₁ (F₁ h))
        ∙ G-seq (F₁ f) (F₁ g) ▹ G₁ (F₁ h) )
      assoc-1 = reassoc!

      -- Cubical/LU2C/Copresheaf/EndoConstructions/Composite.agda:205
      assoc-2 :
        ( G₂ (F.F-seq (f ⋆ g) h)
        ∙ (G₂ (F.F-seq f g ▹ F₁ h)
          ∙ G-seq (F₁ f ⋆ F₁ g) (F₁ h))
        ∙ G-seq (F₁ f) (F₁ g) ▹ G₁ (F₁ h) )
        ≡ ( G₂ (F.F-seq (f ⋆ g) h
          ∙ F.F-seq f g ▹ F₁ h)
        ∙ G-seq (F₁ f ⋆ F₁ g) (F₁ h)
        ∙ G-seq (F₁ f) (F₁ g) ▹ G₁ (F₁ h) )
      assoc-2 = reassoc!

      -- Cubical/LU2C/Copresheaf/EndoConstructions/Composite.agda:215
      assoc-3 :
        ( G₂ (refl ∙ F.F-seq f (g ⋆ h)
            ∙ F₁ f ◃ F.F-seq g h)
        ∙ G-seq (F₁ f ⋆ F₁ g) (F₁ h)
        ∙ G-seq (F₁ f) (F₁ g) ▹ G₁ (F₁ h) )
        ≡ ( refl ∙ (G₂ (F.F-seq f (g ⋆ h)
          ∙ F₁ f ◃ F.F-seq g h))
        ∙ G-seq (F₁ f ⋆ F₁ g) (F₁ h)
        ∙ G-seq (F₁ f) (F₁ g) ▹ G₁ (F₁ h) )
      assoc-3 = reassoc!

      -- Cubical/LU2C/Copresheaf/EndoConstructions/Composite.agda:225
      assoc-4 :
        ( refl ∙ (G₂ (F.F-seq f (g ⋆ h)
          ∙ F₁ f ◃ F.F-seq g h))
        ∙ refl
        ∙ G-seq (F₁ f) (F₁ g ⋆ F₁ h)
        ∙ G₁ (F₁ f) ◃ G-seq (F₁ g) (F₁ h) )
        ≡ ( refl
        ∙ G₂ (F.F-seq f (g ⋆ h))
        ∙ (G₂ (F₁ f ◃ F.F-seq g h)
          ∙ G-seq (F₁ f) (F₁ g ⋆ F₁ h))
        ∙ G₁ (F₁ f) ◃ G-seq (F₁ g) (F₁ h) )
      assoc-4 = reassoc!

      -- Cubical/LU2C/Copresheaf/EndoConstructions/Composite.agda:237
      assoc-5 :
        ( refl
        ∙ G₂ (F.F-seq f (g ⋆ h))
        ∙ (G-seq (F₁ f) (F₁ (g ⋆ h))
          ∙ G₁ (F₁ f) ◃ G₂ (F.F-seq g h))
        ∙ G₁ (F₁ f) ◃ G-seq (F₁ g) (F₁ h) )
        ≡ ( refl
        ∙ (G₂ (F.F-seq f (g ⋆ h))
          ∙ G-seq (F₁ f) (F₁ (g ⋆ h)))
        ∙ G₁ (F₁ f) ◃ (G₂ (F.F-seq g h)
          ∙ G-seq (F₁ g) (F₁ h)) )
      assoc-5 = reassoc!

    module Identity {X Y : HGpd.ob} (f : HGpd.Hom[ X , Y ]) where
      -- Cubical/LU2C/Copresheaf/EndoConstructions.agda:97
      endo-id :
        ( sym (G-seq (F₁ f) id)
        ∙ G-seq id (F₁ f)
        ∙ G-id ▹ G₁ (F₁ f) )
        ≡ ( ((sym (G-seq (F₁ f) id)
            ∙ refl ∙ G-seq id (F₁ f))
          ∙ refl)
        ∙ G-id ▹ G₁ (F₁ f) )
      endo-id = reassoc!
      -- Cubical/WildCat/Monoidal/Instances/GpdEndo.agda:55
      monoidal-triangle :
        ( refl
        ∙ (sym (G.F-seq (F₁ f) id)
          ∙ refl
          ∙ G.F-seq id (F₁ f))
        ∙ refl )
        ≡ ( ((sym (G.F-seq (F₁ f) id)
            ∙ refl)
          ∙ refl ∙ refl
          ∙ G.F-seq id (F₁ f))
        ∙ refl )
      monoidal-triangle = reassoc!

  module WhiskR {F H : WildFunctor HGpd HGpd}
    (α : WildNatTrans _ _ F H) (G : WildFunctor HGpd HGpd) where
    private
      module F = NotF F
      module G = NotF G
      module H = NotF H
    open F using (F₁; F₂)
    open G using () renaming (F₁ to G₁; F₂ to G₂; F-id to G-id; F-seq to G-seq)
    open H using () renaming (F₁ to H₁; F₂ to H₂; F-id to H-id; F-seq to H-seq)
    open WildNatTrans α using () renaming (N-ob to α₀; N-hom to α□)

    module Identity (X : HGpd.ob) where
      -- Cubical/LU2C/Copresheaf/EndoConstructions/WhiskR.agda:130
      id-1 :
        ( (sym (G-seq (F₁ id) (α₀ X))
          ∙ G.F₂ (α□ (id {x = X}))
          ∙ G-seq (α₀ X) (H₁ id))
        ∙ G₁ (α₀ X) ◃ (G.F₂ (H-id) ∙ G-id) )
        ≡ ( sym (G-seq (F₁ id) (α₀ X))
        ∙ G.F₂ (α□ (id {x = X}))
        ∙ (G-seq (α₀ X) (H₁ id)
          ∙ G₁ (α₀ X) ◃ G.F₂ (H-id))
        ∙ G₁ (α₀ X) ◃ G-id )
      id-1 = reassoc!

      -- Cubical/LU2C/Copresheaf/EndoConstructions/WhiskR.agda:141
      id-2 :
        ( sym (G-seq (F₁ id) (α₀ X))
        ∙ G.F₂ (α□ (id {x = X}))
        ∙ (G.F₂ (α₀ X ◃ H-id) ∙ G-seq (α₀ X) id)
        ∙ G₁ (α₀ X) ◃ G-id )
        ≡ ( sym (G-seq (F₁ id) (α₀ X))
        ∙ G.F₂ (α□ (id {x = X}) ∙ α₀ X ◃ H-id)
        ∙ (G-seq (α₀ X) id ∙ G₁ (α₀ X) ◃ G-id) )
      id-2 = reassoc!

      -- Cubical/LU2C/Copresheaf/EndoConstructions/WhiskR.agda:150
      id-3 :
        ( sym (G-seq (F₁ id) (α₀ X))
        ∙ G-seq (F₁ id) (α₀ X)
        ∙ G.F₂ (F.F-id) ▹ G₁ (α₀ X)
        ∙ sym (G-seq id (α₀ X)) )
        ≡ ( (sym (G-seq (F₁ id) (α₀ X))
          ∙ G-seq (F₁ id) (α₀ X))
        ∙ G.F₂ (F.F-id) ▹ G₁ (α₀ X)
        ∙ sym (G-seq id (α₀ X)) )
      id-3 = reassoc!

      -- Cubical/LU2C/Copresheaf/EndoConstructions/WhiskR.agda:160
      id-4 :
        ( G.F₂ (F.F-id) ▹ G₁ (α₀ X)
        ∙ G-id ▹ G₁ (α₀ X) )
        ≡ ( (G.F₂ (F.F-id) ∙ G-id) ▹ G₁ (α₀ X) )
      id-4 = reassoc!

    module Sequence {X Y Z : HGpd.ob}
      (f : HGpd.Hom[ X , Y ]) (g : HGpd.Hom[ Y , Z ]) where
      -- Cubical/LU2C/Copresheaf/EndoConstructions/WhiskR.agda:295
      seq-1 :
        ( (sym (G-seq (F₁ (f ⋆ g)) (α₀ Z))
          ∙ G.F₂ (α□ (f ⋆ g))
          ∙ G-seq (α₀ X) (H₁ (f ⋆ g)))
        ∙ G₁ (α₀ X) ◃ (G.F₂ (H-seq f g) ∙ G-seq (H₁ f) (H₁ g)) )
        ≡ ( sym (G-seq (F₁ (f ⋆ g)) (α₀ Z))
        ∙ G.F₂ (α□ (f ⋆ g))
        ∙ (G-seq (α₀ X) (H₁ (f ⋆ g))
          ∙ G₁ (α₀ X) ◃ G.F₂ (H-seq f g))
        ∙ G₁ (α₀ X) ◃ G-seq (H₁ f) (H₁ g) )
      seq-1 = reassoc!

      -- Cubical/LU2C/Copresheaf/EndoConstructions/WhiskR.agda:306
      seq-2 :
        ( sym (G-seq (F₁ (f ⋆ g)) (α₀ Z))
        ∙ G.F₂ (α□ (f ⋆ g))
        ∙ (G.F₂ (α₀ X ◃ H-seq f g)
          ∙ G-seq (α₀ X) (H₁ f ⋆ H₁ g))
        ∙ G₁ (α₀ X) ◃ G-seq (H₁ f) (H₁ g) )
        ≡ ( sym (G-seq (F₁ (f ⋆ g)) (α₀ Z))
        ∙ G.F₂ (α□ (f ⋆ g) ∙ α₀ X ◃ H-seq f g)
        ∙ (G-seq (α₀ X) (H₁ f ⋆ H₁ g)
          ∙ G₁ (α₀ X) ◃ G-seq (H₁ f) (H₁ g)) )
      seq-2 = reassoc!

      -- Cubical/LU2C/Copresheaf/EndoConstructions/WhiskR.agda:317
      seq-3 :
        ( sym (G-seq (F₁ (f ⋆ g)) (α₀ Z))
        ∙ G.F₂ (F.F-seq f g ▹ α₀ Z
          ∙ F₁ f ◃ α□ g ∙ α□ f ▹ H₁ g)
        ∙ G-seq (α₀ X ⋆ H₁ f) (H₁ g)
        ∙ G-seq (α₀ X) (H₁ f) ▹ G₁ (H₁ g) )
        ≡ ( sym (G-seq (F₁ (f ⋆ g)) (α₀ Z))
        ∙ G.F₂ (F.F-seq f g ▹ α₀ Z)
        ∙ G.F₂ (F₁ f ◃ α□ g)
        ∙ (G.F₂ (α□ f ▹ H₁ g)
          ∙ G-seq (α₀ X ⋆ H₁ f) (H₁ g))
        ∙ G-seq (α₀ X) (H₁ f) ▹ G₁ (H₁ g) )
      seq-3 = reassoc!

      -- Cubical/LU2C/Copresheaf/EndoConstructions/WhiskR.agda:330
      seq-4 :
        ( sym (G-seq (F₁ (f ⋆ g)) (α₀ Z))
        ∙ G.F₂ (F.F-seq f g ▹ α₀ Z)
        ∙ G.F₂ (F₁ f ◃ α□ g)
        ∙ (((G-seq (F₁ f) (α₀ Y ⋆ H₁ g)
            ∙ G₁ (F₁ f) ◃ G-seq (α₀ Y) (H₁ g))
            ∙ sym (G-seq (F₁ f) (α₀ Y)) ▹ G₁ (H₁ g))
          ∙ G.F₂ (α□ f) ▹ G₁ (H₁ g))
        ∙ G-seq (α₀ X) (H₁ f) ▹ G₁ (H₁ g) )
        ≡ ( sym (G-seq (F₁ (f ⋆ g)) (α₀ Z))
        ∙ G.F₂ (F.F-seq f g ▹ α₀ Z)
        ∙ (G.F₂ (F₁ f ◃ α□ g) ∙ G-seq (F₁ f) (α₀ Y ⋆ H₁ g))
        ∙ G₁ (F₁ f) ◃ G-seq (α₀ Y) (H₁ g)
        ∙ sym (G-seq (F₁ f) (α₀ Y)) ▹ G₁ (H₁ g)
        ∙ G.F₂ (α□ f) ▹ G₁ (H₁ g)
        ∙ G-seq (α₀ X) (H₁ f) ▹ G₁ (H₁ g) )
      seq-4 = reassoc!

      -- Cubical/LU2C/Copresheaf/EndoConstructions/WhiskR.agda:347
      seq-5 :
        ( sym (G-seq (F₁ (f ⋆ g)) (α₀ Z))
        ∙ G.F₂ (F.F-seq f g ▹ α₀ Z)
        ∙ (((G-seq (F₁ f ⋆ F₁ g) (α₀ Z)
            ∙ G-seq (F₁ f) (F₁ g) ▹ G₁ (α₀ Z))
            ∙ G₁ (F₁ f) ◃ sym (G-seq (F₁ g) (α₀ Z)))
          ∙ G₁ (F₁ f) ◃ G.F₂ (α□ g))
        ∙ G₁ (F₁ f) ◃ G-seq (α₀ Y) (H₁ g)
        ∙ sym (G-seq (F₁ f) (α₀ Y)) ▹ G₁ (H₁ g)
        ∙ G.F₂ (α□ f) ▹ G₁ (H₁ g)
        ∙ G-seq (α₀ X) (H₁ f) ▹ G₁ (H₁ g) )
        ≡ ( sym (G-seq (F₁ (f ⋆ g)) (α₀ Z))
        ∙ (G.F₂ (F.F-seq f g ▹ α₀ Z)
          ∙ G-seq (F₁ f ⋆ F₁ g) (α₀ Z))
        ∙ G-seq (F₁ f) (F₁ g) ▹ G₁ (α₀ Z)
        ∙ G₁ (F₁ f) ◃ sym (G-seq (F₁ g) (α₀ Z))
        ∙ G₁ (F₁ f) ◃ G.F₂ (α□ g)
        ∙ G₁ (F₁ f) ◃ G-seq (α₀ Y) (H₁ g)
        ∙ sym (G-seq (F₁ f) (α₀ Y)) ▹ G₁ (H₁ g)
        ∙ G.F₂ (α□ f) ▹ G₁ (H₁ g)
        ∙ G-seq (α₀ X) (H₁ f) ▹ G₁ (H₁ g) )
      seq-5 = reassoc!

      -- Cubical/LU2C/Copresheaf/EndoConstructions/WhiskR.agda:369
      seq-6 :
        ( sym (G-seq (F₁ (f ⋆ g)) (α₀ Z))
        ∙ (G-seq (F₁ (f ⋆ g)) (α₀ Z) ∙ G.F₂ (F.F-seq f g) ▹ G₁ (α₀ Z))
        ∙ G-seq (F₁ f) (F₁ g) ▹ G₁ (α₀ Z)
        ∙ G₁ (F₁ f) ◃ sym (G-seq (F₁ g) (α₀ Z))
        ∙ G₁ (F₁ f) ◃ G.F₂ (α□ g)
        ∙ G₁ (F₁ f) ◃ G-seq (α₀ Y) (H₁ g)
        ∙ sym (G-seq (F₁ f) (α₀ Y)) ▹ G₁ (H₁ g)
        ∙ G.F₂ (α□ f) ▹ G₁ (H₁ g)
        ∙ G-seq (α₀ X) (H₁ f) ▹ G₁ (H₁ g) )
        ≡ ( (sym (G-seq (F₁ (f ⋆ g)) (α₀ Z)) ∙ G-seq (F₁ (f ⋆ g)) (α₀ Z))
        ∙ G.F₂ (F.F-seq f g) ▹ G₁ (α₀ Z)
        ∙ G-seq (F₁ f) (F₁ g) ▹ G₁ (α₀ Z)
        ∙ G₁ (F₁ f) ◃ sym (G-seq (F₁ g) (α₀ Z))
        ∙ G₁ (F₁ f) ◃ G.F₂ (α□ g)
        ∙ G₁ (F₁ f) ◃ G-seq (α₀ Y) (H₁ g)
        ∙ sym (G-seq (F₁ f) (α₀ Y)) ▹ G₁ (H₁ g)
        ∙ G.F₂ (α□ f) ▹ G₁ (H₁ g)
        ∙ G-seq (α₀ X) (H₁ f) ▹ G₁ (H₁ g) )
      seq-6 = reassoc!

      -- Cubical/LU2C/Copresheaf/EndoConstructions/WhiskR.agda:389
      seq-7 :
        ( refl
        ∙ G.F₂ (F.F-seq f g) ▹ G₁ (α₀ Z)
        ∙ G-seq (F₁ f) (F₁ g) ▹ G₁ (α₀ Z)
        ∙ G₁ (F₁ f) ◃ sym (G-seq (F₁ g) (α₀ Z))
        ∙ G₁ (F₁ f) ◃ G.F₂ (α□ g)
        ∙ G₁ (F₁ f) ◃ G-seq (α₀ Y) (H₁ g)
        ∙ sym (G-seq (F₁ f) (α₀ Y)) ▹ G₁ (H₁ g)
        ∙ G.F₂ (α□ f) ▹ G₁ (H₁ g)
        ∙ G-seq (α₀ X) (H₁ f) ▹ G₁ (H₁ g) )
        ≡ ( (G.F₂ (F.F-seq f g) ∙ G-seq (F₁ f) (F₁ g)) ▹ G₁ (α₀ Z)
        ∙ G₁ (F₁ f) ◃ (sym (G-seq (F₁ g) (α₀ Z))
          ∙ G.F₂ (α□ g) ∙ G-seq (α₀ Y) (H₁ g))
        ∙ (sym (G-seq (F₁ f) (α₀ Y))
          ∙ G.F₂ (α□ f) ∙ G-seq (α₀ X) (H₁ f)) ▹ G₁ (H₁ g) )
      seq-7 = reassoc!

  module Pseudonat {ℓC ℓC′ : Level} (C : WildCat ℓC ℓC′)
    {F G H : WildFunctor C HGpd}
    (α : WildNatTrans _ _ F G) (β : WildNatTrans _ _ G H) where
    private module C = WildCat C
    open NotWC C
    open NotF F using (F₁; F-id; F-seq)
    open NotF G using () renaming (F₁ to G₁; F-id to G-id; F-seq to G-seq)
    open NotF H using () renaming (F₁ to H₁; F-id to H-id; F-seq to H-seq)
    open WildNatTrans α using () renaming (N-ob to α₀; N-hom to α□)
    open WildNatTrans β using () renaming (N-ob to β₀; N-hom to β□)

    module Identity (X : C.ob) where
      -- Cubical/LU2C/Copresheaf/Pseudonat/Constructions.agda:99
      id-1 :
        ( (α□ id ▹ β₀ X ∙ α₀ X ◃ β□ id) ∙ α₀ X ◃ β₀ X ◃ H-id )
        ≡ ( α□ id ▹ β₀ X ∙ α₀ X ◃ (β□ id ∙ β₀ X ◃ H-id) )
      id-1 = reassoc!

    module Sequence {X Y Z : C.ob}
      (f : C.Hom[ X , Y ]) (g : C.Hom[ Y , Z ]) where
      -- Cubical/LU2C/Copresheaf/Pseudonat/Constructions.agda:114
      seq-1 :
        ( (α□ (f ⋆ g) ▹ β₀ Z ∙ α₀ X ◃ β□ (f ⋆ g))
        ∙ α₀ X ◃ β₀ X ◃ H-seq f g )
        ≡ ( α□ (f ⋆ g) ▹ β₀ Z
        ∙ α₀ X ◃ (β□ (f ⋆ g) ∙ β₀ X ◃ H-seq f g) )
      seq-1 = reassoc!

      -- Cubical/LU2C/Copresheaf/Pseudonat/Constructions.agda:127
      seq-2 :
        ( α□ (f ⋆ g) ▹ β₀ Z
        ∙ α₀ X ◃ (G-seq f g ▹ β₀ Z
          ∙ G₁ f ◃ β□ g ∙ β□ f ▹ H₁ g) )
        ≡ ( (α□ (f ⋆ g) ∙ α₀ X ◃ G-seq f g) ▹ β₀ Z
        ∙ α₀ X ◃ G₁ f ◃ β□ g
        ∙ α₀ X ◃ β□ f ▹ H₁ g )
      seq-2 = reassoc!

      -- Cubical/LU2C/Copresheaf/Pseudonat/Constructions.agda:145
      seq-3 :
        ( (F-seq f g ▹ α₀ Z
          ∙ F₁ f ◃ α□ g ∙ α□ f ▹ G₁ g) ▹ β₀ Z
        ∙ α₀ X ◃ G₁ f ◃ β□ g
        ∙ α₀ X ◃ β□ f ▹ H₁ g )
        ≡ ( F-seq f g ▹ α₀ Z ▹ β₀ Z
        ∙ F₁ f ◃ α□ g ▹ β₀ Z
        ∙ (α□ f ▹ G₁ g ▹ β₀ Z
          ∙ α₀ X ◃ G₁ f ◃ β□ g)
        ∙ α₀ X ◃ β□ f ▹ H₁ g )
      seq-3 = reassoc!

      -- Cubical/LU2C/Copresheaf/Pseudonat/Constructions.agda:169
      seq-4 :
        ( F-seq f g ▹ α₀ Z ▹ β₀ Z
        ∙ F₁ f ◃ α□ g ▹ β₀ Z
        ∙ (F₁ f ◃ α₀ Y ◃ β□ g
          ∙ α□ f ▹ β₀ Y ▹ H₁ g)
        ∙ α₀ X ◃ β□ f ▹ H₁ g )
        ≡ ( F-seq f g ▹ α₀ Z ▹ β₀ Z
        ∙ F₁ f ◃ (α□ g ▹ β₀ Z ∙ α₀ Y ◃ β□ g)
        ∙ (α□ f ▹ β₀ Y ∙ α₀ X ◃ β□ f) ▹ H₁ g )
      seq-4 = reassoc!

  module Assoc (F G H : WildFunctor HGpd HGpd) where
    private
      module F = NotF F
      module G = NotF G
      module H = NotF H
    open F using (F₁; F₂)
    open G using () renaming (F₁ to G₁; F₂ to G₂)
    open H using () renaming (F₁ to H₁; F₂ to H₂)

    module Identity (X : HGpd.ob) where
      -- Cubical/WildCat/Monoidal/Instances/GpdEndo/Assoc.agda:52
      id-1 :
        ( refl ∙ H₂ (G₂ (F.F-id {x = X}) ∙ G.F-id) ∙ H.F-id )
        ≡ ( H₂ (G₂ (F.F-id {x = X})) ∙ H₂ (G.F-id) ∙ H.F-id )
      id-1 = reassoc!

    module Sequence {X Y Z : HGpd.ob}
      (f : HGpd.Hom[ X , Y ]) (g : HGpd.Hom[ Y , Z ]) where
      -- Cubical/WildCat/Monoidal/Instances/GpdEndo/Assoc.agda:57
      seq-1 :
        ( refl
        ∙ (H₂ (G₂ (F.F-seq f g)
          ∙ G.F-seq (F₁ f) (F₁ g)))
        ∙ H.F-seq (G₁ (F₁ f)) (G₁ (F₁ g)) )
        ≡ ( (H₂ (G₂ (F.F-seq f g))
          ∙ H₂ (G.F-seq (F₁ f) (F₁ g))
          ∙ H.F-seq (G₁ (F₁ f)) (G₁ (F₁ g)))
        ∙ refl ∙ refl )
      seq-1 = reassoc!

  module Units (F : WildFunctor HGpd HGpd) {X Y Z : HGpd.ob}
    (f : HGpd.Hom[ X , Y ]) (g : HGpd.Hom[ Y , Z ]) where
    private module F = NotF F
    -- Cubical/WildCat/Monoidal/Instances/GpdEndo/LUnit.agda:40
    left-seq :
      (refl ∙ F.F-seq f g)
      ≡ ((refl ∙ F.F-seq f g) ∙ refl ∙ refl)
    left-seq = reassoc!

    -- Cubical/WildCat/Monoidal/Instances/GpdEndo/LUnit.agda:144
    left-inverse-seq :
      (refl ∙ refl ∙ F.F-seq f g)
      ≡ (F.F-seq f g ∙ refl ∙ refl)
    left-inverse-seq = reassoc!
    -- Cubical/WildCat/Monoidal/Instances/GpdEndo/RUnit.agda:42
    right-seq :
      (refl ∙ F.F-seq f g)
      ≡ ((F.F-seq f g ∙ refl) ∙ refl ∙ refl)
    right-seq = reassoc!

    -- Cubical/WildCat/Monoidal/Instances/GpdEndo/RUnit.agda:75
    right-inverse-seq :
      (refl ∙ F.F-seq f g ∙ refl)
      ≡ (F.F-seq f g ∙ refl ∙ refl)
    right-inverse-seq = reassoc!

  module UnitNaturality {F G : WildFunctor HGpd HGpd}
    (α : WildNatTrans _ _ F G) {x y : HGpd.ob} (f : HGpd.Hom[ x , y ]) where
    private
      module F = NotF F
      module G = NotF G
    open WildNatTrans α using () renaming (N-ob to α₀; N-hom to α□)
    -- Cubical/WildCat/Monoidal/Instances/GpdEndo/LUnit.agda:113
    left-1 :
      ( sym (F.F-seq f id) ▹ α₀ y
      ∙ (F.F-seq id f ∙ (F.F-id {x = x}) ▹ F.F₁ f) ▹ α₀ y
      ∙ α□ f )
      ≡ ( sym (F.F-seq f id) ▹ α₀ y
      ∙ F.F-seq id f ▹ α₀ y
      ∙ ((F.F-id {x = x}) ▹ F.F₁ f ▹ α₀ y
        ∙ α□ f) )
    left-1 = reassoc!

    -- Cubical/WildCat/Monoidal/Instances/GpdEndo/LUnit.agda:122
    left-2 :
      ( sym (F.F-seq f id) ▹ α₀ y
      ∙ F.F-seq id f ▹ α₀ y
      ∙ (F.F₁ id ◃ α□ f
        ∙ (F.F-id {x = x}) ▹ α₀ x ▹ G.F₁ f) )
      ≡ ( (((sym (F.F-seq f id) ∙ refl ∙ F.F-seq id f) ▹ α₀ y
          ∙ F.F₁ id ◃ α□ f)
        ∙ refl)
      ∙ (F.F-id {x = x}) ▹ α₀ x ▹ G.F₁ f )
    left-2 = reassoc!
    -- Cubical/WildCat/Monoidal/Instances/GpdEndo/RUnit.agda:59
    right-1 :
      (((refl ∙ α□ f ∙ refl) ∙ refl) ∙ refl)
      ≡ (refl ∙ α□ f)
    right-1 = reassoc!

module Groupoids (ℓ : Level) where
  open import Cubical.LU2C.Instances.Groupoids ℓ

  original-category : functionCategory (LU2C.ob HGpd) fst ≡ LU2C.str HGpd
  original-category i .WildCat.ob = LU2C.ob HGpd
  original-category i .WildCat.Hom[_,_] X Y = fst X → fst Y
  original-category i .WildCat.id x = x
  original-category i .WildCat._⋆_ f g x = g (f x)
  original-category i .WildCat.⋆IdL f = refl
  original-category i .WildCat.⋆IdR f = refl
  original-category i .WildCat.⋆Assoc f g h = refl

  module Cases = FunctionCategories (LU2C.ob HGpd) fst
