open import Cubical.Foundations.Prelude

open import Cubical.Bicategory.Base

module Cubical.Bicategory.Instances.Walking where

open import Cubical.Data.Unit
open import Cubical.Data.Empty

module Walking where
  data ob : Type where
    𝟘 𝟙 : ob
  
  Hom[_,_] : ob → ob → Type 
  Hom[ 𝟘 , 𝟘 ] = Unit
  Hom[ 𝟘 , 𝟙 ] = Unit
  Hom[ 𝟙 , 𝟘 ] = ⊥
  Hom[ 𝟙 , 𝟙 ] = Unit

  id : {x : ob} → Hom[ x , x ]
  id {(𝟘)} = tt
  id {(𝟙)} = tt

  _⋆_ : {x y z : ob} → Hom[ x , y ] → Hom[ y , z ] → Hom[ x , z ]
  _⋆_ {(𝟘)} {(𝟘)} {(z)} tt g = g
  _⋆_ {(𝟘)} {(𝟙)} {(𝟙)} _ _ = tt
  _⋆_ {(𝟙)} {(𝟙)} {(𝟙)} _ _ = tt

  ⋆IdL : {x y : ob} (f : Hom[ x , y ]) 
    → id ⋆ f ≡ f 
  ⋆IdL {(𝟘)} {(𝟘)} f = refl
  ⋆IdL {(𝟘)} {(𝟙)} f = refl
  ⋆IdL {(𝟙)} {(𝟙)} f = refl

  ⋆IdR : {x y : ob} (f : Hom[ x , y ]) 
    → f ⋆ id ≡ f 
  ⋆IdR {(𝟘)} {(𝟘)} f = refl
  ⋆IdR {(𝟘)} {(𝟙)} f = refl
  ⋆IdR {(𝟙)} {(𝟙)} f = refl

  ⋆Assoc : {u v w x : ob} 
    (f : Hom[ u , v ]) 
    (g : Hom[ v , w ]) 
    (h : Hom[ w , x ])
    → (f ⋆ g) ⋆ h ≡ f ⋆ (g ⋆ h) 
  ⋆Assoc {(𝟘)} {(𝟘)} tt g h = refl
  ⋆Assoc {(𝟘)} {(𝟙)} {(𝟙)} {(𝟙)} _ _ _ = refl
  ⋆Assoc {(𝟙)} {(𝟙)} {(𝟙)} {(𝟙)} _ _ _ = refl

open Walking using (𝟘; 𝟙) public

module _ where
  open Bicategory
  open IsBicategory

  open import Cubical.Foundations.GroupoidLaws
  open import Cubical.Foundations.HLevels

  Walking : Bicategory _ _
  Walking .str = record where
    open Walking using 
      ( ob
      ; Hom[_,_]
      ; id
      ; _⋆_
      ; ⋆IdL
      ; ⋆IdR
      ; ⋆Assoc
      )
  Walking .isBicat .triangle {(𝟘)} {(𝟘)} {(𝟘)} _ _ = lUnit _
  Walking .isBicat .triangle {(𝟘)} {(𝟘)} {(𝟙)} _ _ = lUnit _
  Walking .isBicat .triangle {(𝟘)} {(𝟙)} {(𝟙)} _ _ = lUnit _
  Walking .isBicat .triangle {(𝟙)} {(𝟙)} {(𝟙)} _ _ = lUnit _
  Walking .isBicat .pentagon {(𝟘)} {(𝟘)} {(𝟘)} {(𝟘)} {(𝟘)} _ _ _ _ = lUnit _
  Walking .isBicat .pentagon {(𝟘)} {(𝟘)} {(𝟘)} {(𝟘)} {(𝟙)} _ _ _ _ = lUnit _
  Walking .isBicat .pentagon {(𝟘)} {(𝟘)} {(𝟘)} {(𝟙)} {(𝟙)} _ _ _ _ = lUnit _
  Walking .isBicat .pentagon {(𝟘)} {(𝟘)} {(𝟙)} {(𝟙)} {(𝟙)} _ _ _ _ = lUnit _
  Walking .isBicat .pentagon {(𝟘)} {(𝟙)} {(𝟙)} {(𝟙)} {(𝟙)} _ _ _ _ = lUnit _
  Walking .isBicat .pentagon {(𝟙)} {(𝟙)} {(𝟙)} {(𝟙)} {(𝟙)} _ _ _ _ = lUnit _
  Walking .isBicat .isGpdHom {(𝟘)} {(𝟘)} = isSet→isGroupoid isSetUnit
  Walking .isBicat .isGpdHom {(𝟘)} {(𝟙)} = isSet→isGroupoid isSetUnit
  Walking .isBicat .isGpdHom {(𝟙)} {(𝟙)} = isSet→isGroupoid isSetUnit

-- In a more convoluted way

-- open import Cubical.Bicategory.Instances.FromSetCat

-- open import Cubical.Categories.Instances.Free

-- Walking′ : Bicategory _ _
-- Walking′ = AsBicat ?

module _ {ℓ ℓ′ : _} {C : Bicategory ℓ ℓ′} where
  open import Cubical.Bicategory.Pseudofunctor
  open import Cubical.WildCat.Functor

  open BicatSyntax {{...}}

  open Bicategory C using () renaming (ob to C₀)

  open BicatSynInstBC C

  open import Cubical.Foundations.Function using (homotopyNatural)
  open import Cubical.Foundations.GroupoidLaws
  open import Prelude.ExtraGpdLaws

  -- private
  --   cancel-id◃ : {x y : C₀} {f g : C [ x , y ]} (p q : f ≡ g)
  --     → id ◃ p ≡ id ◃ q → p ≡ q
  --   cancel-id◃ p q e = lCancelEq
  --     (homotopyNatural ⋆IdL p ∙ cong (_∙ ⋆IdL _) e ∙ sym (homotopyNatural ⋆IdL q))
  --
  --   cancel-▹id : {x y : C₀} {f g : C [ x , y ]} (p q : f ≡ g)
  --     → p ▹ id ≡ q ▹ id → p ≡ q
  --   cancel-▹id p q e = lCancelEq
  --     (homotopyNatural ⋆IdR p ∙ cong (_∙ ⋆IdR _) e ∙ sym (homotopyNatural ⋆IdR q))
  --
  --   -- The left-unitor composition law follows by cancelling two edges
  --   -- of the pentagon for id, id, f, g, using the triangle at id, f.
  --   lUnit-comp : {x y z : C₀} (f : C [ x , y ]) (g : C [ y , z ])
  --     → ⋆Assoc id f g ∙ ⋆IdL (f ⋆ g) ≡ ⋆IdL f ▹ g
  --   lUnit-comp f g = cancel-id◃ _ _
  --     (◃-∙ _ _ ∙ lCancelEq {p = ⋆Assoc id (id ⋆ f) g}
  --       (lCancelEq {p = ⋆Assoc id id f ▹ g}
  --         (cong ((⋆Assoc id id f ▹ g) ∙_)
  --             (assoc (⋆Assoc id (id ⋆ f) g) (id ◃ ⋆Assoc id f g) (id ◃ ⋆IdL (f ⋆ g)))
  --           ∙ assoc (⋆Assoc id id f ▹ g)
  --               (⋆Assoc id (id ⋆ f) g ∙ id ◃ ⋆Assoc id f g) (id ◃ ⋆IdL (f ⋆ g))
  --           ∙ cong (_∙ (id ◃ ⋆IdL (f ⋆ g))) (Bicategory.pentagon C id id f g)
  --           ∙ sym (assoc (⋆Assoc (id ⋆ id) f g) (⋆Assoc id id (f ⋆ g)) (id ◃ ⋆IdL (f ⋆ g)))
  --           ∙ cong (⋆Assoc (id ⋆ id) f g ∙_) (Bicategory.triangle C id (f ⋆ g))
  --           ∙ homotopyNatural (λ k → ⋆Assoc k f g) (⋆IdR id)
  --           ∙ cong (λ p → (p ▹ g) ∙ ⋆Assoc id f g) (sym (Bicategory.triangle C id f))
  --           ∙ cong (_∙ ⋆Assoc id f g) (▹-∙ (⋆Assoc id id f) (id ◃ ⋆IdL f))
  --           ∙ sym (assoc (⋆Assoc id id f ▹ g) ((id ◃ ⋆IdL f) ▹ g) (⋆Assoc id f g))
  --           ∙ cong ((⋆Assoc id id f ▹ g) ∙_) (sym (homotopyNatural (λ k → ⋆Assoc id k g) (⋆IdL f))))))
  --
  --   unit-id : {x : C₀} → ⋆IdL (id {x = x}) ≡ ⋆IdR id
  --   unit-id = cancel-▹id _ _
  --     (sym (lUnit-comp id id)
  --       ∙ cong (⋆Assoc id id id ∙_) (rCancelEq (homotopyNatural ⋆IdL (⋆IdL id)))
  --       ∙ Bicategory.triangle C id id)

  -- module _
  --   (𝟘′ 𝟙′ : C₀)
  --   (step′ : C  [ 𝟘′ , 𝟙′ ])
  --   where
  --
  --   open Pseudofunctor
  --   open IsPseudofunctor
  --   open WildFunctor
  --
  --   Elim : Pseudofunctor Walking C
  --   Elim .str .F-ob 𝟘 = 𝟘′
  --   Elim .str .F-ob 𝟙 = 𝟙′
  --   Elim .str .F-hom {(𝟘)} {(𝟘)} f = id
  --   Elim .str .F-hom {(𝟘)} {(𝟙)} f = step′
  --   Elim .str .F-hom {(𝟙)} {(𝟙)} f = id
  --   Elim .str .F-id {(𝟘)} = refl
  --   Elim .str .F-id {(𝟙)} = refl
  --   Elim .str .F-seq {(𝟘)} {(𝟘)} {z} _ _ = sym (⋆IdL _)
  --   Elim .str .F-seq {(𝟘)} {(𝟙)} {(𝟙)} _ _ = sym (⋆IdR _)
  --   Elim .str .F-seq {(𝟙)} {(𝟙)} {(𝟙)} _ _ = sym (⋆IdR _)
  --   Elim .isPseudofunctor = ?
    -- Elim .isPseudofunctor .F-IdL {(𝟘)} {(𝟘)} =
    --   cong (sym (⋆IdL id) ∙_) (sym (lUnit _)) ∙ lCancel _
    -- Elim .isPseudofunctor .F-IdL {(𝟘)} {(𝟙)} =
    --   cong (sym (⋆IdL step′) ∙_) (sym (lUnit _)) ∙ lCancel _
    -- Elim .isPseudofunctor .F-IdL {(𝟙)} {(𝟙)} =
    --   cong (sym (⋆IdR id) ∙_) (sym (lUnit _) ∙ unit-id) ∙ lCancel _
    -- Elim .isPseudofunctor .F-IdR {(𝟘)} {(𝟘)} =
    --   cong (sym (⋆IdL id) ∙_) (sym (lUnit _) ∙ sym unit-id) ∙ lCancel _
    -- Elim .isPseudofunctor .F-IdR {(𝟘)} {(𝟙)} =
    --   cong (sym (⋆IdR step′) ∙_) (sym (lUnit _)) ∙ lCancel _
    -- Elim .isPseudofunctor .F-IdR {(𝟙)} {(𝟙)} =
    --   cong (sym (⋆IdR id) ∙_) (sym (lUnit _)) ∙ lCancel _
    -- Elim .isPseudofunctor .F-Assoc {(𝟘)} {(𝟘)} {(𝟘)} {(𝟘)} =
    --   cong (sym (⋆IdL id) ∙_)
    --     (shuffleSymL (shuffleSymR (Bicategory.triangle C id id ∙ cong (_▹ id) (sym unit-id))))
    --   ∙ lUnit _
    -- Elim .isPseudofunctor .F-Assoc {(𝟘)} {(𝟘)} {(𝟘)} {(𝟙)} =
    --   cong (sym (⋆IdL step′) ∙_)
    --     (shuffleSymL (shuffleSymR (Bicategory.triangle C id step′ ∙ cong (_▹ step′) (sym unit-id))))
    --   ∙ lUnit _
    -- Elim .isPseudofunctor .F-Assoc {(𝟘)} {(𝟘)} {(𝟙)} {(𝟙)} =
    --   cong (sym (⋆IdR step′) ∙_) (shuffleSymL (shuffleSymR (lUnit-comp step′ id)))
    --   ∙ sym (symDistr (⋆IdL (step′ ⋆ id)) (⋆IdR step′))
    --   ∙ cong sym (homotopyNatural ⋆IdL (⋆IdR step′))
    --   ∙ symDistr (id ◃ ⋆IdR step′) (⋆IdL step′)
    --   ∙ lUnit _
    -- Elim .isPseudofunctor .F-Assoc {(𝟘)} {(𝟙)} {(𝟙)} {(𝟙)} =
    --   cong (sym (⋆IdR step′) ∙_)
    --     (shuffleSymL (shuffleSymR (Bicategory.triangle C step′ id))
    --       ∙ cong (λ p → step′ ◃ sym p) unit-id)
    --   ∙ lUnit _
    -- Elim .isPseudofunctor .F-Assoc {(𝟙)} {(𝟙)} {(𝟙)} {(𝟙)} =
    --   cong (sym (⋆IdR id) ∙_)
    --     (shuffleSymL (shuffleSymR (Bicategory.triangle C id id))
    --       ∙ cong (λ p → id ◃ sym p) unit-id)
    --   ∙ lUnit _
