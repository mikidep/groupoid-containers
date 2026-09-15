open import Cubical.Foundations.Prelude

open import Cubical.Foundations.Function
open import Cubical.Data.Unit

open import Cubical.Container.Base

module Cubical.Container.Monoid.Free_ (T : Container) where

open Container T

data S* : Type where
  unit : S*
  sup : (s : S) → (ps* : P s → S*) → S*

module _ 
  {ℓ : Level}
  (B : S* → Type ℓ)
  (unit′ : B unit)
  (sup′ : {s : S} {ps* : P s → S*} 
    (ps*′ : (p : P s) → B (ps* p)) → B (sup s ps*))
  where

  S*-elim : ∀ s* → B s*
  S*-elim unit = unit′
  S*-elim (sup s ps*) = sup′ λ p → S*-elim (ps* p)

-- S* := W λ X → Unit + T X
-- cf. T-uncurry

P* : S* → Type
P* = S*-elim (const Type) Unit (λ {s} → Σ (P s))

T* = S* ⊲ P*

open import Cubical.Container.Constructions as CC
open CC.Monoidal using (𝟙; _⊗₀_)
open CC.Extent

module _ {ℓ' ℓ'' : _} {s : S} 
  {B : P s → Type ℓ'} {C : ∀ p → B p → Type ℓ''}
  where
  -- Is this just the default associativity direction of ⊗?
  -- or def. of composite positions
  open import Cubical.Data.Sigma
  open import Cubical.Foundations.Isomorphism
  Σ-reassoc = Σ-assoc-Iso {A = P s} {B} {C} .Iso.inv
  
record T*-Alg (F : Container) : Type where
  field
    η′ : 𝟙 ⇒ F
    μ′ : F ⊗₀ T ⇒ F

module _
  {F : Container}
  (Alg : T*-Alg F)
  where
    
  open T*-Alg Alg
  open _⇒_
  open Container F renaming (S to Sꟳ; P to Pꟳ)

  T*-elim : T* ⇒ F
  T*-elim = CMor′ T*-elim′
    where
    T*-elim′ : T* ⇒′ F
    T*-elim′ unit = η′ .σ tt , const tt
    T*-elim′ (sup s ps*) = 
      sup′ s s′
      , λ pꟳ → let 
          π′ = μ′ .π (s , s′)
          p = π′ pꟳ .fst
          p* = π′ pꟳ .snd
        in p , ind p .snd p*
      where
      sup′ = curry (μ′ .σ)
      ind : (p : P s) → ⟦ F ⟧₀ (P* (ps* p)) 
      ind p = T*-elim′ (ps* p)
      s′ : P s → Sꟳ
      s′ p = ind p .fst

-- T* ≃ Id + T ⊗ T*

-- S* is fix (1 + T)
-- P* is S*-elim 1 Σ
-- T* is fix (Id + T ⊗ _)
-- So what's going on here?

open import Cubical.Container.Monoid.Definition T*

private module Free where
  import Cubical.Container.Constructions as CC
  open CC.Extent
  open CC.Morphisms using (id; _⋆_)
  open CC.Monoidal using (𝟙; _⊗₀_; _⊗₁_)
  open import Cubical.Container.Path
  open import Prelude.Shapes

  η : 𝟙 ⇒ T*
  η = CMor′ λ _ → unit , _

  μ : T* ⊗₀ T* ⇒ T*
  μ = CMor′ μ′
    where
    B : S* → Type
    B s = _
    unit′ : B unit
    unit′ s′ = s′ tt , λ p → _ , p
    sup′ : {s : S} {ps* : P s → S*} 
      (ps*′ : (p : P s) → B (ps* p)) → B (sup s ps*)
    sup′ {s} {ps*} ps*′ s′ = 
      sup s (λ p → ind p .fst) , sup′-π
      where
      ind : (p : P s) → _
      ind p = ps*′ p (curry s′ p)
      sup′-π : _
      sup′-π (p , p*) = Σ-reassoc (p , ind p .snd p*)
    aux : ∀ s → B s
    aux = S*-elim B unit′ sup′
    μ′ : T* ⊗₀ T* ⇒′ T*
    μ′ = uncurry aux

  lUnit : η ⊗₁ id ⋆ μ ≡ LUnit
  lUnit = CMor≡′ (uncurry lUnit′)
    where
    B : S* → Type
    B s = _
    unit′ : B unit
    unit′ _ = refl
    sup′ : {s : S} {ps* : P s → S*} 
      (ps*′ : (p : P s) → B (ps* p)) → B (sup s ps*)
    sup′ {s} {ps*} ps*′ s′ i = 
      sup s (λ p → ps*′ p _ i .fst)
      , λ { (p , p*) → 
        Σ-reassoc (p , ps*′ p _ i .snd p*) }
    lUnit′ : _
    lUnit′ = S*-elim B unit′ sup′

  rUnit : id ⊗₁ η ⋆ μ ≡ RUnit
  rUnit = CMor≡′ λ _ → refl

  assoc : Assoc ⋆ μ ⊗₁ id ⋆ μ ≡ id ⊗₁ μ ⋆ μ
  assoc = CMor≡′ (uncurry (uncurry assoc′))
    where
    B : S* → Type
    B s = _
    unit′ : B unit
    unit′ s′ s″ = refl
    sup′ : {s : S} {ps* : P s → S*} 
      (ps*′ : (p : P s) → B (ps* p)) → B (sup s ps*)
    sup′ {s} {ps*} ps*′ s′ s″ = goal
      where
      ind : (p : P s) → _
      ind p = ps*′ p (curry s′ p) 
        (λ p* → s″ (Σ-reassoc (p , p*)))
      goal : _
      goal i = 
        sup s (λ p → ind p i .fst) 
        , λ { (p , p*) → 
          ( ( p 
              , ind p i .snd p* .fst .fst) 
            , ind p i .snd p* .fst .snd) 
          , ind p i .snd p* .snd }
    assoc′ : _
    assoc′ = S*-elim B unit′ sup′

  import Cubical.WildCat.Instances.Container as WC
  import Cubical.Bicategory.Base as BB
  open BB.Whiskering WC.ContainerWildCat

  lrUnit-coh :
      Square 
        (id ⊗₁ η ⊗₁ id ◃ assoc)
        (Assoc ◃ rUnit ⊗₂ refl {x = id} ▹ μ)
        refl
        (refl {x = id} ⊗₂ lUnit ▹ μ)
  lrUnit-coh = CMor□′ lrUnit-coh′
    where
    B : S* → Type
    B s = _
    aux : ∀ s → B s
    aux = S*-elim B unit′ sup′
      where
      unit′ : B unit
      unit′ _ s′ = refl 
      sup′ : {s : S} {ps* : P s → S*} 
        (ps*′ : (p : P s) → B (ps* p)) → B (sup s ps*)
      sup′ {s} {ps*} ps*′ _ s′ = goal
        where
        ind : (p : P s) → _
        ind p = ps*′ p _ (uncurry (curry (curry s′) p)) 
        goal : _
        goal i j .fst = sup s λ p → ind p i j .fst
        goal i j .snd (p , p*) =
          ((p , ind p i j .snd p* .fst .fst) , _) 
          , ind p i j .snd p* .snd
    lrUnit-coh′ :
      Square′ 
        (id ⊗₁ η ⊗₁ id ◃ assoc)
        (Assoc ◃ rUnit ⊗₂ refl {x = id} ▹ μ)
        refl
        (refl {x = id} ⊗₂ lUnit ▹ μ)
    lrUnit-coh′ = uncurry (uncurry aux)

  assoc-coh : 
    Hex
      (id ⊗₁ Assoc ◃ Assoc ◃ assoc ⊗₂ refl {x = id} ▹ μ)
      (id ⊗₁ Assoc ◃ id ⊗₁ μ ⊗₁ id ◃ assoc)
      (refl {x = id} ⊗₂ assoc ▹ μ)
      refl
      (Assoc ◃ μ ⊗₁ id ⊗₁ id ◃ assoc)
      (id ⊗₁ id ⊗₁ μ ◃ assoc)
  assoc-coh = {! !}
    -- CMorHex′ assoc-coh′
    -- where
    -- B : S* → Type
    -- B s = _
    -- aux : ∀ s → B s
    -- aux = S*-elim B unit′ sup′
    --   where
    --   unit″ : 
    --     (s′ : S*)
    --     (s″ : P* s′ → S*)
    --     (s‴ : (p′ : P* s′) → (P* (s″ p′)) → S*)
    --     → Hex 
    --       _ _ _ refl _ _ 
    --   unit″ s′ s″ s‴ .fst = refl
    --   unit″ s′ s″ s‴ .snd .fst = {! !}
    --   unit″ s′ s″ s‴ .snd .snd = {! !}
    --   unit′ : B unit
    --   unit′ s′ s″ s‴ = 
    --     {! !}
    --     -- unit″ (s′ tt) (curry s″ tt) (curry (curry s‴) tt)
    --   sup′ : {s : S} {ps* : P s → S*} 
    --     (ps*′ : (p : P s) → B (ps* p)) → B (sup s ps*)
    --   sup′ {s} {ps*} ps*′ _ s′ = goal
    --     where
    --     -- ind : (p : P s) → _
    --     -- ind p = {! !}
    --     goal : _
    --     goal = {! !}
    -- assoc-coh′ :
    --   Hex′
    --     (id ⊗₁ Assoc ◃ Assoc ◃ assoc ⊗₂ refl {x = id} ▹ μ)
    --     refl
    --     (Assoc ◃ μ ⊗₁ id ⊗₁ id ◃ assoc)
    --     (id ⊗₁ id ⊗₁ μ ◃ assoc)
    -- assoc-coh′ = uncurry (uncurry (uncurry aux))

Free : Pseudomonoid
Free = record { Free }
