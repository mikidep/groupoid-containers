open import Cubical.Foundations.Prelude

open import Cubical.Foundations.Function
open import Cubical.Data.Unit

open import Cubical.Container.Base

module Cubical.Container.Monoid.Free_ (F : Container) where

open Container F

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

-- S* := W λ X → Unit + F X
-- cf. T-uncurry

P* : S* → Type
P* = S*-elim (const Type) Unit (λ {s} → Σ (P s))

F* = S* ⊲ P*

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
  
-- record F*-Alg (G : Container) : Type where
--   field
--     η′ : 𝟙 ⇒ G
--     μ′ : G ⊗₀ F ⇒ G

-- Let's see if we can generalise this to
--       H ⇒ G
--   G ⊗ F ⇒ G
--   ----------
--   H ⊗ F* ⇒ G
--
--   i.e. the above with [H/𝟙]

-- module _
--   {G : Container}
--   (Alg : F*-Alg G)
--   where
--
--   open F*-Alg Alg
--   open _⇒_
--   open Container G renaming (S to Sᴳ; P to Pᴳ)
--
--   F*-elim : F* ⇒ G
--   F*-elim = CMor′ F*-elim′
--     where
--     F*-elim′ : F* ⇒′ G
--     F*-elim′ unit = η′ .σ tt , const tt
--     F*-elim′ (sup s ps*) = 
--       -- Looks like a ⟦_⟧₁ ?
--       σ′ , π′ » map-snd (λ {p} → indπ p)
--       where
--       open import Prelude.Utils
--       ind′ : (p : P s) → ⟦ G ⟧₀ (P* (ps* p)) 
--       ind′ p = F*-elim′ (ps* p)
--       ind : P s ⊲ (ps* » P*) ⇒ G
--       ind = CMor′ ind′
--       open _⇒_ ind
--         renaming (σ to indσ; π to indπ)
--       open Σ (CMor′⁻ μ′ (s , indσ)) 
--         renaming (fst to σ′; snd to π′)
--       open import Cubical.Data.Sigma

module _ (H : Container) where
  record F*-Alg (G : Container) : Type where
    field
      η′ : H ⇒ G
      μ′ : G ⊗₀ F ⇒ G

  -- Let's see if we can generalise this to
  --       H ⇒ G
  --   G ⊗ F ⇒ G
  --   ----------
  --   H ⊗ F* ⇒ G
  --
  --   i.e. the above with [H/𝟙]

  module _
    {G : Container}
    (Alg : F*-Alg G)
    where
      
    open F*-Alg Alg
    open _⇒_
    open Container G renaming (S to Sᴳ; P to Pᴳ)
    open Container H renaming (S to Sᴴ; P to Pᴴ)

    -- Usare [un]curry per term. check.
    F*-elim : H ⊗₀ F* ⇒ G
    F*-elim = CMor′ F*-elim′
      where
      F*-elim′ : H ⊗₀ F* ⇒′ G
      F*-elim′ (unit , sᴴ) = η′ .σ (sᴴ tt) , λ pᴳ → tt , η′ .π (sᴴ tt) pᴳ 
      F*-elim′ (sup s ps* , px) =
        -- -- Looks like a ⟦_⟧₁ ?
        σ′ , λ pᴳ → let
            p , pᴳ′ = π′ pᴳ
          in Σ-reassoc (p , indπ p pᴳ′)
        where
        open import Prelude.Utils
        ind′ : (p : P s) 
          → ⟦ G ⟧₀ (Σ (P* (ps* p)) λ p* → Pᴴ (px (p , p*)))
        ind′ p = F*-elim′ (ps* p , λ p* → px (p , p*))
        ind : P s ⊲ (λ z → Σ (P* (ps* z)) (λ p* → Pᴴ (px (z , p*)))) ⇒ G
        ind = CMor′ ind′
        open _⇒_ ind
          renaming (σ to indσ; π to indπ)
        open Σ (CMor′⁻ μ′ (s , indσ)) 
          renaming (fst to σ′; snd to π′)
        open import Cubical.Data.Sigma

-- F* ≃ Id + F ⊗ F*

-- S* is fix (1 + F)
-- P* is S*-elim 1 Σ
-- F* is fix (Id + F ⊗ _)
-- So what's going on here?

-- open import Cubical.Container.Monoid.Definition F*
--
-- private module Free where
--   import Cubical.Container.Constructions as CC
--   open CC.Extent
--   open CC.Morphisms using (id; _⋆_)
--   open CC.Monoidal using (𝟙; _⊗₀_; _⊗₁_)
--   open import Cubical.Container.Path
--   open import Prelude.Shapes
--
--   η : 𝟙 ⇒ F*
--   η = CMor′ λ _ → unit , _
--
--   μ : F* ⊗₀ F* ⇒ F*
--   μ = CMor′ μ′
--     where
--     B : S* → Type
--     B s = _
--     unit′ : B unit
--     unit′ s′ = s′ tt , λ p → _ , p
--     sup′ : {s : S} {ps* : P s → S*} 
--       (ps*′ : (p : P s) → B (ps* p)) → B (sup s ps*)
--     sup′ {s} {ps*} ps*′ s′ = 
--       sup s (λ p → ind p .fst) , sup′-π
--       where
--       ind : (p : P s) → _
--       ind p = ps*′ p (curry s′ p)
--       sup′-π : _
--       sup′-π (p , p*) = Σ-reassoc (p , ind p .snd p*)
--     aux : ∀ s → B s
--     aux = S*-elim B unit′ sup′
--     μ′ : F* ⊗₀ F* ⇒′ F*
--     μ′ = uncurry aux
--
--   lUnit : η ⊗₁ id ⋆ μ ≡ LUnit
--   lUnit = CMor≡′ (uncurry lUnit′)
--     where
--     B : S* → Type
--     B s = _
--     unit′ : B unit
--     unit′ _ = refl
--     sup′ : {s : S} {ps* : P s → S*} 
--       (ps*′ : (p : P s) → B (ps* p)) → B (sup s ps*)
--     sup′ {s} {ps*} ps*′ s′ i = 
--       sup s (λ p → ps*′ p _ i .fst)
--       , λ { (p , p*) → 
--         Σ-reassoc (p , ps*′ p _ i .snd p*) }
--     lUnit′ : _
--     lUnit′ = S*-elim B unit′ sup′
--
--   rUnit : id ⊗₁ η ⋆ μ ≡ RUnit
--   rUnit = CMor≡′ λ _ → refl
--
--   assoc : Assoc ⋆ μ ⊗₁ id ⋆ μ ≡ id ⊗₁ μ ⋆ μ
--   assoc = CMor≡′ (uncurry (uncurry assoc′))
--     where
--     B : S* → Type
--     B s = _
--     unit′ : B unit
--     unit′ s′ s″ = refl
--     sup′ : {s : S} {ps* : P s → S*} 
--       (ps*′ : (p : P s) → B (ps* p)) → B (sup s ps*)
--     sup′ {s} {ps*} ps*′ s′ s″ = goal
--       where
--       ind : (p : P s) → _
--       ind p = ps*′ p (curry s′ p) 
--         (λ p* → s″ (Σ-reassoc (p , p*)))
--       goal : _
--       goal i = 
--         sup s (λ p → ind p i .fst) 
--         , λ { (p , p*) → 
--           ( ( p 
--               , ind p i .snd p* .fst .fst) 
--             , ind p i .snd p* .fst .snd) 
--           , ind p i .snd p* .snd }
--     assoc′ : _
--     assoc′ = S*-elim B unit′ sup′
--
--   import Cubical.WildCat.Instances.Container as WC
--   import Cubical.Bicategory.Base as BB
--   open BB.Whiskering WC.ContainerWildCat
--
--   lrUnit-coh :
--       Square 
--         (id ⊗₁ η ⊗₁ id ◃ assoc)
--         (Assoc ◃ rUnit ⊗₂ refl {x = id} ▹ μ)
--         refl
--         (refl {x = id} ⊗₂ lUnit ▹ μ)
--   lrUnit-coh = CMor□′ lrUnit-coh′
--     where
--     B : S* → Type
--     B s = _
--     aux : ∀ s → B s
--     aux = S*-elim B unit′ sup′
--       where
--       unit′ : B unit
--       unit′ _ s′ = refl 
--       sup′ : {s : S} {ps* : P s → S*} 
--         (ps*′ : (p : P s) → B (ps* p)) → B (sup s ps*)
--       sup′ {s} {ps*} ps*′ _ s′ = goal
--         where
--         ind : (p : P s) → _
--         ind p = ps*′ p _ (uncurry (curry (curry s′) p)) 
--         goal : _
--         goal i j .fst = sup s λ p → ind p i j .fst
--         goal i j .snd (p , p*) =
--           ((p , ind p i j .snd p* .fst .fst) , _) 
--           , ind p i j .snd p* .snd
--     lrUnit-coh′ :
--       Square′ 
--         (id ⊗₁ η ⊗₁ id ◃ assoc)
--         (Assoc ◃ rUnit ⊗₂ refl {x = id} ▹ μ)
--         refl
--         (refl {x = id} ⊗₂ lUnit ▹ μ)
--     lrUnit-coh′ = uncurry (uncurry aux)
--
--   assoc-coh : 
--     Hex
--       (id ⊗₁ Assoc ◃ Assoc ◃ assoc ⊗₂ refl {x = id} ▹ μ)
--       (id ⊗₁ Assoc ◃ id ⊗₁ μ ⊗₁ id ◃ assoc)
--       (refl {x = id} ⊗₂ assoc ▹ μ)
--       refl
--       (Assoc ◃ μ ⊗₁ id ⊗₁ id ◃ assoc)
--       (id ⊗₁ id ⊗₁ μ ◃ assoc)
--   assoc-coh = {! !}
--     -- CMorHex′ assoc-coh′
--     -- where
--     -- B : S* → Type
--     -- B s = _
--     -- aux : ∀ s → B s
--     -- aux = S*-elim B unit′ sup′
--     --   where
--     --   unit″ : 
--     --     (s′ : S*)
--     --     (s″ : P* s′ → S*)
--     --     (s‴ : (p′ : P* s′) → (P* (s″ p′)) → S*)
--     --     → Hex 
--     --       _ _ _ refl _ _ 
--     --   unit″ s′ s″ s‴ .fst = refl
--     --   unit″ s′ s″ s‴ .snd .fst = {! !}
--     --   unit″ s′ s″ s‴ .snd .snd = {! !}
--     --   unit′ : B unit
--     --   unit′ s′ s″ s‴ = 
--     --     {! !}
--     --     -- unit″ (s′ tt) (curry s″ tt) (curry (curry s‴) tt)
--     --   sup′ : {s : S} {ps* : P s → S*} 
--     --     (ps*′ : (p : P s) → B (ps* p)) → B (sup s ps*)
--     --   sup′ {s} {ps*} ps*′ _ s′ = goal
--     --     where
--     --     -- ind : (p : P s) → _
--     --     -- ind p = {! !}
--     --     goal : _
--     --     goal = {! !}
--     -- assoc-coh′ :
--     --   Hex′
--     --     (id ⊗₁ Assoc ◃ Assoc ◃ assoc ⊗₂ refl {x = id} ▹ μ)
--     --     refl
--     --     (Assoc ◃ μ ⊗₁ id ⊗₁ id ◃ assoc)
--     --     (id ⊗₁ id ⊗₁ μ ◃ assoc)
--     -- assoc-coh′ = uncurry (uncurry (uncurry aux))
--
-- Free : Pseudomonoid
-- Free = record { Free }
