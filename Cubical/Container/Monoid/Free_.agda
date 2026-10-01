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

module _ 
  {ℓ : Level}
  (B : Type ℓ)
  (unit′ : B)
  (sup′ : {s : S} (ps*′ : P s → B) → B)
  where

  S*-rec : S* → B
  S*-rec = S*-elim (const B) unit′ sup′

module Irec 
  {ℓ : Level}
  (B : I → Type ℓ)
  (unit′ : ∀ i → B i)
  (sup′ : ∀ i → {s : S} (ps*′ : ∀ j → P s → B j) → B i)
  where

  IS*-rec : S* → ∀ i → B i
  IS*-rec unit i = unit′ i
  IS*-rec (sup s ps*) i = sup′ i λ j p → IS*-rec (ps* p) j

-- module _ 
--   {ℓ : Level}
--   (B : Type ℓ)
--   (unit′ : B)
--   (sup′ : {s : S} (ps*′ : P s → B) → B)
--   (rec′ : S* → B)
--   where
--
--   open Irec
--
--   S*-rec-init : 
--     -- qualcosa
--     --  →
--     rec′ ≡ S*-rec B unit′ sup′
--   S*-rec-init = funExt λ s i → IS*-rec {! !} {! !} {! !} s ?
--
--
--
-- S* := W λ X → Unit + F X
-- cf. T-uncurry

P* : S* → Type
P* = S*-rec Type Unit (λ {s} → Σ (P s))

F* = S* ⊲ P*

open import Cubical.Container.Constructions as CC
open CC.Monoidal using (𝟙; _⊗₀_)
open CC.Extent

open import Cubical.Data.Sigma
open import Prelude.Utils

module _ {ℓ' ℓ'' : _} {s : S} 
  {B : P s → Type ℓ'} {C : ∀ p → B p → Type ℓ''}
  where
  open import Cubical.Foundations.Isomorphism
  Σ-reassoc = Σ-assoc-Iso {A = P s} {B} {C} .Iso.inv
  
module F*-Rec where
  record F*-Alg (G : Container) : Type where
    field
      η′ : 𝟙 ⇒ G
      μ′ : G ⊗₀ F ⇒ G

  record F*-Alg′ (G : Container) : Type where
    field
      η′ : 𝟙 ⇒′ G
      μ′ : G ⊗₀ F ⇒′ G

  fold′ : F*-Alg′ F*
  fold′ = record where
    η′ s = unit , const s 
    μ′ (s , s′) = sup s s′ , idfun _ 
  
  open import Cubical.Data.Sum
  𝟙+_⨾F : (G : Container) → Container 
  𝟙+ G ⨾F = record where
    open Container (G ⊗₀ F)
      renaming (S to S⨾; P to P⨾)
    S = Unit ⊎ S⨾
    P = λ where
      (inl tt) → Unit
      (inr s⨾) → P⨾ s⨾

  𝟙+F⨾ : (G : Container) → Container 
  𝟙+F⨾ G = record where
    open Container (F ⊗₀ G)
      renaming (S to S⨾; P to P⨾)
    S = Unit ⊎ S⨾
    P = λ where
      (inl tt) → Unit
      (inr s⨾) → P⨾ s⨾

  module _ {G H : Container} (α : G ⇒′ H) where
  
    open Container G renaming (S to Sᴳ; P to Pᴳ)
    open Container H renaming (S to Sᴴ; P to Pᴴ)

    F⨾-map : G ⊗₀ F ⇒′ H ⊗₀ F
    F⨾-map (s , s′) = (s , s′ » α » fst) 
      , uncurry λ p p′ → p , (s′ » α » snd) p p′

    𝟙+-⨾F-map : 𝟙+ G ⨾F ⇒′ 𝟙+ H ⨾F
    𝟙+-⨾F-map (inl tt) = inl tt , idfun Unit
    𝟙+-⨾F-map (inr (s , s′)) = inr (s , s′ » α » fst) 
      , uncurry λ p p′ → p , (s′ » α » snd) p p′

    𝟙+F⨾-map : 𝟙+F⨾ G  ⇒′ 𝟙+F⨾ H
    𝟙+F⨾-map (inl tt) = inl tt , idfun Unit
    𝟙+F⨾-map (inr (s , s′)) = inr (α s .fst , α s .snd » s′) 
      -- map-fst?
      , uncurry λ p p′ → α s .snd p , p′

  unfold′ : F* ⇒′ 𝟙+ F* ⨾F
  unfold′ unit = inl tt , idfun Unit
  unfold′ (sup s ps*) = inr (s , ps*) , idfun _

  -- unfold″ : F* ⇒′ 𝟙+F⨾ F*
  -- unfold″ = S*-elim B unit′ sup′
  --   where
  --   B : S* → Type
  --   B = (F* ⇒ₛ 𝟙+F⨾ F*)
  --   unit′ : B  unit
  --   unit′ = inl tt , idfun Unit
  --   sup′ : ∀ {s : S} {ps* : P s → S*} 
  --     (ps*′ : (p : P s) → B (ps* p))
  --     → B (sup s ps*)
  --   sup′ {s} {ps*} ind = ?
  --     where
  --     inds : (p : P s) → _
  --     inds p = {! ind p .fst  !}

  -- unfold″ unit = inl tt , idfun Unit
  -- unfold″ (sup s ps*) = inr ({! !} , {! !}) , {! !}
  --   where
  --   ind : (p : P s) → ?
  --   ind p = unfold″ (ps* p)

  module Elim′
    {G : Container}
    (Alg : F*-Alg′ G)
    where

    open F*-Alg′ Alg
    open Container G renaming (S to Sᴳ; P to Pᴳ)

    -- F*-rec′ : F* ⇒′ G
    -- F*-rec′ unit = η′ tt
    -- F*-rec′ (sup s ps*) = 
    --   -- Looks like a ⟦_⟧₁ ?
    --   μσ , μπ » map-snd (λ {p} → ind p .snd)
    --   where
    --   X : Container
    --   X = record where
    --     S = P s
    --     P p = P* (ps* p)
    --   ind : X ⇒′ G
    --   ind p = F*-rec′ (ps* p)
    --   open Σ (μ′ (s , ind » fst)) 
    --     renaming (fst to μσ; snd to μπ)

    module _ {F G H : Container} where
      infixr 20 _⋆′_
      _⋆′_ : F ⇒′ G → G ⇒′ H → F ⇒′ H
      (α ⋆′ β) s = 
        β (α s .fst) .fst
        , β (α s .fst) .snd » α s .snd

    -- F ⇒′ G ≡ (s : S) → ⟦ G ⟧ (P s)
    F*-rec′ : F* ⇒′ G
    F*-rec′ = S*-elim B unit′ sup′
      where
      B : _
      B = F* ⇒ₛ G
      unit′ : B unit
      unit′ = η′ tt
      sup′ : ∀ {s : S} {ps* : P s → S*} 
        (ps*′ : (p : P s) → B (ps* p))
        → B (sup s ps*)
      sup′ {s} {ps*} ps*′ = goal
        where
        X : Container
        X = record where
          S = P s
          P p = P* (ps* p)
        ind : X ⇒′ G
        ind = ps*′ 
        μ′∙ : ⟦ G ⟧₀ (Σ[ p ∈ P s ] (Pᴳ (ind p .fst)))
        μ′∙ = μ′ (s , ind » fst)
        μσ : Sᴳ
        μσ = μ′∙ .fst
        μπ : Pᴳ μσ → Σ[ p ∈ P s ] (Pᴳ (ind p .fst))
        μπ = μ′∙ .snd
        -- goalπ : Pᴳ μσ → P* (sup s ps*)
        goalπ : Pᴳ μσ → Σ[ p ∈ P s ] (P* (ps* p))
        goalπ = μπ » λ where
          (p , pᴳ) → p , ind p .snd pᴳ
        goal : (F* ⇒ₛ G) (sup s ps*)
        goal =
          μσ , μπ » map-snd (λ {p} → ind p .snd)
        -- goal = (unfold′ ⋆′ {! !} ⋆′ xx ⋆′ μ′) (sup s ps*)

    F*-rec : F* ⇒ G
    F*-rec = CMor′ F*-rec′

module F*-Rec-Parm (H : Container) where
  record F*-Alg (G : Container) : Type where
    field
      η′ : H ⇒ G
      μ′ : G ⊗₀ F ⇒ G

  record F*-Alg′ (G : Container) : Type where
    field
      η′ : H ⇒′ G
      μ′ : G ⊗₀ F ⇒′ G

  -- We can generalise the above to
  --       H ⇒ G
  --   G ⊗ F ⇒ G
  --   ----------
  --   H ⊗ F* ⇒ G
  --
  --   i.e. the above with [H/𝟙]

  -- TODO: read https://philipsaville.co.uk/fscd2017.pdf

  module Rec′
    {G : Container}
    (Alg : F*-Alg′ G)
    where
      
    open F*-Alg′ Alg
    open Container G renaming (S to Sᴳ; P to Pᴳ)
    open Container H renaming (S to Sᴴ; P to Pᴴ)

    F*-rec′ : H ⊗₀ F* ⇒′ G
    F*-rec′ = uncurry goal
      where
      goal : 
        (s* : S*) 
        (→sᴴ : P* s* → Sᴴ) 
        → (H ⊗₀ F* ⇒ₛ G) (s* , →sᴴ)
      goal unit →sᴴ = ησ , λ pᴳ → tt , ηπ pᴳ
        where
        open Σ (η′ (→sᴴ tt)) renaming (fst to ησ; snd to ηπ)
      goal (sup s ps*) →sᴴ = μσ , λ pᴳ → 
        -- somehow sequencing μπ then ind .snd?
        let
          p , pᴳ′ = μπ pᴳ
        in Σ-reassoc (p , ind p .snd pᴳ′)
        where
        open import Prelude.Utils
        -- X is a container which can be defined when fixing
        -- the shape of the first branching
        X : Container
        X = record where
          open Container (H ⊗₀ F*) using ()
            renaming (P to PH*)
          -- A shape is a position in the first branching
          S = P s
          -- A position is a position in the sub-tree
          -- including the last H-branch
          -- P p = Σ (P* (ps* p)) (λ p* → Pᴴ (→sᴴ (p , p*)))
          P p = PH* (ps* p , curry →sᴴ p)
        ind : X ⇒′ G
        ind p = goal (ps* p) (curry →sᴴ p)
        open Σ (μ′ (s , ind » fst)) 
          renaming (fst to μσ; snd to μπ)
  
    -- F*-rec′ : H ⊗₀ F* ⇒′ G
    -- F*-rec′ = uncurry goal
    --   where
    --   B : S* → Type
    --   B s* =
    --     (→sᴴ : P* s* → Sᴴ) 
    --     → (H ⊗₀ F* ⇒ₛ G) (s* , →sᴴ)
    --   unit′ : B unit
    --   unit′ →sᴴ = ησ , λ pᴳ → tt , ηπ pᴳ
    --     where
    --     open Σ (η′ (→sᴴ tt)) 
    --       renaming (fst to ησ; snd to ηπ)
    --   goal : 
    --     (s* : S*) 
    --     (→sᴴ : P* s* → Sᴴ) 
    --     → (H ⊗₀ F* ⇒ₛ G) (s* , →sᴴ)
    --   goal = S*-elim B unit′ {! !}

    F*-rec : H ⊗₀ F* ⇒ G
    F*-rec = CMor′ F*-rec′

open import Cubical.Container.Monoid.Definition F*

private module Free where
  import Cubical.Container.Constructions as CC
  open CC.Extent
  open CC.Morphisms using (id; _⋆_)
  open CC.Monoidal using (𝟙; _⊗₀_; _⊗₁_)
  open import Cubical.Container.Path
  open import Prelude.Shapes

  η : 𝟙 ⇒ F*
  η = CMor′ λ _ → unit , _

  μ : F* ⊗₀ F* ⇒ F*
  μ = CMor′ goal
    where
    open F*-Rec-Parm F*
    open Rec′
    open F*-Alg′
    alg : F*-Alg′ F*
    alg .η′ = CMor′⁻ id
    alg .μ′ (s , s′) = sup s s′ , idfun _

    goal : F* ⊗₀ F* ⇒′ F* 
    goal = F*-rec′ alg

  -- -- I → 𝟙 ⊗₀ F* ⇒′ F*
  -- lUnitI : η ⊗₁ id ⋆ μ ≡ LUnit
  -- lUnitI i = {! F*-rec alg !}
  --   where
  --   open F*-Rec-Parm 𝟙
  --   open Rec′
  --   open F*-Alg′
  --   alg : F*-Alg′ F*
  --   alg .η′ _ = unit , λ _ → tt
  --   alg .μ′ (s , s′) = sup s s′ , idfun _

  -- P : Type
  -- α : 1 + P → P
  -- f : ℕ → P   1 + (-) alg. morph.
  -- -------------------------------
  -- Path (ℕ-rec α) f

  -- could be something like that?
 
  lUnit : η ⊗₁ id ⋆ μ ≡ LUnit
  lUnit = CMor≡′ (uncurry lUnit′)
    where
    LUnit′ = CMor′⁻ LUnit
    B : S* → Type
    B s = (p : P* s → Unit) 
      → Path
        ((𝟙 ⊗₀ F* ⇒ₛ F*) (s , const tt))
        (CMor′⁻ (η ⊗₁ id ⋆ μ) (s , const ttη ⊗₁ id ⋆ μ)) 
        (LUnit′ (s , const tt))
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
