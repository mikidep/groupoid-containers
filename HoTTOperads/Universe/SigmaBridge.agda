{-# OPTIONS --cubical --no-import-sorts #-}

-- Generic (FreeOps-free) Σ-bridge for the associativity coherence.  This is
-- the universe-level core of `Free/HIT.agda`'s `graft-assoc` node case,
-- abstracted over the four index families `(A' , B' , B , C)` so it is
-- proved ONCE over abstract parameters (small neutral terms) and then
-- instantiated cheaply at concrete families (instantiating a proven lemma
-- does not re-normalise its proof).  Used by `Free/HIT` (the node case) and
-- `Monad.TwoCellCoherence` (the pentagon's `⟨σ-bridge⟩`).
module HoTTOperads.Universe.SigmaBridge where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (homotopyNatural)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Transport using (substComposite)
open import Cubical.Foundations.GroupoidLaws
  using (lCancel ; rUnit ; lUnit ; assoc ; congFunct ; symDistr)
open import Cubical.Foundations.Univalence using (uaβ ; pathToEquiv)
open import Cubical.Data.Sigma using (_,_ ; fst ; snd ; Σ ; ΣPathP)
open import Cubical.Data.Sigma.Properties
  using (Σ-cong-equiv-snd ; Σ-cong-equiv-fst ; Σ-assoc-≃)

open import HoTTOperads.Universe.Base
open import HoTTOperads.Universe.Derived
open import HoTTOperads.Universe.IRDerived
open import HoTTOperads.Universe.Assoc
  using ( adj-coh ; ⅀-subst-path ; transp-⅀-subst-path
        ; Assoc-cont ; Assoc-cont-at-pair
        ; step-Assoc-on-pair ; transp-⅀AssocD-pair )

private
  variable
    ℓc ℓe : Level

module _ {𝒰 : Universe ℓc ℓe} where
  open Universe 𝒰

  -- The four abstract index families.  (In `Free/HIT` `A' , B'` come from
  -- the `node A' B' k ts'` pattern and `B , C` from `graft-assoc`'s
  -- parameters; in `TwoCellCoherence` they instantiate `Index w , Bj ,
  -- Bᶜ , Cnᶜ`.)  Proved here over the abstract families (small neutral
  -- terms) and instantiated cheaply at the use sites.
  module Fam (A' : Code) (B' : El A' → Code)
             (B : El (⅀ A' B') → Code)
             (C : (ab : El (⅀ A' B')) → El (B ab) → Code) where

   -- The explicit Σ-pre-image used everywhere `⅀AssocD A' B' _` is unfolded.
   paired : (a' : El A') → El (B' a') → El (⅀ A' B')
   paired a' b' = invEq (⟦⅀⟧ A' B') (a' , b')

   -- Intermediate index family: each `a' : El A'` fibre is `⅀ (B' a') (B ∘ paired a')`.
   B'' : El A' → Code
   B'' a' = ⅀ (B' a') (λ b' → B (paired a' b'))

   -- Transport along `⅀AssocD 𝒰 A' B' B`.
   transp-⅀AB : El (⅀ A' B'') → El (⅀ (⅀ A' B') B)
   transp-⅀AB = transport (cong El (⅀AssocD 𝒰 A' B' B))

   -- The post-`⅀AssocD` codomain on `B''`.
   C1 : El (⅀ A' B'') → Code
   C1 z = ⅀Assoc-C' (⅀ A' B') B C (transp-⅀AB z)

   -- Uncurried view of `C` at the top Σ-level (over `⅀ A' B'`).
   C-curry-top : Σ (El (⅀ A' B')) (λ ab → El (B ab)) → Code
   C-curry-top (ab , b'') = C ab b''

   -- LHS-side / RHS-side per-fibre index families.
   B-LHS : El A' → Code
   B-LHS a' = ⅀ (B' a') (λ b' → ⅀ (B (paired a' b')) (C (paired a' b')))

   B-RHS : El A' → Code
   B-RHS a' = ⅀ (B'' a') (λ b' → C1 (invEq (⟦⅀⟧ A' B'') (a' , b')))

   -- The two Code paths `bridge-node` equates.
   LHS-path : ⅀ A' B-LHS ≡ ⅀ (⅀ (⅀ A' B') B) (⅀Assoc-C' (⅀ A' B') B C)
   LHS-path = ⅀AssocD 𝒰 A' B' (λ a → ⅀ (B a) (C a))
            ∙ Inj (⅀Assoc≃ (⅀ A' B') B C)

   RHS-path-tail : ⅀ A' B-RHS ≡ ⅀ (⅀ (⅀ A' B') B) (⅀Assoc-C' (⅀ A' B') B C)
   RHS-path-tail = ⅀AssocD 𝒰 A' B'' C1
                 ∙ ⅀-subst-path 𝒰 (⅀AssocD 𝒰 A' B' B)
                                  (⅀Assoc-C' (⅀ A' B') B C)

   -- The mid-level family and its `⟦⅀⟧`-destructurings.
   C'-out : (a : El A') → El (B' a) → Code
   C'-out a b = ⅀ (B (paired a b)) (C (paired a b))

   b-of-LHS : (a : El A') (z : El (B-LHS a)) → El (B' a)
   b-of-LHS a z = fst (equivFun (⟦⅀⟧ (B' a) (C'-out a)) z)

   w-of-LHS : (a : El A') (z : El (B-LHS a)) → El (C'-out a (b-of-LHS a z))
   w-of-LHS a z = snd (equivFun (⟦⅀⟧ (B' a) (C'-out a)) z)

   a-of-x : El (⅀ A' B-LHS) → El A'
   a-of-x x = fst (equivFun (⟦⅀⟧ A' B-LHS) x)

   z-of-x : (x : El (⅀ A' B-LHS)) → El (B-LHS (a-of-x x))
   z-of-x x = snd (equivFun (⟦⅀⟧ A' B-LHS) x)

   -- The canonical Σ-form both LHS and RHS chains reduce to.
   canonical-form : (a : El A') (z : El (B-LHS a))
                  → El (⅀ (⅀ (⅀ A' B') B) (⅀Assoc-C' (⅀ A' B') B C))
   canonical-form a z =
     Assoc-cont 𝒰 (⅀ A' B') B C (paired a (b-of-LHS a z) , w-of-LHS a z)

   -- RHS-side intermediate family and its `⟦⅀⟧`-destructurings.
   C1'-out : (a : El A') → El (B'' a) → Code
   C1'-out a b = C1 (invEq (⟦⅀⟧ A' B'') (a , b))

   b-of-RHS : (a : El A') (z : El (B-RHS a)) → El (B'' a)
   b-of-RHS a z = fst (equivFun (⟦⅀⟧ (B'' a) (C1'-out a)) z)

   w-of-RHS : (a : El A') (z : El (B-RHS a)) → El (C1'-out a (b-of-RHS a z))
   w-of-RHS a z = snd (equivFun (⟦⅀⟧ (B'' a) (C1'-out a)) z)

   -- Per-fibre destructuring of `z : El (B'' a')`.
   module _ (a' : El A') (z : El (B'' a')) where
     b'-of : El (B' a')
     b'-of = fst (equivFun (⟦⅀⟧ (B' a') (λ b' → B (paired a' b'))) z)
     c'-of : El (B (paired a' b'-of))
     c'-of = snd (equivFun (⟦⅀⟧ (B' a') (λ b' → B (paired a' b'))) z)

   -- The `⅀AssocD`-internal intermediate family and its `retEq`-correction.
   C-int : (a : El A') → El (B' a) → Code
   C-int a b = B (paired a b)

   C'-eq : ⅀Assoc-C' A' B' C-int ≡ B
   C'-eq = funExt (λ x → cong B (retEq (⟦⅀⟧ A' B') x))

   transp-C'-eq : El (⅀ (⅀ A' B') (⅀Assoc-C' A' B' C-int))
                → El (⅀ (⅀ A' B') B)
   transp-C'-eq = transport (cong (λ F → El (⅀ (⅀ A' B') F)) C'-eq)

   -- Destructuring of `w : El (C'-out a b)`.
   b''-of : (a : El A') (b : El (B' a)) (w : El (C'-out a b))
          → El (B (paired a b))
   b''-of a b w = fst (equivFun (⟦⅀⟧ (B (paired a b)) (C (paired a b))) w)

   c''-of : (a : El A') (b : El (B' a)) (w : El (C'-out a b))
          → El (C (paired a b) (b''-of a b w))
   c''-of a b w = snd (equivFun (⟦⅀⟧ (B (paired a b)) (C (paired a b))) w)

   -- The `subst`-shifted `c`-component arising inside the per-fibre `Assoc-cont`.
   shifted-c''-per-fibre
     : (a : El A') (b : El (B' a)) (w : El (C'-out a b))
     → El (⅀Assoc-C' (B' a) (λ b' → B (paired a b'))
                             (λ b' b'' → C (paired a b') b'')
                      (invEq (⟦⅀⟧ (B' a) (λ b' → B (paired a b')))
                             (b , b''-of a b w)))
   shifted-c''-per-fibre a b w =
     subst (λ p → El (C (paired a (fst p)) (snd p)))
           (sym (secEq (⟦⅀⟧ (B' a) (λ b' → B (paired a b')))
                       (b , b''-of a b w)))
           (c''-of a b w)

   -- `transp-⅀AB` factors through `transp-C'-eq ∘ Assoc-cont` (`congFunct`/
   -- `substComposite` split + the §5 toolkit `step-Assoc-on-pair`).
   opaque
     transp-⅀AB-factored : (a' : El A') (z : El (B'' a'))
                         → transp-⅀AB (invEq (⟦⅀⟧ A' B'') (a' , z))
                         ≡ transp-C'-eq (Assoc-cont 𝒰 A' B' C-int (a' , z))
     transp-⅀AB-factored a' z =
         cong (λ p → transport p (invEq (⟦⅀⟧ A' B'') (a' , z)))
              (congFunct El (Inj (⅀Assoc≃ A' B' C-int))
                            (cong (⅀ (⅀ A' B')) C'-eq))
       ∙ substComposite (λ X → X)
                        (cong El (Inj (⅀Assoc≃ A' B' C-int)))
                        (cong El (cong (⅀ (⅀ A' B')) C'-eq))
                        (invEq (⟦⅀⟧ A' B'') (a' , z))
       ∙ cong transp-C'-eq (step-Assoc-on-pair 𝒰 A' B' C-int (a' , z))

   -- The `subst`-shifted `c`-component arising when `Assoc-cont A' B' C-int
   -- (a' , z)` unfolds along its inverse-`Σ-cong-equiv-fst` step.
   substed-c-of : (a' : El A') (z : El (B'' a'))
                → El (⅀Assoc-C' A' B' C-int (paired a' (b'-of a' z)))
   substed-c-of a' z =
     subst (λ ab → El (C-int (fst ab) (snd ab)))
           (sym (secEq (⟦⅀⟧ A' B') (a' , b'-of a' z)))
           (c'-of a' z)

   -- `transp-C'-eq` on a canonical pair lands in another canonical pair with
   -- `snd` transported along `funExt⁻ C'-eq` (`⟦⅀⟧-natural-snd` + `secEq`).
   opaque
     transp-C'-eq-on-canonical
       : (a' : El A') (z : El (B'' a'))
       → transp-C'-eq (invEq (⟦⅀⟧ (⅀ A' B') (⅀Assoc-C' A' B' C-int))
                              (paired a' (b'-of a' z) , substed-c-of a' z))
       ≡ invEq (⟦⅀⟧ (⅀ A' B') B)
               ( paired a' (b'-of a' z)
               , transport (cong El (funExt⁻ C'-eq (paired a' (b'-of a' z))))
                           (substed-c-of a' z))
     transp-C'-eq-on-canonical a' z =
         cong (λ e → equivFun e
                       (invEq (⟦⅀⟧ (⅀ A' B') (⅀Assoc-C' A' B' C-int))
                              (paired a' (b'-of a' z) , substed-c-of a' z)))
              (⟦⅀⟧-natural-snd 𝒰 (⅀ A' B') C'-eq)
       ∙ cong (λ p → invEq (⟦⅀⟧ (⅀ A' B') B)
                           ( fst p
                           , transport (cong El (funExt⁻ C'-eq (fst p)))
                                       (snd p)))
              (secEq (⟦⅀⟧ (⅀ A' B') (⅀Assoc-C' A' B' C-int))
                     (paired a' (b'-of a' z) , substed-c-of a' z))

   -- `equivFun ⟦⅀⟧` of a canonical `transp-⅀AB`-image recovers the explicit
   -- Σ-pair (`transp-⅀AB-factored` ∙ `transp-C'-eq-on-canonical` ∙ `secEq`).
   opaque
     ⟦⅀⟧-on-transp : (a' : El A') (z : El (B'' a'))
                   → equivFun (⟦⅀⟧ (⅀ A' B') B)
                              (transp-⅀AB (invEq (⟦⅀⟧ A' B'') (a' , z)))
                   ≡ ( paired a' (b'-of a' z)
                     , transport (cong El (funExt⁻ C'-eq
                                             (paired a' (b'-of a' z))))
                                 (substed-c-of a' z))
     ⟦⅀⟧-on-transp a' z =
         cong (equivFun (⟦⅀⟧ (⅀ A' B') B))
              (transp-⅀AB-factored a' z ∙ transp-C'-eq-on-canonical a' z)
       ∙ secEq (⟦⅀⟧ (⅀ A' B') B) _

   -- `funExt⁻ C'-eq` at `paired a' (b'-of a' z)` is the `secEq`-image of
   -- `C-int`'s fibre (via the adjunction coherence `adj-coh`).
   opaque
     key-eq : (a' : El A') (z : El (B'' a'))
            → cong El (funExt⁻ C'-eq (paired a' (b'-of a' z)))
            ≡ cong (λ ab → El (C-int (fst ab) (snd ab)))
                   (secEq (⟦⅀⟧ A' B') (a' , b'-of a' z))
     key-eq a' z = cong (cong (λ x → El (B x)))
                        (sym (adj-coh (⟦⅀⟧ A' B') (a' , b'-of a' z)))

   -- Recovers `c'-of` from `substed-c-of` by transporting along `funExt⁻
   -- C'-eq` (the two subst paths are inverse modulo `key-eq`).
   opaque
     c'-of-eq : (a' : El A') (z : El (B'' a'))
              → c'-of a' z
              ≡ transport (cong El (funExt⁻ C'-eq (paired a' (b'-of a' z))))
                          (substed-c-of a' z)
     c'-of-eq a' z =
         sym (transportRefl (c'-of a' z))
       ∙ cong (λ p → transport p (c'-of a' z))
              (sym (lCancel (cong (λ ab → El (C-int (fst ab) (snd ab)))
                                   (secEq (⟦⅀⟧ A' B') (a' , b'-of a' z)))))
       ∙ cong (λ p → transport
                       (cong (λ ab → El (C-int (fst ab) (snd ab)))
                             (sym (secEq (⟦⅀⟧ A' B')
                                         (a' , b'-of a' z))) ∙ p)
                       (c'-of a' z))
              (sym (key-eq a' z))
       ∙ substComposite (λ X → X)
                        (cong (λ ab → El (C-int (fst ab) (snd ab)))
                              (sym (secEq (⟦⅀⟧ A' B') (a' , b'-of a' z))))
                        (cong El (funExt⁻ C'-eq (paired a' (b'-of a' z))))
                        (c'-of a' z)

   -- The LHS-side and RHS-side codomain families on `B'' a'` agree
   -- (`c'-of-eq`-shift on `snd`, then `sym ⟦⅀⟧-on-transp`).
   opaque
     snd-adjust-a' : (a' : El A')
                   → ⅀Assoc-C' (B' a') (λ b' → B (paired a' b'))
                                       (λ b' b'' → C (paired a' b') b'')
                   ≡ (λ z → C1 (invEq (⟦⅀⟧ A' B'') (a' , z)))
     snd-adjust-a' a' = funExt (λ z →
         cong C-curry-top (ΣPathP (refl , c'-of-eq a' z))
       ∙ sym (cong C-curry-top (⟦⅀⟧-on-transp a' z)))

   -- `transp-⅀AB` on a doubly-canonical pair recovers `invEq ⟦⅀⟧ (paired a
   -- b , b'')` (`transp-⅀AB-factored` ∙ `transp-C'-eq-on-canonical` ∙ a
   -- `c'-of-eq`-driven `ΣPathP` ∙ `secEq`).
   opaque
     transp-⅀AssocD-on-canonical
       : (a : El A') (b : El (B' a)) (b'' : El (B (paired a b)))
       → transp-⅀AB (invEq (⟦⅀⟧ A' B'')
                       (a , invEq (⟦⅀⟧ (B' a) (λ b' → B (paired a b')))
                                  (b , b'')))
       ≡ invEq (⟦⅀⟧ (⅀ A' B') B) (paired a b , b'')
     transp-⅀AssocD-on-canonical a b b'' =
         transp-⅀AB-factored a
           (invEq (⟦⅀⟧ (B' a) (λ b' → B (paired a b'))) (b , b''))
       ∙ transp-C'-eq-on-canonical a
           (invEq (⟦⅀⟧ (B' a) (λ b' → B (paired a b'))) (b , b''))
       ∙ cong (λ p → invEq (⟦⅀⟧ (⅀ A' B') B) (paired a (fst p) , snd p))
              ( ΣPathP
                  ( refl
                  , sym (c'-of-eq a
                           (invEq (⟦⅀⟧ (B' a) (λ b' → B (paired a b')))
                                  (b , b''))))
              ∙ secEq (⟦⅀⟧ (B' a) (λ b' → B (paired a b'))) (b , b''))

   -- LHS chain: `transport (cong El LHS-path)` on a canonical pair reduces
   -- to `canonical-form` (generic `transp-⅀AssocD-pair` + `step-Assoc-on-pair`).
   opaque
     transp-⅀AssocD-LHS-on-pair
       : (a : El A') (z : El (B-LHS a))
       → transport (cong El (⅀AssocD 𝒰 A' B' (λ a → ⅀ (B a) (C a))))
                   (invEq (⟦⅀⟧ A' B-LHS) (a , z))
       ≡ invEq (⟦⅀⟧ (⅀ A' B') (λ a → ⅀ (B a) (C a)))
               (paired a (b-of-LHS a z) , w-of-LHS a z)
     transp-⅀AssocD-LHS-on-pair a z =
       transp-⅀AssocD-pair 𝒰 A' B' (λ ab → ⅀ (B ab) (C ab)) a z

   opaque
     LHS-chain-on-pair
       : (a : El A') (z : El (B-LHS a))
       → transport (cong El LHS-path) (invEq (⟦⅀⟧ A' B-LHS) (a , z))
       ≡ canonical-form a z
     LHS-chain-on-pair a z =
         cong (λ p → transport p (invEq (⟦⅀⟧ A' B-LHS) (a , z)))
              (congFunct El (⅀AssocD 𝒰 A' B' (λ a → ⅀ (B a) (C a)))
                            (Inj (⅀Assoc≃ (⅀ A' B') B C)))
       ∙ substComposite (λ X → X)
                        (cong El (⅀AssocD 𝒰 A' B' (λ a → ⅀ (B a) (C a))))
                        (cong El (Inj (⅀Assoc≃ (⅀ A' B') B C)))
                        (invEq (⟦⅀⟧ A' B-LHS) (a , z))
       ∙ cong (transport (cong El (Inj (⅀Assoc≃ (⅀ A' B') B C))))
              (transp-⅀AssocD-LHS-on-pair a z)
       ∙ step-Assoc-on-pair 𝒰 (⅀ A' B') B C
                            (paired a (b-of-LHS a z) , w-of-LHS a z)

   opaque
     LHS-chain-node
       : (x : El (⅀ A' B-LHS))
       → transport (cong El LHS-path) x
       ≡ canonical-form (a-of-x x) (z-of-x x)
     LHS-chain-node x =
         cong (transport (cong El LHS-path)) (sym (retEq (⟦⅀⟧ A' B-LHS) x))
       ∙ LHS-chain-on-pair (a-of-x x) (z-of-x x)

   opaque
     transp-⅀AssocD-RHS-on-pair
       : (a : El A') (z : El (B-RHS a))
       → transport (cong El (⅀AssocD 𝒰 A' B'' C1))
                   (invEq (⟦⅀⟧ A' B-RHS) (a , z))
       ≡ invEq (⟦⅀⟧ (⅀ A' B'') C1)
               (invEq (⟦⅀⟧ A' B'') (a , b-of-RHS a z) , w-of-RHS a z)
     transp-⅀AssocD-RHS-on-pair a z = transp-⅀AssocD-pair 𝒰 A' B'' C1 a z

   -- Per-fibre Code path: the fibre associator then the `snd-adjust-a'` rebase.
   per-fibre-Δ : (a' : El A') → B-LHS a' ≡ B-RHS a'
   per-fibre-Δ a' =
       Inj (⅀Assoc≃ (B' a') (λ b' → B (paired a' b'))
                            (λ b' b'' → C (paired a' b') b''))
     ∙ cong (⅀ (B'' a')) (snd-adjust-a' a')

   R1-snd-on-pair : (a : El A') (b : El (B' a)) (w : El (C'-out a b))
                  → El (B-RHS a)
   R1-snd-on-pair a b w =
     transport (cong El (per-fibre-Δ a))
               (invEq (⟦⅀⟧ (B' a) (C'-out a)) (b , w))

   R1-snd-form : (a : El A') (b : El (B' a)) (w : El (C'-out a b))
               → El (B-RHS a)
   R1-snd-form a b w =
     invEq (⟦⅀⟧ (B'' a) (C1'-out a))
           ( invEq (⟦⅀⟧ (B' a) (λ b' → B (paired a b'))) (b , b''-of a b w)
           , transport (cong El (funExt⁻ (snd-adjust-a' a)
                         (invEq (⟦⅀⟧ (B' a) (λ b' → B (paired a b')))
                                (b , b''-of a b w))))
                       (shifted-c''-per-fibre a b w))

   opaque
     R1-snd-on-pair-eq
       : (a : El A') (b : El (B' a)) (w : El (C'-out a b))
       → R1-snd-on-pair a b w ≡ R1-snd-form a b w
     R1-snd-on-pair-eq a b w =
         cong (λ p → transport p (invEq (⟦⅀⟧ (B' a) (C'-out a)) (b , w)))
              (congFunct El
                 (Inj (⅀Assoc≃ (B' a) (λ b' → B (paired a b'))
                                      (λ b' b'' → C (paired a b') b'')))
                 (cong (⅀ (B'' a)) (snd-adjust-a' a)))
       ∙ substComposite (λ X → X)
                        (cong El (Inj (⅀Assoc≃ (B' a)
                                         (λ b' → B (paired a b'))
                                         (λ b' b'' → C (paired a b') b''))))
                        (cong El (cong (⅀ (B'' a)) (snd-adjust-a' a)))
                        (invEq (⟦⅀⟧ (B' a) (C'-out a)) (b , w))
       ∙ cong (transport (cong (λ F → El (⅀ (B'' a) F))
                               (snd-adjust-a' a)))
              (step-Assoc-on-pair 𝒰 (B' a) (λ b' → B (paired a b'))
                                      (λ b' b'' → C (paired a b') b'')
                                      (b , w))
       ∙ cong (λ e → equivFun e
                 (invEq (⟦⅀⟧ (B'' a)
                             (⅀Assoc-C' (B' a) (λ b' → B (paired a b'))
                                         (λ b' b'' → C (paired a b') b'')))
                        ( invEq (⟦⅀⟧ (B' a) (λ b' → B (paired a b')))
                                (b , b''-of a b w)
                        , shifted-c''-per-fibre a b w)))
              (⟦⅀⟧-natural-snd 𝒰 (B'' a) (snd-adjust-a' a))
       ∙ cong (λ p → invEq (⟦⅀⟧ (B'' a) (C1'-out a))
                           ( fst p
                           , transport (cong El (funExt⁻ (snd-adjust-a' a)
                                                         (fst p)))
                                       (snd p)))
              (secEq (⟦⅀⟧ (B'' a)
                          (⅀Assoc-C' (B' a) (λ b' → B (paired a b'))
                                      (λ b' b'' → C (paired a b') b'')))
                     ( invEq (⟦⅀⟧ (B' a) (λ b' → B (paired a b')))
                             (b , b''-of a b w)
                     , shifted-c''-per-fibre a b w))

   opaque
     R1-on-pair
       : (a : El A') (z : El (B-LHS a))
       → transport (cong (λ F → El (⅀ A' F)) (funExt per-fibre-Δ))
                   (invEq (⟦⅀⟧ A' B-LHS) (a , z))
       ≡ invEq (⟦⅀⟧ A' B-RHS) (a , transport (cong El (per-fibre-Δ a)) z)
     R1-on-pair a z =
         cong (λ e → equivFun e (invEq (⟦⅀⟧ A' B-LHS) (a , z)))
              (⟦⅀⟧-natural-snd 𝒰 A' (funExt per-fibre-Δ))
       ∙ cong (λ p → invEq (⟦⅀⟧ A' B-RHS)
                           ( fst p
                           , transport (cong El (funExt⁻ (funExt per-fibre-Δ)
                                                         (fst p)))
                                       (snd p)))
              (secEq (⟦⅀⟧ A' B-LHS) (a , z))

   RHS-form : (a : El A') (z : El (B-LHS a))
            → El (⅀ (⅀ (⅀ A' B') B) (⅀Assoc-C' (⅀ A' B') B C))
   RHS-form a z =
     invEq (⟦⅀⟧ (⅀ (⅀ A' B') B) (⅀Assoc-C' (⅀ A' B') B C))
           ( transp-⅀AB
               (invEq (⟦⅀⟧ A' B'')
                      ( a
                      , b-of-RHS a (transport (cong El (per-fibre-Δ a)) z)))
           , w-of-RHS a (transport (cong El (per-fibre-Δ a)) z))

   opaque
     RHS-chain-on-pair
       : (a : El A') (z : El (B-LHS a))
       → transport (cong El (cong (⅀ A') (funExt per-fibre-Δ)
                             ∙ RHS-path-tail))
                   (invEq (⟦⅀⟧ A' B-LHS) (a , z))
       ≡ RHS-form a z
     RHS-chain-on-pair a z =
         cong (λ p → transport p (invEq (⟦⅀⟧ A' B-LHS) (a , z)))
              (congFunct El (cong (⅀ A') (funExt per-fibre-Δ)) RHS-path-tail)
       ∙ substComposite (λ X → X)
                        (cong El (cong (⅀ A') (funExt per-fibre-Δ)))
                        (cong El RHS-path-tail)
                        (invEq (⟦⅀⟧ A' B-LHS) (a , z))
       ∙ cong (transport (cong El RHS-path-tail)) (R1-on-pair a z)
       ∙ cong (λ p → transport p
                       (invEq (⟦⅀⟧ A' B-RHS)
                              (a , transport (cong El (per-fibre-Δ a)) z)))
              (congFunct El (⅀AssocD 𝒰 A' B'' C1)
                            (⅀-subst-path 𝒰 (⅀AssocD 𝒰 A' B' B)
                               (⅀Assoc-C' (⅀ A' B') B C)))
       ∙ substComposite (λ X → X)
                        (cong El (⅀AssocD 𝒰 A' B'' C1))
                        (cong El (⅀-subst-path 𝒰 (⅀AssocD 𝒰 A' B' B)
                                    (⅀Assoc-C' (⅀ A' B') B C)))
                        (invEq (⟦⅀⟧ A' B-RHS)
                               (a , transport (cong El (per-fibre-Δ a)) z))
       ∙ cong (transport (cong El (⅀-subst-path 𝒰 (⅀AssocD 𝒰 A' B' B)
                                     (⅀Assoc-C' (⅀ A' B') B C))))
              (transp-⅀AssocD-RHS-on-pair a
                 (transport (cong El (per-fibre-Δ a)) z))
       ∙ transp-⅀-subst-path 𝒰 (⅀AssocD 𝒰 A' B' B)
                               (⅀Assoc-C' (⅀ A' B') B C)
                               (invEq (⟦⅀⟧ (⅀ A' B'') C1)
                                 ( invEq (⟦⅀⟧ A' B'')
                                     ( a
                                     , b-of-RHS a
                                         (transport (cong El
                                                      (per-fibre-Δ a)) z))
                                 , w-of-RHS a
                                     (transport (cong El
                                                  (per-fibre-Δ a)) z)))
       ∙ cong (λ p → invEq (⟦⅀⟧ (⅀ (⅀ A' B') B)
                                (⅀Assoc-C' (⅀ A' B') B C))
                           ( transp-⅀AB (fst p) , snd p ))
              (secEq (⟦⅀⟧ (⅀ A' B'') C1)
                     ( invEq (⟦⅀⟧ A' B'')
                         ( a
                         , b-of-RHS a
                             (transport (cong El (per-fibre-Δ a)) z))
                     , w-of-RHS a
                         (transport (cong El (per-fibre-Δ a)) z)))

   -- The outer-Σ `shifted` `c''`-component, and the explicit `canonical-form`.
   shifted-c''-outer
     : (a : El A') (b : El (B' a)) (w : El (C'-out a b))
     → El (⅀Assoc-C' (⅀ A' B') B C
                      (invEq (⟦⅀⟧ (⅀ A' B') B)
                             (paired a b , b''-of a b w)))
   shifted-c''-outer a b w =
     subst (λ p → El (C (fst p) (snd p)))
           (sym (secEq (⟦⅀⟧ (⅀ A' B') B) (paired a b , b''-of a b w)))
           (c''-of a b w)

   shifted-c''-outer-z
     : (a : El A') (z : El (B-LHS a))
     → El (⅀Assoc-C' (⅀ A' B') B C
                      (invEq (⟦⅀⟧ (⅀ A' B') B)
                             (paired a (b-of-LHS a z)
                             , b''-of a (b-of-LHS a z) (w-of-LHS a z))))
   shifted-c''-outer-z a z =
     shifted-c''-outer a (b-of-LHS a z) (w-of-LHS a z)

   canonical-form-explicit
     : (a : El A') (z : El (B-LHS a))
     → canonical-form a z
     ≡ invEq (⟦⅀⟧ (⅀ (⅀ A' B') B) (⅀Assoc-C' (⅀ A' B') B C))
             ( invEq (⟦⅀⟧ (⅀ A' B') B)
                     (paired a (b-of-LHS a z)
                     , b''-of a (b-of-LHS a z) (w-of-LHS a z))
             , shifted-c''-outer-z a z)
   canonical-form-explicit _ _ = refl

   opaque
     ⟦⅀⟧-on-R1-snd-form
       : (a : El A') (b : El (B' a)) (w : El (C'-out a b))
       → equivFun (⟦⅀⟧ (B'' a) (C1'-out a)) (R1-snd-form a b w)
       ≡ ( invEq (⟦⅀⟧ (B' a) (λ b' → B (paired a b'))) (b , b''-of a b w)
         , transport (cong El (funExt⁻ (snd-adjust-a' a)
                       (invEq (⟦⅀⟧ (B' a) (λ b' → B (paired a b')))
                              (b , b''-of a b w))))
                     (shifted-c''-per-fibre a b w))
     ⟦⅀⟧-on-R1-snd-form a b w =
       secEq (⟦⅀⟧ (B'' a) (C1'-out a))
             ( invEq (⟦⅀⟧ (B' a) (λ b' → B (paired a b'))) (b , b''-of a b w)
             , transport (cong El (funExt⁻ (snd-adjust-a' a)
                           (invEq (⟦⅀⟧ (B' a) (λ b' → B (paired a b')))
                                  (b , b''-of a b w))))
                         (shifted-c''-per-fibre a b w))

   canonical-form-on-pair-Σ
     : (a : El A') (b : El (B' a)) (w : El (C'-out a b))
     → Assoc-cont 𝒰 (⅀ A' B') B C (paired a b , w)
     ≡ invEq (⟦⅀⟧ (⅀ (⅀ A' B') B) (⅀Assoc-C' (⅀ A' B') B C))
             ( invEq (⟦⅀⟧ (⅀ A' B') B) (paired a b , b''-of a b w)
             , shifted-c''-outer a b w)
   canonical-form-on-pair-Σ _ _ _ = refl

   opaque
     path1
       : (a : El A') (b : El (B' a)) (w : El (C'-out a b))
       → equivFun (⟦⅀⟧ (B'' a) (C1'-out a)) (R1-snd-on-pair a b w)
       ≡ ( invEq (⟦⅀⟧ (B' a) (λ b' → B (paired a b'))) (b , b''-of a b w)
         , transport (cong El (funExt⁻ (snd-adjust-a' a)
                       (invEq (⟦⅀⟧ (B' a) (λ b' → B (paired a b')))
                              (b , b''-of a b w))))
                     (shifted-c''-per-fibre a b w))
     path1 a b w =
         cong (equivFun (⟦⅀⟧ (B'' a) (C1'-out a))) (R1-snd-on-pair-eq a b w)
       ∙ ⟦⅀⟧-on-R1-snd-form a b w

   opaque
     Σ-bridge-fst
       : (a : El A') (b : El (B' a)) (w : El (C'-out a b))
       → invEq (⟦⅀⟧ (⅀ A' B') B) (paired a b , b''-of a b w)
       ≡ transp-⅀AB
           (invEq (⟦⅀⟧ A' B'')
                  ( a
                  , fst (equivFun (⟦⅀⟧ (B'' a) (C1'-out a))
                                  (R1-snd-on-pair a b w))))
     Σ-bridge-fst a b w =
         sym (transp-⅀AssocD-on-canonical a b (b''-of a b w))
       ∙ cong (λ x → transp-⅀AB (invEq (⟦⅀⟧ A' B'') (a , x)))
              (sym (cong fst (path1 a b w)))

   Σ-bridge-mid-snd
     : (a : El A') (b : El (B' a)) (w : El (C'-out a b))
     → El (⅀Assoc-C' (⅀ A' B') B C
             (transp-⅀AB
               (invEq (⟦⅀⟧ A' B'')
                      ( a
                      , invEq (⟦⅀⟧ (B' a) (λ b' → B (paired a b')))
                              (b , b''-of a b w)))))
   Σ-bridge-mid-snd a b w =
     transport (cong El (funExt⁻ (snd-adjust-a' a)
                   (invEq (⟦⅀⟧ (B' a) (λ b' → B (paired a b')))
                          (b , b''-of a b w))))
               (shifted-c''-per-fibre a b w)

   opaque
     Σ-bridge-snd-part2
       : (a : El A') (b : El (B' a)) (w : El (C'-out a b))
       → PathP (λ i → El (⅀Assoc-C' (⅀ A' B') B C
                            (transp-⅀AB
                              (invEq (⟦⅀⟧ A' B'')
                                     (a , cong fst (path1 a b w) (~ i))))))
               (Σ-bridge-mid-snd a b w)
               (w-of-RHS a (R1-snd-on-pair a b w))
     Σ-bridge-snd-part2 a b w = λ i → snd (path1 a b w (~ i))

   opaque
     unfolding snd-adjust-a'
     snd-adjust-on-pair-decomp
       : (a' : El A') (z' : El (B'' a'))
       → funExt⁻ (snd-adjust-a' a') z'
       ≡ cong C-curry-top (ΣPathP (refl , c'-of-eq a' z'))
       ∙ sym (cong C-curry-top (⟦⅀⟧-on-transp a' z'))
     snd-adjust-on-pair-decomp _ _ = refl

   -- Code path-of-paths bridging the LHS-side and RHS-side `snd`-Code moves
   -- (closes via one `homotopyNatural` against `secEq (⟦⅀⟧ (⅀ A' B') B)`).
   opaque
     unfolding transp-⅀AssocD-on-canonical snd-adjust-a' transp-⅀AB-factored transp-C'-eq-on-canonical ⟦⅀⟧-on-transp
     path-bridge-LHS-to-RHS
       : (a : El A') (b : El (B' a)) (w : El (C'-out a b))
       → ( cong (λ p → C (fst p) (snd p))
                (sym (secEq (⟦⅀⟧ (⅀ A' B') B) (paired a b , b''-of a b w)))
         ∙ cong (⅀Assoc-C' (⅀ A' B') B C)
                (sym (transp-⅀AssocD-on-canonical a b (b''-of a b w))) )
       ≡ ( cong (λ p → C (paired a (fst p)) (snd p))
                (sym (secEq (⟦⅀⟧ (B' a) (λ b' → B (paired a b')))
                            (b , b''-of a b w)))
         ∙ funExt⁻ (snd-adjust-a' a)
                    (invEq (⟦⅀⟧ (B' a) (λ b' → B (paired a b')))
                           (b , b''-of a b w)) )
     path-bridge-LHS-to-RHS a b w =
       let
         ⟦⅀⟧'  = ⟦⅀⟧ (⅀ A' B') B
         ⟦⅀⟧'' = ⟦⅀⟧ (B' a) (λ b' → B (paired a b'))
         z'    : El (B'' a)
         z'    = invEq ⟦⅀⟧'' (b , b''-of a b w)
         secO  = secEq ⟦⅀⟧' (paired a b , b''-of a b w)
         secF  = secEq ⟦⅀⟧'' (b , b''-of a b w)
         M     : Σ (El (⅀ A' B')) (λ ab → El (B ab))
         M     = paired a (b'-of a z')
               , transport (cong El (funExt⁻ C'-eq (paired a (b'-of a z'))))
                           (substed-c-of a z')
         secM  = secEq ⟦⅀⟧' M

         pfs : Σ (El (B' a)) (λ b' → El (B (paired a b')))
             → Σ (El (⅀ A' B')) (λ ab → El (B ab))
         pfs p = paired a (fst p) , snd p

         Q1 : Path (Σ (El (B' a)) (λ b' → El (B (paired a b'))))
                  ( b'-of a z'
                  , transport (cong El (funExt⁻ C'-eq
                                          (paired a (b'-of a z'))))
                              (substed-c-of a z') )
                  ( b'-of a z' , c'-of a z' )
         Q1 = ΣPathP (refl , sym (c'-of-eq a z'))
         P  = Q1 ∙ secF

         step1 = transp-⅀AB-factored a z'
         step3 = transp-C'-eq-on-canonical a z'
         step4 = cong (λ p → invEq ⟦⅀⟧' (paired a (fst p) , snd p)) P
         step123 = step1 ∙ step3

         TAC = transp-⅀AssocD-on-canonical a b (b''-of a b w)

         H-pfs : (p : Σ (El (B' a)) (λ b' → El (B (paired a b'))))
               → equivFun ⟦⅀⟧' (invEq ⟦⅀⟧' (pfs p)) ≡ pfs p
         H-pfs p = secEq ⟦⅀⟧' (pfs p)

         TAC-rearrange : TAC ≡ step123 ∙ step4
         TAC-rearrange = assoc step1 step3 step4

         sym-cong-step123
           : sym (cong (equivFun ⟦⅀⟧') step123)
           ≡ secM ∙ sym (⟦⅀⟧-on-transp a z')
         sym-cong-step123 = sym (
             cong (secM ∙_) (symDistr (cong (equivFun ⟦⅀⟧') step123) secM)
           ∙ assoc secM (sym secM) (sym (cong (equivFun ⟦⅀⟧') step123))
           ∙ cong (_∙ sym (cong (equivFun ⟦⅀⟧') step123))
                  (lCancel (sym secM))
           ∙ sym (lUnit (sym (cong (equivFun ⟦⅀⟧') step123))) )

         cong-e-sym-TAC
           : cong (equivFun ⟦⅀⟧') (sym TAC)
           ≡ sym (cong (equivFun ⟦⅀⟧') step4)
             ∙ secM ∙ sym (⟦⅀⟧-on-transp a z')
         cong-e-sym-TAC =
             cong (λ p → cong (equivFun ⟦⅀⟧') (sym p)) TAC-rearrange
           ∙ cong (cong (equivFun ⟦⅀⟧')) (symDistr step123 step4)
           ∙ congFunct (equivFun ⟦⅀⟧') (sym step4) (sym step123)
           ∙ cong (sym (cong (equivFun ⟦⅀⟧') step4) ∙_) sym-cong-step123

         Σ-eq
           : sym secO ∙ cong (equivFun ⟦⅀⟧') (sym TAC)
           ≡ cong pfs (sym secF) ∙ ΣPathP (refl , c'-of-eq a z')
                                 ∙ sym (⟦⅀⟧-on-transp a z')
         Σ-eq =
             cong (sym secO ∙_) cong-e-sym-TAC
           ∙ cong (sym secO ∙_)
                  (assoc (sym (cong (equivFun ⟦⅀⟧') step4))
                         secM (sym (⟦⅀⟧-on-transp a z')))
           ∙ cong (λ q → sym secO ∙ (q ∙ sym (⟦⅀⟧-on-transp a z')))
                  (sym (homotopyNatural H-pfs (sym P)))
           ∙ assoc (sym secO) (secO ∙ cong pfs (sym P))
                   (sym (⟦⅀⟧-on-transp a z'))
           ∙ cong (_∙ sym (⟦⅀⟧-on-transp a z'))
                  (assoc (sym secO) secO (cong pfs (sym P)))
           ∙ cong (λ q → (q ∙ cong pfs (sym P))
                         ∙ sym (⟦⅀⟧-on-transp a z'))
                  (lCancel secO)
           ∙ cong (_∙ sym (⟦⅀⟧-on-transp a z'))
                  (sym (lUnit (cong pfs (sym P))))
           ∙ cong (_∙ sym (⟦⅀⟧-on-transp a z'))
                  (cong (cong pfs) (symDistr Q1 secF))
           ∙ cong (_∙ sym (⟦⅀⟧-on-transp a z'))
                  (congFunct pfs (sym secF) (ΣPathP (refl , c'-of-eq a z')))
           ∙ sym (assoc (cong pfs (sym secF))
                        (ΣPathP (refl , c'-of-eq a z'))
                        (sym (⟦⅀⟧-on-transp a z')))
       in
           sym (congFunct C-curry-top (sym secO)
                          (cong (equivFun ⟦⅀⟧') (sym TAC)))
         ∙ cong (cong C-curry-top) Σ-eq
         ∙ congFunct C-curry-top (cong pfs (sym secF))
                                 (ΣPathP (refl , c'-of-eq a z')
                                  ∙ sym (⟦⅀⟧-on-transp a z'))
         ∙ cong (cong C-curry-top (cong pfs (sym secF)) ∙_)
                (congFunct C-curry-top (ΣPathP (refl , c'-of-eq a z'))
                                       (sym (⟦⅀⟧-on-transp a z')))

   -- First leg of the Σ-bridge `snd`-component: endpoint-fix.
   opaque
     Σ-bridge-snd-part1-endpoint
       : (a : El A') (b : El (B' a)) (w : El (C'-out a b))
       → transport (cong (λ x → El (⅀Assoc-C' (⅀ A' B') B C x))
                          (sym (transp-⅀AssocD-on-canonical a b
                                  (b''-of a b w))))
                   (shifted-c''-outer a b w)
       ≡ Σ-bridge-mid-snd a b w
     Σ-bridge-snd-part1-endpoint a b w =
         sym (substComposite (λ X → X)
                             (cong (λ p → El (C (fst p) (snd p)))
                                   (sym (secEq (⟦⅀⟧ (⅀ A' B') B)
                                                (paired a b , b''-of a b w))))
                             (cong (λ x → El (⅀Assoc-C' (⅀ A' B') B C x))
                                   (sym (transp-⅀AssocD-on-canonical a b
                                           (b''-of a b w))))
                             (c''-of a b w))
       ∙ cong (λ p → transport p (c''-of a b w))
              (sym (congFunct El
                     (cong (λ p → C (fst p) (snd p))
                           (sym (secEq (⟦⅀⟧ (⅀ A' B') B)
                                        (paired a b , b''-of a b w))))
                     (cong (⅀Assoc-C' (⅀ A' B') B C)
                           (sym (transp-⅀AssocD-on-canonical a b
                                   (b''-of a b w))))))
       ∙ cong (λ p → transport (cong El p) (c''-of a b w))
              (path-bridge-LHS-to-RHS a b w)
       ∙ cong (λ p → transport p (c''-of a b w))
              (congFunct El
                 (cong (λ p → C (paired a (fst p)) (snd p))
                       (sym (secEq (⟦⅀⟧ (B' a) (λ b' → B (paired a b')))
                                    (b , b''-of a b w))))
                 (funExt⁻ (snd-adjust-a' a)
                           (invEq (⟦⅀⟧ (B' a) (λ b' → B (paired a b')))
                                  (b , b''-of a b w))))
       ∙ substComposite (λ X → X)
                        (cong (λ p → El (C (paired a (fst p)) (snd p)))
                              (sym (secEq (⟦⅀⟧ (B' a) (λ b' → B (paired a b')))
                                           (b , b''-of a b w))))
                        (cong El (funExt⁻ (snd-adjust-a' a)
                                     (invEq (⟦⅀⟧ (B' a)
                                                 (λ b' → B (paired a b')))
                                            (b , b''-of a b w))))
                        (c''-of a b w)

   -- On a canonical pair, `canonical-form` coincides with `RHS-form`.
   opaque
     unfolding Σ-bridge-fst
     σ-bridge-on-pair
       : (a : El A') (b : El (B' a)) (w : El (C'-out a b))
       → Assoc-cont 𝒰 (⅀ A' B') B C (paired a b , w)
       ≡ RHS-form a (invEq (⟦⅀⟧ (B' a) (C'-out a)) (b , w))
     σ-bridge-on-pair a b w =
       cong (invEq (⟦⅀⟧ (⅀ (⅀ A' B') B) (⅀Assoc-C' (⅀ A' B') B C)))
            (ΣPathP (Σ-bridge-fst a b w
                    , compPathP' {B = λ x → El (⅀Assoc-C' (⅀ A' B') B C x)}
                                 (toPathP (Σ-bridge-snd-part1-endpoint a b w))
                                 (Σ-bridge-snd-part2 a b w)))

   opaque
     σ-bridge-base
       : (a : El A') (z : El (B-LHS a))
       → canonical-form a z ≡ RHS-form a z
     σ-bridge-base a z =
         σ-bridge-on-pair a (b-of-LHS a z) (w-of-LHS a z)
       ∙ cong (RHS-form a) (retEq (⟦⅀⟧ (B' a) (C'-out a)) z)

   opaque
     pointwise-node
       : (x : El (⅀ A' B-LHS))
       → transport (cong El LHS-path) x
       ≡ transport (cong El (cong (⅀ A') (funExt per-fibre-Δ)
                             ∙ RHS-path-tail)) x
     pointwise-node x =
         LHS-chain-node x
       ∙ σ-bridge-base (a-of-x x) (z-of-x x)
       ∙ sym (RHS-chain-on-pair (a-of-x x) (z-of-x x))
       ∙ cong (transport (cong El (cong (⅀ A') (funExt per-fibre-Δ)
                                   ∙ RHS-path-tail)))
              (retEq (⟦⅀⟧ A' B-LHS) x)

   equivs-agree-node
     : pathToEquiv (cong El LHS-path)
     ≡ pathToEquiv (cong El (cong (⅀ A') (funExt per-fibre-Δ)
                             ∙ RHS-path-tail))
   equivs-agree-node = equivEq (funExt pointwise-node)

   opaque
     bridge-node : LHS-path
                 ≡ cong (⅀ A') (funExt per-fibre-Δ) ∙ RHS-path-tail
     bridge-node =
         sym (InjSec 𝒰 LHS-path)
       ∙ cong Inj equivs-agree-node
       ∙ InjSec 𝒰 (cong (⅀ A') (funExt per-fibre-Δ) ∙ RHS-path-tail)
