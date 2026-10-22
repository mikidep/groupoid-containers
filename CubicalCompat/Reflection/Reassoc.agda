{-
  Goal-directed front end to Prelude.Reassoc.

    reassoc!                 -- the normal forms are definitionally equal
    reassoc-with proof       -- supply a proof between the normal forms
    reassoc-on lhs rhs proof -- also specify the endpoints (e.g. in a where block)

  Recognises composition, reflexivity and congruence, including transparent
  wrappers such as whiskering and a functor's action on paths. Other paths are
  atoms. Like Prelude.Reassoc, this does not itself cancel inverse paths.
  Supplied proofs use Prelude.Reassoc's normal forms: right-associated paths
  with a final refl. See ReassocTests.CurrentCases for the existing examples.
-}
module CubicalCompat.Reflection.Reassoc where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_$_; flip)
open import Cubical.Data.List.Base using (List; []; _∷_; [_])
open import Cubical.Data.Nat.Base using (ℕ; zero; suc; _+_; _∸_)
open import Cubical.Data.Unit.Base using (Unit; tt)
open import Cubical.Data.Bool using (Bool; true; false; if_then_else_)
open import Cubical.Data.Sigma using (_×_; _,_; fst; snd)
open import CubicalCompat.Reflection.Base
import Agda.Builtin.Reflection as R
import Prelude.Reassoc as Q

private
  Arrow : ∀ {ℓ ℓ′} → Type ℓ → Type ℓ′ → Type (ℓ-max ℓ ℓ′)
  Arrow A B = A → B

  -- Infer the path's type before checking the reflected function, which is
  -- often an unannotated lambda. The opposite order creates large families
  -- of higher-order metavariables for nested whiskering of function paths.
  congTerm : ∀ {ℓ ℓ′} {A : Type ℓ} {B : Type ℓ′} {x y : A}
    (p : Q.Term x y) (f : A → B) → Q.Term (f x) (f y)
  congTerm p f = Q.cong′ f p

  visible : List (R.Arg R.Term) → List R.Term
  visible [] = []
  visible (varg t ∷ ts) = t ∷ visible ts
  visible (_ ∷ ts) = visible ts

  -- Unfold notation, but do not erase the operations we want to reify.
  inspect : R.Term → R.TC R.Term
  inspect t = R.runSpeculative (
    R.noConstraints (R.withReduceDefs
      (false , quote _∙_ ∷ quote refl ∷ quote cong ∷ quote congS ∷
        quote cong₂ ∷ quote sym ∷ []) (R.reduce t)) >>= λ t′ →
    R.returnTC (t′ , false))

  pathEnds : R.Type → R.TC (R.Term × R.Term)
  pathEnds (R.meta m _) = R.blockTC (R.blockerMeta m)
  pathEnds (R.def n args)
    with R.primQNameEquality n (quote PathP) | R.primQNameEquality n (quote _≡_) | visible args
  ... | true | _ | _ ∷ p ∷ q ∷ [] = R.returnTC (p , q)
  ... | _ | true | p ∷ q ∷ [] = R.returnTC (p , q)
  ... | _ | _ | _ = R.typeError [ R.strErr "reassoc: expected an equality between paths" ]
  pathEnds t = R.typeError
    (R.strErr "reassoc: expected an equality between paths, got " ∷ R.termErr t ∷ [])

  -- Rechecking a reflected goal with reduce creates many redundant metas.
  -- inferType already gives its elaborated _≡_ or PathP application.
  endpoints : R.Term → R.TC (R.Term × R.Term)
  endpoints t = R.inferType t >>= pathEnds

  -- Some goals hide their composites in record projections or pattern
  -- lambdas. Normalise the inferred type only as a fallback, preserving ∙
  -- so that it is not expanded into hcomp. Unlike reduce on a reflected
  -- endpoint, this does not re-elaborate those pattern lambdas without an
  -- expected type.
  normalisedType : R.Term → R.TC R.Type
  normalisedType t = R.withReduceDefs (false , [ quote _∙_ ])
    (R.withNormalisation true (R.inferType t))

  reflexive : R.Term → R.TC Bool
  reflexive (R.meta m _) = R.blockTC (R.blockerMeta m)
  reflexive t = R.catchTC
    (R.runSpeculative
      (R.noConstraints (R.unify t (R.def (quote refl) [])) >>
        R.returnTC (true , false)))
    (R.returnTC false)

  atom : R.Term → R.Term
  atom p = R.con (quote Q.↑_) (p v∷ [])

  -- A projection from an inferred record may be stuck until its implicit
  -- record argument is solved. Do not freeze such a path as an atom.
  mutual
    waitForMetas : R.Term → R.TC Unit
    waitForMetas (R.meta m _) = R.blockTC (R.blockerMeta m)
    waitForMetas (R.var _ args) = waitForArgs args
    waitForMetas (R.def _ args) = waitForArgs args
    waitForMetas (R.con _ args) = waitForArgs args
    waitForMetas (R.lam _ (R.abs _ t)) = waitForMetas t
    waitForMetas (R.pi (R.arg _ a) (R.abs _ b)) = waitForMetas a >> waitForMetas b
    waitForMetas (R.agda-sort (R.set t)) = waitForMetas t
    waitForMetas (R.agda-sort (R.prop t)) = waitForMetas t
    waitForMetas _ = R.returnTC tt

    waitForArgs : List (R.Arg R.Term) → R.TC Unit
    waitForArgs [] = R.returnTC tt
    waitForArgs (R.arg _ t ∷ ts) = waitForMetas t >> waitForArgs ts

  mapPath : R.Term → R.Term → R.Term
  mapPath f p = R.def (quote congTerm) (p v∷ f v∷ [])

  below : ℕ → ℕ → Bool
  below _ zero = false
  below zero (suc _) = true
  below (suc n) (suc m) = below n m

  sameNat : ℕ → ℕ → Bool
  sameNat zero zero = true
  sameNat (suc n) (suc m) = sameNat n m
  sameNat _ _ = false

  cannotFactor : ∀ {ℓ} {A : Type ℓ} → R.TC A
  cannotFactor = R.typeError [ R.strErr "reassoc: not a non-dependent congruence" ]

  -- Remove k free binders, failing if the term depends on any of them.
  mutual
    strengthen : ℕ → ℕ → R.Term → R.TC R.Term
    strengthen k d (R.var n args) =
      (if below n d then R.returnTC n else
       if below n (d + k) then cannotFactor else R.returnTC (n ∸ k)) >>= λ n′ →
      liftTC (R.var n′) (strengthenArgs k d args)
    strengthen k d (R.def n args) = liftTC (R.def n) (strengthenArgs k d args)
    strengthen k d (R.con n args) = liftTC (R.con n) (strengthenArgs k d args)
    strengthen k d (R.meta n args) = liftTC (R.meta n) (strengthenArgs k d args)
    strengthen k d (R.lam i (R.abs s t)) =
      liftTC (λ t′ → R.lam i (R.abs s t′)) (strengthen k (suc d) t)
    strengthen k d (R.pi (R.arg i a) (R.abs s b)) =
      strengthen k d a >>= λ a′ →
      liftTC (λ b′ → R.pi (R.arg i a′) (R.abs s b′)) (strengthen k (suc d) b)
    strengthen k d (R.agda-sort (R.set t)) =
      liftTC (λ t′ → R.agda-sort (R.set t′)) (strengthen k d t)
    strengthen k d (R.agda-sort (R.prop t)) =
      liftTC (λ t′ → R.agda-sort (R.prop t′)) (strengthen k d t)
    strengthen _ _ (R.pat-lam _ _) = cannotFactor
    strengthen _ _ t = R.returnTC t

    strengthenArgs : ℕ → ℕ → List (R.Arg R.Term) → R.TC (List (R.Arg R.Term))
    strengthenArgs _ _ [] = R.returnTC []
    strengthenArgs k d (R.arg i t ∷ ts) =
      strengthen k d t >>= λ t′ →
      liftTC (R.arg i t′ ∷_) (strengthenArgs k d ts)

  data Variation : Type where
    constant : Variation
    varying : R.Term → Variation

  merge : Variation → Variation → R.TC Variation
  merge constant q = R.returnTC q
  merge p constant = R.returnTC p
  merge (varying p) (varying q) =
    R.runSpeculative (R.noConstraints (R.unify p q) >> R.returnTC (varying p , false))

  intervalArgs : ℕ → List (R.Arg R.Term)
    → R.TC (List (R.Arg R.Term) × List (R.Arg R.Term))
  intervalArgs _ [] = cannotFactor
  intervalArgs d (varg (R.var n []) ∷ args) with sameNat d n
  ... | true = R.returnTC ([] , args)
  ... | false = liftTC (λ { (before , after) → varg (v n) ∷ before , after })
      (intervalArgs d args)
  intervalArgs d (a ∷ args) =
    liftTC (λ { (before , after) → a ∷ before , after }) (intervalArgs d args)

  -- INLINE cong/whiskering is often reflected as λ i → f (p i).
  -- Factor p out, reusing the interval binder as the argument of f. Tracking
  -- binder depth also handles function-valued paths and implicit lambdas.
  mutual
    occurs : ℕ → R.Term → Bool
    occurs d (R.var n args) = if sameNat n d then true else occursArgs d args
    occurs d (R.def _ args) = occursArgs d args
    occurs d (R.con _ args) = occursArgs d args
    occurs d (R.meta _ args) = occursArgs d args
    occurs d (R.lam _ (R.abs _ t)) = occurs (suc d) t
    occurs d (R.pi (R.arg _ a) (R.abs _ b)) =
      if occurs d a then true else occurs (suc d) b
    occurs d (R.agda-sort (R.set t)) = occurs d t
    occurs d (R.agda-sort (R.prop t)) = occurs d t
    occurs _ (R.pat-lam _ _) = true
    occurs _ _ = false

    occursArgs : ℕ → List (R.Arg R.Term) → Bool
    occursArgs _ [] = false
    occursArgs d (R.arg _ t ∷ ts) = if occurs d t then true else occursArgs d ts

  mutual
    scan : ℕ → ℕ → R.Term → R.TC (Variation × R.Term)
    scan zero _ _ = cannotFactor
    scan (suc fuel) d t =
      -- Most implicit arguments are constant, including large type indices.
      if occurs d t then scanDependent fuel d t else R.returnTC (constant , t)

    scanDependent : ℕ → ℕ → R.Term → R.TC (Variation × R.Term)
    scanDependent fuel d (R.var n args) =
      if sameNat n d then cannotFactor else scanApp fuel d (R.var n) args
    scanDependent fuel d (R.def n args) = scanApp fuel d (R.def n) args
    scanDependent fuel d (R.con n args) = scanApp fuel d (R.con n) args
    scanDependent fuel d (R.meta n args) = scanApp fuel d (R.meta n) args
    scanDependent fuel d (R.lam i (R.abs s t)) =
      liftTC (λ { (p , t′) → p , R.lam i (R.abs s t′) }) (scan fuel (suc d) t)
    scanDependent _ _ _ = cannotFactor

    scanApp : ℕ → ℕ → (List (R.Arg R.Term) → R.Term) → List (R.Arg R.Term)
      → R.TC (Variation × R.Term)
    scanApp fuel d head args =
      (intervalArgs d args >>= λ { (before , after) →
        strengthen (suc d) 0 (head before) >>= λ p →
        -- This is only a test: discard its temporary elaboration state.
        R.runSpeculative
          (R.noConstraints (endpoints p) >> R.returnTC (tt , false)) >>
        scanArgs fuel d after >>= λ { (q , after′) →
        merge (varying p) q >>= λ variation →
        R.returnTC (variation , R.var d after′) } })
      <|> liftTC (λ { (p , args′) → p , head args′ }) (scanArgs fuel d args)

    scanArgs : ℕ → ℕ → List (R.Arg R.Term)
      → R.TC (Variation × List (R.Arg R.Term))
    scanArgs _ _ [] = R.returnTC (constant , [])
    scanArgs fuel d (R.arg i t ∷ ts) =
      scan fuel d t >>= λ { (p , t′) →
      scanArgs fuel d ts >>= λ { (q , ts′) →
      merge p q >>= λ variation →
      R.returnTC (variation , R.arg i t′ ∷ ts′) } }

  -- Fuel bounds unfolding of user definitions, not just the surface syntax.
  mutual
    reify : ℕ → R.Term → R.TC R.Term
    reify zero _ = R.typeError [ R.strErr "reassoc: path expression is too deeply nested" ]
    reify (suc fuel) p@(R.lam _ _) = reifyHead fuel p p
    reify (suc fuel) p@(R.var _ _) = leaf p
    -- reduce rechecks its argument: avoid repeatedly checking entire composites.
    reify (suc fuel) p@(R.def n _) =
      if R.primQNameEquality n (quote _∙_) then reifyHead fuel p p else
      if R.primQNameEquality n (quote cong) then reifyHead fuel p p else
      if R.primQNameEquality n (quote congS) then reifyHead fuel p p else
      if R.primQNameEquality n (quote cong₂) then reifyHead fuel p p else
      if R.primQNameEquality n (quote refl) then reifyHead fuel p p else
      if R.primQNameEquality n (quote sym) then reifyHead fuel p p else
      inspect p >>= reifyHead fuel p
    reify (suc fuel) p = inspect p >>= reifyHead fuel p

    reifyHead : ℕ → R.Term → R.Term → R.TC R.Term
    reifyHead fuel original (R.def n args) =
      (if R.primQNameEquality n (quote _∙_) then composition (visible args) else
      if R.primQNameEquality n (quote refl) then R.returnTC (R.con (quote Q.refl′) []) else
      if R.primQNameEquality n (quote cong) then congruence (visible args) else
      if R.primQNameEquality n (quote congS) then congruence (visible args) else
      if R.primQNameEquality n (quote cong₂) then binary (visible args) else
      leaf original)
      where
      composition : List R.Term → R.TC R.Term
      composition (p ∷ q ∷ []) =
        reify fuel p >>= λ p′ →
        reify fuel q >>= λ q′ →
        R.returnTC (R.con (quote Q._∙′_) (p′ v∷ q′ v∷ []))
      composition _ = leaf original

      congruence : List R.Term → R.TC R.Term
      congruence (f ∷ p ∷ []) = liftTC (mapPath f) (reify fuel p)
      congruence _ = leaf original

      binary : List R.Term → R.TC R.Term
      binary (f ∷ p ∷ q ∷ []) =
        reflexive p >>= λ pRefl →
        if pRefl then (
          endpoints p >>= λ { (x , _) →
          liftTC (mapPath (R.def (quote _$_) (f v∷ x v∷ []))) (reify fuel q) })
        else (
          reflexive q >>= λ qRefl →
          if qRefl then (
            endpoints q >>= λ { (y , _) →
            liftTC (mapPath (R.def (quote flip) (f v∷ y v∷ []))) (reify fuel p) })
          else leaf original)
      binary _ = leaf original
    reifyHead fuel original (R.lam R.visible (R.abs _ body)) =
      (scan fuel 0 body >>= λ where
        (varying p , body′) →
          liftTC (mapPath (vlam "x" body′)) (reify fuel p)
        (constant , _) → R.returnTC (R.con (quote Q.refl′) []))
      <|> leaf original
    reifyHead _ original _ = leaf original

    leaf : R.Term → R.TC R.Term
    leaf p = waitForMetas p >> R.returnTC (atom p)

reassocMacro : R.Term → R.Term → R.TC Unit
reassocMacro proof hole = R.withNormalisation false (
  solve (R.inferType hole) <|> solve (normalisedType hole))
  where
  solve : R.TC R.Type → R.TC Unit
  solve ty = ty >>= pathEnds >>= λ { (p , q) →
    reify 256 p >>= λ p′ →
    reify 256 q >>= λ q′ →
    R.unify hole (R.def (quote Q.reassoc) (p′ v∷ q′ v∷ proof v∷ [])) }

-- Generate a function whose ordinary argument is the normal-form witness.
-- Quoting that witness as a macro argument elaborates it too early: the
-- implicit prefixes in expressions such as ∙l ∙l (shuffleSymL refl) then
-- have no expected type. Establish a non-dependent arrow first, so its
-- codomain can be inferred from the goal without depending on the witness.
-- Commit this constraint before possibly blocking on the goal's type.
reassocWithMacro : R.Term → R.TC Unit
reassocWithMacro hole = R.withNormalisation false (
  R.checkType hole (R.def (quote Arrow) (R.unknown v∷ R.unknown v∷ [])) >>
  R.commitTC >>
  (solve (R.inferType hole) <|> solve (normalisedType hole)))
  where
  solve : R.TC R.Type → R.TC Unit
  solve ty = ty >>= λ where
    (R.meta m _) → R.blockTC (R.blockerMeta m)
    (R.pi dom (R.abs _ ty)) →
      pathEnds ty >>= λ { (p , q) →
      strengthen 1 0 p >>= λ p →
      strengthen 1 0 q >>= λ q →
      reify 256 p >>= λ p′ →
      reify 256 q >>= λ q′ →
      R.unify hole (R.def (quote Q.reassoc) (p′ v∷ q′ v∷ [])) }
    _ → R.typeError [ R.strErr "reassoc-with: expected a normal-form proof argument" ]

macro
  reassoc! : R.Term → R.TC Unit
  reassoc! = reassocMacro (R.def (quote refl) [])

  reassoc-with : R.Term → R.TC Unit
  reassoc-with = reassocWithMacro

  reassoc-on : R.Term → R.Term → R.Term → R.TC Unit
  reassoc-on p q hole =
    R.checkType hole (R.def (quote Arrow)
      (R.unknown v∷ R.def (quote _≡_) (p v∷ q v∷ []) v∷ [])) >>
    reassocWithMacro hole
