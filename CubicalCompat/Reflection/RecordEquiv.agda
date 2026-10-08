{-

  Reflection-based tools for converting between iterated record types, particularly between
  record types and iterated Σ-types.

  The main functions are `declareRecordIsoΣ` and `declareRecordIsoΣ'`. See end of file for
  example usage.

-}
{-# OPTIONS --no-exact-split #-}
module CubicalCompat.Reflection.RecordEquiv where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (case_return_of_)
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Data.List as List
open import Cubical.Data.Nat
open import Cubical.Data.Bool using (Bool; true; false; if_then_else_)
open import Cubical.Data.Maybe as Maybe
open import Cubical.Data.Sigma

open import Agda.Builtin.String
import Agda.Builtin.Reflection as R
open import CubicalCompat.Reflection.Base

-- Intended to represent a (possibly nested) field of a record type. For example, the list
-- "snd" ∷ fst" ∷ []` would represent the field `.fst .snd`.
Projections = List R.Name

-- Intended to represent a bijection between two record types by an association list
-- between (possibly nested) fields of the one and the other. The `Maybe`s are included to
-- allow dropping fields of Unit (or other definitionally unique) type.
--
-- For example, the correspondence
--
--   .fst .fst ↔ .snd
--   .fst .snd ↔ .fst
--   .snd ↔ ∅
--
-- between (A × B) × Unit and B × A would be represented by the list
--
--   [ (just ["fst"; "fst"] , just ["snd"])
--   ; (just ["snd"; "fst"] , just ["fst"])
--   ; (just ["snd"] , nothing)
--   ]
RecordAssoc = List (Maybe Projections × Maybe Projections)

-- Describes a correspondence between a non-nested record and an iterated Σ-type; more
-- convenient to work with than RecordAssoc in this special case, which is the most common
-- one. For example,
--
--   leaf "a" , (leaf "b" , leaf "c")
--
-- describes the following RecordAssoc:
--
--   .fst ↔ .a
--   .snd .fst ↔ .b
--   .snd .snd ↔ .c
--
-- The `unit` constructor is the correspondence between Unit ("nullary Σ") and the empty
-- record.
data ΣFormat : Type where
  leaf : R.Name → ΣFormat
  _,_ : ΣFormat → ΣFormat → ΣFormat
  unit : ΣFormat

infixr 4 _,_

-- Inverse of a correspondence between record types
flipRecordAssoc : RecordAssoc → RecordAssoc
flipRecordAssoc = List.map λ {p .fst → p .snd; p .snd → p .fst}

-- The identity correspondence on the domain of a given correspondence
fstIdRecordAssoc : RecordAssoc → RecordAssoc
fstIdRecordAssoc = List.map λ {p .fst → p .fst; p .snd → p .fst}

-- Constructs a ΣFormat from a list of fields meant to represent a right-associated Σ-type
List→ΣFormat : List R.Name → ΣFormat
List→ΣFormat [] = unit
List→ΣFormat (x ∷ []) = leaf x
List→ΣFormat (x ∷ y ∷ xs) = leaf x , List→ΣFormat (y ∷ xs)

-- Converts a ΣFormat to an association list as described above.
-- The domain of the RecordAssoc is the record type, the codomain is the Σ-type.
ΣFormat→RecordAssoc : ΣFormat → RecordAssoc
ΣFormat→RecordAssoc = go []
  where
  go : List R.Name → ΣFormat → RecordAssoc
  go prefix unit = [ nothing , just prefix ]
  go prefix (leaf fieldName) = [ just [ fieldName ] , just prefix ]
  go prefix (sig₁ , sig₂) =
    go (quote fst ∷ prefix) sig₁ ++ go (quote snd ∷ prefix) sig₂

-- Define a reflected type with the shape of the Σ-type described by a ΣFormat.
-- The type arguments to the Σ are filled in with unsolved metavariables.
ΣFormat→Ty : ΣFormat → R.Type
ΣFormat→Ty unit = R.def (quote Unit) []
ΣFormat→Ty (leaf _) = R.unknown
ΣFormat→Ty (sig₁ , sig₂) =
  R.def (quote Σ) (ΣFormat→Ty sig₁ v∷ R.lam R.visible (R.abs "_" (ΣFormat→Ty sig₂)) v∷ [])

-- Given the name of a record type and a ΣFormat describing an isomorphism between this
-- type and a Σ-type, constructs a reflected type of isomorphisms between the record and
-- Σ-type. If the record type takes parameters or indices, then the result is a similarly
-- parameterized family of isomorphisms. All parameters to the isomorphism are made
-- implicit.
recordName→isoTy : R.Name → ΣFormat → R.TC R.Term
recordName→isoTy name σ =
  R.withReconstructed true (
    R.getDefinition name >>= λ where
      (R.record-type ctor fs) →
        R.getType name >>= λ recordTy →
        R.getType ctor >>= go [] (List.map (λ {(R.arg _ n) → n}) fs) recordTy
      _ → R.typeError (R.strErr "Not a record type name: " ∷ R.nameErr name ∷ []))
  where
  -- Field types in the constructor telescope refer to earlier fields by de Bruijn
  -- indices. Reindex those references to the appropriate Σ variables/projections.
  -- Unlike inferring unknown Σ components from projections, this keeps complete
  -- implicit/instance Π-types, including the types of dependent law fields.
  FieldTypes = List (R.Name × (List R.Name × R.Type))
  FieldValues = List (R.Name × (ℕ × Projections))

  project : Projections → R.Term → R.Term
  project [] t = t
  project (p ∷ ps) t = R.def p (project ps t v∷ [])

  appendArgs : R.Term → List (R.Arg R.Term) → R.TC R.Term
  appendArgs (R.var n args) ts = R.returnTC (R.var n (args ++ ts))
  appendArgs (R.def n args) ts = R.returnTC (R.def n (args ++ ts))
  appendArgs R.unknown [] = R.returnTC R.unknown
  appendArgs _ _ = R.typeError [ R.strErr "Expected a variable or field projection" ]

  freeIndex : ℕ → ℕ → Maybe ℕ
  freeIndex n zero = just n
  freeIndex zero (suc d) = nothing
  freeIndex (suc n) (suc d) = freeIndex n d

  mutual
    hasPatternLambda : R.Term → Bool
    hasPatternLambda (R.pat-lam _ _) = true
    hasPatternLambda (R.var _ args) = hasPatternLambdaArgs args
    hasPatternLambda (R.con _ args) = hasPatternLambdaArgs args
    hasPatternLambda (R.def _ args) = hasPatternLambdaArgs args
    hasPatternLambda (R.meta _ args) = hasPatternLambdaArgs args
    hasPatternLambda (R.lam _ (R.abs _ t)) = hasPatternLambda t
    hasPatternLambda (R.pi (R.arg _ a) (R.abs _ b)) =
      if hasPatternLambda a then true else hasPatternLambda b
    hasPatternLambda (R.agda-sort (R.set t)) = hasPatternLambda t
    hasPatternLambda (R.agda-sort (R.prop t)) = hasPatternLambda t
    hasPatternLambda _ = false

    hasPatternLambdaArgs : List (R.Arg R.Term) → Bool
    hasPatternLambdaArgs [] = false
    hasPatternLambdaArgs (R.arg _ t ∷ ts) =
      if hasPatternLambda t then true else hasPatternLambdaArgs ts

  -- Copying a pattern lambda creates a new auxiliary definition that need not
  -- be definitionally equal to the original. Keep all Π-binders (especially
  -- hidden/instance binders), but infer such a field's body from its projection.
  inferBody : R.Type → R.Type
  inferBody (R.pi (R.arg i a) (R.abs s b)) =
    R.pi (R.arg i (if hasPatternLambda a then R.unknown else a)) (R.abs s (inferBody b))
  inferBody _ = R.unknown

  mutual
    reindex : (ℕ → ℕ → R.TC R.Term) → ℕ → R.Term → R.TC R.Term
    reindex f d (R.var n args) =
      Maybe.rec (R.returnTC (v n)) (λ k → f k d) (freeIndex n d) >>= λ t →
      reindexArgs f d args >>= appendArgs t
    reindex f d (R.con n args) = liftTC (R.con n) (reindexArgs f d args)
    reindex f d (R.def n args) = liftTC (R.def n) (reindexArgs f d args)
    reindex f d (R.meta n args) = liftTC (R.meta n) (reindexArgs f d args)
    reindex f d (R.lam i (R.abs s t)) =
      liftTC (λ t′ → R.lam i (R.abs s t′)) (reindex f (suc d) t)
    reindex f d (R.pi (R.arg i a) (R.abs s b)) =
      reindex f d a >>= λ a′ →
      liftTC (λ b′ → R.pi (R.arg i a′) (R.abs s b′)) (reindex f (suc d) b)
    reindex f d (R.agda-sort (R.set t)) =
      liftTC (λ t′ → R.agda-sort (R.set t′)) (reindex f d t)
    reindex f d (R.agda-sort (R.prop t)) =
      liftTC (λ t′ → R.agda-sort (R.prop t′)) (reindex f d t)
    -- Pattern lambdas have already been removed by inferBody.
    reindex _ _ (R.pat-lam _ _) = R.returnTC R.unknown
    reindex _ _ t = R.returnTC t

    reindexArgs : (ℕ → ℕ → R.TC R.Term) → ℕ
      → List (R.Arg R.Term) → R.TC (List (R.Arg R.Term))
    reindexArgs _ _ [] = R.returnTC []
    reindexArgs f d (R.arg i t ∷ ts) =
      reindex f d t >>= λ t′ →
      liftTC (R.arg i t′ ∷_) (reindexArgs f d ts)

  fieldTypes : List R.Name → List R.Name → R.Type → R.TC FieldTypes
  fieldTypes _ [] _ = R.returnTC []
  fieldTypes previous (n ∷ ns) (R.pi (R.arg _ ty) (R.abs _ rest)) =
    liftTC ((n , (previous , ty)) ∷_) (fieldTypes (n ∷ previous) ns rest)
  fieldTypes _ _ _ = R.typeError [ R.strErr "Expected a record constructor telescope" ]

  fieldValue : FieldValues → R.Name → ℕ → R.TC R.Term
  -- As in convertClauses, let Agda fill dropped, definitionally unique fields.
  fieldValue [] _ _ = R.returnTC R.unknown
  fieldValue ((n , (i , ps)) ∷ values) m d =
    if R.primQNameEquality n m then R.returnTC (project ps (v (i + d)))
    else fieldValue values m d

  resolve : FieldValues → ℕ → List R.Name → ℕ → ℕ → R.TC R.Term
  resolve _ depth [] n d = R.returnTC (v (n + depth + d))
  resolve values _ (n ∷ _) zero d = fieldValue values n d
  resolve values depth (_ ∷ ns) (suc n) d = resolve values depth ns n d

  leafTy : FieldTypes → FieldValues → ℕ → R.Name → R.TC R.Type
  leafTy [] _ _ n = R.typeError (R.strErr "Not a record field: " ∷ R.nameErr n ∷ [])
  leafTy ((n , (previous , ty)) ∷ types) values depth m =
    if R.primQNameEquality n m then
      reindex (resolve values depth previous) 0 (if hasPatternLambda ty then inferBody ty else ty)
    else leafTy types values depth m

  bindValues : Projections → ΣFormat → FieldValues
  bindValues ps unit = []
  bindValues ps (leaf n) = [ n , (0 , ps) ]
  bindValues ps (l , r) =
    bindValues (quote fst ∷ ps) l ++ bindValues (quote snd ∷ ps) r

  sigmaTy : FieldTypes → FieldValues → ℕ → ΣFormat → R.TC R.Type
  sigmaTy _ _ _ unit = R.returnTC (R.def (quote Unit) [])
  sigmaTy types values depth (leaf n) = leafTy types values depth n
  sigmaTy types values depth (l , r) =
    sigmaTy types values depth l >>= λ a →
    sigmaTy types
      (bindValues [] l ++ List.map (λ {(n , (i , ps)) → n , (suc i , ps)}) values)
      (suc depth) r >>= λ b →
    R.returnTC (R.def (quote Σ) (a v∷ R.lam R.visible (R.abs "_" b) v∷ []))

  -- Recurses on the type of the named record type
  go : List R.ArgInfo → List R.Name → R.Type → R.Type → R.TC R.Term
  go acc fs (R.pi (R.arg i argTy) (R.abs s ty)) (R.pi _ (R.abs _ rest)) =
    -- If the record takes a parameter, the returned isomorphism is likewise parameterized
    liftTC (λ t → R.pi (R.arg i' argTy) (R.abs s t)) (go (i ∷ acc) fs ty rest)
    where
    i' = R.arg-info R.hidden (R.modality R.relevant R.quantity-ω)
  go acc fs (R.agda-sort _) ctorTy =
    -- Main case, constructs isomorphism type
    fieldTypes [] fs ctorTy >>= λ types →
    sigmaTy types [] 0 σ >>= λ σTy →
    R.returnTC (R.def (quote Iso) (R.def name (makeArgs 0 [] acc) v∷ σTy v∷ []))
    where
    makeArgs : ℕ → List (R.Arg R.Term) → List R.ArgInfo → List (R.Arg R.Term)
    makeArgs n acc [] = acc
    makeArgs n acc (i ∷ infos) = makeArgs (suc n) (R.arg i (v n) ∷ acc) infos
  go _ _ _ _ = R.typeError (R.strErr "Not a record type name: " ∷ R.nameErr name ∷ [])

-- Given an association list `al` defining a correspondence between record types (say R
-- and S) and a `term` belonging to R, produces clauses defining an element of S, with
-- each field of S instantiated with a field of `term` according to `al`.  For example,
-- the correspondence
--
--   .fst ↔ .a
--   .snd .fst ↔ .b
--   .snd .snd ↔ ∅
--   ∅ ↔ .c
--
-- would produce the clauses
--
-- ... .a = term .fst
-- ... .b = term .snd
-- ... .c = _
--
-- Here the type of .c should have a definitionally unique element, so
-- we can safely fill it with an unsolved metavariable.
convertClauses : RecordAssoc → R.Term → List R.Clause
convertClauses al term = fixIfEmpty (List.filterMap makeClause al)
  where
  makeClause : Maybe Projections × Maybe Projections → Maybe R.Clause
  makeClause (projl , just projr) =
    just (R.clause [] (goPat [] projr) (Maybe.rec R.unknown goTm projl))
    where
    goPat : List (R.Arg R.Pattern) → List R.Name → List (R.Arg R.Pattern)
    goPat acc [] = acc
    goPat acc (π ∷ projs) = goPat (varg (R.proj π) ∷ acc) projs

    goTm : List R.Name → R.Term
    goTm [] = term
    goTm (π ∷ projs) = R.def π [ varg (goTm projs) ]
  makeClause (_ , nothing) = nothing

  -- If there end up being zero clauses, then S should be a type with a definitionally
  -- unique element, so we return a single clause defined by an unsolved metavariable.
  fixIfEmpty : List R.Clause → List R.Clause
  fixIfEmpty [] = [ R.clause [] [] R.unknown ]
  fixIfEmpty (c ∷ cs) = c ∷ cs

-- Apply functions to the telescope and pattern parts of a clause
mapClause :
  (List (String × R.Arg R.Type) → List (String × R.Arg R.Type))
  → (List (R.Arg R.Pattern) → List (R.Arg R.Pattern))
  → (R.Clause → R.Clause)
mapClause f g (R.clause tel ps t) = R.clause (f tel) (g ps) t
mapClause f g (R.absurd-clause tel ps) = R.absurd-clause (f tel) (g ps)

-- Given a ΣFormat `σ` relating a record type R and Σ-type S, returns
-- a list of clauses defining an isomorphism between R and S.
recordIsoΣClauses : ΣFormat → List R.Clause
recordIsoΣClauses σ =
  funClauses (quote Iso.fun) R↔Σ ++
  funClauses (quote Iso.inv) Σ↔R ++
  -- Clauses for the forward and backward inverse conditions
  pathClauses (quote Iso.rightInv) Σ↔R ++
  pathClauses (quote Iso.leftInv) R↔Σ
  where
  R↔Σ = ΣFormat→RecordAssoc σ
  Σ↔R = flipRecordAssoc R↔Σ

  -- Given an association list `al` for a correspondence R ↔ S, produces the list of
  -- clauses defining a function from R to S.
  -- The `prefix` will be either `Iso.fun` or `Iso.inv`.
  funClauses : R.Name → RecordAssoc → List R.Clause
  funClauses prefix al =
    List.map
      -- Introduce a new variable of the input type
      (mapClause
        (("_" , varg R.unknown) ∷_)
        (λ ps → R.proj prefix v∷ R.var 0 v∷ ps))
      -- Each clause is a projection applied to the input variable
      (convertClauses al (v 0))

  -- Given an association list `al` for a correspondence R ↔ S, produces the list of
  -- clauses defining the inverse path for the round-trip R → S → R.
  -- The `prefix` will be either `Iso.rightInv` or `Iso.leftInv`.
  pathClauses : R.Name → RecordAssoc → List R.Clause
  pathClauses prefix al =
    List.map
      -- Introduce a variable of the input type and an interval variable
      (mapClause
        (λ vs → ("_" , varg R.unknown) ∷ ("_" , varg (R.def (quote I) [])) ∷ vs)
        (λ ps → R.proj prefix v∷ R.var 1 v∷ R.var 0 v∷ ps))
      -- The inverse condition at each clause holds by reflexivity
      (convertClauses (fstIdRecordAssoc al) (v 1))


------------------------------------------------------------------------------------------
-- Main functions
------------------------------------------------------------------------------------------

-- Given a ΣFormat describing a correspondence between a record and nested Σ-type,
-- constructs an isomorphism between them as a term.
--
-- Because this term is a large pattern-matching lambda, it is better to use the
-- declare* functions below, which declare a named function.
recordIsoΣTerm : ΣFormat → R.Term
recordIsoΣTerm σ = R.pat-lam (recordIsoΣClauses σ) []

-- Given a name `idName`, a ΣFormat `σ` describing a correspondence between a record and
-- nested Σ-type, and the name `recordName` of the record type, declares a function with
-- name `idName` defining an isomorphism between the two types (with implicit parameters
-- corresponding to the parameters and indices of the record type).
declareRecordIsoΣ' : R.Name → ΣFormat → R.Name → R.TC Unit
declareRecordIsoΣ' idName σ recordName =
  recordName→isoTy recordName σ >>= λ isoTy →
  R.declareDef (varg idName) isoTy >>
  R.getDefinition recordName >>= λ where
    (R.record-type ctor fs) →
      R.getType recordName >>= λ recordTy →
      R.getType ctor >>= R.normalise >>= λ ctorTy →
      fieldBinders fs recordTy ctorTy >>= λ binders →
      R.defineFun idName (List.map (etaClause binders) (recordIsoΣClauses σ))
    _ → R.typeError [ R.strErr "Expected a record type" ]
  where
  Binders = List (String × R.ArgInfo)
  FieldBinders = List (R.Name × Binders)

  leadingBinders : R.Type → Binders
  leadingBinders (R.pi (R.arg (R.arg-info R.visible _) _) _) = []
  leadingBinders (R.pi (R.arg i _) (R.abs s ty)) = (s , i) ∷ leadingBinders ty
  leadingBinders _ = []

  collectBinders : List (R.Arg R.Name) → R.Type → R.TC FieldBinders
  collectBinders [] _ = R.returnTC []
  collectBinders (R.arg _ n ∷ fs) (R.pi (R.arg _ ty) (R.abs _ rest)) =
    liftTC ((n , leadingBinders ty) ∷_) (collectBinders fs rest)
  collectBinders _ _ = R.typeError [ R.strErr "Expected a record constructor telescope" ]

  fieldBinders : List (R.Arg R.Name) → R.Type → R.Type → R.TC FieldBinders
  fieldBinders fs (R.pi _ (R.abs _ ty)) (R.pi _ (R.abs _ rest)) = fieldBinders fs ty rest
  fieldBinders fs (R.agda-sort _) ctorTy = collectBinders fs ctorTy
  fieldBinders _ _ _ = R.typeError [ R.strErr "Expected a record type" ]

  lookupBinders : R.Name → FieldBinders → Binders
  lookupBinders _ [] = []
  lookupBinders n ((m , bs) ∷ fields) =
    if R.primQNameEquality n m then bs else lookupBinders n fields

  binderArgs : Binders → List (R.Arg R.Term)
  binderArgs [] = []
  binderArgs ((_ , i) ∷ bs) = R.arg i (v (List.length bs)) ∷ binderArgs bs

  binderPatterns : Binders → List (R.Arg R.Pattern)
  binderPatterns [] = []
  binderPatterns ((_ , i) ∷ bs) = R.arg i (R.var (List.length bs)) ∷ binderPatterns bs

  raisePattern : ℕ → R.Arg R.Pattern → R.Arg R.Pattern
  raisePattern k (R.arg i (R.var n)) = R.arg i (R.var (n + k))
  raisePattern _ p = p

  -- Force the field's implicit-only arguments to remain bound variables even
  -- when its inferred body is still a meta. This also avoids instance search.
  etaClause : FieldBinders → R.Clause → R.Clause
  etaClause fields c@(R.clause tel (varg (R.proj p) ∷ ps) (R.def n (varg (R.var zero []) ∷ []))) =
    let bs = lookupBinders n fields in
    if R.primQNameEquality p (quote Iso.fun) then
      R.clause (tel ++ List.map (λ {(s , i) → s , R.arg i R.unknown}) bs)
        (R.proj p v∷ (List.map (raisePattern (List.length bs)) ps ++ binderPatterns bs))
        (R.def n (v (List.length bs) v∷ binderArgs bs))
    else c
  etaClause _ c = c

-- Given a name `idName` and the name `recordName` of a record type, declares a function
-- with name `idName` defining an isomorphism from the record type to the right-associated
-- Σ-type corresponding to its list of fields (with implicit parameters corresponding to
-- the parameters and indices of the record type).
declareRecordIsoΣ : R.Name → R.Name → R.TC Unit
declareRecordIsoΣ idName recordName =
  R.getDefinition recordName >>= λ where
  (R.record-type _ fs) →
    let σ = List→ΣFormat (List.map (λ {(R.arg _ n) → n}) fs) in
    declareRecordIsoΣ' idName σ recordName
  _ →
    R.typeError (R.strErr "Not a record type name:" ∷ R.nameErr recordName ∷ [])


------------------------------------------------------------------------------------------
-- Examples
------------------------------------------------------------------------------------------

private
  module Example where
    variable
      ℓ ℓ' : Level
      A : Type ℓ
      B : A → Type ℓ'

    record Example0 {A : Type ℓ} (B : A → Type ℓ') : Type (ℓ-max ℓ ℓ') where
      no-eta-equality -- works with or without eta equality
      field
        cool : A
        fun : A
        wow : B cool

    -- Declares a function `Example0IsoΣ` that gives an isomorphism between the record type and a
    -- right-associated nested Σ-type (with the parameters to Example0 as implict arguments).
    unquoteDecl Example0IsoΣ = declareRecordIsoΣ Example0IsoΣ (quote Example0)

    -- `Example0IsoΣ` has the type we expect
    test0 : Iso (Example0 B) (Σ[ a ∈ A ] (Σ[ _ ∈ A ] B a))
    test0 = Example0IsoΣ

    -- Custom association and reordering must also reindex dependent field types.
    unquoteDecl Example0LeftIsoΣ = declareRecordIsoΣ' Example0LeftIsoΣ
      ((leaf (quote Example0.cool) , leaf (quote Example0.fun)) , leaf (quote Example0.wow))
      (quote Example0)

    test0-left : Iso (Example0 B) (Σ[ p ∈ (A × A) ] B (fst p))
    test0-left = Example0LeftIsoΣ

    unquoteDecl Example0ReorderedIsoΣ = declareRecordIsoΣ' Example0ReorderedIsoΣ
      (leaf (quote Example0.fun) , leaf (quote Example0.cool) , leaf (quote Example0.wow))
      (quote Example0)

    test0-reordered : Iso (Example0 B) (Σ[ _ ∈ A ] (Σ[ a ∈ A ] B a))
    test0-reordered = Example0ReorderedIsoΣ

    -- A record with no fields is isomorphic to Unit

    record Example1 : Type where

    unquoteDecl Example1IsoΣ = declareRecordIsoΣ Example1IsoΣ (quote Example1)

    test1 : Iso Example1 Unit
    test1 = Example1IsoΣ

    record Example2 : Type₁ where
      field
        implicit-id : {A : Type} → A → A
        implicit-id-law : {A : Type} (a : A) → implicit-id a ≡ a

    unquoteDecl Example2IsoΣ = declareRecordIsoΣ Example2IsoΣ (quote Example2)

    test2 : Iso Example2
      (Σ[ f ∈ ({A : Type} → A → A) ] ({A : Type} (a : A) → f a ≡ a))
    test2 = Example2IsoΣ

    implicit-example : Example2
    implicit-example .Example2.implicit-id a = a
    implicit-example .Example2.implicit-id-law a = refl

    test2-fun : Iso.fun Example2IsoΣ implicit-example
      ≡ ((λ {A} (a : A) → a) , (λ {A} (a : A) → refl))
    test2-fun = refl

    test2-inv : {A : Type} (a : A)
      → Iso.inv Example2IsoΣ ((λ {A} (a : A) → a) , (λ {A} (a : A) → refl))
          .Example2.implicit-id a ≡ a
    test2-inv a = refl

    test2-term : Iso Example2
      (Σ[ f ∈ ({A : Type} → A → A) ] ({A : Type} (a : A) → f a ≡ a))
    unquoteDef test2-term =
      R.defineFun test2-term [ R.clause [] []
        (recordIsoΣTerm (leaf (quote Example2.implicit-id) , leaf (quote Example2.implicit-id-law))) ]

    record Example3 {A : Type ℓ} (B : A → Type ℓ') : Type (ℓ-max ℓ ℓ') where
      no-eta-equality
      field
        choose : {a : A} {b : B a} → B a
        choose-law : {a : A} {b : B a} → choose {a} {b} ≡ b

    unquoteDecl Example3IsoΣ = declareRecordIsoΣ Example3IsoΣ (quote Example3)

    test3 : Iso (Example3 B)
      (Σ[ f ∈ ({a : A} {b : B a} → B a) ] ({a : A} {b : B a} → f {a} {b} ≡ b))
    test3 = Example3IsoΣ

    unquoteDecl Example3CustomIsoΣ = declareRecordIsoΣ' Example3CustomIsoΣ
      ((unit , leaf (quote Example3.choose)) , leaf (quote Example3.choose-law))
      (quote Example3)

    test3-custom : Iso (Example3 B)
      (Σ[ p ∈ (Unit × ({a : A} {b : B a} → B a)) ]
        ({a : A} {b : B a} → snd p {a} {b} ≡ b))
    test3-custom = Example3CustomIsoΣ

    record Example4 : Type₁ where
      field
        from-instance : {A : Type} → {{a : A}} → A
        from-instance-law : {A : Type} {{a : A}} → from-instance {A} {{a}} ≡ a

    unquoteDecl Example4IsoΣ = declareRecordIsoΣ Example4IsoΣ (quote Example4)

    test4 : Iso Example4
      (Σ[ f ∈ ({A : Type} → {{a : A}} → A) ] ({A : Type} {{a : A}} → f {A} {{a}} ≡ a))
    test4 = Example4IsoΣ

    record Example5 : Type₁ where
      field
        {Carrier} : Type
        value : Carrier

    unquoteDecl Example5IsoΣ = declareRecordIsoΣ Example5IsoΣ (quote Example5)

    test5 : Iso Example5 (Σ[ A ∈ Type ] A)
    test5 = Example5IsoΣ

    module Parameterised (A : Type) where
      record Example6 : Type₁ where
        field
          apply : {B : Type} → (A → B) → A → B

      unquoteDecl Example6IsoΣ = declareRecordIsoΣ Example6IsoΣ (quote Example6)

      test6 : Iso Example6 ({B : Type} → (A → B) → A → B)
      test6 = Example6IsoΣ

    record Example7 (B : Unit → Type ℓ) : Type ℓ where
      field
        ignored : Unit
        dependent : B ignored

    unquoteDecl Example7IsoΣ = declareRecordIsoΣ' Example7IsoΣ
      (leaf (quote Example7.dependent) , leaf (quote Example7.ignored)) (quote Example7)

    test7 : {B : Unit → Type ℓ} → Iso (Example7 B) (B tt × Unit)
    test7 = Example7IsoΣ

    -- Dependencies also occur inside reflected pattern lambdas in field types.
    record Example8 : Type₁ where
      field
        implicit-id : {A : Type} → A → A
        case-law : {A : Type} (a : A) (b : Bool)
          → (case b return (λ _ → A) of λ { true → implicit-id a ; false → a }) ≡ a
        hidden-case-law : {A : Type} {a : A} {{b : Bool}}
          → (case b return (λ _ → A) of λ { true → implicit-id a ; false → a }) ≡ a

    unquoteDecl Example8IsoΣ = declareRecordIsoΣ Example8IsoΣ (quote Example8)

    example8 : Example8
    example8 .Example8.implicit-id a = a
    example8 .Example8.case-law a true = refl
    example8 .Example8.case-law a false = refl
    example8 .Example8.hidden-case-law {{b = true}} = refl
    example8 .Example8.hidden-case-law {{b = false}} = refl

    test8 : {A : Type} (a : A) → Iso.fun Example8IsoΣ example8 .fst a ≡ a
    test8 a = refl

    open import Cubical.WildCat.Functor using (WildFunctor)

    unquoteDecl WildFunctorIsoΣ = declareRecordIsoΣ WildFunctorIsoΣ (quote WildFunctor)
