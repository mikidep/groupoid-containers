{-

  Generate record equality constructors from fieldwise dependent paths.

    unquoteDecl MyRecord≡ = declareRecordPath MyRecord≡ (quote MyRecord)

  Record parameters and the two endpoints are implicit. There is one explicit
  path argument for each field, in declaration order. Constant-domain function
  fields are characterised pointwise, preserving hidden and instance binders.
  When a function's domain depends on an earlier field, its remaining function
  type is kept inside PathP instead.

  Alternatively, give the characterisation's type by hand and generate just
  its proof with defineRecordPath. Record parameters are fixed along the path.
  Empty records need eta equality or permission to pattern match (`pattern`).

-}
{-# OPTIONS --no-exact-split #-}
module CubicalCompat.Reflection.RecordPath where

open import Cubical.Foundations.Prelude
open import Cubical.Data.List as List
open import Cubical.Data.Nat
open import Cubical.Data.Bool using (Bool; true; false; if_then_else_)
open import Cubical.Data.Sigma
open import Agda.Builtin.String
open import Agda.Builtin.Char using (Char; primCharEquality)
import Agda.Builtin.Reflection as R
open import CubicalCompat.Reflection.Base

private
  Binders = List (String × R.ArgInfo)
  FieldInfo = R.Name × (R.Type × Binders)

  below : ℕ → ℕ → Bool
  below _ zero = false
  below zero (suc _) = true
  below (suc n) (suc m) = below n m

  inFields : ℕ → ℕ → ℕ → Bool
  inFields n zero p = below n p
  inFields zero (suc _) _ = false
  inFields (suc n) (suc d) p = inFields n d p

  -- A pattern lambda is conservatively treated as a dependency too: rechecking
  -- it would introduce a fresh, potentially non-convertible auxiliary function.
  mutual
    mentions : (ℕ → Bool) → ℕ → R.Term → Bool
    mentions f d (R.var n args) =
      if below n d then mentionsArgs f d args else
      if f (n ∸ d) then true else mentionsArgs f d args
    mentions f d (R.def _ args) = mentionsArgs f d args
    mentions f d (R.con _ args) = mentionsArgs f d args
    mentions f d (R.meta _ args) = mentionsArgs f d args
    mentions f d (R.lam _ (R.abs _ t)) = mentions f (suc d) t
    mentions f d (R.pi (R.arg _ a) (R.abs _ b)) =
      if mentions f d a then true else mentions f (suc d) b
    mentions f d (R.agda-sort (R.set t)) = mentions f d t
    mentions f d (R.agda-sort (R.prop t)) = mentions f d t
    mentions _ _ (R.pat-lam _ _) = true
    mentions _ _ _ = false

    mentionsArgs : (ℕ → Bool) → ℕ → List (R.Arg R.Term) → Bool
    mentionsArgs _ _ [] = false
    mentionsArgs f d (R.arg _ t ∷ ts) =
      if mentions f d t then true else mentionsArgs f d ts

  constantBinders : ℕ → ℕ → R.Type → Binders
  constantBinders p d (R.pi (R.arg i a) (R.abs s b)) =
    if mentions (λ n → inFields n d p) 0 a then []
    else (s , i) ∷ constantBinders p (suc d) b
  constantBinders _ _ _ = []

  fieldInfos : ℕ → List (R.Arg R.Name) → R.Type → R.TC (List FieldInfo)
  fieldInfos _ [] _ = R.returnTC []
  fieldInfos p (R.arg _ n ∷ fs) (R.pi (R.arg _ ty) (R.abs _ rest)) =
    liftTC ((n , (ty , constantBinders p 0 ty)) ∷_) (fieldInfos (suc p) fs rest)
  fieldInfos _ _ _ = R.typeError [ R.strErr "Expected a record constructor telescope" ]

  recordFields : R.Type → List (R.Arg R.Name) → R.Type → R.TC (List FieldInfo)
  recordFields (R.pi _ (R.abs _ ty)) fs (R.pi _ (R.abs _ rest)) = recordFields ty fs rest
  recordFields (R.agda-sort _) fs ctorTy = fieldInfos 0 fs ctorTy
  recordFields _ _ _ = R.typeError [ R.strErr "Expected a record type" ]

  fieldLabel : R.Name → String
  fieldLabel n = lastSegment (primStringToList (R.primShowQName n)) []
    where
    lastSegment : List Char → List Char → String
    lastSegment [] acc = primStringFromList (List.rev acc)
    lastSegment (c ∷ cs) acc =
      if primCharEquality c '.' then lastSegment cs [] else lastSegment cs (c ∷ acc)

  mutual
    shift : ℕ → ℕ → R.Term → R.Term
    shift k d (R.var n args) =
      R.var (if below n d then n else n + k) (shiftArgs k d args)
    shift k d (R.def n args) = R.def n (shiftArgs k d args)
    shift k d (R.con n args) = R.con n (shiftArgs k d args)
    shift k d (R.meta n args) = R.meta n (shiftArgs k d args)
    shift k d (R.lam i (R.abs s t)) = R.lam i (R.abs s (shift k (suc d) t))
    shift k d (R.pi (R.arg i a) (R.abs s b)) =
      R.pi (R.arg i (shift k d a)) (R.abs s (shift k (suc d) b))
    shift k d (R.agda-sort (R.set t)) = R.agda-sort (R.set (shift k d t))
    shift k d (R.agda-sort (R.prop t)) = R.agda-sort (R.prop (shift k d t))
    shift _ _ (R.pat-lam _ _) = R.unknown
    shift _ _ t = t

    shiftArgs : ℕ → ℕ → List (R.Arg R.Term) → List (R.Arg R.Term)
    shiftArgs _ _ [] = []
    shiftArgs k d (R.arg i t ∷ ts) = R.arg i (shift k d t) ∷ shiftArgs k d ts

  binderArgs : Binders → List (R.Arg R.Term)
  binderArgs [] = []
  binderArgs ((_ , i) ∷ bs) = R.arg i (v (List.length bs)) ∷ binderArgs bs

  lambdas : Binders → R.Term → R.Term
  lambdas [] t = t
  lambdas ((s , R.arg-info i _) ∷ bs) t = R.lam i (R.abs s (lambdas bs t))

  -- A pointwise path is applied to its ordinary arguments before the interval.
  -- Eta-expand partial applications when an earlier field occurs as a function.
  fieldValue : Binders → ℕ → ℕ → List (R.Arg R.Term) → R.Term
  fieldValue bs pathIndex intervalIndex args = consume bs [] args
    where
    consume : Binders → List (R.Arg R.Term) → List (R.Arg R.Term) → R.Term
    consume [] acc rest = R.var pathIndex (acc ++ (v intervalIndex v∷ rest))
    consume (_ ∷ bs) acc (a ∷ args) = consume bs (acc ++ [ a ]) args
    consume bs acc [] =
      let k = List.length bs in
      lambdas bs (R.var (pathIndex + k)
        (shiftArgs k 0 acc ++ binderArgs bs ++ (v (intervalIndex + k) v∷ [])))

  lookupField : ℕ → List FieldInfo → R.TC FieldInfo
  lookupField zero (f ∷ _) = R.returnTC f
  lookupField (suc n) (_ ∷ fs) = lookupField n fs
  lookupField _ [] = R.typeError [ R.strErr "Invalid earlier-field index" ]

  -- sourceBound counts the function arguments already peeled off the source
  -- field type. previous is innermost-first. There are also two endpoint records
  -- between the record parameters and the preceding field-path arguments.
  mutual
    rewriteTerm : List FieldInfo → ℕ → Bool → ℕ → R.Term → R.TC R.Term
    rewriteTerm previous sourceBound interval d (R.var n args) =
      rewriteArgs previous sourceBound interval d args >>= λ args′ →
      if below n d then R.returnTC (R.var n args′) else
      freeVariable (n ∸ d) args′
      where
      extra = if interval then 1 else 0

      freeVariable : ℕ → List (R.Arg R.Term) → R.TC R.Term
      freeVariable n args with below n sourceBound
      ... | true = R.returnTC (R.var (n + extra + d) args)
      ... | false with below (n ∸ sourceBound) (List.length previous)
      ...   | false = R.returnTC (R.var (n + extra + 2 + d) args)
      ...   | true =
        if interval then (
          lookupField (n ∸ sourceBound) previous >>= λ { (_ , (_ , bs)) →
            R.returnTC (fieldValue bs (n + 1 + d) d args) })
        else R.typeError [ R.strErr "Cannot make a changing function domain pointwise" ]
    rewriteTerm previous k i d (R.def n args) = liftTC (R.def n) (rewriteArgs previous k i d args)
    rewriteTerm previous k i d (R.con n args) = liftTC (R.con n) (rewriteArgs previous k i d args)
    rewriteTerm previous k i d (R.meta n args) = liftTC (R.meta n) (rewriteArgs previous k i d args)
    rewriteTerm previous k i d (R.lam info (R.abs s t)) =
      liftTC (λ t′ → R.lam info (R.abs s t′)) (rewriteTerm previous k i (suc d) t)
    rewriteTerm previous k i d (R.pi (R.arg info a) (R.abs s b)) =
      rewriteTerm previous k i d a >>= λ a′ →
      liftTC (λ b′ → R.pi (R.arg info a′) (R.abs s b′)) (rewriteTerm previous k i (suc d) b)
    rewriteTerm previous k i d (R.agda-sort (R.set t)) =
      liftTC (λ t′ → R.agda-sort (R.set t′)) (rewriteTerm previous k i d t)
    rewriteTerm previous k i d (R.agda-sort (R.prop t)) =
      liftTC (λ t′ → R.agda-sort (R.prop t′)) (rewriteTerm previous k i d t)
    rewriteTerm _ _ _ _ (R.pat-lam _ _) = R.returnTC R.unknown
    rewriteTerm _ _ _ _ t = R.returnTC t

    rewriteArgs : List FieldInfo → ℕ → Bool → ℕ
      → List (R.Arg R.Term) → R.TC (List (R.Arg R.Term))
    rewriteArgs _ _ _ _ [] = R.returnTC []
    rewriteArgs previous k i d (R.arg info t ∷ ts) =
      rewriteTerm previous k i d t >>= λ t′ →
      liftTC (R.arg info t′ ∷_) (rewriteArgs previous k i d ts)

  fieldPathType : List FieldInfo → FieldInfo → R.TC R.Type
  fieldPathType previous (n , (ty , bs)) = go 0 [] bs ty
    where
    go : ℕ → Binders → Binders → R.Type → R.TC R.Type
    go k acc ((_ , _) ∷ bs) (R.pi (R.arg info a) (R.abs s b)) =
      rewriteTerm previous k false 0 a >>= λ a′ →
      liftTC (λ b′ → R.pi (R.arg info a′) (R.abs s b′)) (go (suc k) (acc ++ [ s , info ]) bs b)
    go k acc [] body =
      (if mentions (λ _ → false) 0 body then R.returnTC R.unknown
       else rewriteTerm previous k true 0 body) >>= λ family →
      R.returnTC (R.def (quote PathP)
        (R.lam R.visible (R.abs "i" family) v∷
         R.def n (v (k + List.length previous + 1) v∷ binderArgs acc) v∷
         R.def n (v (k + List.length previous) v∷ binderArgs acc) v∷ []))
    go _ _ _ _ = R.typeError [ R.strErr "Invalid field function telescope" ]

  recordArgs : ℕ → List (R.Arg R.Term) → List R.ArgInfo → List (R.Arg R.Term)
  recordArgs _ acc [] = acc
  recordArgs k acc (info ∷ infos) = recordArgs (suc k) (R.arg info (v k) ∷ acc) infos

  pathType : R.Name → List R.ArgInfo → List FieldInfo → R.TC R.Type
  pathType recordName parameters fields =
    go [] fields >>= λ ty →
    R.returnTC (R.pi (harg {q = R.quantity-ω} (R.def recordName (recordArgs 0 [] parameters)))
      (R.abs "x" (R.pi (harg {q = R.quantity-ω} (R.def recordName (recordArgs 1 [] parameters)))
        (R.abs "y" ty))))
    where
    go : List FieldInfo → List FieldInfo → R.TC R.Type
    go previous [] =
      let p = List.length previous in
      R.returnTC (R.def (quote PathP)
        (R.lam R.visible (R.abs "i" (R.def recordName (recordArgs (p + 3) [] parameters))) v∷
         v (p + 1) v∷ v p v∷ []))
    go previous (f@(n , _) ∷ fs) =
      fieldPathType previous f >>= λ fieldTy →
      liftTC (λ ty → R.pi (varg fieldTy) (R.abs (primStringAppend (fieldLabel n) "≡") ty))
        (go (f ∷ previous) fs)

  implicitInfo : R.ArgInfo → R.ArgInfo
  implicitInfo (R.arg-info R.instance′ m) = R.arg-info R.instance′ m
  implicitInfo (R.arg-info _ m) = R.arg-info R.hidden m

  binderPatterns : Binders → List (R.Arg R.Pattern)
  binderPatterns [] = []
  binderPatterns ((_ , info) ∷ bs) = R.arg info (R.var (List.length bs)) ∷ binderPatterns bs

  pathClauses : List FieldInfo → List R.Clause
  pathClauses fields = go 0 fields
    where
    paths = List.map (λ {(n , _) → fieldLabel n , varg R.unknown}) fields

    pathPatterns : ℕ → ℕ → List (R.Arg R.Pattern)
    pathPatterns _ zero = []
    pathPatterns k (suc n) = R.var (n + k + 1) v∷ pathPatterns k n

    go : ℕ → List FieldInfo → List R.Clause
    go _ [] = []
    go j ((n , (_ , bs)) ∷ fs) =
      let k = List.length bs in
      R.clause
        (paths ++ [ "i" , varg (R.def (quote I) []) ] ++
          List.map (λ {(s , info) → s , R.arg info R.unknown}) bs)
        (pathPatterns k (List.length fields) ++
          (R.var k v∷ R.proj n v∷ binderPatterns bs))
        (R.var (k + (List.length fields ∸ j)) (binderArgs bs ++ (v k v∷ []))) ∷
      go (suc j) fs

  telescope : R.Type → R.Telescope
  telescope (R.pi a (R.abs s b)) = (s , a) ∷ telescope b
  telescope _ = []

  takeParameters : ℕ → R.Telescope → R.Telescope
  takeParameters zero _ = []
  takeParameters (suc n) (a ∷ as) = a ∷ takeParameters n as
  takeParameters _ [] = []

  emptyPathClause : R.Name → R.Type → R.Clause
  emptyPathClause ctor ty =
    R.clause (parameters ++ [ "i" , varg (R.def (quote I) []) ])
      (parameterPatterns parameters ++
        (harg {q = R.quantity-ω} (R.con ctor []) ∷
         harg {q = R.quantity-ω} (R.con ctor []) ∷ R.var 0 v∷ []))
      (R.con ctor [])
    where
    tel = telescope ty
    parameters = takeParameters (List.length tel ∸ 2) tel

    parameterPatterns : R.Telescope → List (R.Arg R.Pattern)
    parameterPatterns [] = []
    parameterPatterns ((_ , R.arg info _) ∷ ps) =
      R.arg info (R.var (suc (List.length ps))) ∷ parameterPatterns ps

  -- Check the interpolated record without endpoint constraints first. In
  -- particular, this infers pattern-lambda families directly from the original
  -- constructor type, rather than making a copy of their auxiliary definitions.
  withoutBoundary : R.Type → R.TC R.Type
  withoutBoundary (R.pi a (R.abs s b)) =
    liftTC (λ b′ → R.pi a (R.abs s b′)) (withoutBoundary b)
  withoutBoundary (R.def n args) = family args
    where
    family : List (R.Arg R.Term) → R.TC R.Type
    family (R.arg _ (R.lam _ (R.abs s b)) ∷ _ ∷ _ ∷ []) =
      R.returnTC (R.pi (varg (R.def (quote I) [])) (R.abs s b))
    family (R.arg _ a ∷ _ ∷ _ ∷ []) =
      if R.primQNameEquality n (quote _≡_) then
        R.returnTC (R.pi (varg (R.def (quote I) [])) (R.abs "i" (shift 1 0 a)))
      else R.typeError [ R.strErr "Expected a record path type" ]
    family (_ ∷ args) = family args
    family [] = R.typeError [ R.strErr "Expected a record path type" ]
  withoutBoundary _ = R.typeError [ R.strErr "Expected a record path type" ]

  constructorParameters : R.Type → R.Type → List (R.Arg R.Term)
  constructorParameters (R.pi _ (R.abs _ b)) (R.pi (R.arg info _) (R.abs _ rest)) =
    R.arg info R.unknown ∷ constructorParameters b rest
  constructorParameters _ _ = []

  constructorBody : R.Name → List (R.Arg R.Term) → List (R.Arg R.Name) → List FieldInfo → R.Term
  constructorBody ctor parameters fs fields = R.con ctor (parameters ++ go 0 fs fields)
    where
    go : ℕ → List (R.Arg R.Name) → List FieldInfo → List (R.Arg R.Term)
    go j (R.arg info _ ∷ fs) ((_ , (_ , bs)) ∷ rest) =
      let k = List.length bs in
      R.arg info (lambdas bs (R.var (k + (List.length fields ∸ j))
        (binderArgs bs ++ (v k v∷ [])))) ∷ go (suc j) fs rest
    go _ _ _ = []

  abstractTelescope : R.Type → R.Term → R.Term
  abstractTelescope (R.pi (R.arg (R.arg-info info _) _) (R.abs s b)) t =
    R.lam info (R.abs s (abstractTelescope b t))
  abstractTelescope _ t = t

-- The type generated by declareRecordPath, with all record parameters implicit.
-- Families containing pattern lambdas are completed when defineRecordPath checks
-- the interpolated constructor, so use the two operations together.
recordPathType : R.Name → R.TC R.Type
recordPathType recordName = R.withReconstructed true (R.withExpandLast false (
  R.getDefinition recordName >>= λ where
    (R.record-type ctor fs) →
      R.getType recordName >>= λ ty →
      -- Normalise internally before quoting: normalising an already-quoted type
      -- would recheck implicit-only function values and insert fresh arguments.
      R.withNormalisation true (R.getType ctor) >>= go [] fs ty
    _ → R.typeError (R.strErr "Not a record type: " ∷ R.nameErr recordName ∷ [])))
  where
  go : List R.ArgInfo → List (R.Arg R.Name) → R.Type → R.Type → R.TC R.Type
  go infos fs (R.pi (R.arg info a) (R.abs s b)) (R.pi _ (R.abs _ rest)) =
    liftTC (λ ty → R.pi (R.arg (implicitInfo info) a) (R.abs s ty))
      (go (info ∷ infos) fs b rest)
  go infos fs ty@(R.agda-sort _) ctorTy =
    recordFields ty fs ctorTy >>= pathType recordName infos
  go _ _ _ _ = R.typeError [ R.strErr "Expected a record type" ]

-- Define an already-declared fieldwise path constructor.
defineRecordPath : R.Name → R.Name → R.TC Unit
defineRecordPath pathName recordName = R.withReconstructed true (R.withExpandLast false (
  R.getDefinition recordName >>= λ where
    (R.record-type ctor fs) →
      R.getType recordName >>= λ ty →
      R.withNormalisation true (R.getType ctor) >>= λ ctorTy →
      recordFields ty fs ctorTy >>= λ where
        [] → R.getType pathName >>= λ pathTy → R.defineFun pathName [ emptyPathClause ctor pathTy ]
        fields@(_ ∷ _) →
          -- Reconstructing the incomplete families can crash Agda 2.9.0; neither
          -- the type nor the discarded check result needs reconstructed args.
          R.withReconstructed false (R.withNormalisation true (R.getType pathName)) >>=
            withoutBoundary >>= λ constructorTy →
          R.withReconstructed false
            (R.checkType (abstractTelescope constructorTy
              (constructorBody ctor (constructorParameters ty ctorTy) fs fields)) constructorTy) >>
          R.defineFun pathName (pathClauses fields)
    _ → R.typeError (R.strErr "Not a record type: " ∷ R.nameErr recordName ∷ [])))

-- Generate the WildFunctor≡-style characterisation, including its type.
declareRecordPath : R.Name → R.Name → R.TC Unit
declareRecordPath pathName recordName =
  recordPathType recordName >>= λ ty →
  R.declareDef (varg pathName) ty >>
  defineRecordPath pathName recordName

private
  module Examples where
    variable
      ℓ ℓ' : Level
      A : Type ℓ
      B : A → Type ℓ'

    record Example {A : Type ℓ} (B : A → Type ℓ') : Type (ℓ-max ℓ ℓ') where
      no-eta-equality
      field
        shape : A
        position : B shape

    unquoteDecl Example≡ = declareRecordPath Example≡ (quote Example)

    example-type : {x y : Example B}
      → (p : x .Example.shape ≡ y .Example.shape)
      → PathP (λ i → B (p i)) (x .Example.position) (y .Example.position)
      → x ≡ y
    example-type = Example≡

    example-shape : {x y : Example B}
      (p : x .Example.shape ≡ y .Example.shape)
      (q : PathP (λ i → B (p i)) (x .Example.position) (y .Example.position))
      → cong (λ (r : Example B) → r .Example.shape) (Example≡ {x = x} {y = y} p q) ≡ p
    example-shape _ _ = refl

    record Implicits : Type₁ where
      field
        apply : {A : Type} → A → A
        apply-law : {A : Type} (a : A) → apply a ≡ a
        choose : {A : Type} → {{a : A}} → A
        choose-law : {A : Type} {{a : A}} → choose {{a}} ≡ a

    unquoteDecl Implicits≡ = declareRecordPath Implicits≡ (quote Implicits)

    implicits-type : {x y : Implicits}
      → (apply≡ : {A : Type} (a : A) → x .Implicits.apply a ≡ y .Implicits.apply a)
      → ({A : Type} (a : A) → PathP (λ i → apply≡ a i ≡ a)
          (x .Implicits.apply-law a) (y .Implicits.apply-law a))
      → (choose≡ : {A : Type} {{a : A}} → x .Implicits.choose {{a}} ≡ y .Implicits.choose {{a}})
      → ({A : Type} {{a : A}} → PathP (λ i → choose≡ {{a}} i ≡ a)
          (x .Implicits.choose-law {{a}}) (y .Implicits.choose-law {{a}}))
      → x ≡ y
    unquoteDef implicits-type = defineRecordPath implicits-type (quote Implicits)

    implicits-refl : (x : Implicits) → x ≡ x
    implicits-refl x = Implicits≡
      (λ a _ → x .Implicits.apply a)
      (λ a _ → x .Implicits.apply-law a)
      (λ {{a}} _ → x .Implicits.choose {{a}})
      (λ {{a}} _ → x .Implicits.choose-law {{a}})

    implicits-refl-computes : (x : Implicits) → implicits-refl x ≡ refl
    implicits-refl-computes _ = refl

    record HiddenFields (A : Type ℓ) : Type ℓ where
      field
        {hidden} : A
        {{instance-field}} : A
        equation : hidden ≡ instance-field

    unquoteDecl HiddenFields≡ = declareRecordPath HiddenFields≡ (quote HiddenFields)

    hidden-fields-type : {x y : HiddenFields A}
      → (p : x .HiddenFields.hidden ≡ y .HiddenFields.hidden)
      → (q : x .HiddenFields.instance-field ≡ y .HiddenFields.instance-field)
      → PathP (λ i → p i ≡ q i) (x .HiddenFields.equation) (y .HiddenFields.equation)
      → x ≡ y
    hidden-fields-type = HiddenFields≡

    record InstanceParameter {{n : ℕ}} : Type where
      field
        value : ℕ

    unquoteDecl InstanceParameter≡ = declareRecordPath InstanceParameter≡ (quote InstanceParameter)

    instance-parameter-type : {{n : ℕ}} {x y : InstanceParameter {{n}}}
      → x .InstanceParameter.value ≡ y .InstanceParameter.value
      → x ≡ y
    instance-parameter-type = InstanceParameter≡

    record HigherOrder (A : Type ℓ) : Type ℓ where
      field
        apply : {a : A} → A
        law : PathP (λ _ → {a : A} → A) (λ {a} → apply {a}) (λ {a} → apply {a})

    unquoteDecl HigherOrder≡ = declareRecordPath HigherOrder≡ (quote HigherOrder)

    higher-order-type : {x y : HigherOrder A}
      → (p : {a : A} → x .HigherOrder.apply {a} ≡ y .HigherOrder.apply {a})
      → PathP (λ i → PathP (λ _ → {a : A} → A)
          (λ {a} → p {a} i) (λ {a} → p {a} i))
          (x .HigherOrder.law) (y .HigherOrder.law)
      → x ≡ y
    higher-order-type = HigherOrder≡

    record ChangingDomain : Type₁ where
      field
        Carrier : Type
        value : Carrier
        apply : Carrier → Carrier
        law : (a : Carrier) → apply a ≡ a

    unquoteDecl ChangingDomain≡ = declareRecordPath ChangingDomain≡ (quote ChangingDomain)

    changing-domain-type : {x y : ChangingDomain}
      → (Carrier≡ : x .ChangingDomain.Carrier ≡ y .ChangingDomain.Carrier)
      → PathP (λ i → Carrier≡ i) (x .ChangingDomain.value) (y .ChangingDomain.value)
      → (apply≡ : PathP (λ i → Carrier≡ i → Carrier≡ i)
          (x .ChangingDomain.apply) (y .ChangingDomain.apply))
      → PathP (λ i → (a : Carrier≡ i) → apply≡ i a ≡ a)
          (x .ChangingDomain.law) (y .ChangingDomain.law)
      → x ≡ y
    changing-domain-type = ChangingDomain≡

    record MixedDomain : Type₁ where
      field
        Carrier : Type
        apply : {n : ℕ} → Carrier → Carrier
        law : {n : ℕ} (a : Carrier) → apply {n} a ≡ a

    unquoteDecl MixedDomain≡ = declareRecordPath MixedDomain≡ (quote MixedDomain)

    mixed-domain-type : {x y : MixedDomain}
      → (Carrier≡ : x .MixedDomain.Carrier ≡ y .MixedDomain.Carrier)
      → (apply≡ : {n : ℕ} → PathP (λ i → Carrier≡ i → Carrier≡ i)
          (x .MixedDomain.apply {n}) (y .MixedDomain.apply {n}))
      → ({n : ℕ} → PathP (λ i → (a : Carrier≡ i) → apply≡ {n} i a ≡ a)
          (x .MixedDomain.law {n}) (y .MixedDomain.law {n}))
      → x ≡ y
    mixed-domain-type = MixedDomain≡

    record Empty : Type where

    unquoteDecl Empty≡ = declareRecordPath Empty≡ (quote Empty)

    empty-type : {x y : Empty} → x ≡ y
    empty-type = Empty≡

    record EmptyNoEta : Type where
      no-eta-equality
      pattern

    unquoteDecl EmptyNoEta≡ = declareRecordPath EmptyNoEta≡ (quote EmptyNoEta)

    empty-no-eta-type : {x y : EmptyNoEta} → x ≡ y
    empty-no-eta-type = EmptyNoEta≡

    module Parameterised (A : Type ℓ) where
      record InModule : Type ℓ where
        field
          choose : {a : A} → A

      unquoteDecl InModule≡ = declareRecordPath InModule≡ (quote InModule)

      in-module-type : {x y : InModule}
        → ({a : A} → x .InModule.choose {a} ≡ y .InModule.choose {a})
        → x ≡ y
      in-module-type = InModule≡

      record EmptyInModule : Type ℓ where
        no-eta-equality
        pattern

      unquoteDecl EmptyInModule≡ = declareRecordPath EmptyInModule≡ (quote EmptyInModule)

      empty-in-module-type : {x y : EmptyInModule} → x ≡ y
      empty-in-module-type = EmptyInModule≡

    open import Cubical.Foundations.Function using (case_return_of_)

    record WithCase : Type₁ where
      field
        apply : {A : Type} → A → A
        law : {A : Type} (a : A) (b : Bool)
          → (case b return (λ _ → A) of λ { true → apply a ; false → a }) ≡ a

    unquoteDecl WithCase≡ = declareRecordPath WithCase≡ (quote WithCase)

    with-case-refl : (x : WithCase) → x ≡ x
    with-case-refl x = WithCase≡
      (λ a _ → x .WithCase.apply a)
      (λ a b _ → x .WithCase.law a b)

    with-case-refl-computes : (x : WithCase) → with-case-refl x ≡ refl
    with-case-refl-computes _ = refl

    open import Cubical.WildCat.Base
    open import Cubical.WildCat.Functor using (WildFunctor)
    open WildCat
    open WildFunctor

    unquoteDecl WildFunctor≡ = declareRecordPath WildFunctor≡ (quote WildFunctor)

    wild-functor-type : ∀ {ℓC ℓC' ℓD ℓD'}
      {C : WildCat ℓC ℓC'} {D : WildCat ℓD ℓD'} {F G : WildFunctor C D}
      → (F-ob≡ : (c : C .ob) → F .F-ob c ≡ G .F-ob c)
      → (F-hom≡ : {x y : C .ob} (f : C Cubical.WildCat.Base.[ x , y ])
          → PathP (λ i → D Cubical.WildCat.Base.[ F-ob≡ x i , F-ob≡ y i ]) (F .F-hom f) (G .F-hom f))
      → (F-id≡ : {x : C .ob}
          → PathP (λ i → F-hom≡ {y = x} (id C) i ≡ id D) (F .F-id {x}) (G .F-id {x}))
      → (F-seq≡ : {x y z : C .ob}
          (f : C Cubical.WildCat.Base.[ x , y ]) (g : C Cubical.WildCat.Base.[ y , z ])
          → PathP (λ i → F-hom≡ (f ⋆⟨ C ⟩ g) i ≡ (F-hom≡ f i) ⋆⟨ D ⟩ (F-hom≡ g i))
            (F .F-seq f g) (G .F-seq f g))
      → F ≡ G
    wild-functor-type = WildFunctor≡
