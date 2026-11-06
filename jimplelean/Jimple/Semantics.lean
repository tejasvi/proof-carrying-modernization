/-
  Jimple/Semantics.lean

  The formal semantics of Jimple.

  * `step P b pc fr σ : Res StepOut` — one statement, as a pure function in the request
    monad. Every Jimple construct is interpreted here directly: typed traps, class
    initialization, virtual/interface/special/static dispatch, library models. Nothing
    is lowered to JVM stack bytecode.
  * `MExec`/`VExec`/`RExec`/`BExec` — the big-step relational semantics: the official
    meaning of a program. Nondeterministic choices may take any value; divergence has
    no outcome; ill-formed or unmodelled behaviour has the outcome `wrong`.
  * `runM`/`runB` — an executable interpreter (fuel-bounded, choices resolved to `0`),
    proved to produce only outcomes allowed by the relational semantics
    (`Jimple/Interp.lean`). It is used to test the semantics against the JVM.
-/
import Jimple.Native

namespace Jimple
open Native

/-! ## Immediates and operators -/

/-- `Lfoo/Bar;` ↦ `foo.Bar`; array descriptors keep the JVM form with dots (`[Ljava.lang.String;`). -/
def descToName (d : String) : String :=
  -- over the characters (structural recursion), so that the kernel evaluates it on literals
  let cs := d.toList.map fun c => if c = '/' then '.' else c
  match cs with
  | 'L' :: rest => if rest.getLast? = some ';' then String.ofList rest.dropLast else String.ofList cs
  | _ => String.ofList cs

def evalConst (c : Const) (σ : State) : Value × State :=
  match c with
  | .int v => (.int (BitVec.ofInt 32 v), σ)
  | .long v => (.long (BitVec.ofInt 64 v), σ)
  | .float b => (.float b, σ)
  | .double b => (.double b, σ)
  | .str s => allocStr (JStr.ofString s) σ
  | .strUnits u => allocStr (u.map (BitVec.ofNat 16)) σ
  | .null => (.null, σ)
  | .clazz d => let (a, σ) := σ.alloc (.clazz (descToName d)); (.ref a, σ)
  | .methodHandle d => let (a, σ) := σ.alloc (.clazz d); (.ref a, σ)

def evalImm (fr : Frame) (σ : State) : Imm → Option (Value × State)
  | .loc x => (fr.get x).map (·, σ)
  | .const c => some (evalConst c σ)

def evalArgs (fr : Frame) (σ : State) : List Imm → Option (List Value × State)
  | [] => some ([], σ)
  | a :: as =>
    match evalImm fr σ a with
    | some (v, σ) =>
      match evalArgs fr σ as with
      | some (vs, σ) => some (v :: vs, σ)
      | none => none
    | none => none

def intCmp (op : BinOp) (a b : I32) : Option Bool :=
  match op with
  | .eq => some (decide (a = b))
  | .ne => some (decide (a ≠ b))
  | .lt => some (decide (a.toInt < b.toInt))
  | .le => some (decide (a.toInt ≤ b.toInt))
  | .gt => some (decide (a.toInt > b.toInt))
  | .ge => some (decide (a.toInt ≥ b.toInt))
  | _ => none

def divZero (σ : State) : EvOut := throwNew "java.lang.ArithmeticException" (some (JStr.ofString "/ by zero")) σ

/-- Arithmetic, bitwise, shift and comparison operators (JVMS `iadd` … `dcmpg`). -/
def evalBinop (op : BinOp) (v w : Value) (σ : State) : EvOut :=
  match op, v, w with
  | .add, .int a, .int b => .ok (.int (a + b)) σ
  | .add, .long a, .long b => .ok (.long (a + b)) σ
  | .add, .float a, .float b => .ok (.float (JFloat.fadd a b)) σ
  | .add, .double a, .double b => .ok (.double (JFloat.dadd a b)) σ
  | .sub, .int a, .int b => .ok (.int (a - b)) σ
  | .sub, .long a, .long b => .ok (.long (a - b)) σ
  | .sub, .float a, .float b => .ok (.float (JFloat.fsub a b)) σ
  | .sub, .double a, .double b => .ok (.double (JFloat.dsub a b)) σ
  | .mul, .int a, .int b => .ok (.int (a * b)) σ
  | .mul, .long a, .long b => .ok (.long (a * b)) σ
  | .mul, .float a, .float b => .ok (.float (JFloat.fmul a b)) σ
  | .mul, .double a, .double b => .ok (.double (JFloat.dmul a b)) σ
  | .div, .int a, .int b => if b = 0 then divZero σ else .ok (.int (a.sdiv b)) σ
  | .div, .long a, .long b => if b = 0 then divZero σ else .ok (.long (a.sdiv b)) σ
  | .div, .float a, .float b => .ok (.float (JFloat.fdiv a b)) σ
  | .div, .double a, .double b => .ok (.double (JFloat.ddiv a b)) σ
  | .rem, .int a, .int b => if b = 0 then divZero σ else .ok (.int (a.srem b)) σ
  | .rem, .long a, .long b => if b = 0 then divZero σ else .ok (.long (a.srem b)) σ
  | .rem, .float a, .float b => .ok (.float (JFloat.frem a b)) σ
  | .rem, .double a, .double b => .ok (.double (JFloat.drem a b)) σ
  | .and, .int a, .int b => .ok (.int (a &&& b)) σ
  | .and, .long a, .long b => .ok (.long (a &&& b)) σ
  | .or, .int a, .int b => .ok (.int (a ||| b)) σ
  | .or, .long a, .long b => .ok (.long (a ||| b)) σ
  | .xor, .int a, .int b => .ok (.int (a ^^^ b)) σ
  | .xor, .long a, .long b => .ok (.long (a ^^^ b)) σ
  | .shl, .int a, .int b => .ok (.int (JInt.shl a b)) σ
  | .shl, .long a, .int b => .ok (.long (JLong.shl a b)) σ
  | .shr, .int a, .int b => .ok (.int (JInt.shr a b)) σ
  | .shr, .long a, .int b => .ok (.long (JLong.shr a b)) σ
  | .ushr, .int a, .int b => .ok (.int (JInt.ushr a b)) σ
  | .ushr, .long a, .int b => .ok (.long (JLong.ushr a b)) σ
  | .cmp, .long a, .long b => .ok (.int (JLong.cmp a b)) σ
  | .cmpl, .float a, .float b => .ok (.int (JFloat.fcmpl a b)) σ
  | .cmpl, .double a, .double b => .ok (.int (JFloat.dcmpl a b)) σ
  | .cmpg, .float a, .float b => .ok (.int (JFloat.fcmpg a b)) σ
  | .cmpg, .double a, .double b => .ok (.int (JFloat.dcmpg a b)) σ
  | op, .int a, .int b =>
    match intCmp op a b with
    | some r => .ok (Value.ofBool r) σ
    | none => .wrong "ill-typed binary operation"
  | _, _, _ => .wrong "ill-typed binary operation"

def evalUnop (op : UnOp) (v : Value) (σ : State) : EvOut :=
  match op, v with
  | .neg, .int a => .ok (.int (-a)) σ
  | .neg, .long a => .ok (.long (-a)) σ
  | .neg, .float a => .ok (.float (JFloat.fneg a)) σ
  | .neg, .double a => .ok (.double (JFloat.dneg a)) σ
  | .lengthof, .null => npe σ
  | .lengthof, .ref a =>
    match σ.heap a with
    | some (.array _ xs) => .ok (.int (BitVec.ofNat 32 xs.length)) σ
    | _ => .wrong "lengthof on a non-array"
  | _, _ => .wrong "ill-typed unary operation"

/-- `==` on references. Value objects (strings, boxed primitives, big numbers) with equal
    contents may or may not be the same object: the JDK leaves that open (caches,
    interning), so the result is a nondeterministic choice. -/
def refEq (σ : State) (v w : Value) : Res (Option Bool) :=
  match v, w with
  | .null, .null => .ret (some true)
  | .null, .ref _ => .ret (some false)
  | .ref _, .null => .ret (some false)
  | .ref a, .ref b =>
    if a = b then .ret (some true)
    else
      match σ.heap a, σ.heap b with
      | some (.rmode r), some (.rmode r') => .ret (some (r == r'))
      | some (.clazz c), some (.clazz c') => .ret (some (c == c'))
      | some o, some o' =>
        if o.isValueObj && o.sameContent o' then .choose fun n => .ret (some (n % 2 == 0))
        else .ret (some false)
      | _, _ => .ret none
  | _, _ => .ret none

/-- Condition of an `if` statement. -/
def evalCond (op : BinOp) (v w : Value) (σ : State) : Res (Option Bool) :=
  match v, w with
  | .int a, .int b => .ret (intCmp op a b)
  | _, _ =>
    match op with
    | .eq => refEq σ v w
    | .ne => (refEq σ v w).bind fun r => .ret (r.map (!·))
    | _ => .ret none

/-- Primitive conversions (`i2l`, `l2i`, `i2b`, `f2i`, ...). -/
def primCast (t : PrimType) (v : Value) : Option Value :=
  let narrow (t : PrimType) (x : I32) : Value :=
    match t with
    | .byte => .int (JInt.toByte x)
    | .short => .int (JInt.toShort x)
    | .char => .int (JInt.toChar x)
    | _ => .int x
  match t, v with
  | .long, .int a => some (.long (JInt.toLong a))
  | .float, .int a => some (.float (JFloat.i2f a))
  | .double, .int a => some (.double (JFloat.i2d a))
  | t, .int a => some (narrow t a)
  | .long, .long a => some (.long a)
  | .float, .long a => some (.float (JFloat.l2f a))
  | .double, .long a => some (.double (JFloat.l2d a))
  | t, .long a => some (narrow t (JLong.toInt a))
  | .long, .float a => some (.long (JFloat.f2l a))
  | .float, .float a => some (.float a)
  | .double, .float a => some (.double (JFloat.f2d a))
  | t, .float a => some (narrow t (JFloat.f2i a))
  | .long, .double a => some (.long (JFloat.d2l a))
  | .float, .double a => some (.float (JFloat.d2f a))
  | .double, .double a => some (.double a)
  | t, .double a => some (narrow t (JFloat.d2i a))
  | _, _ => none

def evalCast (P : Program) (t : JType) (v : Value) (σ : State) : EvOut :=
  match t with
  | .prim p => match primCast p v with
    | some w => .ok w σ
    | none => .wrong "ill-typed primitive cast"
  | _ =>
    match v with
    | .null => .ok .null σ
    | .ref a =>
      match σ.heap a with
      | none => .wrong "dangling reference"
      | some o =>
        match P.subtype o.ty t with
        | some true => .ok v σ
        | some false => throwNew "java.lang.ClassCastException" none σ
        | none => .wrong "checkcast involving an unknown class"
    | _ => .wrong "checkcast of a non-reference"

def evalInstOf (P : Program) (t : JType) (v : Value) (σ : State) : EvOut :=
  match v with
  | .null => .ok (.int 0) σ
  | .ref a =>
    match σ.heap a with
    | none => .wrong "dangling reference"
    | some o =>
      match P.subtype o.ty t with
      | some r => .ok (Value.ofBool r) σ
      | none => .wrong "instanceof involving an unknown class"
  | _ => .wrong "instanceof of a non-reference"

/-! ## Class initialization (JVMS 5.5) -/

/-! ## Memory accesses -/

def fieldKey (P : Program) (f : FieldSig) : Option (FieldKey × FieldDecl) :=
  (P.resolveField f).map fun (dc, fd) => ((dc, f.name), fd)

def getField (P : Program) (f : FieldSig) (v : Value) (σ : State) : EvOut :=
  match v with
  | .null => npe σ
  | .ref a =>
    match σ.heap a, fieldKey P f with
    | some (.plain _ fs), some (k, fd) =>
      if fd.isStatic then .wrong "getfield of a static field"
      else match Fields.get fs k with
        | some x => .ok x σ
        | none => .wrong "object has no such field"
    | some _, some _ => .wrong "field access on a library object"
    | none, _ => .wrong "dangling reference"
    | _, none => .wrong "unresolved field"
  | _ => .wrong "getfield on a non-reference"

def putField (P : Program) (f : FieldSig) (v x : Value) (σ : State) : EvOut :=
  match v with
  | .null => npe σ
  | .ref a =>
    match σ.heap a, fieldKey P f with
    | some (.plain c fs), some (k, fd) =>
      if fd.isStatic then .wrong "putfield of a static field"
      else match Fields.get fs k with
        | some _ => .ok .null (σ.setObj a (.plain c (Fields.set fs k (fd.ty.narrow x))))
        | none => .wrong "object has no such field"
    | some _, some _ => .wrong "field access on a library object"
    | none, _ => .wrong "dangling reference"
    | _, none => .wrong "unresolved field"
  | _ => .wrong "putfield on a non-reference"

def getStatic (P : Program) (f : FieldSig) (σ : State) : Res EvOut :=
  match fieldKey P f with
  | some (k, fd) =>
    if !fd.isStatic then .ret (.wrong "getstatic of an instance field")
    else initThen P k.1 σ fun σ => .ret (.ok ((σ.static k).getD fd.ty.default) σ)
  | none =>
    match Native.libStatic f σ with
    | some r => .ret r
    | none => .ret (.wrong s!"no model for static field {f.cls}.{f.name}")

def putStatic (P : Program) (f : FieldSig) (x : Value) (σ : State) : Res EvOut :=
  match fieldKey P f with
  | some (k, fd) =>
    if !fd.isStatic then .ret (.wrong "putstatic of an instance field")
    else if !P.isProgClass k.1 then .ret (.wrong "putstatic of a library field")
    else initThen P k.1 σ fun σ => .ret (.ok .null (σ.setStatic k (fd.ty.narrow x)))
  | none => .ret (.wrong s!"no model for static field {f.cls}.{f.name}")

def aioobe (i : Int) (n : Nat) (σ : State) : EvOut :=
  throwNew "java.lang.ArrayIndexOutOfBoundsException"
    (some (JStr.ofString s!"Index {i} out of bounds for length {n}")) σ

def arrayLoad (v i : Value) (σ : State) : EvOut :=
  match v, i with
  | .null, _ => npe σ
  | .ref a, .int i =>
    match σ.heap a with
    | some (.array _ xs) =>
      if 0 ≤ i.toInt ∧ i.toInt < xs.length then
        match xs[i.toNat]? with
        | some x => .ok x σ
        | none => .wrong "unreachable"
      else aioobe i.toInt xs.length σ
    | _ => .wrong "array access on a non-array"
  | _, _ => .wrong "ill-typed array access"

def arrayStore (P : Program) (v i x : Value) (σ : State) : EvOut :=
  match v, i with
  | .null, _ => npe σ
  | .ref a, .int i =>
    match σ.heap a with
    | some (.array t xs) =>
      if 0 ≤ i.toInt ∧ i.toInt < xs.length then
        let store := fun (σ : State) => EvOut.ok .null (σ.setObj a (.array t (xs.set i.toNat (t.narrow x))))
        if t.isRef then
          match x with
          | .null => store σ
          | .ref b =>
            match σ.heap b with
            | some o =>
              match P.subtype o.ty t with
              | some true => store σ
              | some false => throwNew "java.lang.ArrayStoreException" none σ
              | none => .wrong "array store involving an unknown class"
            | none => .wrong "dangling reference"
          | _ => .wrong "ill-typed array store"
        else store σ
      else aioobe i.toInt xs.length σ
    | _ => .wrong "array access on a non-array"
  | _, _ => .wrong "ill-typed array access"

/-! ## Allocation -/

def newObj (P : Program) (c : ClassName) (σ : State) : Res EvOut :=
  match P.lookup c with
  | none => .ret (.wrong s!"new of unknown class {c}")
  | some d =>
    if d.isAbstract || d.isInterface then
      .ret (throwNew "java.lang.InstantiationError" (some (JStr.ofString c)) σ)
    else initThen P c σ fun σ =>
      .ret (retObj (.plain c ((P.instanceFields c).map fun (k, t) => (k, t.default))) σ)

def newArray (t : JType) (n : Value) (σ : State) : EvOut :=
  match n with
  | .int n =>
    if n.toInt < 0 then throwNew "java.lang.NegativeArraySizeException"
      (some (JStr.ofInt n.toInt)) σ
    else retObj (.array t (List.replicate n.toNat t.default)) σ
  | _ => .wrong "ill-typed array size"

/-- `base[]` nested `k` times -/
def arrTy (base : JType) : Nat → JType
  | 0 => base
  | k + 1 => .array (arrTy base k)

def allocMulti (base : JType) : List Nat → Nat → State → Value × State
  | [], _, σ => (.null, σ)
  | [n], d, σ =>
    let et := arrTy base (d - 1)
    let (a, σ) := σ.alloc (.array et (List.replicate n et.default)); (.ref a, σ)
  | n :: ns, d, σ =>
    let et := arrTy base (d - 1)
    let (vs, σ) := (List.range n).foldl
      (fun (acc : List Value × State) _ =>
        let (v, σ') := allocMulti base ns (d - 1) acc.2; (acc.1 ++ [v], σ')) ([], σ)
    let (a, σ) := σ.alloc (.array et vs); (.ref a, σ)

def newMultiArray (base : JType) (sizes : List Value) (dims : Nat) (σ : State) : EvOut :=
  match sizes.mapM Value.asInt with
  | none => .wrong "ill-typed array size"
  | some ns =>
    match ns.find? (fun n => n.toInt < 0) with
    | some n => throwNew "java.lang.NegativeArraySizeException" (some (JStr.ofInt n.toInt)) σ
    | none => let (v, σ) := allocMulti base (ns.map BitVec.toNat) dims σ; .ok v σ

/-! ## Invocation -/

def outToEv (out : Outcome) : EvOut :=
  match out with
  | .normal v σ => .ok (v.getD .null) σ
  | .exc e σ => .thr e σ
  | .wrong m => .wrong m

def EvOut.toOutcome : EvOut → Outcome
  | .ok v σ => .normal (some v) σ
  | .thr e σ => .exc e σ
  | .wrong m => .wrong m

def callM (sig : MethodSig) (m : MethodRef) (args : List Value) (σ : State) : Res EvOut :=
  .call sig (.method m) args σ fun out => .ret (outToEv out)

def noModel (sig : MethodSig) : Res EvOut :=
  .ret (.wrong s!"no model for library method {sig.cls}.{sig.name}")

/-- `makeConcatWithConstants` recipes: `\u0001` takes the next argument, `\u0002` the
    next bootstrap constant. -/
def concatRecipe (P : Program) (consts : List Value) :
    JStr → List JType → List Value → State → JStr → Res EvOut
  | [], _, _, σ, acc => .ret (retObj (.str acc) σ)
  | c :: rest, ts, vs, σ, acc =>
    if c = 1 then
      match ts, vs with
      | t :: ts', v :: vs' => valueOfArg P t v σ fun s σ' => concatRecipe P consts rest ts' vs' σ' (acc ++ s)
      | _, _ => .ret (.wrong "concat recipe arity")
    else if c = 2 then
      match consts with
      | k :: _ => valueOfArg P .string k σ fun s σ' => concatRecipe P (consts.drop 1) rest ts vs σ' (acc ++ s)
      | [] => .ret (.wrong "concat recipe constants")
    else concatRecipe P consts rest ts vs σ (acc ++ [c])

def evalDynamic (P : Program) (name : String) (params : List JType) (args : List Value) (bsm : MethodSig)
    (bsmArgs : List Value) (σ : State) : Res EvOut :=
  if bsm.cls == "java.lang.invoke.StringConcatFactory" ∧ name == "makeConcatWithConstants" then
    match bsmArgs with
    | recipe :: consts =>
      match strOf σ recipe with
      | some r => concatRecipe P consts r params args σ []
      | none => .ret (.wrong "concat recipe")
    | [] => .ret (.wrong "concat recipe")
  else if bsm.cls == "java.lang.invoke.StringConcatFactory" ∧ name == "makeConcat" then
    concatRecipe P [] (List.replicate args.length 1) params args σ []
  else (Native.dynCall P name params args bsm bsmArgs σ).getD
    (.ret (.wrong s!"invokedynamic {name} is not modelled"))

def evalInvoke (P : Program) (inv : Invoke) (fr : Frame) (σ : State) : Res EvOut :=
  match inv with
  | .static sig as =>
    match evalArgs fr σ as with
    | none => .ret (.wrong "undefined local")
    | some (vs, σ) =>
      match P.selectStatic sig with
      | .jimple m => initThen P m.cls σ fun σ => callM sig m vs σ
      | .native _ => (Native.staticCall P sig vs σ).getD (noModel sig)
      | .none why => .ret (.wrong why)
  | .inst kind base sig as =>
    match fr.get base, evalArgs fr σ as with
    | some recv, some (vs, σ) =>
      match recv with
      | .null => .ret (npe σ)
      | .ref a =>
        match σ.heap a with
        | none => .ret (.wrong "dangling reference")
        | some o =>
          match kind with
          | .special =>
            match P.selectSpecial sig with
            | .jimple m => callM sig m (recv :: vs) σ
            | .native lc =>
              if sig.name == "<init>" then (Native.ctorCall P sig a o vs σ).getD (noModel sig)
              else match o with
                | .plain c fs => (Native.plainInst P sig lc a c fs vs σ).getD (noModel sig)
                | _ => (Native.instCall P sig a o vs σ).getD (noModel sig)
            | .none why => .ret (.wrong why)
          | _ =>
            match P.subtype o.ty (.cls sig.cls) with
            | some true =>
              match o with
              | .plain c fs =>
                if P.isProgClass c then .call sig (.virtual c) (recv :: vs) σ fun out => .ret (outToEv out)
                else match P.selectVirtual c sig.sub with
                  | .native lc => (Native.plainInst P sig lc a c fs vs σ).getD (noModel sig)
                  | _ => .ret (.wrong "method selection on a library object failed")
              | _ => (Native.instCall P sig a o vs σ).getD (noModel sig)
            | some false => .ret (.wrong "receiver is not an instance of the referenced class")
            | none => .ret (.wrong "receiver class unknown")
      | _ => .ret (.wrong "ill-typed receiver")
    | _, _ => .ret (.wrong "undefined local")
  | .dynamic name _ params as bsm bsmAs =>
    match evalArgs fr σ as with
    | none => .ret (.wrong "undefined local")
    | some (vs, σ) =>
      match evalArgs fr σ bsmAs with
      | none => .ret (.wrong "bootstrap arguments")
      | some (bvs, σ) => evalDynamic P name params vs bsm bvs σ

/-! ## Expressions and statements -/

def evalExpr (P : Program) (e : Expr) (fr : Frame) (σ : State) : Res EvOut :=
  match e with
  | .imm a => .ret (match evalImm fr σ a with
      | some (v, σ) => .ok v σ
      | none => .wrong "undefined local")
  | .binop op a b => .ret (match evalImm fr σ a with
      | some (v, σ) => match evalImm fr σ b with
        | some (w, σ) => evalBinop op v w σ
        | none => .wrong "undefined local"
      | none => .wrong "undefined local")
  | .unop op a => .ret (match evalImm fr σ a with
      | some (v, σ) => evalUnop op v σ
      | none => .wrong "undefined local")
  | .cast t a => .ret (match evalImm fr σ a with
      | some (v, σ) => evalCast P t v σ
      | none => .wrong "undefined local")
  | .instOf a t => .ret (match evalImm fr σ a with
      | some (v, σ) => evalInstOf P t v σ
      | none => .wrong "undefined local")
  | .new c => newObj P c σ
  | .newArray t n => .ret (match evalImm fr σ n with
      | some (v, σ) => newArray t v σ
      | none => .wrong "undefined local")
  | .newMultiArray base sizes dims => .ret (match evalArgs fr σ sizes with
      | some (vs, σ) => newMultiArray base vs dims σ
      | none => .wrong "undefined local")
  | .invoke inv => evalInvoke P inv fr σ
  | .ref (.instField base f) => .ret (match fr.get base with
      | some v => getField P f v σ
      | none => .wrong "undefined local")
  | .ref (.staticField f) => getStatic P f σ
  | .ref (.arrayElem base i) => .ret (match fr.get base, evalImm fr σ i with
      | some v, some (iv, σ) => arrayLoad v iv σ
      | _, _ => .wrong "undefined local")

/-- Continue with the next statement, or propagate an exception / error. -/
def afterEv (r : EvOut) (k : Value → State → StepOut) : StepOut :=
  match r with
  | .ok v σ => k v σ
  | .thr e σ => .thr e σ
  | .wrong m => .wrong m

def storeRef (P : Program) (pc : Nat) (r : Ref) (x : Value) (fr : Frame) (σ : State) :
    Res StepOut :=
  let fin (e : EvOut) : StepOut := afterEv e fun _ σ => .next (pc + 1) fr σ
  match r with
  | .instField base f => .ret (match fr.get base with
      | some v => fin (putField P f v x σ)
      | none => .wrong "undefined local")
  | .staticField f => (putStatic P f x σ).bind fun e => .ret (fin e)
  | .arrayElem base i => .ret (match fr.get base, evalImm fr σ i with
      | some v, some (iv, σ) => fin (arrayStore P v iv x σ)
      | _, _ => .wrong "undefined local")

def switchTarget (low : Int) (targets : List Label) (dflt : Label) (k : I32) : Label :=
  let i := k.toInt - low
  if 0 ≤ i then (targets[i.toNat]?).getD dflt else dflt

def stepStmt (P : Program) (pc : Nat) (s : Stmt) (fr : Frame) (σ : State) : Res StepOut :=
  match s with
  | .nop | .breakpoint => .ret (.next (pc + 1) fr σ)
  | .identity x r => .ret (match r with
      | .this _ => match fr.this with
        | some v => .next (pc + 1) (fr.setLocal x v) σ
        | none => .wrong "@this in a static method"
      | .param i _ => match fr.args[i]? with
        | some v => .next (pc + 1) (fr.setLocal x v) σ
        | none => .wrong "missing parameter"
      | .caught => match fr.caught with
        | some v => .next (pc + 1) (fr.setLocal x v) σ
        | none => .wrong "@caughtexception outside a handler")
  | .assign (.loc x) rhs =>
    (evalExpr P rhs fr σ).bind fun r =>
      .ret (afterEv r fun v σ => .next (pc + 1) (fr.setLocal x v) σ)
  | .assign (.ref r) rhs =>
    (evalExpr P rhs fr σ).bind fun e =>
      match e with
      | .ok v σ => storeRef P pc r v fr σ
      | .thr e σ => .ret (.thr e σ)
      | .wrong m => .ret (.wrong m)
  | .enterMonitor a => .ret (match evalImm fr σ a with
      | some (.null, σ) => afterEv (npe σ) fun _ σ => .next (pc + 1) fr σ
      | some (.ref x, σ) => .next (pc + 1) fr (σ.setMonitor x (σ.monitorOf x + 1))
      | _ => .wrong "ill-typed monitor")
  | .exitMonitor a => .ret (match evalImm fr σ a with
      | some (.null, σ) => afterEv (npe σ) fun _ σ => .next (pc + 1) fr σ
      | some (.ref x, σ) =>
        if σ.monitorOf x = 0 then
          afterEv (throwNew "java.lang.IllegalMonitorStateException" none σ) fun _ σ => .next (pc + 1) fr σ
        else .next (pc + 1) fr (σ.setMonitor x (σ.monitorOf x - 1))
      | _ => .wrong "ill-typed monitor")
  | .goto t => .ret (.next t fr σ)
  | .ifGoto op a b t =>
    match evalImm fr σ a with
    | some (v, σ) =>
      match evalImm fr σ b with
      | some (w, σ) =>
        (evalCond op v w σ).bind fun c =>
          .ret (match c with
            | some true => .next t fr σ
            | some false => .next (pc + 1) fr σ
            | none => .wrong "ill-typed condition")
      | none => .ret (.wrong "undefined local")
    | none => .ret (.wrong "undefined local")
  | .invoke inv =>
    (evalInvoke P inv fr σ).bind fun r =>
      .ret (afterEv r fun _ σ => .next (pc + 1) fr σ)
  | .tableSwitch key low targets dflt => .ret (match evalImm fr σ key with
      | some (.int k, σ) => .next (switchTarget low targets dflt k) fr σ
      | _ => .wrong "ill-typed switch")
  | .lookupSwitch key cases dflt => .ret (match evalImm fr σ key with
      | some (.int k, σ) => .next (((cases.find? (·.1 == k.toInt)).map (·.2)).getD dflt) fr σ
      | _ => .wrong "ill-typed switch")
  | .ret x => .ret (match fr.get x with
      | some (.retAddr l) => .next l fr σ
      | _ => .wrong "ret without a return address")
  | .returnVal a => .ret (match evalImm fr σ a with
      | some (v, σ) => .ret (some v) σ
      | none => .wrong "undefined local")
  | .returnVoid => .ret (.ret none σ)
  | .throw a => .ret (match evalImm fr σ a with
      | some (.null, σ) => afterEv (npe σ) fun _ σ => .next (pc + 1) fr σ
      | some (.ref e, σ) => .thr e σ
      | _ => .wrong "throw of a non-reference")

/-- One statement of body `b` at `pc`. -/
def step (P : Program) (b : Body) (pc : Nat) (fr : Frame) (σ : State) : Res StepOut :=
  match b.stmtAt pc with
  | some s => stepStmt P pc s fr σ
  | none => .ret (.wrong "control left the method body")

/-! ## Exception dispatch through the trap table -/

/-- First trap covering `pc` whose class is a supertype of the exception's class
    (`some none`: no handler; `none`: the hierarchy is unknown). -/
def findHandler (P : Program) (pc : Nat) (eTy : JType) : List Trap → Option (Option Label)
  | [] => some none
  | t :: ts =>
    if t.first ≤ pc ∧ pc < t.last then
      match P.subtype eTy (.cls t.exc) with
      | some true => some (some t.handler)
      | some false => findHandler P pc eTy ts
      | none => none
    else findHandler P pc eTy ts

inductive BRes where
  | cont (pc : Nat) (fr : Frame) (σ : State)
  | done (o : Outcome)

def afterStep (P : Program) (b : Body) (pc : Nat) (fr : Frame) : StepOut → BRes
  | .next pc' fr' σ' => .cont pc' fr' σ'
  | .ret v σ' => .done (.normal v σ')
  | .wrong m => .done (.wrong m)
  | .thr e σ' =>
    match σ'.heap e with
    | none => .done (.wrong "dangling exception")
    | some o =>
      match findHandler P pc o.ty b.traps with
      | some (some h) => .cont h (fr.withCaught (some (.ref e))) σ'
      | some none => .done (.exc e σ')
      | none => .done (.wrong "exception class unknown")

def Program.concrete (P : Program) (c : ClassName) : Bool :=
  match P.lookup c with
  | some d => !d.isAbstract && !d.isInterface
  | none => false

/-! ## Relational big-step semantics -/

mutual
/-- `MExec P m args σ o`: invoking the selected method `m` terminates with outcome `o`. -/
inductive MExec (P : Program) : MethodRef → List Value → State → Outcome → Prop
  | body {m : MethodRef} {args σ b o} :
      m.decl.body = some b → BExec P b 0 (Frame.init m.decl.mods.isStatic args) σ o →
      MExec P m args σ o
  | noBody {m : MethodRef} {args σ} :
      m.decl.body = none → MExec P m args σ (.wrong "abstract or native method")

/-- `VExec P sig c args σ o`: a virtual call of `sig` on an object of runtime class `c`.
    Method selection failing on a concrete class is `wrong`; on an abstract or unknown
    class (which no JVM heap contains) there is no outcome. -/
inductive VExec (P : Program) : MethodSig → ClassName → List Value → State → Outcome → Prop
  | jimple {sig c m args σ o} :
      P.selectVirtual c sig.sub = .jimple m → MExec P m args σ o → VExec P sig c args σ o
  | native {sig c lc a rest fs σ r ev} :
      P.selectVirtual c sig.sub = .native lc → σ.heap a = some (.plain c fs) →
      Native.plainInst P sig lc a c fs rest σ = some r → RExec P r ev →
      VExec P sig c (.ref a :: rest) σ ev.toOutcome
  | noModel {sig c lc a rest fs σ} :
      P.selectVirtual c sig.sub = .native lc → σ.heap a = some (.plain c fs) →
      Native.plainInst P sig lc a c fs rest σ = none →
      VExec P sig c (.ref a :: rest) σ (.wrong "no model for library method")
  | none {sig c why args σ} :
      P.selectVirtual c sig.sub = .none why → P.concrete c = true →
      VExec P sig c args σ (.wrong why)

/-- `RExec P r a`: the request tree `r` can produce `a`. -/
inductive RExec (P : Program) : {α : Type} → Res α → α → Prop
  | ret {α} {a : α} : RExec P (.ret a) a
  | callM {α} {sig m args σ o} {k : Outcome → Res α} {a : α} :
      MExec P m args σ o → RExec P (k o) a → RExec P (.call sig (.method m) args σ k) a
  | callV {α} {sig c args σ o} {k : Outcome → Res α} {a : α} :
      VExec P sig c args σ o → RExec P (k o) a → RExec P (.call sig (.virtual c) args σ k) a
  | choose {α} {k : Nat → Res α} {a : α} (n : Nat) :
      RExec P (k n) a → RExec P (.choose k) a

/-- `BExec P b pc fr σ o`: executing body `b` from `pc` terminates with outcome `o`. -/
inductive BExec (P : Program) : Body → Nat → Frame → State → Outcome → Prop
  | cont {b pc fr σ r pc' fr' σ' o} :
      RExec P (step P b pc fr σ) r → afterStep P b pc fr r = .cont pc' fr' σ' →
      BExec P b pc' fr' σ' o → BExec P b pc fr σ o
  | done {b pc fr σ r o} :
      RExec P (step P b pc fr σ) r → afterStep P b pc fr r = .done o → BExec P b pc fr σ o
end

end Jimple
