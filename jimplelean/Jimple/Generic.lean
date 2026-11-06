/-
  Jimple/Generic.lean

  Contracts that need no method-specific input, and running one method on concrete arguments.

  * `ValueTyped`, `ArgsTyped`, `StateTyped`: the states a well-typed JVM can call a method in —
    arguments of the declared types (references `null` or to objects of a subtype), objects
    whose instance fields all exist with values of their declared types, arrays whose elements
    have the element type, typed static fields, application classes initialized.
  * `genericSpec P m allowed`: from such a state, `m` returns normally or throws an exception of
    a class in `allowed` (or a subclass), and never goes `wrong`; with `allowed := m.decl.throws`
    this is "no exception the method does not declare".
  * `runMethod`: initialize the method's class, then run the method with the interpreter.
-/
import Jimple.Verify

namespace Jimple

/-- The object at `a` as a JVM state can hold it at class type `c`: instances of application
    classes are plain objects of one of `P.progSubclasses c`; the library's value classes are
    modelled by their own object kinds. Split on `isProg` (`P.isProgClass c`) so that the
    subclass list is only computed for application classes. -/
def RefTyped (P : Program) (σ : State) (c : ClassName) (a : Addr) : Bool → Prop
  | true => ∃ c' fs, σ.heap a = some (.plain c' fs) ∧ c' ∈ P.progSubclasses c
  | false =>
    if c = "java.lang.String" then ∃ s, σ.heap a = some (.str s)
    else if c = "java.math.BigDecimal" then ∃ d, σ.heap a = some (.dec d)
    else if c = "java.math.BigInteger" then ∃ i, σ.heap a = some (.bigInt i)
    else if c ∈ ["java.lang.Integer", "java.lang.Long", "java.lang.Short", "java.lang.Byte",
        "java.lang.Character", "java.lang.Boolean"] then ∃ w, σ.heap a = some (.boxed c w)
    else ∃ o, σ.heap a = some o ∧ P.subtype o.ty (.cls c) = some true

/-- A value of type `t` in heap `σ`: the JVM's typing of operand values (with the ranges of
    the sub-`int` types), references `null` or to an object of a subtype. -/
def ValueTyped (P : Program) (σ : State) : JType → Value → Prop
  | .prim .boolean, v => ∃ x : I32, v = .int x ∧ (x = 0 ∨ x = 1)
  | .prim .byte, v => ∃ x : I32, v = .int x ∧ -128 ≤ x.toInt ∧ x.toInt ≤ 127
  | .prim .short, v => ∃ x : I32, v = .int x ∧ -32768 ≤ x.toInt ∧ x.toInt ≤ 32767
  | .prim .char, v => ∃ x : I32, v = .int x ∧ 0 ≤ x.toInt ∧ x.toInt ≤ 65535
  | .prim .int, v => ∃ x : I32, v = .int x
  | .prim .long, v => ∃ x : I64, v = .long x
  | .prim .float, v => ∃ x : BitVec 32, v = .float x
  | .prim .double, v => ∃ x : BitVec 64, v = .double x
  | .cls c, v => v = .null ∨ ∃ a, v = .ref a ∧ RefTyped P σ c a (P.isProgClass c)
  | t, v => v = .null ∨ ∃ a o, v = .ref a ∧ σ.heap a = some o ∧ P.subtype o.ty t = some true

/-- Arguments matching a parameter list (by recursion on the types, so that it unfolds for a
    known signature and unknown arguments). -/
def ArgsTypedL (P : Program) (σ : State) : List JType → List Value → Prop
  | [], vs => vs = []
  | t :: ts, vs => ∃ v rest, vs = v :: rest ∧ ValueTyped P σ t v ∧ ArgsTypedL P σ ts rest

/-- The arguments of a call of `m`: for an instance method a non-`null` receiver of a subclass
    of the declaring class first, then the declared parameters. -/
def ArgsTyped (P : Program) (m : MethodRef) (args : List Value) (σ : State) : Prop :=
  if m.decl.mods.isStatic then ArgsTypedL P σ m.decl.params args
  else ∃ a rest, args = .ref a :: rest ∧
    (∃ c fs, σ.heap a = some (.plain c fs) ∧ c ∈ P.progSubclasses m.cls) ∧
    ArgsTypedL P σ m.decl.params rest

/-- An object whose contents have their declared types: the instance fields declared by each
    supertype of an application object's class present and typed (stated per supertype, so that
    an object only known to be of some subclass of `c` has the fields of `c`), array elements
    of the element type, a boxed primitive of its wrapper's type, a string shorter than `2^31`
    (its length is an `int`). Library objects hold references or `null` where Java holds
    objects. -/
def ObjTyped (P : Program) (σ : State) : Obj → Prop
  | .plain c fs => ∀ ds, P.supers c = some ds → ∀ d ∈ ds, ∀ p ∈ P.declaredFields d,
      ∃ v, Fields.get fs p.1 = some v ∧ ValueTyped P σ p.2 v
  | .array t xs => ∀ v ∈ xs, ValueTyped P σ t v
  | .list _ xs _ => ∀ v ∈ xs, ValueTyped P σ (.cls "java.lang.Object") v
  | .set _ xs _ => ∀ v ∈ xs, ValueTyped P σ (.cls "java.lang.Object") v
  | .map _ kvs _ => ∀ p ∈ kvs, ValueTyped P σ (.cls "java.lang.Object") p.1 ∧
      ValueTyped P σ (.cls "java.lang.Object") p.2
  | .boxed c v =>
    if c = "java.lang.Boolean" then ValueTyped P σ (.prim .boolean) v
    else if c = "java.lang.Integer" then ValueTyped P σ (.prim .int) v
    else if c = "java.lang.Long" then ValueTyped P σ (.prim .long) v
    else if c = "java.lang.Character" then ValueTyped P σ (.prim .char) v
    else if c = "java.lang.Short" then ValueTyped P σ (.prim .short) v
    else if c = "java.lang.Byte" then ValueTyped P σ (.prim .byte) v
    else if c = "java.lang.Double" then ValueTyped P σ (.prim .double) v
    else if c = "java.lang.Float" then ValueTyped P σ (.prim .float) v
    else True
  | .str s => s.length < 2147483648
  | _ => True

/-- Every object of the heap is typed. -/
def HeapTyped (P : Program) (σ : State) : Prop :=
  ∀ a o, σ.heap a = some o → ObjTyped P σ o

/-- An object of some subclass `c'` of `c` in a typed heap has the fields `c` declares, typed
    (used by the tactics when `c'` is unknown, as in proofs for every program). -/
theorem fields_of_sub {P : Program} {σ : State} {a : Addr} {c c' : ClassName}
    {fs : List (FieldKey × Value)} (hH : ∀ a o, σ.heap a = some o → ObjTyped P σ o)
    (hh : σ.heap a = some (.plain c' fs)) (hsub : c' ∈ P.progSubclasses c) :
    ∀ p ∈ P.declaredFields c, ∃ v, Fields.get fs p.1 = some v ∧ ValueTyped P σ p.2 v := by
  have h := hH a _ hh
  simp only [ObjTyped] at h
  simp only [Program.progSubclasses, List.mem_map, List.mem_filter] at hsub
  obtain ⟨cd, ⟨_, hs⟩, rfl⟩ := hsub
  simp only [Program.isSubclass] at hs
  cases hsup : P.supers cd.name with
  | none => simp [hsup] at hs
  | some ds =>
    simp only [hsup, Option.map_some, beq_iff_eq, Option.some.injEq, List.contains_iff_mem] at hs
    exact h ds hsup c hs

/-- Static fields hold values of their declared types. -/
def StaticsTyped (P : Program) (σ : State) : Prop :=
  ∀ k v, σ.static k = some v → ValueTyped P σ (P.staticFieldType k) v

/-- The application classes are initialized. Class initializers are verified on their own
    (with their own contracts); a generic per-method contract starts after them. -/
def ClassesInitialized (P : Program) (σ : State) : Prop :=
  ∀ c, P.isProgClass c = true → σ.initOf c = .done

/-- A state a well-typed JVM run can be in after class initialization: typed heap and
    statics, application classes initialized. -/
def StateTyped (P : Program) (σ : State) : Prop :=
  HeapTyped P σ ∧ StaticsTyped P σ ∧ ClassesInitialized P σ

/-- The exception at `e` is an instance of one of `allowed` (or of a subclass). -/
def ExcIn (P : Program) (allowed : List ClassName) (σ : State) (e : Addr) : Prop :=
  ∃ o, σ.heap e = some o ∧ ∃ t ∈ allowed, P.subtype o.ty (.cls t) = some true

/-- The generic contract of `m`: called with typed arguments in a typed heap, `m` returns
    normally or throws an instance of `allowed`, and never goes `wrong` (unmodelled library
    behaviour, ill-formed code). -/
def genericSpec (P : Program) (m : MethodRef) (allowed : List ClassName := m.decl.throws) : Spec :=
  Spec.of (fun args σ => ArgsTyped P m args σ ∧ StateTyped P σ)
    (fun _ _ _ _ => True)
    (fun _ _ e σ' => ExcIn P allowed σ' e)

/-- `genericSpec` with an additional precondition (e.g. "this field is not `null`", found by a
    failed generic proof). -/
def genericSpecWith (P : Program) (m : MethodRef) (pre : List Value → State → Prop)
    (allowed : List ClassName := m.decl.throws) : Spec :=
  Spec.of (fun args σ => ArgsTyped P m args σ ∧ StateTyped P σ ∧ pre args σ)
    (fun _ _ _ _ => True)
    (fun _ _ e σ' => ExcIn P allowed σ' e)

/-- Run `m` on `args` from `σ`: initialize its class, then execute it (`none` when the fuel
    runs out). The result is an outcome of `MExec`-style execution after class
    initialization (`runR_sound`). -/
def runMethod (P : Program) (m : MethodRef) (args : List Value) (σ : State)
    (fuel : Nat := 100000000) : Option Outcome :=
  runR P fuel ((ensureInit P m.cls σ).bind fun r =>
    match r with
    | .ok σ => .call m.sig (.method m) args σ fun o => .ret o
    | .thr e σ => .ret (.exc e σ)
    | .wrong msg => .ret (.wrong msg))

end Jimple

namespace Jimple

/-- `jverify_generic [defs]`: prove `MethodVC P Γ d m (genericSpec P m allowed) A fuel` (or
    `genericSpecWith`, unfolding the extra precondition's `defs`). The typing facts of the
    arguments and of every object the method reaches are unfolded on demand. -/
syntax (name := jverifyGenericTac) "jverify_generic" (" [" ident,* "]")? : tactic

macro_rules
  | `(tactic| jverify_generic) => `(tactic| jverify [genericSpec, genericSpecWith, ArgsTyped,
      ArgsTypedL, StateTyped, HeapTyped, StaticsTyped, ClassesInitialized, ExcIn])
  | `(tactic| jverify_generic [$ids,*]) => `(tactic| jverify [genericSpec, genericSpecWith,
      ArgsTyped, ArgsTypedL, StateTyped, HeapTyped, StaticsTyped, ClassesInitialized, ExcIn,
      $ids,*])

/-- `jverify_generic_body [defs]`: prove a generic contract once for every program satisfying
    the facts, `BodyVCP F Γ d m (genericSpec · m) A fuel` (typically
    `F := (Contains · [HC.C, …])`: the method's class and the application classes it uses).
    The proof does not look at the rest of the program, however large. -/
syntax (name := jverifyGenericBodyTac) "jverify_generic_body" (" [" ident,* "]")? : tactic

macro_rules
  | `(tactic| jverify_generic_body) => `(tactic| jverify_body [genericSpec, genericSpecWith,
      ArgsTyped, ArgsTypedL, StateTyped, HeapTyped, StaticsTyped, ClassesInitialized, ExcIn,
      Contains, Program.staticFieldType, Program.declaredFields])
  | `(tactic| jverify_generic_body [$ids,*]) => `(tactic| jverify_body [genericSpec,
      genericSpecWith, ArgsTyped, ArgsTypedL, StateTyped, HeapTyped, StaticsTyped,
      ClassesInitialized, ExcIn, Contains, Program.staticFieldType, Program.declaredFields,
      $ids,*])

end Jimple
