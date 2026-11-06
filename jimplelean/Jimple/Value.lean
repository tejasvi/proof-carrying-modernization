/-
  Jimple/Value.lean

  Runtime values, heap objects, machine state and frames.

  Library objects are represented by native Lean mathematical data, not by their
  JDK implementation fields:
    java.lang.String          ↦ `JStr`  (list of UTF-16 code units)
    java.math.BigDecimal      ↦ `BigDec` (exact decimal, `BigDec.toRat : ℚ`)
    java.math.BigInteger      ↦ `Int`
    java.util.List            ↦ `List Value`
    java.util.Map             ↦ `List (Value × Value)` (finite map, keys unique)
    java.util.Set             ↦ `List Value` (no duplicates)
    boxed primitives          ↦ the primitive `Value`
  Application objects (`plain`) carry their exact runtime class and their fields,
  keyed by (declaring class, field name), so field hiding and inheritance are exact.
-/
import Jimple.Decimal

namespace Jimple

abbrev Addr := Nat

inductive Value where
  | int (v : I32)
  | long (v : I64)
  | float (v : BitVec 32)
  | double (v : BitVec 64)
  | null
  | ref (a : Addr)
  /-- JSR/RET return address (only reachable from legacy bytecode) -/
  | retAddr (l : Label)
  deriving DecidableEq, Repr, Inhabited

namespace Value
def ofBool (b : Bool) : Value := .int (JInt.ofBool b)
def ofInt (i : Int) : Value := .int (BitVec.ofInt 32 i)
def ofLong (i : Int) : Value := .long (BitVec.ofInt 64 i)
end Value

/-- Default (zero) value of a type: fields, array elements, statics. -/
def JType.default : JType → Value
  | .prim .long => .long 0
  | .prim .float => .float 0
  | .prim .double => .double 0
  | .prim _ => .int 0
  | _ => .null

/-- Store-time narrowing of `int` values into `boolean`/`byte`/`short`/`char` slots. -/
def JType.narrow : JType → Value → Value
  | .prim .boolean, .int v => .int (v &&& 1)
  | .prim .byte, .int v => .int (JInt.toByte v)
  | .prim .short, .int v => .int (JInt.toShort v)
  | .prim .char, .int v => .int (JInt.toChar v)
  | _, v => v

/-- Field identity after resolution: (declaring class, name). -/
abbrev FieldKey := ClassName × String

inductive ListKind where
  | arrayList | linkedList
  /-- `List.of`, `Collections.emptyList`, `Collections.unmodifiableList` copies -/
  | immutable
  deriving DecidableEq, Repr, Inhabited

inductive MapKind where
  | hash | linked | tree
  deriving DecidableEq, Repr, Inhabited

inductive SetKind where
  | hash | linked | tree
  deriving DecidableEq, Repr, Inhabited

inductive ViewKind where
  | keys | values | entries
  deriving DecidableEq, Repr, Inhabited

inductive IterSrc where
  | list | set | keys | values | entries
  deriving DecidableEq, Repr, Inhabited

inductive Obj where
  /-- application object (also library exceptions and `java.lang.Object`) -/
  | plain (cls : ClassName) (fields : List (FieldKey × Value))
  | array (elem : JType) (data : List Value)
  | str (s : JStr)
  /-- `java.lang.StringBuilder` / `StringBuffer` -/
  | builder (cls : ClassName) (s : JStr)
  /-- boxed primitive (`java.lang.Integer`, ...) -/
  | boxed (cls : ClassName) (v : Value)
  | bigInt (i : Int)
  | dec (d : BigDec)
  /-- a `java.math.RoundingMode` enum constant -/
  | rmode (rm : RoundingMode)
  | mctx (mc : MathCtx)
  /-- `mods` is the structural modification count (fail-fast iterators) -/
  | list (k : ListKind) (xs : List Value) (mods : Nat)
  | map (k : MapKind) (kvs : List (Value × Value)) (mods : Nat)
  | set (k : SetKind) (xs : List Value) (mods : Nat)
  /-- `keySet()` / `values()` / `entrySet()` view of the map at `src` -/
  | view (src : Addr) (part : ViewKind)
  /-- iterator over the collection at `src`, created when its modification count was
      `mods`. Lists are read live by position; sets and maps use the key order `order`
      fixed at creation (nondeterministic for hash-based collections). Using an iterator
      after a structural modification of its source is undefined behaviour (`wrong`). -/
  | iter (src : Addr) (part : IterSrc) (order : List Value) (pos : Nat) (mods : Nat)
  /-- `Map.Entry` of the map at `src` for key `k` (created at modification count `mods`) -/
  | entry (src : Addr) (k : Value) (mods : Nat)
  /-- `System.out` (1) / `System.err` (2) -/
  | stream (fd : Nat)
  /-- `java.lang.Class` object for a class constant -/
  | clazz (desc : String)
  deriving Repr, Inhabited

def ListKind.cls : ListKind → ClassName
  | .arrayList => "java.util.ArrayList"
  | .linkedList => "java.util.LinkedList"
  | .immutable => "java.util.ImmutableCollections$ListN"
def MapKind.cls : MapKind → ClassName
  | .hash => "java.util.HashMap"
  | .linked => "java.util.LinkedHashMap"
  | .tree => "java.util.TreeMap"
def SetKind.cls : SetKind → ClassName
  | .hash => "java.util.HashSet"
  | .linked => "java.util.LinkedHashSet"
  | .tree => "java.util.TreeSet"

/-- Runtime type of an object. -/
def Obj.ty : Obj → JType
  | .plain c _ => .cls c
  | .array t _ => .array t
  | .str _ => .cls "java.lang.String"
  | .builder c _ => .cls c
  | .boxed c _ => .cls c
  | .bigInt _ => .cls "java.math.BigInteger"
  | .dec _ => .cls "java.math.BigDecimal"
  | .rmode _ => .cls "java.math.RoundingMode"
  | .mctx _ => .cls "java.math.MathContext"
  | .list k _ _ => .cls k.cls
  | .map k _ _ => .cls k.cls
  | .set k _ _ => .cls k.cls
  | .view _ .keys => .cls "java.util.Map$KeyView"
  | .view _ .values => .cls "java.util.Map$ValuesView"
  | .view _ .entries => .cls "java.util.Map$EntryView"
  | .iter .. => .cls "java.util.Iterator$Snapshot"
  | .entry .. => .cls "java.util.Map$EntrySnapshot"
  | .stream _ => .cls "java.io.PrintStream"
  | .clazz _ => .cls "java.lang.Class"

/-- Immutable value objects: their identity is unobservable except through `==`,
    which the semantics treats nondeterministically when contents are equal. -/
def Obj.isValueObj : Obj → Bool
  | .str _ | .boxed .. | .bigInt _ | .dec _ | .mctx _ => true
  | _ => false

/-- Content equality of value objects (decides `==` when contents differ). -/
def Obj.sameContent : Obj → Obj → Bool
  | .str a, .str b => a == b
  | .boxed c v, .boxed d w => c == d && v == w
  | .bigInt a, .bigInt b => a == b
  | .dec a, .dec b => a == b
  | .mctx a, .mctx b => a == b
  | _, _ => false

/-- Class initialization status (JVMS 5.5). -/
inductive InitSt where
  | none | done | failed
  deriving DecidableEq, Repr, Inhabited

structure State where
  /-- the heap: addresses are indices; allocation appends, so `mem.size` is fresh -/
  mem : Array Obj
  statics : List (FieldKey × Value)
  inits : List (ClassName × InitSt)
  monitors : List (Addr × Nat)
  /-- text written to `System.out` (standard error is not modelled) -/
  out : JStr

instance : Inhabited State := ⟨⟨#[], [], [], [], []⟩⟩

namespace State

def empty : State := default

/-- The object at an address. -/
def heap (σ : State) (a : Addr) : Option Obj := σ.mem[a]?

/-- The next fresh address. -/
def next (σ : State) : Addr := σ.mem.size

/-- Update the heap at one (allocated) address. -/
def setObj (σ : State) (a : Addr) (o : Obj) : State :=
  { σ with mem := σ.mem.setIfInBounds a o }

/-- Allocate a fresh object. -/
def alloc (σ : State) (o : Obj) : Addr × State :=
  (σ.mem.size, { σ with mem := σ.mem.push o })

/-- Value of a static field (`none`: never written, i.e. the default value). -/
def static (σ : State) (k : FieldKey) : Option Value := σ.statics.lookup k

def setStatic (σ : State) (k : FieldKey) (v : Value) : State :=
  { σ with statics := (k, v) :: σ.statics.filter (fun p => p.1 != k) }

def initOf (σ : State) (c : ClassName) : InitSt := (σ.inits.lookup c).getD .none

def setInit (σ : State) (c : ClassName) (s : InitSt) : State :=
  { σ with inits := (c, s) :: σ.inits.filter (fun p => p.1 != c) }

def monitorOf (σ : State) (a : Addr) : Nat := (σ.monitors.lookup a).getD 0

def setMonitor (σ : State) (a : Addr) (n : Nat) : State :=
  { σ with monitors := (a, n) :: σ.monitors.filter (fun p => p.1 != a) }

end State

/-! Field list operations (association list keyed by `FieldKey`). -/
namespace Fields
def get (fs : List (FieldKey × Value)) (k : FieldKey) : Option Value := fs.lookup k
def set (fs : List (FieldKey × Value)) (k : FieldKey) (v : Value) : List (FieldKey × Value) :=
  (k, v) :: fs.filter (fun p => p.1 != k)
end Fields

/-- A method activation: locals, receiver, arguments and the pending caught exception. -/
structure Frame where
  locals : Array (Option Value)
  this : Option Value
  args : List Value
  caught : Option Value

instance : Inhabited Frame := ⟨⟨#[], none, [], none⟩⟩

/-- `a` with position `i` set to `v`, growing the array (with `none`) if needed. -/
def Array.setGrow (a : Array (Option α)) (i : Nat) (v : α) : Array (Option α) :=
  if i < a.size then a.set! i (some v)
  else (a ++ Array.replicate (i - a.size) none).push (some v)

namespace Frame
/-- Value of a local (`none`: not yet assigned). -/
def get (fr : Frame) (x : LocalIdx) : Option Value := (fr.locals[x]?).join

def setLocal (fr : Frame) (x : LocalIdx) (v : Value) : Frame :=
  { fr with locals := Array.setGrow fr.locals x v }

/-- The frame with a pending caught exception (handler entry). -/
def withCaught (fr : Frame) (c : Option Value) : Frame := { fr with caught := c }

/-- Entry frame of a method: instance methods receive `this` as the first argument. -/
def init (isStatic : Bool) (args : List Value) : Frame :=
  if isStatic then ⟨#[], none, args, none⟩
  else ⟨#[], args.head?, args.tail, none⟩
end Frame

/-- Final outcome of a method invocation. -/
inductive Outcome where
  | normal (v : Option Value) (σ : State)
  | exc (e : Addr) (σ : State)
  /-- the program went wrong: ill-formed code, unsupported library call, or
      behaviour the Java specification leaves undefined -/
  | wrong (msg : String)
  deriving Inhabited

end Jimple
