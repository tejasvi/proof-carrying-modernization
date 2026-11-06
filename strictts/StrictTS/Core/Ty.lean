/-
StrictTS core: types, contexts and the type table.

StrictTS is the statically typed subset of TypeScript described in DESIGN.md: no `any`,
no implicit coercions, no prototype mutation. Because every operation in the IR is typed,
the semantics never has to branch on the dynamic type of a value.
-/
import StrictTS.Num.F64
import StrictTS.Str.JSStr

namespace StrictTS

/-- Element kinds of typed arrays (`Int8Array`, ..., `BigUint64Array`). -/
inductive TAKind where
  | i8 | u8 | u8c | i16 | u16 | i32 | u32 | f32 | f64 | bi64 | bu64
  deriving DecidableEq, Repr, Hashable, Inhabited

/-- Bit width of a typed-array element. -/
def TAKind.width : TAKind → Nat
  | .i8 | .u8 | .u8c => 8
  | .i16 | .u16 => 16
  | .i32 | .u32 | .f32 => 32
  | .f64 | .bi64 | .bu64 => 64

mutual
/-- StrictTS types.
* primitives: `number` (`num`), `bigint`, `boolean`, `string`, `undefined`, `null`;
  `err` is the type of `Error` objects (immutable name + message);
* heap-allocated, identity-carrying: arrays, typed arrays, `Map`, `Set`, class instances (`obj`),
  `Promise`, and internal mutable cells (`box`, used for captured `let` variables);
* immutable values: tuples, records (object types that are never mutated), named recursive types;
* sums: `opt t` (`t | undefined`), tagged `union`s, string-literal `enum`s;
* functions: `fn args ret` (closures). -/
inductive Ty where
  | num | bigint | bool | str | undef | null | err
  | arr (t : Ty)
  | tarr (k : TAKind)
  | map (k v : Ty)
  | set (t : Ty)
  | tup (ts : Tys)
  | record (fs : Fields)
  | obj (c : String)
  | named (n : String)
  | opt (t : Ty)
  | union (ts : Tys)
  | enum (cases : List String)
  | fn (args : Tys) (ret : Ty)
  | promise (t : Ty)
  | box (t : Ty)
  /-- an object of an external (library or host) type, e.g. a Firestore document reference:
  an opaque handle with identity, used only through external calls -/
  | ext (name : String)
  /-- an object used as a dictionary (`{ [k: string]: T }`, `Record<string, T>`): string keys
  in ECMA-262 property order, values of type `t`; it inherits `Object.prototype` -/
  | dict (t : Ty)
  /-- a value of any type paired with its runtime type (`unknown`): inspected only through the
  `dyn` operations (`typeof`, casts, property reads, `===`, `String(x)`) -/
  | dyn
/-- Lists of types (a separate inductive so that `DecidableEq`/`Hashable` can be derived). -/
inductive Tys where
  | nil
  | cons (t : Ty) (ts : Tys)
/-- Named fields of a record or class. -/
inductive Fields where
  | nil
  | cons (name : String) (t : Ty) (fs : Fields)
end

deriving instance DecidableEq for Ty, Tys, Fields
deriving instance Hashable for Ty, Tys, Fields
deriving instance Repr for Ty, Tys, Fields

instance : Inhabited Ty := ⟨.undef⟩

namespace Tys
@[reducible] def toList : Tys → List Ty
  | nil => []
  | cons t ts => t :: ts.toList
def ofList : List Ty → Tys
  | [] => nil
  | t :: ts => cons t (ofList ts)
@[simp] theorem toList_nil : nil.toList = [] := rfl
@[simp] theorem toList_cons (t : Ty) (ts : Tys) : (cons t ts).toList = t :: ts.toList := rfl
@[simp] theorem toList_ofList (l : List Ty) : (ofList l).toList = l := by
  induction l with
  | nil => rfl
  | cons t ts ih => simp [ofList, ih]
/-- Each type mapped by `f` (the tuple of promises that `Promise.all` takes over a tuple). -/
@[reducible] def map (f : Ty → Ty) : Tys → Tys
  | nil => nil
  | cons t ts => cons (f t) (map f ts)
end Tys

/-- The result of one promise of `Promise.allSettled` (TypeScript's `PromiseSettledResult<T>`):
`{ reason: unknown; status: string } | { status: string; value: T }` (`status` is `"rejected"`
resp. `"fulfilled"`), members and fields in the translator's canonical order. -/
@[reducible] def Ty.settled (t : Ty) : Ty :=
  .union (.cons (.record (.cons "reason" .dyn (.cons "status" .str .nil)))
    (.cons (.record (.cons "status" .str (.cons "value" t .nil))) .nil))

namespace Fields
@[reducible] def types : Fields → List Ty
  | nil => []
  | cons _ t fs => t :: fs.types
def names : Fields → List String
  | nil => []
  | cons n _ fs => n :: fs.names
@[simp] theorem types_nil : nil.types = [] := rfl
@[simp] theorem types_cons (n : String) (t : Ty) (fs : Fields) :
    (cons n t fs).types = t :: fs.types := rfl
end Fields

/-- Definitions of named types and classes of a program.
* `alias n`: the definition of the named (possibly recursive) immutable value type `n`;
* `fields c`: the fields of the class / mutable record type `c`. -/
structure TypeTable where
  alias : String → Ty
  fields : String → Fields

/-- A variable slot: its type, and whether it may be assigned after initialisation.
Closures may capture only non-mutable slots (mutable captured variables are boxed). -/
structure Slot where
  ty : Ty
  mutable : Bool := false
  deriving DecidableEq, Repr

abbrev Ctx := List Slot

/-- Typed de Bruijn variables. -/
inductive Var : Ctx → Ty → Type where
  | here {Γ : Ctx} {t : Ty} {m : Bool} : Var (⟨t, m⟩ :: Γ) t
  | there {Γ : Ctx} {s : Slot} {t : Ty} : Var Γ t → Var (s :: Γ) t

/-- Assignable variables (`let` slots). -/
inductive MVar : Ctx → Ty → Type where
  | here {Γ : Ctx} {t : Ty} : MVar (⟨t, true⟩ :: Γ) t
  | there {Γ : Ctx} {s : Slot} {t : Ty} : MVar Γ t → MVar (s :: Γ) t

/-- Capturable variables (`const` slots). -/
inductive CVar : Ctx → Ty → Type where
  | here {Γ : Ctx} {t : Ty} : CVar (⟨t, false⟩ :: Γ) t
  | there {Γ : Ctx} {s : Slot} {t : Ty} : CVar Γ t → CVar (s :: Γ) t

/-- The variables captured by a closure: builds its capture context `Δ` (all const). -/
inductive Caps : Ctx → Ctx → Type where
  | nil {Γ : Ctx} : Caps Γ []
  | cons {Γ Δ : Ctx} {t : Ty} : CVar Γ t → Caps Γ Δ → Caps Γ (⟨t, false⟩ :: Δ)

/-- Typed membership of a type in a list (union members, record and tuple fields). -/
inductive Mem : Ty → List Ty → Type where
  | here {t : Ty} {ts : List Ty} : Mem t (t :: ts)
  | there {t u : Ty} {ts : List Ty} : Mem t ts → Mem t (u :: ts)

mutual
/-- Types whose values can be compared with `===` (primitives, enums, references, and
optionals/unions of those). Records and tuples are values without identity in StrictTS,
so `===` on them is rejected. -/
def Ty.eqable : Ty → Bool
  | .num | .bigint | .bool | .str | .undef | .null => true
  | .arr _ | .tarr _ | .map _ _ | .set _ | .obj _ | .promise _ | .box _ | .ext _ | .dict _ => true
  | .enum _ => true
  | .opt t => t.eqable
  | .union ts => Tys.eqable ts
  | _ => false
def Tys.eqable : Tys → Bool
  | .nil => true
  | .cons t ts => t.eqable && Tys.eqable ts
end

/-- Types usable as `Map` keys and `Set` elements: SameValueZero is decidable on them. -/
abbrev Ty.keyable (t : Ty) : Bool := t.eqable

end StrictTS
