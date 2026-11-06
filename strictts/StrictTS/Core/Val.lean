/-
StrictTS core: runtime values and environments.

`Val TT t` has one constructor per runtime shape of type `t`; for primitive types there is
exactly one, so a case split on a value of a primitive type never branches. Closures are
syntactic (function literal + captured environment), which keeps the heap first-order.
-/
import StrictTS.Core.Syntax

namespace StrictTS

/-- `Error` objects (immutable in StrictTS): constructor name and message. -/
structure ErrVal where
  name : JSStr
  message : JSStr
  deriving DecidableEq, Repr

mutual
/-- Runtime values of type `t`. Heap-allocated objects are represented by their address. -/
inductive Val (TT : TypeTable) : Ty → Type where
  | num : F64 → Val TT .num
  | bigint : Int → Val TT .bigint
  | bool : Bool → Val TT .bool
  | str : JSStr → Val TT .str
  | undef : Val TT .undef
  | null : Val TT .null
  | err : ErrVal → Val TT .err
  | arr {t : Ty} : Nat → Val TT (.arr t)
  | tarr {k : TAKind} : Nat → Val TT (.tarr k)
  | map {k v : Ty} : Nat → Val TT (.map k v)
  | set {t : Ty} : Nat → Val TT (.set t)
  | tup {ts : Tys} : Vals TT ts.toList → Val TT (.tup ts)
  | record {fs : Fields} : Vals TT fs.types → Val TT (.record fs)
  | obj {c : String} : Nat → Val TT (.obj c)
  | fold {n : String} : Val TT (TT.alias n) → Val TT (.named n)
  | none {t : Ty} : Val TT (.opt t)
  | some {t : Ty} : Val TT t → Val TT (.opt t)
  | inj {t : Ty} {ts : Tys} : Mem t ts.toList → Val TT t → Val TT (.union ts)
  | enum {cs : List String} : Fin cs.length → Val TT (.enum cs)
  | clo {args : Tys} {ret : Ty} (Δ : Ctx) : Lam TT args ret Δ → Env TT Δ → Val TT (.fn args ret)
  | fnRef {args : Tys} {ret : Ty} : FunRef args ret → Val TT (.fn args ret)
  /-- The `resolve` function handed to a `new Promise` executor (promise address). -/
  | resolver {t : Ty} : Nat → Val TT (.fn (.cons t .nil) .undef)
  /-- The `reject` function handed to a `new Promise` executor (promise type and address). -/
  | rejecter (t : Ty) : Nat → Val TT (.fn (.cons .err .nil) .undef)
  | promise {t : Ty} : Nat → Val TT (.promise t)
  | box {t : Ty} : Nat → Val TT (.box t)
  /-- A handle to an object of an external type (its identity). -/
  | ext {name : String} : Nat → Val TT (.ext name)
  | dict {t : Ty} : Nat → Val TT (.dict t)
  /-- A value of type `unknown`: a value of any type with that type (no copy: references keep
  their identity). -/
  | dyn (t : Ty) : Val TT t → Val TT .dyn

/-- Value lists, indexed by their types. -/
inductive Vals (TT : TypeTable) : List Ty → Type where
  | nil : Vals TT []
  | cons {t : Ty} {ts : List Ty} : Val TT t → Vals TT ts → Vals TT (t :: ts)

/-- Environments, indexed by their context. -/
inductive Env (TT : TypeTable) : Ctx → Type where
  | nil : Env TT []
  | cons {s : Slot} {Γ : Ctx} : Val TT s.ty → Env TT Γ → Env TT (s :: Γ)
end

variable {TT : TypeTable}

namespace Val
/-! Accessors for single-constructor types (no case split in proofs). -/
abbrev toNum : Val TT .num → F64 | .num x => x
abbrev toBig : Val TT .bigint → Int | .bigint x => x
abbrev toBool : Val TT .bool → Bool | .bool b => b
abbrev toStr : Val TT .str → JSStr | .str s => s
abbrev toErr : Val TT .err → ErrVal | .err e => e
abbrev arrAddr {t : Ty} : Val TT (.arr t) → Nat | .arr a => a
abbrev tarrAddr {k : TAKind} : Val TT (.tarr k) → Nat | .tarr a => a
abbrev mapAddr {k v : Ty} : Val TT (.map k v) → Nat | .map a => a
abbrev setAddr {t : Ty} : Val TT (.set t) → Nat | .set a => a
abbrev objAddr {c : String} : Val TT (.obj c) → Nat | .obj a => a
abbrev promAddr {t : Ty} : Val TT (.promise t) → Nat | .promise a => a
abbrev boxAddr {t : Ty} : Val TT (.box t) → Nat | .box a => a
abbrev extId {name : String} : Val TT (.ext name) → Nat | .ext a => a
abbrev dictAddr {t : Ty} : Val TT (.dict t) → Nat | .dict a => a
abbrev dynTy : Val TT .dyn → Ty | .dyn t _ => t
abbrev dynVal : (v : Val TT .dyn) → Val TT v.dynTy | .dyn _ x => x
abbrev tupVals {ts : Tys} : Val TT (.tup ts) → Vals TT ts.toList | .tup vs => vs
abbrev recVals {fs : Fields} : Val TT (.record fs) → Vals TT fs.types | .record vs => vs
abbrev unfold {n : String} : Val TT (.named n) → Val TT (TT.alias n) | .fold v => v
abbrev enumIdx {cs : List String} : Val TT (.enum cs) → Fin cs.length | .enum i => i

@[simp] theorem toNum_num (x : F64) : (Val.num x : Val TT .num).toNum = x := rfl
@[simp] theorem toBig_bigint (x : Int) : (Val.bigint x : Val TT .bigint).toBig = x := rfl
@[simp] theorem toBool_bool (b : Bool) : (Val.bool b : Val TT .bool).toBool = b := rfl
@[simp] theorem toStr_str (s : JSStr) : (Val.str s : Val TT .str).toStr = s := rfl
@[simp] theorem toErr_err (e : ErrVal) : (Val.err e : Val TT .err).toErr = e := rfl
@[simp] theorem arrAddr_arr {t : Ty} (a : Nat) : (Val.arr a : Val TT (.arr t)).arrAddr = a := rfl
@[simp] theorem mapAddr_map {k v : Ty} (a : Nat) : (Val.map a : Val TT (.map k v)).mapAddr = a := rfl
@[simp] theorem setAddr_set {t : Ty} (a : Nat) : (Val.set a : Val TT (.set t)).setAddr = a := rfl
@[simp] theorem objAddr_obj {c : String} (a : Nat) : (Val.obj a : Val TT (.obj c)).objAddr = a := rfl
@[simp] theorem promAddr_promise {t : Ty} (a : Nat) : (Val.promise a : Val TT (.promise t)).promAddr = a := rfl
@[simp] theorem boxAddr_box {t : Ty} (a : Nat) : (Val.box a : Val TT (.box t)).boxAddr = a := rfl
@[simp] theorem extId_ext {name : String} (a : Nat) : (Val.ext a : Val TT (.ext name)).extId = a := rfl
@[simp] theorem dictAddr_dict {t : Ty} (a : Nat) : (Val.dict a : Val TT (.dict t)).dictAddr = a := rfl
@[simp] theorem tarrAddr_tarr {k : TAKind} (a : Nat) : (Val.tarr a : Val TT (.tarr k)).tarrAddr = a := rfl
@[simp] theorem unfold_fold {n : String} (v : Val TT (TT.alias n)) : (Val.fold v).unfold = v := rfl

/-! Eta rules: every value of a single-constructor type is that constructor. -/
@[simp] theorem num_toNum (v : Val TT .num) : Val.num v.toNum = v := by cases v; rfl
@[simp] theorem bool_toBool (v : Val TT .bool) : Val.bool v.toBool = v := by cases v; rfl
@[simp] theorem str_toStr (v : Val TT .str) : Val.str v.toStr = v := by cases v; rfl
@[simp] theorem bigint_toBig (v : Val TT .bigint) : Val.bigint v.toBig = v := by cases v; rfl
@[simp] theorem arr_arrAddr {t : Ty} (v : Val TT (.arr t)) : Val.arr v.arrAddr = v := by cases v; rfl
@[simp] theorem map_mapAddr {k w : Ty} (v : Val TT (.map k w)) : Val.map v.mapAddr = v := by cases v; rfl
@[simp] theorem obj_objAddr {c : String} (v : Val TT (.obj c)) : Val.obj v.objAddr = v := by cases v; rfl
theorem undef_eq (v : Val TT .undef) : v = .undef := by cases v; rfl
end Val

namespace Vals
abbrev head {t : Ty} {ts : List Ty} : Vals TT (t :: ts) → Val TT t | .cons v _ => v
abbrev tail {t : Ty} {ts : List Ty} : Vals TT (t :: ts) → Vals TT ts | .cons _ vs => vs
/-- The value at a typed position. -/
def get : {ts : List Ty} → {t : Ty} → Vals TT ts → Mem t ts → Val TT t
  | _, _, .cons v _, .here => v
  | _, _, .cons _ vs, .there m => vs.get m
/-- Replace the value at a typed position. -/
def set : {ts : List Ty} → {t : Ty} → Vals TT ts → Mem t ts → Val TT t → Vals TT ts
  | _, _, .cons _ vs, .here, w => .cons w vs
  | _, _, .cons v vs, .there m, w => .cons v (vs.set m w)
/-- Values of a homogeneous list type. -/
def toList {t : Ty} : {n : Nat} → Vals TT (List.replicate n t) → List (Val TT t)
  | 0, .nil => []
  | _ + 1, .cons v vs => v :: toList vs
@[simp] theorem head_cons {t : Ty} {ts : List Ty} (v : Val TT t) (vs : Vals TT ts) :
    (Vals.cons v vs).head = v := rfl
@[simp] theorem tail_cons {t : Ty} {ts : List Ty} (v : Val TT t) (vs : Vals TT ts) :
    (Vals.cons v vs).tail = vs := rfl
@[simp] theorem get_here {t : Ty} {ts : List Ty} (v : Val TT t) (vs : Vals TT ts) :
    (Vals.cons v vs).get .here = v := rfl
@[simp] theorem get_there {t u : Ty} {ts : List Ty} (v : Val TT u) (vs : Vals TT ts) (m : Mem t ts) :
    (Vals.cons v vs).get (.there m) = vs.get m := rfl
end Vals

namespace Vals
/-! Positional accessors (used instead of patterns, which keeps `match` simple). -/
abbrev a0 {t : Ty} {ts : List Ty} (vs : Vals TT (t :: ts)) : Val TT t := vs.head
abbrev a1 {t u : Ty} {ts : List Ty} (vs : Vals TT (t :: u :: ts)) : Val TT u := vs.tail.head
abbrev a2 {t u w : Ty} {ts : List Ty} (vs : Vals TT (t :: u :: w :: ts)) : Val TT w := vs.tail.tail.head
abbrev a3 {t u w x : Ty} {ts : List Ty} (vs : Vals TT (t :: u :: w :: x :: ts)) : Val TT x :=
  vs.tail.tail.tail.head
@[simp] theorem a0_cons {t : Ty} {ts : List Ty} (v : Val TT t) (vs : Vals TT ts) :
    (Vals.cons v vs).a0 = v := rfl
@[simp] theorem a1_cons {t u : Ty} {ts : List Ty} (v : Val TT t) (w : Val TT u) (vs : Vals TT ts) :
    (Vals.cons v (Vals.cons w vs)).a1 = w := rfl
@[simp] theorem a2_cons {t u x : Ty} {ts : List Ty} (v : Val TT t) (w : Val TT u) (y : Val TT x) (vs : Vals TT ts) :
    (Vals.cons v (Vals.cons w (Vals.cons y vs))).a2 = y := rfl
@[simp] theorem a3_cons {t u x z : Ty} {ts : List Ty} (v : Val TT t) (w : Val TT u) (y : Val TT x) (q : Val TT z)
    (vs : Vals TT ts) : (Vals.cons v (Vals.cons w (Vals.cons y (Vals.cons q vs)))).a3 = q := rfl
end Vals

namespace Env
abbrev head {s : Slot} {Γ : Ctx} : Env TT (s :: Γ) → Val TT s.ty | .cons v _ => v
abbrev tail {s : Slot} {Γ : Ctx} : Env TT (s :: Γ) → Env TT Γ | .cons _ e => e
def get : {Γ : Ctx} → {t : Ty} → Env TT Γ → Var Γ t → Val TT t
  | _, _, .cons v _, .here => v
  | _, _, .cons _ e, .there x => e.get x
def set : {Γ : Ctx} → {t : Ty} → Env TT Γ → MVar Γ t → Val TT t → Env TT Γ
  | _, _, .cons _ e, .here, w => .cons w e
  | _, _, .cons v e, .there x, w => .cons v (e.set x w)
def getC : {Γ : Ctx} → {t : Ty} → Env TT Γ → CVar Γ t → Val TT t
  | _, _, .cons v _, .here => v
  | _, _, .cons _ e, .there x => e.getC x
def append : {Γ Δ : Ctx} → Env TT Γ → Env TT Δ → Env TT (Γ ++ Δ)
  | _, _, .nil, d => d
  | _, _, .cons v e, d => .cons v (e.append d)
@[simp] theorem head_cons {s : Slot} {Γ : Ctx} (v : Val TT s.ty) (e : Env TT Γ) :
    (Env.cons v e).head = v := rfl
@[simp] theorem tail_cons {s : Slot} {Γ : Ctx} (v : Val TT s.ty) (e : Env TT Γ) :
    (Env.cons v e).tail = e := rfl
@[simp] theorem get_here {t : Ty} {m : Bool} {Γ : Ctx} (v : Val TT t) (e : Env TT Γ) :
    (Env.cons (s := ⟨t, m⟩) v e).get .here = v := rfl
@[simp] theorem get_there {s : Slot} {Γ : Ctx} {t : Ty} (v : Val TT s.ty) (e : Env TT Γ) (x : Var Γ t) :
    (Env.cons v e).get (.there x) = e.get x := rfl
@[simp] theorem set_here {t : Ty} {Γ : Ctx} (v w : Val TT t) (e : Env TT Γ) :
    (Env.cons (s := ⟨t, true⟩) v e).set .here w = .cons w e := rfl
@[simp] theorem set_there {s : Slot} {Γ : Ctx} {t : Ty} (v : Val TT s.ty) (e : Env TT Γ) (x : MVar Γ t) (w : Val TT t) :
    (Env.cons v e).set (.there x) w = .cons v (e.set x w) := by
  obtain ⟨ty, m⟩ := s; cases m <;> rfl
@[simp] theorem getC_here {t : Ty} {Γ : Ctx} (v : Val TT t) (e : Env TT Γ) :
    (Env.cons (s := ⟨t, false⟩) v e).getC .here = v := rfl
@[simp] theorem getC_there {s : Slot} {Γ : Ctx} {t : Ty} (v : Val TT s.ty) (e : Env TT Γ) (x : CVar Γ t) :
    (Env.cons v e).getC (.there x) = e.getC x := by
  obtain ⟨ty, m⟩ := s; cases m <;> rfl
@[simp] theorem append_nil {Δ : Ctx} (d : Env TT Δ) : (Env.nil : Env TT []).append d = d := rfl
@[simp] theorem append_cons {s : Slot} {Γ Δ : Ctx} (v : Val TT s.ty) (e : Env TT Γ) (d : Env TT Δ) :
    (Env.cons v e).append d = .cons v (e.append d) := rfl
@[simp] theorem cons_head_tail {s : Slot} {Γ : Ctx} (e : Env TT (s :: Γ)) : Env.cons e.head e.tail = e := by
  cases e; rfl

/-! Reads and writes on a symbolic environment (used by loop summarization). -/
theorem get_here' {t : Ty} {m : Bool} {Γ : Ctx} (e : Env TT (⟨t, m⟩ :: Γ)) : e.get .here = e.head := by
  cases e; rfl
theorem get_there' {s : Slot} {Γ : Ctx} {t : Ty} (e : Env TT (s :: Γ)) (x : Var Γ t) :
    e.get (.there x) = e.tail.get x := by
  cases e; rfl
theorem set_here' {t : Ty} {Γ : Ctx} (e : Env TT (⟨t, true⟩ :: Γ)) (w : Val TT t) :
    e.set .here w = .cons w e.tail := by
  cases e; rfl
theorem set_there' {s : Slot} {Γ : Ctx} {t : Ty} (e : Env TT (s :: Γ)) (x : MVar Γ t) (w : Val TT t) :
    e.set (.there x) w = .cons e.head (e.tail.set x w) := by
  cases e; obtain ⟨ty, m⟩ := s; cases m <;> rfl
theorem getC_here' {t : Ty} {Γ : Ctx} (e : Env TT (⟨t, false⟩ :: Γ)) : e.getC .here = e.head := by
  cases e; rfl
theorem getC_there' {s : Slot} {Γ : Ctx} {t : Ty} (e : Env TT (s :: Γ)) (x : CVar Γ t) :
    e.getC (.there x) = e.tail.getC x := by
  cases e; obtain ⟨ty, m⟩ := s; cases m <;> rfl
end Env

/-- Build a closure's captured environment. -/
def Caps.capture : {Γ Δ : Ctx} → Caps Γ Δ → Env TT Γ → Env TT Δ
  | _, _, .nil, _ => .nil
  | _, _, .cons x cs, env => .cons (env.getC x) (cs.capture env)

@[simp] theorem Caps.capture_nil {Γ : Ctx} (env : Env TT Γ) : (Caps.nil : Caps Γ []).capture env = .nil := rfl
@[simp] theorem Caps.capture_cons {Γ Δ : Ctx} {t : Ty} (x : CVar Γ t) (cs : Caps Γ Δ) (env : Env TT Γ) :
    (Caps.cons x cs).capture env = .cons (env.getC x) (cs.capture env) := rfl

/-- Bind argument values to parameter slots. -/
def Vals.toEnv : {ts : List Ty} → Vals TT ts → (params : Ctx) → params.map Slot.ty = ts → Env TT params
  | [], .nil, [], _ => .nil
  | _ :: _, .cons v vs, p :: ps, h =>
    have h1 : p.ty = _ := (List.cons.inj h).1
    have h2 : ps.map Slot.ty = _ := (List.cons.inj h).2
    .cons (h1 ▸ v) (vs.toEnv ps h2)

@[simp] theorem Vals.toEnv_nil (h : ([] : Ctx).map Slot.ty = []) :
    (Vals.nil : Vals TT []).toEnv [] h = .nil := rfl
@[simp] theorem Vals.toEnv_cons {t : Ty} {m : Bool} {ts : List Ty} (v : Val TT t) (vs : Vals TT ts) (ps : Ctx)
    (h : (⟨t, m⟩ :: ps : Ctx).map Slot.ty = t :: ts) :
    (Vals.cons v vs).toEnv (⟨t, m⟩ :: ps) h = .cons v (vs.toEnv ps (List.cons.inj h).2) := rfl

/-- Literal values. -/
def Lit.val : {t : Ty} → Lit t → Val TT t
  | _, .num x => .num x
  | _, .bigint x => .bigint x
  | _, .bool b => .bool b
  | _, .str s => .str s
  | _, .undef => .undef
  | _, .null => .null

@[simp] theorem Lit.val_num (x : F64) : (Lit.num x).val (TT := TT) = .num x := rfl
@[simp] theorem Lit.val_bigint (x : Int) : (Lit.bigint x).val (TT := TT) = .bigint x := rfl
@[simp] theorem Lit.val_bool (b : Bool) : (Lit.bool b).val (TT := TT) = .bool b := rfl
@[simp] theorem Lit.val_str (s : JSStr) : (Lit.str s).val (TT := TT) = .str s := rfl
@[simp] theorem Lit.val_undef : (Lit.undef).val (TT := TT) = .undef := rfl
@[simp] theorem Lit.val_null : (Lit.null).val (TT := TT) = .null := rfl

end StrictTS
