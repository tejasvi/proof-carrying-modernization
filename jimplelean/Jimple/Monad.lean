/-
  Jimple/Monad.lean

  The request monad `Res` in which the one-step semantics is written.

  A step of a method body is a pure function of the program, the frame and the state,
  except for two effects, which it *requests*:
  * `call sig callee args σ k` — run the method selected for the reference `sig`
    (`callee` is the selected method or the receiver's runtime class) and continue
    with its outcome;
  * `choose k` — a nondeterministic choice (behaviour the JDK leaves unspecified:
    identity hash codes, hash-based iteration order, `==` on equal value objects).
  The relational semantics (`Jimple/Semantics.lean`) answers requests by executing
  callees and by allowing every choice; the verification condition generator
  (`Jimple/Logic.lean`) answers them with method specifications and `∀`.
-/
import Jimple.Program

namespace Jimple

/-- The target of a call request: an already selected method, or a virtual call on an
    application object of runtime class `c` (method selection is part of answering the
    request, so a proof can use the referenced method's contract without knowing `c`). -/
inductive Callee where
  | method (m : MethodRef)
  | virtual (c : ClassName)
  deriving Inhabited

inductive Res (α : Type) where
  | ret (a : α)
  | call (sig : MethodSig) (callee : Callee) (args : List Value) (σ : State)
      (k : Outcome → Res α)
  | choose (k : Nat → Res α)
  deriving Inhabited

namespace Res

def bind {α β : Type} : Res α → (α → Res β) → Res β
  | .ret a, f => f a
  | .call sig c args σ k, f => .call sig c args σ (fun o => (k o).bind f)
  | .choose k, f => .choose (fun n => (k n).bind f)

instance : Monad Res where
  pure := .ret
  bind := Res.bind

@[simp] theorem bind_ret {α β} (a : α) (f : α → Res β) : (Res.ret a).bind f = f a := rfl
@[simp] theorem bind_call {α β} sig c args σ (k : Outcome → Res α) (f : α → Res β) :
    (Res.call sig c args σ k).bind f = .call sig c args σ (fun o => (k o).bind f) := rfl
@[simp] theorem bind_choose {α β} (k : Nat → Res α) (f : α → Res β) :
    (Res.choose k).bind f = .choose (fun n => (k n).bind f) := rfl
@[simp] theorem monad_bind_eq {α β} (x : Res α) (f : α → Res β) : (x >>= f) = x.bind f := rfl
@[simp] theorem monad_pure_eq {α} (a : α) : (pure a : Res α) = .ret a := rfl

end Res

/-- Result of evaluating an expression or a native method. -/
inductive EvOut where
  | ok (v : Value) (σ : State)
  | thr (e : Addr) (σ : State)
  | wrong (msg : String)
  deriving Inhabited

/-- Result of one statement. -/
inductive StepOut where
  | next (pc : Nat) (fr : Frame) (σ : State)
  | ret (v : Option Value) (σ : State)
  | thr (e : Addr) (σ : State)
  | wrong (msg : String)
  deriving Inhabited

abbrev NRes := Res EvOut

/-! ### Allocation helpers -/

def allocStr (s : JStr) (σ : State) : Value × State :=
  let (a, σ) := σ.alloc (.str s); (.ref a, σ)

def retObj (o : Obj) (σ : State) : EvOut :=
  let (a, σ) := σ.alloc o; .ok (.ref a) σ

/-- Allocate a library exception (a `Throwable` with message and no cause). -/
def mkExc (cls : ClassName) (msg : Option JStr) (σ : State) : Addr × State :=
  let (mv, σ) := match msg with
    | none => (Value.null, σ)
    | some s => allocStr s σ
  σ.alloc (.plain cls [(("java.lang.Throwable", "detailMessage"), mv),
                       (("java.lang.Throwable", "cause"), .null)])

def throwNew (cls : ClassName) (msg : Option JStr) (σ : State) : EvOut :=
  let (e, σ) := mkExc cls msg σ; .thr e σ

def npe (σ : State) : EvOut := throwNew "java.lang.NullPointerException" none σ

/-! ### Reading values -/

def objAt (σ : State) (v : Value) : Option (Addr × Obj) :=
  match v with
  | .ref a => (σ.heap a).map (a, ·)
  | _ => none

def strOf (σ : State) (v : Value) : Option JStr :=
  match v with
  | .ref a => match σ.heap a with
    | some (.str s) => some s
    | _ => none
  | _ => none

def decOf (σ : State) (v : Value) : Option BigDec :=
  match v with
  | .ref a => match σ.heap a with
    | some (.dec d) => some d
    | _ => none
  | _ => none

def bigIntOf (σ : State) (v : Value) : Option Int :=
  match v with
  | .ref a => match σ.heap a with
    | some (.bigInt i) => some i
    | _ => none
  | _ => none

def Value.asInt : Value → Option I32
  | .int v => some v
  | _ => none

def Value.asLong : Value → Option I64
  | .long v => some v
  | _ => none

/-- Pick an ordering of a list from a choice index; as `n` ranges over `Nat` every
    permutation is produced (used for unspecified hash-based iteration orders). -/
def permuteBy : Nat → List α → List α
  | _, [] => []
  | n, x :: xs =>
    let len := xs.length + 1
    let i := n % len
    let l := x :: xs
    match l[i]? with
    | some y => y :: permuteBy (n / len) (l.eraseIdx i)
    | none => l
termination_by _ l => l.length
decreasing_by
  have h := Nat.mod_lt n (Nat.succ_pos xs.length)
  simp only [List.length_eraseIdx, List.length_cons] at *
  split <;> omega

end Jimple
