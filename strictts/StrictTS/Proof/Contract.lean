/-
StrictTS proof layer: contracts.

* Canonical statements about a run: `JS.NoFault` (no panic, no uncaught exception; divergence
  allowed), `JS.NoPanic` (exceptions allowed) and `JS.Returns` (terminates with a value).
* Liveness: `Val.Live w v` (every reference in `v`, including inside records, tuples, unions
  and closure environments, names an existing cell of `w`) and `World.Closed w` (the
  references stored in data cells and in fulfilled promises are live). Types need no
  precondition: a reference of type `T[]` can only name a cell of kind `.arr T`.
* `callFun_of_lookup` (from `StrictTS.Proof.CallRule`): the call rule over an abstract
  program, so that a proof about one function mentions only that function's definition (and
  its callees' contracts).
-/
import StrictTS.Proof.Exec
import StrictTS.Proof.CallRule

namespace StrictTS
open JS

variable {TT : TypeTable}

namespace JS

/-- The run of `m` from `w` neither panics nor ends with an uncaught exception (partial
correctness: divergence is allowed). -/
def NoFault {α : Type} (m : JS TT α) (w : World TT) : Prop :=
  ∀ r w', exec m w = some (r, w') → ∃ a, r = .ok a

/-- The run of `m` from `w` does not panic (it may throw or diverge). -/
def NoPanic {α : Type} (m : JS TT α) (w : World TT) : Prop :=
  ∀ msg w', exec m w ≠ some (.error (.panic msg), w')

/-- The run of `m` from `w` terminates with a value. -/
def Returns {α : Type} (m : JS TT α) (w : World TT) : Prop :=
  ∃ a w', exec m w = some (.ok a, w')

theorem NoFault.noPanic {α : Type} {m : JS TT α} {w : World TT} (h : NoFault m w) : NoPanic m w := by
  intro msg w' he
  obtain ⟨a, ha⟩ := h _ _ he
  cases ha

theorem Returns.noFault {α : Type} {m : JS TT α} {w : World TT} (h : Returns m w) : NoFault m w := by
  obtain ⟨a, w', he⟩ := h
  intro r w'' he'
  rw [he] at he'
  cases he'
  exact ⟨a, rfl⟩

theorem returns_of_eq {α : Type} {m : JS TT α} {w w' : World TT} {a : α}
    (h : exec m w = some (.ok a, w')) : Returns m w := ⟨a, w', h⟩

theorem noFault_of_eq {α : Type} {m : JS TT α} {w w' : World TT} {a : α}
    (h : exec m w = some (.ok a, w')) : NoFault m w := (returns_of_eq h).noFault

theorem noFault_of_none {α : Type} {m : JS TT α} {w : World TT} (h : exec m w = none) : NoFault m w := by
  intro r w' he
  rw [h] at he
  cases he

end JS

mutual
/-- Every reference in a value names an existing cell. -/
def Val.Live (w : World TT) : {t : Ty} → Val TT t → Prop
  | _, .arr (t := t) a => w.heap.contains (.arr t, a)
  | _, .tarr (k := k) a => w.heap.contains (.tarr k, a)
  | _, .map (k := k) (v := v) a => w.heap.contains (.map k v, a)
  | _, .set (t := t) a => w.heap.contains (.set t, a)
  | _, .obj (c := c) a => ∃ fs, w.heap.contains (.obj c fs, a)
  | _, .promise (t := t) a => w.heap.contains (.promise t, a)
  | _, .box (t := t) a => w.heap.contains (.box t, a)
  | _, .dict (t := t) a => w.heap.contains (.dict t, a)
  | _, .resolver (t := t) p => w.heap.contains (.promise t, p)
  | _, .rejecter t p => w.heap.contains (.promise t, p)
  | _, .tup vs => Vals.Live w vs
  | _, .record vs => Vals.Live w vs
  | _, .fold v => Val.Live w v
  | _, .some v => Val.Live w v
  | _, .inj _ v => Val.Live w v
  | _, .dyn _ v => Val.Live w v
  | _, .clo _ _ cenv => Env.Live w cenv
  | _, .num _ | _, .bigint _ | _, .bool _ | _, .str _ | _, .undef | _, .null | _, .err _
  | _, .none | _, .enum _ | _, .fnRef _ | _, .ext _ => True

/-- Every reference in a list of values names an existing cell. -/
def Vals.Live (w : World TT) : {ts : List Ty} → Vals TT ts → Prop
  | _, .nil => True
  | _, .cons v vs => Val.Live w v ∧ Vals.Live w vs

/-- Every reference in an environment names an existing cell. -/
def Env.Live (w : World TT) : {Γ : Ctx} → Env TT Γ → Prop
  | _, .nil => True
  | _, .cons v e => Val.Live w v ∧ Env.Live w e
end

/-- The initialised fields of an object are live. -/
def OVals.Live (w : World TT) : {ts : List Ty} → OVals TT ts → Prop
  | _, .nil => True
  | _, .cons o vs => (∀ v, o = some v → Val.Live w v) ∧ OVals.Live w vs

/-- The references stored in a cell are live (for promises: the fulfilment value; pending
reactions are not covered). -/
def CellLive (w : World TT) : (k : HKind) → k.Cell TT → Prop
  | .arr _, xs => ∀ v ∈ xs.toList, Val.Live w v
  | .tarr _, _ => True
  | .map _ _, m => ∀ e ∈ m.entries, ∀ kv, e = some kv → Val.Live w kv.1 ∧ Val.Live w kv.2
  | .set _, m => ∀ e ∈ m.entries, ∀ kv, e = some kv → Val.Live w kv.1
  | .obj _ _, fs => OVals.Live w fs
  | .promise _, c => ∀ v, c.state = .fulfilled v → Val.Live w v
  | .box _, c => ∀ v, c = some v → Val.Live w v
  | .dict _, m => ∀ e ∈ m.entries, ∀ kv, e = some kv → Val.Live w kv.2

/-- Every reference stored in the heap names an existing cell. -/
def World.Closed (w : World TT) : Prop :=
  ∀ (k : HKind) (a : Nat) (c : k.Cell TT), w.heap.get? (k, a) = some c → CellLive w k c

@[simp] theorem Vals.live_nil (w : World TT) : Vals.Live w (.nil : Vals TT []) ↔ True := by
  simp [Vals.Live]
@[simp] theorem Vals.live_cons (w : World TT) {t : Ty} {ts : List Ty} (v : Val TT t) (vs : Vals TT ts) :
    Vals.Live w (.cons v vs) ↔ Val.Live w v ∧ Vals.Live w vs := by
  simp [Vals.Live]

end StrictTS
