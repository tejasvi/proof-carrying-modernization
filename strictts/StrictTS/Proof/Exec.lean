/-
StrictTS proof layer: symbolic execution on explicit worlds.

`JS.exec m w` runs `m` on the world `w`. The `@[simp]` lemmas below push `exec` through the
monad operations, so `simp` evaluates straight-line code on a symbolic world: reads become
lookups `w.heap.get? (k, a)`, writes become `insert`s, and the result is an explicit
`some (.ok v, w')`.
-/
import StrictTS.Core.Sem
import StrictTS.Proof.Attr

namespace StrictTS
namespace JS

variable {TT : TypeTable} {α β : Type}

/-- Run a computation on a world: `none` = divergence. -/
def exec (m : JS TT α) (w : World TT) : Option (Except Exc α × World TT) := m.run.run w

@[simp, ts_sym] theorem exec_pure (a : α) (w : World TT) : exec (pure a : JS TT α) w = some (.ok a, w) := rfl

@[simp, ts_sym] theorem exec_bind (m : JS TT α) (f : α → JS TT β) (w : World TT) :
    exec (m >>= f) w =
      (match exec m w with
        | some (.ok a, w') => exec (f a) w'
        | some (.error e, w') => some (.error e, w')
        | none => none) := by
  simp only [exec, bind, ExceptT.bind, ExceptT.run, ExceptT.mk, ExceptT.bindCont, StateT.run, StateT.bind,
    Option.bind]
  cases h : m w with
  | none => rfl
  | some p =>
    obtain ⟨r, w'⟩ := p
    cases r <;> rfl

@[simp, ts_sym] theorem exec_map (f : α → β) (m : JS TT α) (w : World TT) :
    exec (f <$> m) w =
      (match exec m w with
        | some (.ok a, w') => some (.ok (f a), w')
        | some (.error e, w') => some (.error e, w')
        | none => none) := by
  rw [← bind_pure_comp, exec_bind]
  cases exec m w with
  | none => rfl
  | some p => obtain ⟨r, w'⟩ := p; cases r <;> rfl

@[simp, ts_sym] theorem exec_ite (c : Prop) [Decidable c] (a b : JS TT α) (w : World TT) :
    exec (if c then a else b) w = if c then exec a w else exec b w := by
  split <;> rfl

@[simp, ts_sym] theorem exec_dite (c : Prop) [Decidable c] (a : c → JS TT α) (b : ¬c → JS TT α) (w : World TT) :
    exec (dite c a b) w = if h : c then exec (a h) w else exec (b h) w := by
  split <;> rfl

@[simp, ts_sym] theorem exec_throw (e : Exc) (w : World TT) : exec (throw e : JS TT α) w = some (.error e, w) := rfl

@[simp, ts_sym] theorem exec_get (w : World TT) : exec (get : JS TT (World TT)) w = some (.ok w, w) := rfl

@[simp, ts_sym] theorem exec_set (w w' : World TT) : exec (set w' : JS TT PUnit) w = some (.ok ⟨⟩, w') := rfl

@[simp, ts_sym] theorem exec_modify (f : World TT → World TT) (w : World TT) :
    exec (modify f : JS TT PUnit) w = some (.ok ⟨⟩, f w) := rfl

@[simp, ts_sym] theorem exec_modifyGet (f : World TT → α × World TT) (w : World TT) :
    exec (modifyGet f : JS TT α) w = some (.ok (f w).1, (f w).2) := rfl

@[simp, ts_sym] theorem exec_panic (msg : String) (w : World TT) :
    exec (JS.panic msg : JS TT α) w = some (.error (.panic msg), w) := rfl

@[simp, ts_sym] theorem exec_throwJS (k : ErrKind) (msg : String) (w : World TT) :
    exec (JS.throwJS k msg : JS TT α) w = some (.error (.thrown (mkErr k (JSStr.ofString msg))), w) := rfl

@[simp, ts_sym] theorem exec_liftExcept_ok (a : α) (w : World TT) :
    exec (JS.liftExcept (.ok a) : JS TT α) w = some (.ok a, w) := rfl

@[simp, ts_sym] theorem exec_liftExcept_error (e : Exc) (w : World TT) :
    exec (JS.liftExcept (.error e) : JS TT α) w = some (.error e, w) := rfl

@[simp, ts_sym] theorem exec_catchThrown (m : JS TT α) (w : World TT) :
    exec (JS.catchThrown m) w =
      (match exec m w with
        | some (.ok a, w') => some (.ok (.ok a), w')
        | some (.error (.thrown e), w') => some (.ok (.error e), w')
        | some (.error (.panic s), w') => some (.error (.panic s), w')
        | none => none) := by
  simp only [exec, catchThrown, ExceptT.run, ExceptT.mk, StateT.run, bind, StateT.bind, Option.bind]
  cases h : m w with
  | none => rfl
  | some p =>
    obtain ⟨r, w'⟩ := p
    cases r with
    | ok a => rfl
    | error e => cases e <;> rfl

@[simp, ts_sym] theorem exec_read (k : HKind) (a : Nat) (w : World TT) :
    exec (JS.read k a) w =
      (match w.heap.get? (k, a) with
        | some c => some (.ok c, w)
        | none => some (.error (.panic "dangling reference"), w)) := by
  simp only [JS.read]
  rw [exec_bind, exec_get]
  dsimp only
  cases w.heap.get? (k, a) <;> rfl

@[simp, ts_sym] theorem exec_write (k : HKind) (a : Nat) (c : k.Cell TT) (w : World TT) :
    exec (JS.write k a c) w = some (.ok ⟨⟩, { w with heap := w.heap.insert (k, a) c }) := rfl

@[simp, ts_sym] theorem exec_alloc (k : HKind) (c : k.Cell TT) (w : World TT) :
    exec (JS.alloc k c) w =
      some (.ok w.next, { w with heap := w.heap.insert (k, w.next) c, next := w.next + 1 }) := rfl

@[simp, ts_sym] theorem exec_log (s : JSStr) (w : World TT) :
    exec (JS.log s) w = some (.ok ⟨⟩, { w with out := w.out ++ [s] }) := rfl

@[simp, ts_sym] theorem exec_enqueue (j : Job TT) (w : World TT) :
    exec (JS.enqueue j) w = some (.ok ⟨⟩, { w with jobs := w.jobs ++ [j] }) := rfl

/-! Heap lookups after updates. Keys of different kinds never collide, so
`get?_insert_kind_ne` fires with a side condition `simp` proves by computation. -/

@[simp, ts_sym] theorem heap_get_insert_self (h : Heap TT) (k : HKind) (a : Nat) (c : k.Cell TT) :
    (h.insert (k, a) c).get? (k, a) = some c :=
  Std.ExtDHashMap.get?_insert_self

theorem heap_get_insert_ne (h : Heap TT) {k k' : HKind} {a a' : Nat} (c : k.Cell TT)
    (hne : (k, a) ≠ (k', a')) : (h.insert (k, a) c).get? (k', a') = h.get? (k', a') := by
  rw [Std.ExtDHashMap.get?_insert]
  have : ((k, a) == (k', a')) = false := by
    simpa using hne
  simp [this]

@[simp, ts_sym] theorem heap_get_insert_kind_ne (h : Heap TT) {k k' : HKind} (a a' : Nat) (c : k.Cell TT)
    (hk : k ≠ k') : (h.insert (k, a) c).get? (k', a') = h.get? (k', a') :=
  heap_get_insert_ne h c (by intro e; exact hk (Prod.mk.inj e).1)

@[simp, ts_sym] theorem heap_get_insert_addr_ne (h : Heap TT) (k k' : HKind) {a a' : Nat} (c : k.Cell TT)
    (ha : a ≠ a') : (h.insert (k, a) c).get? (k', a') = h.get? (k', a') :=
  heap_get_insert_ne h c (by intro e; exact ha (Prod.mk.inj e).2)

/-- Two writes to the same cell: the second wins (the heap is extensional). -/
@[simp, ts_sym] theorem heap_insert_insert (h : Heap TT) (k : HKind) (a : Nat) (c₁ c₂ : k.Cell TT) :
    (h.insert (k, a) c₁).insert (k, a) c₂ = h.insert (k, a) c₂ := by
  apply Std.ExtDHashMap.ext_get?
  intro key
  rw [Std.ExtDHashMap.get?_insert, Std.ExtDHashMap.get?_insert, Std.ExtDHashMap.get?_insert]
  split <;> simp_all

/-- A fresh address is not in use (for worlds produced by allocation only). -/
def Fresh (w : World TT) : Prop := ∀ k a, w.next ≤ a → w.heap.get? (k, a) = none

end JS
end StrictTS
