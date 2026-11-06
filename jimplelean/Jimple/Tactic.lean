/-
  Jimple/Tactic.lean

  Automation for the verification conditions of `Jimple/Logic.lean`.

  * `jsimp` simp set: unfolds the one-step semantics and the WP calculus, and normalizes
    state and frame operations (`Frame.get_setLocal`, `State.heap_alloc`, ...).
  * `jground` simproc: evaluates closed terms of program-structure functions (statement
    lookup, class lookup, subtyping, method selection, trap lookup) to constructor form.
    The result is definitionally equal, so the kernel re-checks every such step.
  * `jvc`: symbolic execution loop — simplify, split on branches, introduce and
    destructure hypotheses — then `jauto` on the remaining arithmetic leaves
    (`omega`, `bv_decide`, `grind`, `decide`).
-/
import Jimple.Logic
import Jimple.SimpAttr
import Jimple.DecimalLemmas
import Lean

set_option linter.deprecated false

register_option jimple.debug : Bool := {
  defValue := false
  descr := "print each symbolic execution phase to stderr as it starts (to locate a hang)"
}

/-- Write a debugging line at once: appended to the file named by the environment variable
    `JIMPLE_DEBUG_LOG` if set (the elaborator captures `stderr` until a command ends, so a
    killed run would lose it), else to `stderr`. -/
def dbgOut (msg : String) : IO Unit := do
  match ← IO.getEnv "JIMPLE_DEBUG_LOG" with
  | some path =>
    let h ← IO.FS.Handle.mk path .append
    h.putStrLn msg
    h.flush
  | none =>
    let e ← IO.getStderr
    e.putStrLn msg
    e.flush

register_option jimple.foldCuts : Bool := {
  defValue := true
  descr := "keep the cut list and the postcondition of the method folded during symbolic execution (jFoldCuts)"
}

register_option jimple.dumpFuel : Nat := {
  defValue := 0
  descr := "with jimple.debug: write the goal before each jvc simp step at this loop fuel to $JIMPLE_DEBUG_LOG"
}

register_option jimple.dischFailFast : Bool := {
  defValue := false
  descr := "jdisch fails at once on side conditions about variables bound in the goal (no omega run)"
}

register_option jimple.hypHeapFacts : Bool := {
  defValue := false
  descr := "simplify hypotheses (jHypEval) with the heap facts of the context too"
}

register_option jimple.trace : Bool := {
  defValue := false
  descr := "trace the steps and failures of the jvc/jverify tactics" }

register_option jimple.modelContracts : Bool := {
  defValue := false
  descr := "the automation for contracts on abstract states (snapshot 20261025T0000Z): witnesses \
    of existential preconditions from hypotheses (`jExistsHyp`), postconditions still matching on \
    the outcome instantiated (`jForward`), heap facts carried back through frame rules \
    (`jFrameInst`), address disequalities from heap contents (`jne_heap`), conditional rewrites \
    in hypotheses discharged (`jHypEval`), any frame relation in `jframe` lemmas (`jFrameStep`), \
    string concatenation with literal recipes (`jconcat`, simp set `jsimpc`)" }

namespace Jimple

/-! ## Simp set -/

/-! Deciding `∃ x : BitVec n, P x` or `∀ x : BitVec n, P x` by enumeration (core's
    `instDecidableExistsBitVec`, …) does not finish for machine words, and simp's
    `decide := true` tries it on every closed such proposition (`∃ x, some (.int 1) = some (.int x)`
    from a postcondition, a method returning a constant). These instances take precedence and do
    not reduce, so such propositions are left to the simp lemmas. -/
noncomputable instance (priority := high) decExistsBV8 (P : BitVec 8 → Prop) : Decidable (∃ x, P x) :=
  Classical.propDecidable _
noncomputable instance (priority := high) decExistsBV16 (P : BitVec 16 → Prop) : Decidable (∃ x, P x) :=
  Classical.propDecidable _
noncomputable instance (priority := high) decExistsBV32 (P : BitVec 32 → Prop) : Decidable (∃ x, P x) :=
  Classical.propDecidable _
noncomputable instance (priority := high) decExistsBV64 (P : BitVec 64 → Prop) : Decidable (∃ x, P x) :=
  Classical.propDecidable _
noncomputable instance (priority := high) decForallBV8 (P : BitVec 8 → Prop) : Decidable (∀ x, P x) :=
  Classical.propDecidable _
noncomputable instance (priority := high) decForallBV16 (P : BitVec 16 → Prop) : Decidable (∀ x, P x) :=
  Classical.propDecidable _
noncomputable instance (priority := high) decForallBV32 (P : BitVec 32 → Prop) : Decidable (∀ x, P x) :=
  Classical.propDecidable _
noncomputable instance (priority := high) decForallBV64 (P : BitVec 64 → Prop) : Decidable (∀ x, P x) :=
  Classical.propDecidable _

section Lemmas

@[jsimp] theorem Frame.get_setLocal (fr : Frame) (x y : LocalIdx) (v : Value) :
    (fr.setLocal x v).get y = if y = x then some v else fr.get y := by
  unfold Frame.setLocal Frame.get Array.setGrow
  split
  · next h =>
    rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
    by_cases hxy : y = x
    · subst hxy; simp [h]
    · rw [if_neg (Ne.symm hxy), if_neg hxy]
  · next h =>
    rw [Array.getElem?_push, Array.size_append, Array.size_replicate]
    have hs : fr.locals.size + (x - fr.locals.size) = x := by omega
    rw [hs]
    by_cases hxy : y = x
    · subst hxy; simp
    · rw [if_neg hxy, if_neg hxy, Array.getElem?_append]
      split
      · rfl
      · next h2 =>
        rw [Array.getElem?_replicate]
        have h3 : fr.locals[y]? = none := Array.getElem?_eq_none (by omega)
        split <;> simp [h3]

@[jsimp] theorem Frame.get_init (s : Bool) (args : List Value) (y : LocalIdx) :
    (Frame.init s args).get y = none := by
  cases s <;> simp [Frame.init, Frame.get]

@[jsimp] theorem Frame.setLocal_this (fr : Frame) x v : (fr.setLocal x v).this = fr.this := rfl
@[jsimp] theorem Frame.setLocal_args (fr : Frame) x v : (fr.setLocal x v).args = fr.args := rfl
@[jsimp] theorem Frame.setLocal_caught (fr : Frame) x v : (fr.setLocal x v).caught = fr.caught := rfl
@[jsimp] theorem Frame.init_true (args : List Value) : Frame.init true args = ⟨#[], none, args, none⟩ := rfl
@[jsimp] theorem Frame.init_false (args : List Value) :
    Frame.init false args = ⟨#[], args.head?, args.tail, none⟩ := rfl
@[jsimp] theorem Frame.get_mk_empty (t : Option Value) (as : List Value) (c : Option Value) (y : LocalIdx) :
    (Frame.mk #[] t as c).get y = none := by simp [Frame.get]
@[jsimp] theorem Frame.get_withCaught (fr : Frame) (c : Option Value) (y : LocalIdx) :
    (fr.withCaught c).get y = fr.get y := rfl
@[jsimp] theorem Frame.withCaught_caught (fr : Frame) (c : Option Value) : (fr.withCaught c).caught = c := rfl
@[jsimp] theorem Frame.withCaught_this (fr : Frame) (c : Option Value) : (fr.withCaught c).this = fr.this := rfl
@[jsimp] theorem Frame.withCaught_args (fr : Frame) (c : Option Value) : (fr.withCaught c).args = fr.args := rfl
@[jsimp] theorem Frame.withCaught_setLocal (fr : Frame) (c : Option Value) x v :
    (fr.withCaught c).setLocal x v = (fr.setLocal x v).withCaught c := rfl

@[jsimp] theorem State.alloc_fst (σ : State) (o : Obj) : (σ.alloc o).1 = σ.next := rfl
@[jsimp] theorem State.heap_alloc (σ : State) (o : Obj) (b : Addr) :
    (σ.alloc o).2.heap b = if b = σ.next then some o else σ.heap b := by
  unfold State.alloc State.heap State.next
  simp [Array.getElem?_push]
/-- A comparison of addresses that `jdisch` refutes (`x < σ0.next ≤ σ.next`, so `x ≠ σ.next + 1`):
    no branch left for the jvc loop to split on. Not in `jsimp`: tried on every `if` over `Nat` it
    made `jdisch` run on each of them, and on CBACT04C's segments memory grew past 10 GB (pass it
    to `jvc`/`jverify` where wanted). -/
theorem ite_nat_ne {b a : Nat} {α : Sort _} [Decidable (b = a)] {x y : α} (h : b ≠ a) :
    (if b = a then x else y) = y := if_neg h

/-- An object that existed before an allocation (`b < σ.next` by `jdisch`). -/
@[jsimp high] theorem State.heap_alloc_of_lt {σ : State} {b : Addr} (h : b < σ.next) (o : Obj) :
    (σ.alloc o).2.heap b = σ.heap b := by
  rw [State.heap_alloc, if_neg (Nat.ne_of_lt h)]
@[jsimp] theorem State.next_alloc (σ : State) (o : Obj) : (σ.alloc o).2.next = σ.next + 1 := by
  simp [State.alloc, State.next]
@[jsimp] theorem State.heap_next (σ : State) : σ.heap σ.next = none := by
  simp [State.heap, State.next]
theorem State.lt_next_of_heap {σ : State} {a : Addr} {o : Obj} (h : σ.heap a = some o) : a < σ.next := by
  have h' : σ.mem[a]? = some o := h
  obtain ⟨hlt, _⟩ := Array.getElem?_eq_some_iff.mp h'
  exact hlt
theorem State.ne_next_of_heap {σ : State} {a : Addr} {o : Obj} (h : σ.heap a = some o) : a ≠ σ.next :=
  Nat.ne_of_lt (State.lt_next_of_heap h)
@[jsimp] theorem State.heap_setObj (σ : State) (a : Addr) (o : Obj) (b : Addr) :
    (σ.setObj a o).heap b = if b = a then (if a < σ.next then some o else none) else σ.heap b := by
  unfold State.setObj State.heap State.next
  rw [Array.getElem?_setIfInBounds]
  by_cases h : b = a
  · subst h; simp
  · rw [if_neg (Ne.symm h), if_neg h]
/-- Writing an object that exists (the usual case, `a < σ.next` by `jdisch`): no `a < σ.next`
    condition left in the goal, where it would be a branch for the jvc loop to split on. -/
@[jsimp high] theorem State.heap_setObj_of_lt {σ : State} {a : Addr} (h : a < σ.next) (o : Obj) (b : Addr) :
    (σ.setObj a o).heap b = if b = a then some o else σ.heap b := by
  rw [State.heap_setObj, if_pos h]
@[jsimp] theorem State.next_setObj (σ : State) a o : (σ.setObj a o).next = σ.next := by
  simp [State.setObj, State.next]
@[jsimp] theorem State.alloc_statics (σ : State) o : (σ.alloc o).2.statics = σ.statics := rfl
@[jsimp] theorem State.alloc_inits (σ : State) o : (σ.alloc o).2.inits = σ.inits := rfl
@[jsimp] theorem State.alloc_monitors (σ : State) o : (σ.alloc o).2.monitors = σ.monitors := rfl
@[jsimp] theorem State.alloc_out (σ : State) o : (σ.alloc o).2.out = σ.out := rfl
@[jsimp] theorem State.setObj_statics (σ : State) a o : (σ.setObj a o).statics = σ.statics := rfl
@[jsimp] theorem State.setObj_inits (σ : State) a o : (σ.setObj a o).inits = σ.inits := rfl
@[jsimp] theorem State.setObj_monitors (σ : State) a o : (σ.setObj a o).monitors = σ.monitors := rfl
@[jsimp] theorem State.setObj_out (σ : State) a o : (σ.setObj a o).out = σ.out := rfl
@[jsimp] theorem State.initOf_alloc (σ : State) o c : (σ.alloc o).2.initOf c = σ.initOf c := rfl
@[jsimp] theorem State.initOf_setObj (σ : State) a o c : (σ.setObj a o).initOf c = σ.initOf c := rfl
@[jsimp] theorem State.initOf_setStatic (σ : State) k v c : (σ.setStatic k v).initOf c = σ.initOf c := rfl
@[jsimp] theorem State.initOf_setMonitor (σ : State) a n c : (σ.setMonitor a n).initOf c = σ.initOf c := rfl
@[jsimp] theorem State.initOf_setInit (σ : State) c s c' :
    (σ.setInit c s).initOf c' = if c' = c then s else σ.initOf c' := by
  simp only [State.setInit, State.initOf, List.lookup]
  by_cases h : c' = c
  · subst h; simp
  · have : (c' == c) = false := by simp [h]
    simp only [this, h, ite_false]
    induction σ.inits with
    | nil => rfl
    | cons p l ih =>
      obtain ⟨k, v⟩ := p
      by_cases hk : k = c
      · subst hk; simp [List.filter, List.lookup, ih]; have : (c' == k) = false := by simp [h]
        simp [this]
      · have hk' : (k != c) = true := by simp [hk]
        simp only [List.filter, hk', List.lookup]
        split <;> simp_all
@[jsimp] theorem State.static_alloc (σ : State) o k : (σ.alloc o).2.static k = σ.static k := rfl
@[jsimp] theorem State.static_setObj (σ : State) a o k : (σ.setObj a o).static k = σ.static k := rfl
@[jsimp] theorem State.static_setInit (σ : State) c s k : (σ.setInit c s).static k = σ.static k := rfl
@[jsimp] theorem State.static_setMonitor (σ : State) a n k : (σ.setMonitor a n).static k = σ.static k := rfl
@[jsimp] theorem State.static_setStatic (σ : State) (k k' : FieldKey) (v : Value) :
    (σ.setStatic k v).static k' = if k' = k then some v else σ.static k' := by
  simp only [State.setStatic, State.static, List.lookup]
  by_cases h : k' = k
  · subst h; simp
  · have : (k' == k) = false := by simp [h]
    simp only [this, h, ite_false]
    induction σ.statics with
    | nil => rfl
    | cons p l ih =>
      obtain ⟨k2, v2⟩ := p
      by_cases hk : k2 = k
      · subst hk; simp [List.filter, List.lookup, ih]; have : (k' == k2) = false := by simp [h]
        simp [this]
      · have hk' : (k2 != k) = true := by simp [hk]
        simp only [List.filter, hk', List.lookup]
        split <;> simp_all
@[jsimp] theorem State.heap_setStatic (σ : State) k v a : (σ.setStatic k v).heap a = σ.heap a := rfl
@[jsimp] theorem State.next_setStatic (σ : State) k v : (σ.setStatic k v).next = σ.next := rfl
@[jsimp] theorem State.out_setStatic (σ : State) k v : (σ.setStatic k v).out = σ.out := rfl
@[jsimp] theorem State.heap_setInit (σ : State) c s a : (σ.setInit c s).heap a = σ.heap a := rfl
@[jsimp] theorem State.next_setInit (σ : State) c s : (σ.setInit c s).next = σ.next := rfl
@[jsimp] theorem State.heap_setMonitor (σ : State) a' n a : (σ.setMonitor a' n).heap a = σ.heap a := rfl
@[jsimp] theorem State.next_setMonitor (σ : State) a n : (σ.setMonitor a n).next = σ.next := rfl
@[jsimp] theorem State.monitorOf_setMonitor (σ : State) a n b :
    (σ.setMonitor a n).monitorOf b = if b = a then n else σ.monitorOf b := by
  simp only [State.setMonitor, State.monitorOf, List.lookup]
  by_cases h : b = a
  · subst h; simp
  · have : (b == a) = false := by simp [h]
    simp only [this, h, ite_false]
    induction σ.monitors with
    | nil => rfl
    | cons p l ih =>
      obtain ⟨k, v⟩ := p
      by_cases hk : k = a
      · subst hk; simp [List.filter, List.lookup, ih]; have : (b == k) = false := by simp [h]
        simp [this]
      · have hk' : (k != a) = true := by simp [hk]
        simp only [List.filter, hk', List.lookup]
        split <;> simp_all
@[jsimp] theorem State.monitorOf_alloc (σ : State) o b : (σ.alloc o).2.monitorOf b = σ.monitorOf b := rfl
@[jsimp] theorem State.monitorOf_setObj (σ : State) a o b : (σ.setObj a o).monitorOf b = σ.monitorOf b := rfl

@[jsimp] theorem Fields.get_set (fs : List (FieldKey × Value)) (k k' : FieldKey) (v : Value) :
    Fields.get (Fields.set fs k v) k' = if k' = k then some v else Fields.get fs k' := by
  simp only [Fields.get, Fields.set, List.lookup]
  by_cases h : k' = k
  · subst h; simp
  · have : (k' == k) = false := by simp [h]
    simp only [this, h, ite_false]
    induction fs with
    | nil => rfl
    | cons p fs ih =>
      obtain ⟨k2, v2⟩ := p
      by_cases hk : k2 = k
      · subst hk
        simp [List.filter, List.lookup, ih]
        have : (k' == k2) = false := by simp [h]
        simp [this]
      · have hk' : (k2 != k) = true := by simp [hk]
        simp only [List.filter, hk', List.lookup]
        split <;> simp_all

@[jsimp] theorem Fields.get_nil (k : FieldKey) : Fields.get [] k = none := rfl
/-- The fields of a fresh object (`(P.instanceFields c).map …`, a list literal). -/
@[jsimp] theorem Fields.get_cons (k k' : FieldKey) (v : Value) (fs : List (FieldKey × Value)) :
    Fields.get ((k', v) :: fs) k = if k = k' then some v else Fields.get fs k := by
  simp only [Fields.get, List.lookup]
  split <;> simp_all

@[jsimp] theorem lookup_nil' {β : Type} (a : Nat) : List.lookup a ([] : List (Nat × β)) = none := rfl
@[jsimp] theorem lookup_cons' {β : Type} (a k : Nat) (b : β) (l : List (Nat × β)) :
    List.lookup a ((k, b) :: l) = if a = k then some b else List.lookup a l := by
  simp only [List.lookup]
  split <;> simp_all

/-- `compareTo` results are `-1`, `0` or `1`, so they survive the cast to `int`. -/
theorem compareTo_cases (x y : BigDec) :
    x.compareTo y = -1 ∨ x.compareTo y = 0 ∨ x.compareTo y = 1 := by
  unfold BigDec.compareTo
  simp only []
  split
  · exact Or.inl rfl
  · split
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)

@[jsimp] theorem toInt_ofInt_compareTo (x y : BigDec) :
    (BitVec.ofInt 32 (x.compareTo y)).toInt = x.compareTo y := by
  rcases compareTo_cases x y with h | h | h <;> rw [h] <;> decide

/-- `compareTo` results survive the cast to `int` in `Int` form too. -/
@[jsimp] theorem compareTo_bmod32 (x y : BigDec) : (x.compareTo y).bmod 4294967296 = x.compareTo y := by
  rcases compareTo_cases x y with h | h | h <;> rw [h] <;> decide

@[jsimp] theorem BigDec.negate_mk (u s : Int) : (⟨u, s⟩ : BigDec).negate = ⟨-u, s⟩ := rfl

/-! Comparisons of decimals in constructor form (`⟨unscaled, scale⟩`, e.g. results of
    `divide(y, 2, mode)` and `valueOf` literals) are comparisons of their unscaled values at the
    finer scale: integer facts for `omega`, instead of rational ones. They are in the default
    simp set too, ahead of the rational `BigDec.compareTo_lt_zero_iff` family: `simp` tries the
    default set before `jsimp`. -/

theorem compareTo_mk_of_le {u s v t : Int} (h : t ≤ s) :
    (⟨u, s⟩ : BigDec).compareTo ⟨v, t⟩ =
      if u < v * 10 ^ (s - t).toNat then -1 else if u = v * 10 ^ (s - t).toNat then 0 else 1 := by
  have hm : max s t = s := by omega
  simp only [BigDec.compareTo, BigDec.upscale, hm, Int.sub_self, Int.toNat_zero, pow10Int,
    Int.pow_zero, Int.mul_one]

theorem compareTo_mk_of_ge {u s v t : Int} (h : s ≤ t) :
    (⟨u, s⟩ : BigDec).compareTo ⟨v, t⟩ =
      if u * 10 ^ (t - s).toNat < v then -1 else if u * 10 ^ (t - s).toNat = v then 0 else 1 := by
  have hm : max s t = t := by omega
  simp only [BigDec.compareTo, BigDec.upscale, hm, Int.sub_self, Int.toNat_zero, pow10Int,
    Int.pow_zero, Int.mul_one]

section
variable {u s v t : Int}
@[simp high, jsimp high] theorem compareTo_mk_lt_zero_of_le (h : t ≤ s) :
    (⟨u, s⟩ : BigDec).compareTo ⟨v, t⟩ < 0 ↔ u < v * 10 ^ (s - t).toNat := by
  rw [compareTo_mk_of_le h]; split <;> (try split) <;> omega
@[simp high, jsimp high] theorem compareTo_mk_le_zero_of_le (h : t ≤ s) :
    (⟨u, s⟩ : BigDec).compareTo ⟨v, t⟩ ≤ 0 ↔ u ≤ v * 10 ^ (s - t).toNat := by
  rw [compareTo_mk_of_le h]; split <;> (try split) <;> omega
@[simp high, jsimp high] theorem compareTo_mk_pos_of_le (h : t ≤ s) :
    0 < (⟨u, s⟩ : BigDec).compareTo ⟨v, t⟩ ↔ v * 10 ^ (s - t).toNat < u := by
  rw [compareTo_mk_of_le h]; split <;> (try split) <;> omega
@[simp high, jsimp high] theorem compareTo_mk_nonneg_of_le (h : t ≤ s) :
    0 ≤ (⟨u, s⟩ : BigDec).compareTo ⟨v, t⟩ ↔ v * 10 ^ (s - t).toNat ≤ u := by
  rw [compareTo_mk_of_le h]; split <;> (try split) <;> omega
@[simp high, jsimp high] theorem compareTo_mk_eq_zero_of_le (h : t ≤ s) :
    (⟨u, s⟩ : BigDec).compareTo ⟨v, t⟩ = 0 ↔ u = v * 10 ^ (s - t).toNat := by
  rw [compareTo_mk_of_le h]; split <;> (try split) <;> omega
@[simp high, jsimp high] theorem compareTo_mk_lt_zero_of_ge (h : s ≤ t) :
    (⟨u, s⟩ : BigDec).compareTo ⟨v, t⟩ < 0 ↔ u * 10 ^ (t - s).toNat < v := by
  rw [compareTo_mk_of_ge h]; split <;> (try split) <;> omega
@[simp high, jsimp high] theorem compareTo_mk_le_zero_of_ge (h : s ≤ t) :
    (⟨u, s⟩ : BigDec).compareTo ⟨v, t⟩ ≤ 0 ↔ u * 10 ^ (t - s).toNat ≤ v := by
  rw [compareTo_mk_of_ge h]; split <;> (try split) <;> omega
@[simp high, jsimp high] theorem compareTo_mk_pos_of_ge (h : s ≤ t) :
    0 < (⟨u, s⟩ : BigDec).compareTo ⟨v, t⟩ ↔ v < u * 10 ^ (t - s).toNat := by
  rw [compareTo_mk_of_ge h]; split <;> (try split) <;> omega
@[simp high, jsimp high] theorem compareTo_mk_nonneg_of_ge (h : s ≤ t) :
    0 ≤ (⟨u, s⟩ : BigDec).compareTo ⟨v, t⟩ ↔ v ≤ u * 10 ^ (t - s).toNat := by
  rw [compareTo_mk_of_ge h]; split <;> (try split) <;> omega
@[simp high, jsimp high] theorem compareTo_mk_eq_zero_of_ge (h : s ≤ t) :
    (⟨u, s⟩ : BigDec).compareTo ⟨v, t⟩ = 0 ↔ u * 10 ^ (t - s).toNat = v := by
  rw [compareTo_mk_of_ge h]; split <;> (try split) <;> omega
end

/-- Values in units `c` (e.g. `10^(-2)`) are equal iff the unit counts are. -/
theorem intCast_mul_right_cancel {a b : Int} {c : Rat} (hc : c ≠ 0) :
    (a : Rat) * c = (b : Rat) * c ↔ a = b := by
  constructor
  · intro h
    have h' : (a : Rat) = b := by
      have := congrArg (· * c⁻¹) h
      simpa only [Rat.mul_assoc, Rat.mul_inv_cancel c hc, Rat.mul_one] using this
    exact Rat.intCast_inj.mp h'
  · intro h; rw [h]

theorem inv_ten_pow_ne_zero (k : Nat) : ((10 : Rat) ^ k)⁻¹ ≠ 0 := by
  rw [← pow10_natCast, ← pow10_neg]; exact pow10_ne_zero _

/-! Decimal values at a common scale `k` (`toRat` normal form `u * (10^k)⁻¹`) are equal iff
    their unscaled values are. -/
@[jsimp] theorem intCast_mul_inv_ten_pow_inj {a b : Int} {k : Nat} :
    (a : Rat) * ((10 : Rat) ^ k)⁻¹ = (b : Rat) * ((10 : Rat) ^ k)⁻¹ ↔ a = b :=
  intCast_mul_right_cancel (inv_ten_pow_ne_zero k)
@[jsimp] theorem neg_intCast_mul_inv_ten_pow_inj {a b : Int} {k : Nat} :
    -(a : Rat) * ((10 : Rat) ^ k)⁻¹ = (b : Rat) * ((10 : Rat) ^ k)⁻¹ ↔ -a = b := by
  rw [← Rat.intCast_neg]; exact intCast_mul_right_cancel (inv_ten_pow_ne_zero k)
@[jsimp] theorem intCast_mul_inv_ten_pow_inj_neg {a b : Int} {k : Nat} :
    (a : Rat) * ((10 : Rat) ^ k)⁻¹ = -(b : Rat) * ((10 : Rat) ^ k)⁻¹ ↔ a = -b := by
  rw [← Rat.intCast_neg]; exact intCast_mul_right_cancel (inv_ten_pow_ne_zero k)
@[jsimp] theorem neg_intCast_mul_inv_ten_pow_inj_neg {a b : Int} {k : Nat} :
    -(a : Rat) * ((10 : Rat) ^ k)⁻¹ = -(b : Rat) * ((10 : Rat) ^ k)⁻¹ ↔ a = b := by
  rw [← Rat.intCast_neg, ← Rat.intCast_neg, intCast_mul_right_cancel (inv_ten_pow_ne_zero k)]
  omega

/-- Linear facts about `Int.tmod`/`Int.tdiv` (Java's `%` and `/`, `BigDecimal.remainder`) by a
    positive divisor, for `omega` (which treats them as atoms). The equation is oriented so that,
    as a hypothesis, it cannot loop as a rewrite rule. -/
theorem tmod_facts (a b : Int) (hb : 0 < b) :
    a.tmod b + b * a.tdiv b = a ∧ (0 ≤ a → 0 ≤ a.tmod b) ∧ (a ≤ 0 → a.tmod b ≤ 0) ∧
      -b < a.tmod b ∧ a.tmod b < b := by
  have h1 := Int.tmod_add_tdiv_mul a b
  have h3 := Int.tmod_lt_of_pos a hb
  have h4 := Int.lt_tmod_of_pos a hb
  refine ⟨by rw [Int.mul_comm]; omega, Int.tmod_nonneg b, fun ha => ?_, h4, h3⟩
  have := Int.tmod_nonneg b (show 0 ≤ -a by omega)
  rw [Int.neg_tmod] at this
  omega

@[jsimp] theorem JInt.toInt_toLong (x : I32) : (JInt.toLong x).toInt = x.toInt := by
  simp [JInt.toLong, BitVec.toInt_signExtend_of_le]

/-- Index arithmetic: non-negative `int` values as natural numbers. -/
@[jsimp] theorem bv32_toNat_of_nonneg {x : BitVec 32} (h : 0 ≤ x.toInt) : x.toNat = x.toInt.toNat := by
  rw [BitVec.toInt_eq_toNat_cond] at *
  split at h <;> omega

/-- `lcmp` as a comparison of the values (its result then compares with `0` by `omega`). -/
@[jsimp] theorem JLong.cmp_eq (a b : I64) :
    JLong.cmp a b = if a.toInt < b.toInt then -1 else if a = b then 0 else 1 := by
  simp [JLong.cmp, BitVec.slt_eq_decide]

@[jsimp] theorem JInt.toChar_toChar (x : I32) : JInt.toChar (JInt.toChar x) = JInt.toChar x := by
  apply BitVec.eq_of_toNat_eq
  simp [JInt.toChar, BitVec.toNat_setWidth]

@[jsimp] theorem Native.charsOf_nil : Native.charsOf [] = [] := rfl
@[jsimp] theorem Native.charsOf_cons_int (x : I32) (xs : List Value) :
    Native.charsOf (.int x :: xs) = x.setWidth 16 :: Native.charsOf xs := rfl
@[jsimp] theorem Native.charsOf_append (xs ys : List Value) :
    Native.charsOf (xs ++ ys) = Native.charsOf xs ++ Native.charsOf ys := by
  simp [Native.charsOf]

attribute [jsimp] Int.neg_add_cancel_right

/-- Frame conditions of contracts (`σ'.inits = σ.inits`) as rewrite rules on the lookups
    (`jFrameFacts`). -/
theorem State.initOf_eq_of_inits {σ σ' : State} (h : σ'.inits = σ.inits) :
    ∀ c, σ'.initOf c = σ.initOf c := by
  intro c; simp [State.initOf, h]
theorem State.static_eq_of_statics {σ σ' : State} (h : σ'.statics = σ.statics) :
    ∀ k, σ'.static k = σ.static k := by
  intro k; simp [State.static, h]

/-- A program counter that is not a key of a cut list (`jFoldCuts`' `hcutsNone`). -/
theorem lookup_none_of_keys {β : Type} {I : List (Nat × β)} {ks : List Nat} {pc : Nat}
    (hk : I.map Prod.fst = ks) (h : pc ∉ ks) : I.lookup pc = none := by
  subst hk
  induction I with
  | nil => rfl
  | cons p I ih =>
    obtain ⟨k, b⟩ := p
    simp only [List.map_cons, List.mem_cons, not_or] at h
    have hne : (pc == k) = false := by simpa using h.1
    simp only [List.lookup, hne]
    exact ih h.2

/-! ### Lists of strings in the heap (output lines, `List<String>` contents) -/

/-- Every string object of `σ` is still there in `σ'`. -/
def StrMono (σ σ' : State) : Prop := ∀ x s, σ.heap x = some (.str s) → σ'.heap x = some (.str s)

/-- The values `ys` refer to the strings `ss`, in order. -/
def StrsAt (σ : State) (ys : List Value) (ss : List JStr) : Prop := ys.map (strOf σ) = ss.map some

theorem strOf_eq_some_iff {σ : State} {v : Value} {s : JStr} :
    strOf σ v = some s ↔ ∃ x, v = .ref x ∧ σ.heap x = some (.str s) := by
  unfold strOf
  split
  · simp only [Value.ref.injEq, exists_eq_left']
    split <;> simp_all
  · simp_all

/-- The strings are still there: `jStrsMono` reduces a `StrsAt` goal to `StrMono`. -/
theorem StrsAt.mono {σ σ' : State} {ys : List Value} {ss : List JStr} (h : StrsAt σ ys ss)
    (hm : StrMono σ σ') : StrsAt σ' ys ss := by
  unfold StrsAt at *
  induction ys generalizing ss with
  | nil => exact h
  | cons y ys ih =>
    cases ss with
    | nil => simp at h
    | cons s ss =>
      simp only [List.map_cons, List.cons.injEq] at h ⊢
      refine ⟨?_, ih h.2⟩
      obtain ⟨x, rfl, hx⟩ := strOf_eq_some_iff.1 h.1
      exact strOf_eq_some_iff.2 ⟨x, rfl, hm x s hx⟩

theorem StrsAt.mono_eq {σ σ' : State} {ys : List Value} {ss ss' : List JStr} (h : StrsAt σ ys ss')
    (he : ss' = ss) (hm : StrMono σ σ') : StrsAt σ' ys ss := he ▸ h.mono hm

@[jsimp] theorem StrsAt_nil (σ : State) : StrsAt σ [] [] ↔ True := by simp [StrsAt]
@[jsimp] theorem StrsAt_cons (σ : State) (y : Value) (ys : List Value) (s : JStr) (ss : List JStr) :
    StrsAt σ (y :: ys) (s :: ss) ↔ strOf σ y = some s ∧ StrsAt σ ys ss := by
  simp [StrsAt]
@[jsimp] theorem StrsAt_snoc (σ : State) (ys : List Value) (y : Value) (ss : List JStr) (s : JStr) :
    StrsAt σ (ys ++ [y]) (ss ++ [s]) ↔ StrsAt σ ys ss ∧ strOf σ y = some s := by
  unfold StrsAt
  simp only [List.map_append, List.map_cons, List.map_nil]
  constructor
  · intro h
    have hl : ys.length = ss.length := by
      have := congrArg List.length h
      simp only [List.length_append, List.length_map, List.length_cons, List.length_nil] at this
      omega
    obtain ⟨h1, h2⟩ := List.append_inj h (by simp [hl])
    exact ⟨h1, by simpa using h2⟩
  · rintro ⟨h1, h2⟩
    rw [h1, h2]
/-- The simp normal form of `(s0 :: ss) ++ [s]`. -/
@[jsimp] theorem StrsAt_snoc_cons (σ : State) (ys : List Value) (y : Value) (s0 : JStr)
    (ss : List JStr) (s : JStr) :
    StrsAt σ (ys ++ [y]) (s0 :: (ss ++ [s])) ↔ StrsAt σ ys (s0 :: ss) ∧ strOf σ y = some s := by
  rw [← List.cons_append]; exact StrsAt_snoc ..

/-- `String.valueOf` of an object, kept folded except for strings and `null` (unfolding the
    general case expands every rendering path of every object kind, recursively). -/
def Native.valueOfObjSlow (P : Program) (v : Value) (σ : State) (k : JStr → State → NRes) :
    NRes := Native.valueOfObj P v σ k

@[jsimp] theorem Native.valueOfObj_ref (P : Program) (a : Addr) (σ : State)
    (k : JStr → State → NRes) :
    Native.valueOfObj P (.ref a) σ k =
      match σ.heap a with
      | some (.str s) => k s σ
      | _ => Native.valueOfObjSlow P (.ref a) σ k := by
  unfold Native.valueOfObjSlow
  cases h : σ.heap a with
  | none => rfl
  | some o => cases o <;> first | rfl | simp [Native.valueOfObj, Native.valueOfObjN, h, Native.nObjStr]

@[jsimp] theorem Native.valueOfObj_null (P : Program) (σ : State) (k : JStr → State → NRes) :
    Native.valueOfObj P .null σ k = k (Native.jstr "null") σ := rfl

/-- `invokedynamic makeConcatWithConstants` (string concatenation): the recipe's text, then
    `concatRecipe` (a literal recipe is spelled out by the `jconcat` simproc). -/
@[jsimpc] theorem evalDynamic_concat (P : Program) (params : List JType) (args : List Value)
    (bsm : MethodSig) (recipe : Value) (consts : List Value) (σ : State)
    (h : bsm.cls = "java.lang.invoke.StringConcatFactory") :
    evalDynamic P "makeConcatWithConstants" params args bsm (recipe :: consts) σ =
      match strOf σ recipe with
      | some r => concatRecipe P consts r params args σ []
      | none => .ret (.wrong "concat recipe") := by
  cases hr : strOf σ recipe <;> simp [evalDynamic, h, hr]

attribute [jsimpc] concatRecipe

-- a call answered by a callee contract: the target is the method the call selects
attribute [jsimp] Targets

/-- The range of a machine integer (`jIntBounds` adds these facts for the symbolic ones). -/
theorem bv32_toInt_lt (x : BitVec 32) : x.toInt < 2147483648 := by
  have := BitVec.toInt_lt (x := x); simpa using this
theorem bv32_le_toInt (x : BitVec 32) : -2147483648 ≤ x.toInt := by
  have := BitVec.le_toInt (x := x); simpa using this
theorem bv64_toInt_lt (x : BitVec 64) : x.toInt < 9223372036854775808 := by
  have := BitVec.toInt_lt (x := x); simpa using this
theorem bv64_le_toInt (x : BitVec 64) : -9223372036854775808 ≤ x.toInt := by
  have := BitVec.le_toInt (x := x); simpa using this

@[jsimp] theorem bv32_toInt_ofNat_of_lt {n : Nat} (h : n < 2147483648) : (BitVec.ofNat 32 n).toInt = n := by
  rw [BitVec.toInt_eq_toNat_cond]
  simp only [BitVec.toNat_ofNat]
  split <;> omega

@[jsimp] theorem int_toNat_add_one {a : Int} (h : 0 ≤ a) : (a + 1).toNat = a.toNat + 1 := by omega

attribute [jsimp] Nat.mod_eq_of_lt

/-- `bmod` by `2^32`/`2^64` is the identity on the signed range (overflow-free arithmetic). -/
@[jsimp] theorem bmod32_of_bounds {x : Int} (h1 : -2147483648 ≤ x) (h2 : x ≤ 2147483647) :
    x.bmod 4294967296 = x := by
  rw [Int.bmod_def]; split <;> omega
@[jsimp] theorem bmod64_of_bounds {x : Int} (h1 : -9223372036854775808 ≤ x) (h2 : x ≤ 9223372036854775807) :
    x.bmod 18446744073709551616 = x := by
  rw [Int.bmod_def]; split <;> omega

/-- No application class has the name of a library class: library lookups (exception
    handlers, subtyping between library classes, library statics) do not depend on the program.
    With `NoShadow P` among the facts of a per-method proof (`Jimple/Verify.lean`), the
    `jnoshadow` simproc evaluates them. -/
def NoShadow (P : Program) : Prop := ∀ c, isLibClass c = true → P.findClass c = none

theorem findClass_of_noShadow {P : Program} {c : ClassName} (h : NoShadow P)
    (hc : isLibClass c = true) : P.findClass c = none := h c hc

/-- For `jdisch`: `(P.findClass c).isSome = true` from a fact `P.findClass c = some d`. -/
theorem isSome_of_eq_some {α : Type} {o : Option α} {a : α} (h : o = some a) : o.isSome = true := by
  subst h; rfl

end Lemmas

/-! ## Ground evaluation of program-structure functions -/

open Lean Meta Elab Tactic

/-- Functions whose closed applications are evaluated during symbolic execution. -/
def groundFns : List Name := [
  ``Body.stmtAt, ``Program.lookup, ``Program.findClass, ``Program.method?, ``Program.method!,
  ``ClassTree.toList, ``Program.isProgClass, ``Program.supers, ``Program.isSubclass,
  ``Program.subtype, ``Program.resolveField, ``Program.instanceFields, ``Program.staticFieldType,
  ``Program.progSubclasses,
  ``Program.selectVirtual,
  ``Program.selectSpecial, ``Program.selectStatic, ``Program.concrete, ``Program.initChain,
  ``Program.ClassDecl.findMethod, ``Program.declaredFields, ``Program.ClassDecl.ownFields,
  ``Program.staticDecl, ``Program.ClassDecl.findClinit, ``Program.ClassDecl.hasDefaultMethods,
  ``fieldKey, ``findHandler, ``isLibClass, ``preludeFind, ``preludeAncestors,
  ``MethodRef.decl, ``MethodRef.cls, ``MethodRef.sig, ``MethodDecl.body, ``MethodDecl.mods,
  ``MethodDecl.sub, ``MethodSig.sub, ``MethodMods.isStatic, ``Obj.ty, ``Obj.isValueObj,
  ``JType.default, ``JType.isRef, ``Native.overrides, ``Targets, ``BigDec.parse?, ``JStr.toLean,
  ``Native.parseIntStr, ``RoundingMode.ofName?, ``RoundingMode.ofOrdinal?]

/-- Types whose values are never expanded by ground evaluation (they stay named constants). -/
def opaqueTypes : List Name := [``Body, ``Program, ``ClassDecl, ``Array, ``String]

/-- Evaluate a closed term to constructor normal form, leaving bodies and programs alone. -/
partial def groundEval (e : Lean.Expr) : MetaM Lean.Expr := do
  let e ← whnfD e
  match e.getAppFn with
  | .const c _ =>
    if (← getEnv).isConstructor c then
      let args ← e.getAppArgs.mapM fun a => do
        if a.hasFVar || a.hasMVar || a.hasLooseBVars then return a
        let ty ← whnfD (← inferType a)
        if ty.isSort || ty.isForall then return a
        if (← isProp ty) then return a
        match ty.getAppFn with
        | .const tn _ =>
          if tn == ``String then
            -- named string constants (class names of an import) become their literals
            let a' ← whnfD a
            return if a'.isStringLit then a' else a
          else if opaqueTypes.contains tn then return a else groundEval a
        | _ => return a
      return mkAppN e.getAppFn args
    else return e
  | _ => return e

/-- `groundEval` with simp's unfolding restrictions lifted. -/
def groundEvalClean (e : Lean.Expr) : MetaM Lean.Expr :=
  withTheReader Meta.Context (fun ctx => { ctx with customCanUnfoldPredicate? := none }) <|
    withConfig (fun c => { c with canUnfoldPredicateConfig := .default }) <|
    withTransparency .default <| groundEval e

/-- Whether a closed term of this type may be evaluated (small first-order data only). -/
def groundableType (ty : Lean.Expr) : MetaM Bool := do
  let ty ← whnfR ty
  if ty.isSort || ty.isForall then return false
  if (← isProp ty) then return false
  match ty.getAppFn with
  | .const tn _ =>
    if opaqueTypes.contains tn then return false
    return true
  | _ => return false

/-- Program queries evaluated by compiled code (their `whnf` evaluation walks every class of a
    large program); the kernel re-checks each result by evaluation. -/
def nativeFns : List Name := []  -- disabled: evaluating a large program value ran out of memory

/-- Results of native evaluations (each evaluation compiles an auxiliary definition). -/
initialize nativeCache : IO.Ref (Std.HashMap Lean.Expr Lean.Expr) ← IO.mkRef {}

unsafe def nativeEvalUnsafe (e ty : Lean.Expr) : MetaM (Option Lean.Expr) := do
  let ty ← instantiateMVars ty
  let isStr (t : Lean.Expr) := t.isConstOf ``String || t.isConstOf ``Jimple.ClassName
  if ty.isConstOf ``Bool then return some (toExpr (← Lean.Meta.evalExpr Bool ty e))
  if ty.isAppOfArity ``Option 1 && ty.appArg!.isConstOf ``Bool then
    return some (toExpr (← Lean.Meta.evalExpr (Option Bool) ty e))
  if ty.isAppOfArity ``List 1 && isStr ty.appArg! then
    return some (toExpr (← Lean.Meta.evalExpr (List String) ty e))
  if ty.isAppOfArity ``Option 1 && ty.appArg!.isAppOfArity ``List 1 && isStr ty.appArg!.appArg! then
    return some (toExpr (← Lean.Meta.evalExpr (Option (List String)) ty e))
  return none

@[implemented_by nativeEvalUnsafe]
opaque nativeEval (e ty : Lean.Expr) : MetaM (Option Lean.Expr)

/-- Time spent in each simproc during one `jsym` call (logged under `jimple.trace`). -/
initialize jProf : IO.Ref (Std.HashMap String (Nat × Nat)) ← IO.mkRef {}

def jProfile {α : Type} (name : String) (x : Simp.SimpM α) : Simp.SimpM α := do
  let t0 ← IO.monoNanosNow
  let r ← x
  let t1 ← IO.monoNanosNow
  jProf.modify fun m => let (c, t) := m.getD name (0, 0); m.insert name (c + 1, t + (t1 - t0))
  return r

/-- `jground`: closed, non-constructor terms of small data types are replaced by their
    values (statement lookup, class lookup, subtyping, method selection, trap lookup, …). -/
def jgroundCore (e : Lean.Expr) : Simp.SimpM Simp.DStep := do
  if e.hasFVar || e.hasMVar || e.hasLooseBVars then return .continue
  if e.isLit then return .continue
  let env ← getEnv
  let ok ← match e.getAppFn with
    | .const c _ =>
      if env.isConstructor c then pure false
      else if groundFns.contains c then pure true
      else if (env.getProjectionFnInfo? c).isSome then pure true
      else pure (c == ``GetElem?.getElem? || c == ``List.lookup || c == ``List.find?)
    | .proj .. => pure true
    | _ => pure false
  unless ok do return .continue
  let ty ← inferType e
  -- a string held by a named constant (a class name of an import): its literal
  if ty.isConstOf ``String || ty.isConstOf ``Jimple.ClassName then
    let e' ← whnfD e
    return if e'.isStringLit then .done e' else .continue
  unless ← groundableType ty do return .continue
  -- arithmetic values are normalized by simp's own simprocs
  match (← whnfR ty).getAppFn with
  | .const tn _ =>
    if tn == ``BitVec || tn == ``Fin || tn == ``Int || tn == ``Rat || tn == ``UInt32 || tn == ``UInt64 then
      return .continue
  | _ => pure ()
  if let some fn := e.getAppFn.constName? then
    if nativeFns.contains fn then
      if let some r := (← nativeCache.get).get? e then return .done r
      if let some r ← (try nativeEval e ty catch _ => pure none) then
        nativeCache.modify (·.insert e r)
        return .done r
  let e' ← groundEvalClean e
  if e' == e then return .continue
  return .done e'

dsimproc jground (_) := fun e => jProfile "jground" (jgroundCore e)

/-- `jnoshadow`: `P.findClass c` is `none` for a library class `c` when the context has
    `NoShadow P`. `isLibClass c` is evaluated here (the kernel checks it by `decide`), not by
    discharging a side condition. -/
def jnoshadowCore (e : Lean.Expr) : Simp.SimpM Simp.Step := do
  unless e.isAppOfArity ``Program.findClass 2 do return .continue
  let P := e.appFn!.appArg!
  let c := e.appArg!
  let .lit (.strVal name) := c | return .continue
  unless isLibClass name do return .continue
  let some h := (← getLCtx).findDecl? fun d =>
      if d.isImplementationDetail then none
      else
        let ty := d.type.consumeMData
        if ty.isAppOfArity ``NoShadow 1 && ty.appArg! == P then some d.toExpr else none
    | return .continue
  let hc ← mkDecideProof (← mkEq (mkApp (mkConst ``isLibClass) c) (mkConst ``true))
  return .done { expr := mkApp (mkConst ``Option.none [levelZero]) (mkConst ``ClassDecl),
                 proof? := some (mkApp4 (mkConst ``findClass_of_noShadow) P c h hc) }

simproc jnoshadow (Program.findClass _ _) := fun e => jProfile "jnoshadow" (jnoshadowCore e)

/-- Functions defined by pattern matching on their (first-order) argument: reduced when the
    argument is a constructor application, even with symbolic fields. -/
def ctorFns : List Name := [``Obj.ty, ``Obj.isValueObj, ``Obj.sameContent, ``JType.default,
  ``JType.narrow, ``ListKind.cls, ``MapKind.cls, ``SetKind.cls, ``Native.nObjStr, ``Native.primStr,
  ``Native.boolStr, ``Native.canonBits, ``Native.modsOf, ``Program.subtype, ``outToEv,
  ``EvOut.toOutcome, ``Value.asInt, ``Value.asLong]

/-- Heads of semantic computations: a `jctor` argument containing one is not evaluated
    (`whnf` would run the computation, which is symbolic and stays stuck after seconds). -/
def jctorStuckHeads : List Name := [``evalExpr, ``evalInvoke, ``step, ``stepStmt, ``Res.bind,
  ``wpR, ``bodyWP, ``callWP, ``ensureInit, ``initThen, ``getStatic, ``putStatic,
  ``Native.staticCall, ``Native.plainInst, ``Native.instCall, ``Native.ctorCall]

/-- `jctor`: evaluate `ctorFns` applications whose result is constructor-headed. -/
def jctorCore (e : Lean.Expr) : Simp.SimpM Simp.DStep := do
  let some fn := e.getAppFn.constName? | return .continue
  unless ctorFns.contains fn do return .continue
  if e.hasMVar || e.hasLooseBVars then return .continue
  if e.getAppArgs.any (fun a => (a.find? fun t => match t.getAppFn with
      | .const c _ => jctorStuckHeads.contains c
      | _ => false).isSome) then
    return .continue
  let e' ← tryCatchRuntimeEx
    (withTheReader Meta.Context (fun ctx => { ctx with customCanUnfoldPredicate? := none }) <|
      withConfig (fun c => { c with canUnfoldPredicateConfig := .default }) <|
      withTransparency .default <| whnf e)
    (fun _ => pure e)
  match e'.getAppFn with
  | .const c _ => if (← getEnv).isConstructor c then return .visit e' else return .continue
  | .lit _ => return .visit e'
  | _ => return .continue

dsimproc jctor (_) := fun e => jProfile "jctor" (jctorCore e)

/-! ### Compiled evaluation with a kernel `decide` certificate

  String-processing library functions (decimal parsing, `Integer.parseInt`, enum lookup by
  name) are evaluated by compiled code on closed arguments; the result is certified by
  `decide`, so the kernel re-checks it. -/

deriving instance ToExpr for RoundingMode
deriving instance ToExpr for BigDec

def evalFns : List Name := [``BigDec.parse?, ``Native.parseIntStr, ``RoundingMode.ofName?,
  ``descToName]

/-- The Lean string literal behind `JStr.toLean (JStr.ofString "…")` or `JStr.ofString "…"`. -/
partial def strLitOf? (e : Lean.Expr) : Option String :=
  let e := e.consumeMData
  if e.isAppOfArity ``JStr.toLean 1 then strLitOf? e.appArg!
  else if e.isAppOfArity ``JStr.ofString 1 then
    match e.appArg!.consumeMData with
    | .lit (.strVal s) => some s
    | _ => none
  else match e with
    | .lit (.strVal s) => some s
    | _ => none

/-- Evaluate a closed string-processing call on a literal (compiled code), as an `Expr`. -/
def evalClosed (e : Lean.Expr) : MetaM (Option Lean.Expr) := do
  let some fn := e.getAppFn.constName? | return none
  let args := e.getAppArgs
  if fn == ``BigDec.parse? && args.size == 1 then
    return (strLitOf? args[0]!).map fun s => toExpr (BigDec.parse? s)
  else if fn == ``RoundingMode.ofName? && args.size == 1 then
    return (strLitOf? args[0]!).map fun s => toExpr (RoundingMode.ofName? s)
  else if fn == ``descToName && args.size == 1 then
    return (strLitOf? args[0]!).map fun s => toExpr (descToName s)
  else if fn == ``Native.parseIntStr && args.size == 3 then
    let some s := strLitOf? args[0]! | return none
    let lo ← evalInt? args[1]!
    let hi ← evalInt? args[2]!
    match lo, hi with
    | some lo, some hi => return some (toExpr (Native.parseIntStr (JStr.ofString s) lo hi))
    | _, _ => return none
  else return none
where
  evalInt? (e : Lean.Expr) : MetaM (Option Int) := do
    let e ← instantiateMVars e
    match e.int? with
    | some i => return some i
    | none => match e.nat? with
      | some n => return some n
      | none => return none

/-- `jeval`: closed applications of `evalFns`, evaluated and certified by `decide`. -/
def jevalCore (e : Lean.Expr) : Simp.SimpM Simp.Step := do
  let some fn := e.getAppFn.constName? | return .continue
  unless evalFns.contains fn do return .continue
  if e.hasFVar || e.hasMVar || e.hasLooseBVars then return .continue
  let some v ← evalClosed e | return .continue
  let eq ← mkEq e v
  let pf ← mkDecideProof eq
  return .done { expr := v, proof? := some pf }

simproc jeval (_) := fun e => jProfile "jeval" (jevalCore e)

/-- Library-model dispatch functions: applied to a concrete method reference and concrete
    argument-list shape, they reduce (by evaluating the string tests of their `match`) to
    the selected model. -/
def nativeDispatchFns : List Name := [
  ``Native.staticCall, ``Native.instCall, ``Native.ctorCall, ``Native.plainInst, ``Native.libStatic,
  ``Native.stringInst, ``Native.builderInst, ``Native.boxedInst, ``Native.decInst,
  ``Native.bigIntInst, ``Native.listInst, ``Native.mapInst, ``Native.setInst, ``Native.viewInst,
  ``Native.iterInst, ``Native.entryInst]

/-- `jnative`: resolve library-model dispatch to the selected model (`some body`/`none`). -/
def jnativeCore (e : Lean.Expr) : Simp.SimpM Simp.DStep := do
  let some fn := e.getAppFn.constName? | return .continue
  unless nativeDispatchFns.contains fn do return .continue
  if e.hasMVar || e.hasLooseBVars then return .continue
  let e' ← withTheReader Meta.Context (fun ctx => { ctx with customCanUnfoldPredicate? := none }) <|
    withConfig (fun c => { c with canUnfoldPredicateConfig := .default }) <|
    withTransparency .default <| whnf e
  match e'.getAppFn with
  | .const c _ =>
    if c == ``Option.some || c == ``Option.none then return .visit e'
    -- partial progress: stuck at a `match`/`if` on symbolic data that simp can continue on
    else if (← isMatcher c) || c == ``ite || c == ``dite then return .visit e'
    else return .continue
  | _ => return .continue

dsimproc jnative (_) := fun e => jProfile "jnative" (jnativeCore e)

/-- `jconcat`: a string concatenation's literal recipe (`JStr.ofString "…"`) as its explicit
    list of UTF-16 units, so that `concatRecipe`'s equations take it apart. -/
dsimproc jconcat (concatRecipe _ _ (JStr.ofString _) _ _ _ _) := fun e => do
  let_expr concatRecipe P consts r ts vs σ acc := e | return .continue
  let r := r.consumeMData
  unless r.isAppOfArity ``JStr.ofString 1 do return .continue
  let .lit (.strVal str) := r.appArg!.consumeMData | return .continue
  let elems := (JStr.ofString str).map fun (c : BitVec 16) =>
    mkApp2 (mkConst ``BitVec.ofNat) (mkNatLit 16) (mkNatLit c.toNat)
  let lst ← mkListLit (mkApp (mkConst ``BitVec) (mkNatLit 16)) elems
  return .done (mkAppN e.getAppFn #[P, consts, lst, ts, vs, σ, acc])

end Jimple

namespace Jimple

/-! ## Definitions unfolded during symbolic execution -/

attribute [jsimp] List.take_of_length_le List.length_map List.length_take
attribute [jsimp] List.take_succ List.map_append List.sum_append List.sum_cons List.sum_nil
  Option.toList_some Option.toList_none List.take_zero List.map_nil List.map_cons
attribute [jsimp] wpR evalArgs Res.bind_ret Res.bind_call Res.bind_choose Res.monad_bind_eq
  Res.monad_pure_eq Spec.of Invariants.inst Value.ofBool JInt.ofBool
attribute [jsimp] Native.ok Native.okVoid Native.okObj Native.okStr Native.okInt Native.okBool
  Native.bad Native.thr Native.thrNPE Native.argI Native.argL Native.argObj Native.argDec
  Native.argBigInt Native.argStr Native.argChars Native.argRM Native.argMC Native.rnd
  Native.divZero Native.jstr Native.boxOf Native.idxCheck Native.listMutable Native.charAtIdx
  Native.argSeq Native.seqCharAt Native.valueOfArg Native.valueOfCharsArg Native.primStr
-- `stepStmt` and `evalExpr` match on the statement and the expression, which are known: their
-- equation lemmas fire only on a constructor, so the alternatives of `step`'s match (a bound
-- statement) are not expanded symbolically at every step
attribute [jsimp] stepStmt evalExpr
attribute [jsimp] step.eq_def afterStep.eq_def afterEv.eq_def
  evalImm.eq_def evalConst.eq_def evalBinop.eq_def evalUnop.eq_def evalCond.eq_def intCmp.eq_def
  refEq.eq_def primCast.eq_def evalCast.eq_def evalInstOf.eq_def storeRef.eq_def getField.eq_def
  putField.eq_def getStatic.eq_def putStatic.eq_def initThen.eq_def ensureInit.eq_def
  arrayLoad.eq_def arrayStore.eq_def newObj.eq_def newArray.eq_def evalInvoke.eq_def callM.eq_def
  outToEv.eq_def EvOut.toOutcome.eq_def switchTarget.eq_def noModel.eq_def divZero.eq_def
  aioobe.eq_def allocStr.eq_def retObj.eq_def mkExc.eq_def throwNew.eq_def npe.eq_def objAt.eq_def
  strOf.eq_def decOf.eq_def bigIntOf.eq_def Native.throwsK.eq_def

theorem bodyWP_succ (P : Program) (H : Handler) (b : Body) (I : Cuts) (Post : Outcome → Prop)
    (n pc : Nat) (fr : Frame) (σ : State) :
    bodyWP P H b I Post (n + 1) pc fr σ =
      wpR H (step P b pc fr σ) fun r =>
        match afterStep P b pc fr r with
        | .done o => Post o
        | .cont pc' fr' σ' =>
          match I.lookup pc' with
          | some A => A fr' σ'
          | none => bodyWP P H b I Post n pc' fr' σ' := rfl

/-- The caller's rest after an inlined call: `K` itself, kept folded (the `jkont` simproc
    stops simp at it) so that it is not simplified again at every step of the callee (with
    nested inlining every level's rest was revisited: DigitalRootTest 220 s → 38 s); it unfolds
    when the callee returns. (Folding the rest of each statement the same way made `jverify`
    hang; not used.) -/
def Kont {α : Type} (K : α → Prop) : α → Prop := K

@[jsimp] theorem Kont_apply {α : Type} (K : α → Prop) (a : α) : Kont K a = K a := rfl

/-- `jkont` (pre): `Kont K` is left alone (simp does not enter `K`); `Kont K a` is `K a`. -/
dsimproc ↓ jkont (_) := fun e => do
  unless e.isAppOf ``Kont do return .continue
  match e.getAppNumArgs with
  | 2 => return .done e
  | 3 => return .visit (e.appFn!.appArg!.beta #[e.appArg!])
  | _ => return .continue

@[jsimp] theorem callWP_def (P : Program) (Γ : SpecEnv) (d : Nat) (sig : MethodSig) (callee : Callee)
    (args : List Value) (σ : State) (K : Outcome → Prop) :
    callWP P Γ d sig callee args σ K =
      match Γ sig, callee with
      | some S, .method m => Targets P sig m ∧ S.pre args σ ∧ ∀ o, S.post args σ o → K o
      | some S, .virtual c => P.isProgClass c = true ∧ P.isSubclass c sig.cls = some true ∧
          P.staticDecl sig = false ∧ S.pre args σ ∧ ∀ o, S.post args σ o → K o
      | none, .method m =>
        match d with
        | 0 => False
        | d + 1 =>
          match m.decl.body with
          | some b => bodyWP P (callWP P Γ d) b [] (Kont K) inlineFuel 0 (Frame.init m.decl.mods.isStatic args) σ
          | none => K (.wrong "abstract or native method")
      | none, .virtual c =>
        match d with
        | 0 => False
        | d + 1 =>
          match P.selectVirtual c sig.sub with
          | .jimple m =>
            match m.decl.body with
            | some b => bodyWP P (callWP P Γ d) b [] (Kont K) inlineFuel 0 (Frame.init m.decl.mods.isStatic args) σ
            | none => K (.wrong "abstract or native method")
          | .native lc =>
            match args with
            | .ref a :: rest =>
              match σ.heap a with
              | some (.plain c' fs) =>
                c' = c →
                match Native.plainInst P sig lc a c fs rest σ with
                | some r => wpR (callWP P Γ d) r (fun ev => K ev.toOutcome)
                | none => K (.wrong "no model for library method")
              | _ => True
            | _ => True
          | .none why => P.concrete c = true → K (.wrong why) := by
  rw [callWP.eq_def]; rfl

/-- One unfolding of `bodyWP` (definitionally equal to `bodyWP … (n+1) …`). -/
def bodyWPStep (P : Program) (H : Handler) (b : Body) (I : Cuts) (Post : Outcome → Prop)
    (n pc : Nat) (fr : Frame) (σ : State) : Prop :=
  wpR H (step P b pc fr σ) fun r =>
    match afterStep P b pc fr r with
    | .done o => Post o
    | .cont pc' fr' σ' =>
      match I.lookup pc' with
      | some A => A fr' σ'
      | none => bodyWP P H b I Post n pc' fr' σ'

attribute [jsimp] bodyWPStep

/-- One unfolding of `bodyWP` at a successor fuel (proved once, by unfolding). -/
theorem bodyWP_eq_step (P : Program) (H : Handler) (b : Body) (I : Cuts) (Post : Outcome → Prop)
    (n pc : Nat) (fr : Frame) (σ : State) :
    bodyWP P H b I Post (n + 1) pc fr σ = bodyWPStep P H b I Post n pc fr σ := rfl

theorem bodyWP_eq_false (P : Program) (H : Handler) (b : Body) (I : Cuts) (Post : Outcome → Prop)
    (pc : Nat) (fr : Frame) (σ : State) : bodyWP P H b I Post 0 pc fr σ = False := rfl

open Lean Meta in
/-- `jbodyWP`: one statement of `bodyWP` at a literal program counter and fuel. The step is
    justified by `bodyWP_eq_step` at the literal fuel, not by unfolding: the kernel would
    otherwise evaluate the structural recursion of `bodyWP` from the fuel down (seen as minutes
    and "(kernel) deep recursion" at fuel 400). Literal program counter and fuel only, so that
    symbolic execution proceeds statement by statement along each path. -/
def jbodyWPCore (e : Lean.Expr) : Simp.SimpM Simp.Step := do
  -- never execute under binders (e.g. a cut point's `∀ fr σ, A fr σ → …` before `intro`)
  if e.hasLooseBVars then return .continue
  let_expr bodyWP P H b I Post n pc fr σ := e | return .continue
  -- (an inlined callee runs with `inlineFuel`)
  let natOf (x : Lean.Expr) : Option Nat :=
    x.nat? <|> x.rawNatLit? <|> (if x.isConstOf ``inlineFuel then some inlineFuel else none)
  let some _ := natOf pc | return .continue
  let some nv := natOf n | return .continue
  if nv = 0 then
    return .done { expr := mkConst ``False,
                   proof? := some (mkAppN (mkConst ``bodyWP_eq_false) #[P, H, b, I, Post, pc, fr, σ]) }
  let m := mkNatLit (nv - 1)
  return .visit { expr := mkAppN (mkConst ``bodyWPStep) #[P, H, b, I, Post, m, pc, fr, σ],
                  proof? := some (mkAppN (mkConst ``bodyWP_eq_step) #[P, H, b, I, Post, m, pc, fr, σ]) }

simproc jbodyWP (bodyWP _ _ _ _ _ _ _ _ _) := fun e => jProfile "jbodyWP" (jbodyWPCore e)

/-- `S.pre args σ` / `S.post args σ o` of a contract constant `S` (`def S : Spec := Spec.of …`):
    the condition itself. Contracts are not unfolded anywhere else, so the callee environment
    of a goal (`callWP P (Contracts.env [(sig, S), …]) …`) stays small. -/
def jspecCore (e : Lean.Expr) : Lean.Meta.Simp.SimpM Lean.Meta.Simp.DStep := do
  let fn := e.getAppFn
  -- `Spec.pre S args σ`, or the primitive projection `S.1 args σ`
  let (isPre, S, rest) ← match fn with
    | .const c _ =>
      if c == ``Spec.pre || c == ``Spec.post then
        let args := e.getAppArgs
        let some S := args[0]? | return .continue
        pure (c == ``Spec.pre, S, args.extract 1 args.size)
      else return .continue
    | .proj ``Spec i S => pure (i == 0, S, e.getAppArgs)
    | _ => return .continue
  unless S.getAppFn.isConst do return .continue
  let mut S' := S
  -- unfold the contract constant and `Spec.of` down to `Spec.mk pre post`
  for _ in [0:3] do
    if S'.isAppOfArity ``Spec.mk 2 then break
    -- (simp runs with `instances` transparency, which unfolds no ordinary definition)
    match ← Lean.Meta.withTransparency .default (Lean.Meta.unfoldDefinition? S') with
    | some s => S' := s.headBeta
    | none => return .continue
  unless S'.isAppOfArity ``Spec.mk 2 do return .continue
  let field := if isPre then S'.appFn!.appArg! else S'.appArg!
  return .visit (field.beta rest)

/-- (Keyed on every term: a pattern `Spec.pre _ _ _` is indexed through the projection and
    never matched.) -/
dsimproc jspec (_) := fun e => jspecCore e
dsimproc jspecPost (_) := fun _ => return .continue

/-! ## The symbolic execution tactic -/

open Lean Meta Elab Tactic

/-- `0 ≤ t` facts from integer bound hypotheses (`a ≤ b`, `a < b`, `a ≥ b`, `a > b`). -/
def intBoundFacts (g : MVarId) : MetaM (Array (Lean.Expr × Lean.Expr)) := g.withContext do
  let mut out := #[]
  let intTy := mkConst ``Int
  for h in (← getLCtx) do
    if h.isImplementationDetail then continue
    let ty ← instantiateMVars h.type
    let ty := ty.consumeMData
    let mk (a b : Lean.Expr) (strict : Bool) : MetaM (Option (Lean.Expr × Lean.Expr)) := do
      unless ← isDefEq (← inferType a) intTy do return none
      if strict then
        let a1 ← mkAppM ``HAdd.hAdd #[a, mkIntLit 1]
        let t ← mkAppM ``HSub.hSub #[b, a1]
        let pf ← mkAppM ``Int.sub_nonneg_of_le #[← mkAppM ``Int.add_one_le_of_lt #[h.toExpr]]
        return some (t, pf)
      else
        let t ← mkAppM ``HSub.hSub #[b, a]
        let pf ← mkAppM ``Int.sub_nonneg_of_le #[h.toExpr]
        return some (t, pf)
    let r ← match_expr ty with
      | LE.le _ _ a b => mk a b false
      | LT.lt _ _ a b => mk a b true
      | GE.ge _ _ a b => mk b a false
      | GT.gt _ _ a b => mk b a true
      | _ => pure none
    if let some f := r then out := out.push f
  return out
where
  mkIntLit (n : Nat) : Lean.Expr := mkApp3 (mkConst ``OfNat.ofNat [0]) (mkConst ``Int) (mkRawNatLit n)
    (mkApp (mkConst ``instOfNat) (mkRawNatLit n))

/-- `jnlin`: add pairwise products of integer bound hypotheses (degree-2 certificates for
    nonlinear arithmetic, as in `nlinarith`). -/
def jnlin : TacticM Unit := do
  let g ← getMainGoal
  let facts ← intBoundFacts g
  let facts := facts.extract 0 10
  let mut g := g
  for i in [0:facts.size] do
    for j in [i:facts.size] do
      let (ti, pi) := facts[i]!
      let (tj, pj) := facts[j]!
      let r ← g.withContext do
        try
          let t ← mkAppM ``HMul.hMul #[ti, tj]
          let pf ← mkAppM ``Int.mul_nonneg #[pi, pj]
          let zero ← mkAppOptM ``OfNat.ofNat #[mkConst ``Int, mkRawNatLit 0, none]
          let ty ← mkAppM ``LE.le #[zero, t]
          pure (some (ty, pf))
        catch _ => pure none
      if let some (ty, pf) := r then
        let (_, g') ← (← g.assert `hnl ty pf).intro1P
        g := g'
  replaceMainGoal [g]

elab "jnlin" : tactic => jnlin

/-- The `Nat` abbreviations of the semantics (`Addr`, `Label`, `LocalIdx`) unfolded and raw
    natural number literals (left by evaluation, e.g. `σ.next + nat_lit 1`) put in `OfNat` form
    in the goal and the hypotheses: `omega` only reads facts at type `Nat` or `Int` and only
    `OfNat` numerals. -/
def jNatAbbrevs : TacticM Unit := do
  let abbrevs := [``Addr, ``Label, ``LocalIdx]
  let repl (e : Lean.Expr) : Lean.Expr := e.replace fun t =>
    if t.isAppOfArity ``OfNat.ofNat 3 then some t else
    match t with
    | .const c [] => if abbrevs.contains c then some (mkConst ``Nat) else none
    | .lit (.natVal n) => some (mkNatLit n)
    | _ => none
  liftMetaTactic fun g => do
    let mut g := g
    let tgt ← instantiateMVars (← g.getType)
    if repl tgt != tgt then g ← g.replaceTargetDefEq (repl tgt)
    for d in (← g.getDecl).lctx do
      if d.isImplementationDetail then continue
      let ty ← instantiateMVars d.type
      if repl ty != ty then g ← g.replaceLocalDeclDefEq d.fvarId (repl ty)
    return [g]

/-- `omega` after unfolding the `Nat` abbreviations (address arithmetic). -/
elab "jomega" : tactic => do
  jNatAbbrevs
  evalTactic (← `(tactic| omega))

/-- A hypothesis `omega` can use: (in)equalities of naturals or integers under `¬`, `∧`, `∨`, `↔`. -/
partial def isArithFact (ty : Lean.Expr) : MetaM Bool := do
  let ty := ty.consumeMData
  let num (α : Lean.Expr) : MetaM Bool := do
    let α ← whnfR α
    return α.isConstOf ``Nat || α.isConstOf ``Int
  match ty.getAppFn with
  | .const ``Not _ => if ty.getAppNumArgs == 1 then isArithFact ty.appArg! else return false
  | .const ``And _ | .const ``Or _ | .const ``Iff _ =>
    if ty.getAppNumArgs == 2 then
      return (← isArithFact ty.appFn!.appArg!) && (← isArithFact ty.appArg!)
    else return false
  | .const ``Eq _ | .const ``Ne _ => if ty.getAppNumArgs == 3 then num (ty.getArg! 0) else return false
  | .const ``LT.lt _ | .const ``LE.le _ | .const ``GT.gt _ | .const ``GE.ge _ =>
    if ty.getAppNumArgs == 4 then num (ty.getArg! 0) else return false
  | .const ``Dvd.dvd _ => if ty.getAppNumArgs == 4 then num (ty.getArg! 0) else return false
  | _ => return false

/-- `jomega` on the arithmetic hypotheses only: the others are cleared first (on large
    symbolic-execution contexts `omega` was seen to run without end). -/
elab "jomega_arith" : tactic => do
  jNatAbbrevs
  liftMetaTactic fun g => g.withContext do
    let mut g := g
    for d in (← getLCtx) do
      if d.isImplementationDetail then continue
      unless ← isProp d.type do continue
      unless ← isArithFact (← instantiateMVars d.type) do
        g ← g.tryClear d.fvarId
    return [g]
  evalTactic (← `(tactic| omega))

/-- `omega` on the arithmetic hypotheses that share variables with the goal (three rounds of
    closure); the other arithmetic hypotheses are cleared first. Simp asks `jdisch` hundreds of
    times per step, and on large symbolic-execution contexts a failing `omega` over every
    arithmetic fact took ~0.3 s. -/
elab "jomega_rel" : tactic => do
  jNatAbbrevs
  liftMetaTactic fun g => g.withContext do
    let tgt ← instantiateMVars (← g.getType)
    let mut vars : Std.HashSet FVarId := {}
    for f in (collectFVars {} tgt).fvarIds do vars := vars.insert f
    let lctx ← getLCtx
    let mut cands : Array (FVarId × Array FVarId) := #[]
    for d in lctx do
      if d.isImplementationDetail then continue
      unless ← isProp d.type do continue
      let ty ← instantiateMVars d.type
      if ← isArithFact ty then cands := cands.push (d.fvarId, (collectFVars {} ty).fvarIds)
    let mut keep : Std.HashSet FVarId := {}
    for _ in [0:3] do
      for (h, fs) in cands do
        if keep.contains h then continue
        if fs.any (vars.contains ·) then
          keep := keep.insert h
          for f in fs do vars := vars.insert f
    -- the goal in the sub-context of the variables it needs and the kept facts (building it
    -- is cheaper than clearing the other facts one by one)
    let mut need : Std.HashSet FVarId := vars
    for h in keep do need := need.insert h
    for _ in [0:4] do
      for d in lctx do
        if need.contains d.fvarId then
          for f in (collectFVars {} (← instantiateMVars d.type)).fvarIds do need := need.insert f
    let lctx' := lctx.foldl (init := lctx) fun acc d =>
      if need.contains d.fvarId then acc else acc.erase d.fvarId
    let g' ← mkFreshExprMVarAt lctx' (← getLocalInstances) tgt
    g.assign g'
    return [g'.mvarId!]
  evalTactic (← `(tactic| omega))

/-- Discharger for overflow side conditions: linear, then nonlinear. -/
macro "jbound" : tactic => `(tactic| first | jomega | (jnlin; grind))

/-- `decide`, only on goals without free variables (closed propositions). -/
elab "jdecide" : tactic => do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  if t.hasFVar || t.hasMVar then throwError "jdecide: goal is not closed"
  evalTactic (← `(tactic| decide))

/-- Leaf solver for arithmetic and logic side conditions: removes provably overflow-free
    wraparound (`bmod`), then tries `omega`, `grind`, `bv_decide`, nonlinear products.
    Each attempt is bounded. -/
macro "jauto" : tactic => `(tactic| first
  | with_reducible rfl
  | (set_option maxHeartbeats 200000 in
      (simp_all [-BitVec.toInt_xor, -BitVec.toInt_and, -BitVec.toInt_or]; done))
  | (set_option maxHeartbeats 200000 in
      (simp (disch := jomega) only [bmod32_of_bounds, bmod64_of_bounds] at *; first | jomega | grind))
  | (set_option maxHeartbeats 200000 in jomega)
  | jdecide
  | (set_option maxHeartbeats 400000 in grind)
  | (set_option maxHeartbeats 400000 in
      (simp (disch := jbound) only [bmod32_of_bounds, bmod64_of_bounds] at *;
       first | jomega | grind | (jnlin; grind)))
  | bv_decide)

partial def jDestructAux (inert : Std.HashSet FVarId) : TacticM Unit := do
  if (← getGoals).isEmpty then return
  let g ← getMainGoal
  let (found, inert) ← g.withContext do
    let mut inert := inert
    for h in (← getLCtx) do
      if h.isImplementationDetail || inert.contains h.fvarId then continue
      let ty := (← instantiateMVars h.type).consumeMData
      if ty.isAppOfArity ``Exists 2 || ty.isAppOfArity ``And 2 then return (some h.fvarId, inert)
      -- see through definitions of contracts (`S.pre args σ`), never through equations
      match ty.getAppFn with
      | .const c _ =>
        if [``Eq, ``Ne, ``Not, ``LE.le, ``LT.lt, ``GE.ge, ``GT.gt, ``HEq, ``Iff, ``True, ``False].contains c then
          continue
      | .proj .. => pure ()
      | _ => continue
      let now ← IO.getNumHeartbeats
      let t0 ← IO.monoMsNow
      let ty' ← tryCatchRuntimeEx
        (withTheReader Core.Context (fun ctx => { ctx with maxHeartbeats := 20000000, initHeartbeats := now })
          (whnfD ty))
        (fun _ => pure ty)
      if jimple.trace.get (← getOptions) then
        let dt := (← IO.monoMsNow) - t0
        if dt > 300 then logInfo m!"jvc: unfolding hypothesis {h.userName} took {dt} ms: {ty}"
      if ty'.isAppOfArity ``Exists 2 || ty'.isAppOfArity ``And 2 || ty'.isConstOf ``False then
        return (some h.fvarId, inert)
      -- not destructurable: never unfold it again in this run (other hypotheses keep their
      -- free variables when one is destructured)
      inert := inert.insert h.fvarId
    return (none, inert)
  match found with
  | none => return
  | some fv =>
    let rest ← getGoals
    let newGoals ← destructHyp g fv
    setGoals (newGoals ++ rest.drop 1)
    jDestructAux inert
where
  /-- Destructure `fv : ∃ x, p x`, `A ∧ B` or `False` by assigning the goal directly (`cases`
      reverts and re-checks the goal, which is large during symbolic execution). -/
  destructHyp (g : MVarId) (fv : FVarId) : TacticM (List MVarId) := g.withContext do
    let ty ← whnfD (← instantiateMVars (← fv.getType))
    let tgt ← instantiateMVars (← g.getType)
    if ty.isConstOf ``False then
      g.assign (mkApp2 (mkConst ``False.elim [← getLevel tgt]) tgt (.fvar fv))
      return []
    else if ty.isAppOfArity ``And 2 then
      let a := ty.appFn!.appArg!
      let b := ty.appArg!
      let (_, g1) ← (← g.assert `left a (mkApp3 (mkConst ``And.left) a b (.fvar fv))).intro1P
      let (_, g2) ← (← g1.assert `right b (mkApp3 (mkConst ``And.right) a b (.fvar fv))).intro1P
      return [← g2.tryClear fv]
    else if ty.isAppOfArity ``Exists 2 then
      let α := ty.appFn!.appArg!
      let p := ty.appArg!
      let u ← getLevel α
      -- the goal after the witness and its property are introduced
      let newTy := mkForall `w .default α (mkForall `h .default (mkApp p (.bvar 0)) tgt)
      let newG ← mkFreshExprSyntheticOpaqueMVar newTy (← g.getTag)
      g.assign (mkAppN (mkConst ``Exists.elim [u]) #[α, p, tgt, .fvar fv, newG])
      let (_, g') ← newG.mvarId!.introNP 2
      return [← g'.tryClear fv]
    else
      let subgoals ← g.cases fv
      return (subgoals.map (·.mvarId)).toList

/-- Destructure hypotheses of the main goal: existentials and conjunctions; a hypothesis that
    unfolds to `False` closes the goal. -/
def jDestruct : TacticM Unit := jDestructAux {}

/-- `a ≠ b` (or `¬ a = b`) for two objects the heap tells apart: hypotheses
    `σ.heap a = some o₁` and `σ.heap b = some o₂` about the same state with `o₁`, `o₂` of
    different kinds or classes.  (A read through `σ.setObj a o` asks `b = a`; without this the
    symbolic execution splits on it.) -/
elab "jne_heap" : tactic => do
  unless jimple.modelContracts.get (← getOptions) do throwError "jne_heap: off"
  let g ← getMainGoal
  let pairs ← g.withContext do
    let tgt ← whnfR (← instantiateMVars (← g.getType))
    let some (a, b) := (match tgt with
      | .app (.const ``Not _) e => (e.eq?).map (fun (_, x, y) => (x, y))
      | _ => none) | throwError "jne_heap: not a disequality"
    let lctx ← getLCtx
    let mut facts : Array (Lean.Expr × Lean.Expr × Lean.Expr) := #[]
    for d in lctx do
      if d.isImplementationDetail then continue
      let ty := (← instantiateMVars d.type).consumeMData
      if let some (_, l, r) := ty.eq? then
        if l.isAppOfArity ``State.heap 2 && r.isAppOfArity ``Option.some 2 then
          facts := facts.push (d.toExpr, l.getArg! 0, l.getArg! 1)
    let mut out : Array (Lean.Expr × Lean.Expr) := #[]
    for (h1, s1, x1) in facts do
      unless x1 == a do continue
      for (h2, s2, x2) in facts do
        unless x2 == b && s2 == s1 do continue
        out := out.push (h1, h2)
    return out
  for (h1, h2) in pairs do
    let s ← saveState
    try
      let ok ← g.withContext do
        let ty1 ← instantiateMVars (← inferType h1)
        let ty2 ← instantiateMVars (← inferType h2)
        let some (_, l1, r1) := ty1.consumeMData.eq? | return false
        let some (_, _, r2) := ty2.consumeMData.eq? | return false
        -- `some o₁ ≠ some o₂` by simp (constructors or class names differ)
        let hne ← mkFreshExprSyntheticOpaqueMVar (← mkAppM ``Ne #[r1, r2])
        let rest ← Term.TermElabM.run' <| Tactic.run hne.mvarId! (evalTactic (← `(tactic| simp)))
        unless rest.isEmpty do return false
        let σ := l1.getArg! 0
        let tgt ← whnfR (← instantiateMVars (← g.getType))
        let .app (.const ``Not _) eqab := tgt | return false
        let pf ← withLocalDeclD `h eqab fun h => do
          let heap ← mkAppM ``State.heap #[σ]
          let c ← mkCongrArg heap h
          let e ← mkEqTrans (← mkEqSymm h1) (← mkEqTrans c h2)
          mkLambdaFVars #[h] (mkApp hne e)
        -- (a discharger runs at a deeper metavariable context: the proof must be closed here)
        let pf ← instantiateMVars pf
        if pf.hasMVar then return false
        g.assign pf
        return true
      if ok then
        replaceMainGoal []
        return
      s.restore
    catch _ => s.restore
  throwError "jne_heap: no heap facts tell the objects apart"

/-- Side-condition discharger for conditional rewrites during symbolic execution. -/
macro "jdisch0" : tactic => `(tactic| first
  | assumption
  | decide
  | jomega_rel
  | (simp only [State.next_alloc, State.next_setObj]; jomega_rel)
  | (apply isSome_of_eq_some; assumption)
  | jne_heap
  | (simp only [List.length_cons, List.length_nil, List.length_map, List.length_take,
      List.length_append, List.length_set, List.length_eraseIdx]; jomega))

open Lean Meta in
/-- A side condition that `jdisch` cannot prove: a matcher equation's "the discriminant is not
    this constructor" premise `∀ xs, d = C xs → False` (or a `Nonempty` of a proposition) where
    the discriminant `d` is not a constructor application. simp tries such equations on every
    stuck `match`; failing them at once saves the discharger's `decide`/`omega` runs. -/
def hopelessSideGoal (ty : Lean.Expr) : MetaM Bool := do
  if ty.consumeMData.isAppOfArity ``Nonempty 1 then
    return !(← getLCtx).any fun d => !d.isImplementationDetail && d.type == ty.consumeMData.appArg!
  unless ty.consumeMData.isForall do return false
  forallTelescopeReducing ty fun xs body => do
    unless body.consumeMData.isConstOf ``False do return false
    let some h := xs.back? | return false
    let hty ← instantiateMVars (← inferType h)
    let some (_, lhs, _) := hty.consumeMData.eq? | return false
    if lhs.hasAnyFVar (fun f => xs.any (·.fvarId! == f)) then return false
    let lhs ← whnfR lhs
    match lhs.getAppFn with
    | .const c _ => return !(← getEnv).isConstructor c
    | .lit _ => return false
    | _ => return true

/-- Side conditions `jdisch` failed on during the current `jsym` call (the context is the same
    throughout one simp call; simp asks again for each occurrence). -/
initialize jdischFailed : IO.Ref (Std.HashSet Lean.Expr) ← IO.mkRef {}

/-- The local variables of the goal at the start of the current `jsym` call: a side condition
    about a variable simp introduced under a binder (`∀ x, x < σ0.next → …`) has no hypotheses
    about it (simp is not contextual), so `jdisch` fails on it at once instead of running omega. -/
initialize jsymCtx : IO.Ref (Std.HashSet FVarId) ← IO.mkRef {}

/-- `jdisch0`, timed under `jimple.trace` (`jProf`: successes and failures). -/
elab "jdisch" : tactic => do
  let ty ← instantiateMVars (← getMainTarget)
  if (← jdischFailed.get).contains ty then throwError "jdisch: failed before"
  if jimple.dischFailFast.get (← getOptions) then
    let ctx ← jsymCtx.get
    if !ctx.isEmpty && ty.hasAnyFVar (fun f => !ctx.contains f) then
      throwError "jdisch: a variable bound in the goal"
  if ← hopelessSideGoal ty then
    throwError "jdisch: discriminant not a constructor"
  if !(jimple.trace.get (← getOptions)) then
    try evalTactic (← `(tactic| jdisch0))
    catch e =>
      jdischFailed.modify (·.insert ty)
      throw e
    return
  let t0 ← IO.monoNanosNow
  let ok ← try evalTactic (← `(tactic| jdisch0)); pure true catch _ => pure false
  let t1 ← IO.monoNanosNow
  let key := if ok then "jdisch ok" else "jdisch fail"
  jProf.modify fun m => let (c, t) := m.getD key (0, 0); m.insert key (c + 1, t + (t1 - t0))
  unless ok do
    jdischFailed.modify (·.insert ty)
    if jimple.debug.get (← getOptions) then
      let k := s!"  fail: {(toString (← ppExpr ty)).take 100}"
      jProf.modify fun m => let (c, t) := m.getD k (0, 0); m.insert k (c + 1, t + (t1 - t0))
    throwError "jdisch failed"

/-- One round of symbolic execution: simplify with the Jimple simp set and the context. -/
def jsym (extra : Array Ident) : TacticM Unit := do
  let extra : Array (TSyntax `Lean.Parser.Tactic.simpLemma) ← extra.mapM fun i => `(Lean.Parser.Tactic.simpLemma| $i:ident)
  -- `maxSteps`: a concrete run (a test method) is evaluated in one simp call
  let tr := jimple.trace.get (← getOptions)
  if tr then jProf.set {}
  jdischFailed.set {}
  let ctxSet ← (← getMainGoal).withContext do
    return (← getLCtx).foldl (init := ({} : Std.HashSet FVarId)) fun s d => s.insert d.fvarId
  jsymCtx.set ctxSet
  let t0 ← IO.monoNanosNow
  -- `BitVec.toInt_xor`/`_and`/`_or` (core simp lemmas) stay out here and in the `simp_all` closers: a branch
  -- condition on the signed value of a bitwise result (`if (a ^ b) >= 0`) rewritten by them gave a proof the
  -- kernel rejects ("deep recursion")
  try
    if jimple.modelContracts.get (← getOptions) then
      evalTactic (← `(tactic| simp (config := { decide := true, failIfUnchanged := false, zetaDelta := true, maxSteps := 20000000 })
        (disch := jdisch)
        [jsimp, jsimpc, jground, jnoshadow, jnative, jconcat, jctor, jeval, jbodyWP, jkont, jspec, jspecPost,
         -BitVec.toInt_xor, -BitVec.toInt_and, -BitVec.toInt_or, *, $extra,*]))
    else
      evalTactic (← `(tactic| simp (config := { decide := true, failIfUnchanged := false, zetaDelta := true, maxSteps := 20000000 })
        (disch := jdisch)
        [jsimp, jground, jnoshadow, jnative, jctor, jeval, jbodyWP, jkont, jspec, jspecPost,
         -BitVec.toInt_xor, -BitVec.toInt_and, -BitVec.toInt_or, *, $extra,*]))
  finally
    jdischFailed.set {}
    jsymCtx.set {}
  if tr then
    let dt := ((← IO.monoNanosNow) - t0) / 1000000
    if dt > 1000 then
      let prof := ((← jProf.get).toList.toArray.qsort (fun a b => a.2.1 > b.2.1)).toList.take 40
        |>.map fun (n, c, t) => s!"{n} {c}× {t / 1000000} ms"
      logInfo m!"jvc: simp step took {dt} ms; simprocs: {prof}"
      if jimple.debug.get (← getOptions) then dbgOut s!"[jsym profile] {dt} ms: {prof}"

/-- What blocks symbolic evaluation: a branch condition, or a match discriminant that is not
    in constructor form. -/
inductive Blocker where
  | cond (p : Lean.Expr)
  | discr (d : Lean.Expr)

/-- Head-first search for the blocker of evaluation: in `wpR H r K` only `r` is active; in a
    `match`, only its discriminants; `if`/`decide` conditions block when closed. -/
partial def findBlocker (env : Environment) (enums : Array FVarId) (e : Lean.Expr) : Option Blocker :=
  if e.hasLooseBVars then none else
  match e.getAppFn with
  | .const ``wpR _ =>
    let args := e.getAppArgs
    if h : 2 < args.size then findBlocker env enums args[2] else none
  | .const ``Decidable.decide _ =>
    let args := e.getAppArgs
    if h : 0 < args.size then
      (findBlocker env enums args[0]).orElse fun _ => some (.cond args[0])
    else none
  | .const ``ite _ | .const ``dite _ =>
    let args := e.getAppArgs
    if h : 1 < args.size then
      (findBlocker env enums args[1]).orElse fun _ => some (.cond args[1])
    else none
  | .const c _ =>
    match getMatcherInfoCore? env c with
    | some info =>
      let args := e.getAppArgs
      let discrs := (args.extract (info.numParams + 1) (info.numParams + 1 + info.numDiscrs)).toList
      discrs.findSome? fun d =>
        if d.hasLooseBVars then none
        else (findBlocker env enums d).orElse fun _ => stuckIn d
    | none => e.getAppArgs.toList.findSome? (findBlocker env enums)
  | _ =>
    match e with
    | .app f a => (findBlocker env enums f).orElse fun _ => findBlocker env enums a
    | .mdata _ b => findBlocker env enums b
    | _ => none
where
  /-- The part of a discriminant that blocks the match: the discriminant itself, or, for a
      constructor application (`some (decide p)` from a nondeterministic choice), the first
      argument that is not in constructor form. -/
  stuckIn (d : Lean.Expr) : Option Blocker :=
    match d.getAppFn with
    | .const dc _ =>
      if env.isConstructor dc then
        d.getAppArgs.toList.findSome? fun a =>
          if a.hasLooseBVars || a.isSort || a.isType then none
          else match a.getAppFn with
            | .const ac _ => if env.isConstructor ac then stuckIn a else
                -- type arguments of the constructor are constants applied to nothing
                if a.isConst then none else some (blockerIn a)
            | .lit _ => none
            | .sort _ => none
            | _ => some (blockerIn a)
      else some (blockerIn d)
    | .lit _ => none
    | _ => some (blockerIn d)
  /-- prefer splitting an enumeration-typed variable that occurs in the discriminant -/
  blockerIn (d : Lean.Expr) : Blocker :=
    match d.find? (fun t => t.isFVar && enums.contains t.fvarId!) with
    | some x => .discr x
    | none =>
      -- a default taken from an optional value: split the optional value itself
      if d.isAppOfArity ``Option.getD 3 then .discr d.appFn!.appArg! else .discr d

/-- Branch conditions anywhere in a (non-symbolic) goal: `decide p`, `if p`, closed `p`. -/
partial def findCond (e : Lean.Expr) : Option Lean.Expr :=
  if e.hasLooseBVars then descend e
  else
    match e.getAppFn with
    | .const ``Decidable.decide _ =>
      let args := e.getAppArgs
      if h : 0 < args.size then
        let p := args[0]
        if p.hasLooseBVars || p.hasMVar then descend e else some p
      else descend e
    | .const ``ite _ | .const ``dite _ =>
      let args := e.getAppArgs
      if h : 1 < args.size then
        let p := args[1]
        if p.hasLooseBVars || p.hasMVar then descend e
        else (findCond p).orElse fun _ => some p
      else descend e
    | _ => descend e
where
  descend (e : Lean.Expr) : Option Lean.Expr :=
    match e with
    | .app f a => (findCond f).orElse fun _ => findCond a
    | .lam _ t b _ => (findCond t).orElse fun _ => findCond b
    | .forallE _ t b _ => (findCond t).orElse fun _ => findCond b
    | .letE _ t v b _ => (findCond t).orElse fun _ => (findCond v).orElse fun _ => findCond b
    | .mdata _ b => findCond b
    | .proj _ _ b => findCond b
    | _ => none

/-- Case split by `pf : a ∨ b`: two goals with `a`, resp. `b`, introduced. -/
def orElimGoals (g : MVarId) (a b pf : Lean.Expr) (name : Name := `hcase) : MetaM (MVarId × MVarId) :=
  g.withContext do
    let tgt ← g.getType
    let m1 ← mkFreshExprSyntheticOpaqueMVar (← mkArrow a tgt)
    let m2 ← mkFreshExprSyntheticOpaqueMVar (← mkArrow b tgt)
    g.assign (mkApp6 (mkConst ``Or.elim) a b tgt pf m1 m2)
    let (_, g1) ← m1.mvarId!.intro name
    let (_, g2) ← m2.mvarId!.intro name
    return (g1, g2)

/-- A `tableswitch` on a symbolic key leaves the next statement index as `l[i]?.getD d`
    (`l` the targets, `i` the key minus the low bound): split into `i = 0`, …, `i = n - 1` and
    `n ≤ i`, after which the index evaluates. -/
def splitSwitchIndex (g : MVarId) : TacticM (Option (List MVarId)) := do
  let r ← g.withContext do
    let tgt ← instantiateMVars (← g.getType)
    let found := tgt.find? fun t =>
      t.isAppOfArity ``Option.getD 3 && (t.getArg! 1).isAppOfArity ``GetElem?.getElem? 7 &&
      (let ge := t.getArg! 1
       let xs := ge.getArg! 5
       let i := ge.getArg! 6
       !xs.hasFVar && !xs.hasLooseBVars && !i.hasLooseBVars && i.nat?.isNone && i.rawNatLit?.isNone)
    match found with
    | none => return none
    | some t =>
      let ge := t.getArg! 1
      let xs ← whnfD (ge.getArg! 5)
      let i := ge.getArg! 6
      -- the length of the literal list
      let rec len (e : Lean.Expr) (fuel : Nat) : Option Nat :=
        match fuel with
        | 0 => none
        | f + 1 => if e.isAppOfArity ``List.nil 1 then some 0
          else if e.isAppOfArity ``List.cons 3 then (len e.appArg! f).map (· + 1) else none
      unless (← inferType i).isConstOf ``Nat do return none
      return (len (← instantiateMVars xs) 1000).map (i, ·)
  let some (i, n) := r | return none
  if n == 0 || n > 64 then return none
  let nE := mkNatLit n
  let (gLt, gGe) ← orElimGoals g (← mkLt i nE) (← mkLe nE i)
    (mkApp2 (mkConst ``Nat.lt_or_ge) i nE)
  -- `i < n` gives `i = 0 ∨ … ∨ i = n - 1` (by `omega`), split into one goal per value
  let eqs ← (List.range n).mapM fun k => gLt.withContext do mkEq i (mkNatLit k)
  let disj := eqs.dropLast.foldr (fun a acc => mkApp2 (mkConst ``Or) a acc) eqs.getLast!
  let pD ← gLt.withContext do mkFreshExprSyntheticOpaqueMVar disj
  let saved ← getGoals
  setGoals [pD.mvarId!]
  evalTactic (← `(tactic| omega))
  setGoals saved
  let mut goals : List MVarId := []
  let mut cur := gLt
  let mut pf := pD
  let mut rest := eqs
  while rest.length > 1 do
    let a := rest.head!
    let b := rest.tail!.dropLast.foldr (fun x acc => mkApp2 (mkConst ``Or) x acc) rest.getLast!
    let (g1, g2) ← orElimGoals cur a b pf
    goals := goals ++ [g1]
    -- the remaining disjunction is the hypothesis just introduced in `g2`
    let h ← g2.withContext do return (← getLCtx).lastDecl.get!.toExpr
    cur := g2
    pf := h
    rest := rest.tail!
  goals := goals ++ [cur, gGe]
  return some goals

/-- Case split on what blocks evaluation of the goal (or on a branch condition of a leaf). -/
def splitBlocker (g : MVarId) (symbolic : Bool) : TacticM (Option (List MVarId)) := do
  let tgt ← instantiateMVars (← g.getType)
  let env ← getEnv
  -- variables of enumeration types (few nullary constructors) in the context
  let enums ← g.withContext do
    let mut out := #[]
    for h in (← getLCtx) do
      if h.isImplementationDetail then continue
      let ty ← whnfR (← instantiateMVars h.type)
      if let .const tn _ := ty.getAppFn then
        if let some (.inductInfo iv) := env.find? tn then
          if iv.ctors.length ≤ 8 && iv.numIndices == 0 then
            let nullary ← iv.ctors.allM fun c => do
              match env.find? c with
              | some (.ctorInfo ci) => return ci.numFields == 0
              | _ => return false
            if nullary then out := out.push h.fvarId
    return out
  let b := if symbolic then findBlocker env enums tgt else (findCond tgt).map Blocker.cond
  let s ← saveState
  match b with
  | none => return none
  | some (.cond p) =>
    try
      let (g1, g2) ← g.byCases p `hcond
      return some [g1.mvarId, g2.mvarId]
    catch _ => s.restore; return none
  | some (.discr d) =>
    try
      let (fvs, g') ← g.generalize #[{ expr := d, xName? := some `x, hName? := some `hd }]
      let subgoals ← g'.cases fvs[0]!
      return some (subgoals.map (·.mvarId)).toList
    catch _ => s.restore; return none

/-- Freshness facts: for every hypothesis `σ.heap a = some o`, add `a < σ.next` and
    `a ≠ σ.next` (allocated addresses are below the allocation pointer). -/
def jFresh : TacticM Unit := do
  let g ← getMainGoal
  let mut g := g
  let hyps ← g.withContext do
    let mut out := #[]
    for h in (← getLCtx) do
      if h.isImplementationDetail then continue
      let ty ← instantiateMVars h.type
      match_expr ty with
      | Eq _ lhs rhs =>
        if lhs.isAppOfArity ``State.heap 2 && rhs.isAppOfArity ``Option.some 2 then
          out := out.push h.toExpr
      | _ => pure ()
    return out
  for h in hyps do
    let r ← g.withContext do
      try
        let p1 ← mkAppM ``State.lt_next_of_heap #[h]
        let p2 ← mkAppM ``State.ne_next_of_heap #[h]
        pure (some (p1, ← inferType p1, p2, ← inferType p2))
      catch _ => pure none
    if let some (p1, t1, p2, t2) := r then
      let exists1 ← g.withContext do
        return (← getLCtx).any fun d => d.type == t1
      unless exists1 do
        let (_, g1) ← (← g.assert `hfresh t1 p1).intro1P
        let (_, g2) ← (← g1.assert `hfresh t2 p2).intro1P
        g := g2
  replaceMainGoal [g]

/-- Constants that mark a goal as still under symbolic execution (not an arithmetic leaf). -/
def symbolicHeads : List Name := [``wpR, ``bodyWP, ``bodyWPStep, ``step, ``stepStmt, ``callWP,
  ``afterStep, ``Res.bind, ``Res.call, ``Res.choose, ``evalInvoke, ``evalExpr,
  ``Native.instCall, ``Native.staticCall, ``Native.ctorCall, ``Native.plainInst]

def isSymbolicGoal (g : MVarId) : MetaM Bool := do
  let t ← instantiateMVars (← g.getType)
  return (t.find? fun e => match e.getAppFn with
    | .const c _ => symbolicHeads.contains c
    | _ => false).isSome

/-- `l[i]` with its bound proof replaced by a placeholder (to compare facts modulo proofs). -/
partial def eraseElemProofs (e : Lean.Expr) : Lean.Expr :=
  match e with
  | .app f a =>
    let e' := Lean.Expr.app (eraseElemProofs f) (eraseElemProofs a)
    if e'.isAppOfArity ``GetElem.getElem 8 then
      mkAppN e'.getAppFn (e'.getAppArgs.set! 7 (mkConst ``True))
    else e'
  | .lam n t b bi => .lam n (eraseElemProofs t) (eraseElemProofs b) bi
  | .forallE n t b bi => .forallE n (eraseElemProofs t) (eraseElemProofs b) bi
  | .mdata d b => .mdata d (eraseElemProofs b)
  | _ => e

/-- Quantifier instantiation for collections: for every hypothesis `h : ∀ x ∈ l, P x` and
    every element access `l[i]` occurring in the goal or the context, add `P l[i]`. -/
def jInstMem : TacticM Unit := do
  let g ← getMainGoal
  let mut g := g
  let (hyps, accesses) ← g.withContext do
    let mut hyps : Array (Lean.Expr × Lean.Expr) := #[]   -- (h, l)
    let mut acc : Array Lean.Expr := #[]
    let collect (e : Lean.Expr) (acc : Array Lean.Expr) : Array Lean.Expr :=
      let rec go (t : Lean.Expr) (acc : Array Lean.Expr) : Array Lean.Expr :=
        let acc := if t.isAppOfArity ``GetElem.getElem 8 && !t.hasLooseBVars then acc.push t else acc
        match t with
        | .app f a => go a (go f acc)
        | .lam _ ty b _ | .forallE _ ty b _ => go b (go ty acc)
        | .letE _ ty v b _ => go b (go v (go ty acc))
        | .mdata _ b | .proj _ _ b => go b acc
        | _ => acc
      go e acc
    acc := collect (← instantiateMVars (← g.getType)) acc
    for h in (← getLCtx) do
      if h.isImplementationDetail then continue
      let ty ← instantiateMVars h.type
      acc := collect ty acc
      -- ∀ x, x ∈ l → P x
      if let .forallE _ _ (.forallE _ mem _ _) _ := ty then
        if mem.isAppOfArity ``Membership.mem 5 then
          let l := mem.getAppArgs[3]!
          if !l.hasLooseBVars then hyps := hyps.push (h.toExpr, l)
    return (hyps, acc)
  -- one access per (collection, index), ignoring the bound proof
  let accesses := accesses.foldl (init := #[]) fun acc t =>
    let a := t.getAppArgs
    if acc.any (fun u => let b := u.getAppArgs; b[5]! == a[5]! && b[6]! == a[6]!) then acc else acc.push t
  for (h, l) in hyps do
    for t in accesses do
      let args := t.getAppArgs
      let coll := args[5]!
      let idx := args[6]!
      let pf := args[7]!
      let r ← g.withContext do
        try
          unless ← isDefEq coll l do return none
          let mem ← mkAppOptM ``List.getElem_mem #[none, coll, idx, pf]
          let fact ← mkAppM' h #[t, mem]
          let ty ← instantiateMVars (← inferType fact)
          let tyE := eraseElemProofs ty
          if (← getLCtx).any (fun d => eraseElemProofs d.type == tyE) then
            return none
          return some (fact, ty)
        catch _ => return none
      if let some (fact, ty) := r then
        let (_, g') ← (← g.assert `hmem ty fact).intro1P
        g := g'
  replaceMainGoal [g]

/-- Heap facts of a later state carried back through a frame rule: from `h : σ'.heap a = some o`
    and a frame hypothesis `hf : ∀ y, y < N → σ'.heap y = σ.heap y` (an `Agree`/`Grows` of a
    callee, unfolded) with `a < N` among the hypotheses, add `σ.heap a = some o`, which
    `jUnifyFacts` compares with the earlier state's facts.  (A case split on `σ'.heap a`, e.g. a
    dispatch on a receiver read right after a call, leaves such a fact about an unknown object.) -/
def jFrameInst : TacticM Unit := do
  let g ← getMainGoal
  let mut g := g
  let found ← g.withContext do
    let lctx ← getLCtx
    let mut facts : Array (Lean.Expr × Lean.Expr × Lean.Expr) := #[]   -- (h, σ', a)
    let mut rules : Array Lean.Expr := #[]
    for d in lctx do
      if d.isImplementationDetail then continue
      let ty := (← instantiateMVars d.type).consumeMData
      if let some (_, lhs, rhs) := ty.eq? then
        if lhs.isAppOfArity ``State.heap 2 && rhs.isAppOfArity ``Option.some 2 then
          facts := facts.push (d.toExpr, lhs.getArg! 0, lhs.getArg! 1)
      else if ty.isForall then
        -- ∀ y, y < N → σ'.heap y = σ.heap y
        if let .forallE _ _ (.forallE _ _ body _) _ := ty then
          if let some (_, l, r) := body.eq? then
            if l.isAppOfArity ``State.heap 2 && r.isAppOfArity ``State.heap 2 then
              rules := rules.push d.toExpr
    let mut out : Array (Lean.Expr × Lean.Expr) := #[]
    for (h, σ', a) in facts do
      for hf in rules do
        let s ← saveState
        try
          let hfTy ← inferType hf
          let (ms, _, body) ← forallMetaTelescopeReducing hfTy (some 2)
          let some (_, l, r) := body.eq? | s.restore; continue
          unless ← isDefEq (l.getArg! 0) σ' do s.restore; continue
          unless ← isDefEq ms[0]! a do s.restore; continue
          -- the premise `a < N` by assumption
          let pty ← instantiateMVars (← inferType ms[1]!)
          let mut ok := false
          for d in (← getLCtx) do
            if d.isImplementationDetail then continue
            if ← isDefEq pty d.type then
              ms[1]!.mvarId!.assign d.toExpr; ok := true; break
          unless ok do s.restore; continue
          let r' ← instantiateMVars r
          if r'.hasMVar then s.restore; continue
          let e ← mkEqTrans (← mkEqSymm (mkAppN hf ms)) h
          let ety ← instantiateMVars (← inferType e)
          if lctx.any (fun d => d.type == ety) then s.restore; continue
          out := out.push (← instantiateMVars e, ety)
          s.restore
        catch _ => s.restore
    return out
  for (pf, ty) in found do
    let (_, g') ← (← g.assert `hframeInst ty pf).intro1P
    g := g'
  replaceMainGoal [g]

/-- Unify facts about the same location: from `h₁ : σ.heap a = some o₁` and
    `h₂ : σ.heap a = some o₂` (also for `Fields.get`, `σ.static`, `fr.get`) derive `o₁ = o₂`
    and split it into equations between constructor fields (then substituted). -/
def jUnifyFacts : TacticM Unit := do
  let g ← getMainGoal
  let pairs ← g.withContext do
    let mut seen : Array (Lean.Expr × Lean.Expr) := #[]   -- (lhs, hyp)
    let mut out : Array (Lean.Expr × Lean.Expr) := #[]
    for h in (← getLCtx) do
      if h.isImplementationDetail then continue
      let ty ← instantiateMVars h.type
      match_expr ty with
      | Eq _ lhs rhs =>
        -- facts `t = C …` about the same non-variable term `t`
        if !lhs.isFVar && (rhs.getAppFn.isConst) then
          for (l', h') in seen do
            if l' == lhs then out := out.push (h', h.toExpr)
          seen := seen.push (lhs, h.toExpr)
      | _ => pure ()
    return out
  let mut g := g
  for (h1, h2) in pairs do
    let r ← g.withContext do
      try
        let e ← mkEqTrans (← mkEqSymm h1) h2
        -- strip `some` on both sides when present
        let inj ← (do
          let ety ← instantiateMVars (← inferType e)
          match_expr ety with
          | Eq _ a b =>
            if a.isAppOfArity ``Option.some 2 && b.isAppOfArity ``Option.some 2 then
              mkAppM ``Option.some.inj #[e]
            else pure e
          | _ => pure e)
        let ty ← instantiateMVars (← inferType inj)
        -- skip trivial `o = o`
        match_expr ty with
        | Eq _ a b => if a == b then return none else return some (inj, ty)
        | _ => return some (inj, ty)
      catch _ => return none
    if let some (pf, ty) := r then
      let (_, g') ← (← g.assert `hunify ty pf).intro1P
      g := g'
  replaceMainGoal [g]
  -- split constructor equations and substitute
  if !pairs.isEmpty then
    evalTactic (← `(tactic| try simp only [Obj.plain.injEq, Obj.list.injEq, Obj.map.injEq, Obj.set.injEq,
      Obj.dec.injEq, Obj.str.injEq, Obj.boxed.injEq, Obj.array.injEq, Obj.iter.injEq, Obj.bigInt.injEq,
      Value.ref.injEq, Value.int.injEq, Value.long.injEq, true_and, and_true] at *))

/-- Instantiate ghost-quantified hypotheses (`∀ l k xs, a = l → σ.heap l = some … → P`) by
    simplifying hypotheses against each other with equality-elimination lemmas. -/
def jSimpHyps : TacticM Unit := do
  let g ← getMainGoal
  let hasPi ← g.withContext do
    return (← getLCtx).any fun d => !d.isImplementationDetail && d.type.consumeMData.isForall &&
      !(d.type.consumeMData.isArrow && false)
  unless hasPi do return
  let s ← saveState
  tryCatchRuntimeEx
    (withTheReader Core.Context (fun ctx => { ctx with maxHeartbeats := 200000 * 1000 }) do
      evalTactic (← `(tactic| simp_all (config := { decide := true, failIfUnchanged := false }) only
        [forall_eq, forall_eq', forall_apply_eq_imp_iff, forall_eq_apply_imp_iff, and_imp, true_implies,
         implies_true, and_true, true_and, Value.ref.injEq, Value.int.injEq, Value.long.injEq,
         List.cons.injEq, List.nil_eq, Option.some.injEq, Obj.list.injEq, Obj.plain.injEq,
         Obj.dec.injEq, Obj.str.injEq, Obj.iter.injEq, Obj.map.injEq, reduceCtorEq, exists_prop,
         exists_eq_left, exists_eq_right, exists_eq_left', exists_eq_right'])))
    (fun _ => s.restore)

/-- Head constant of the conclusion of a (syntactically) quantified type. -/
def forallConclHead (ty : Lean.Expr) : Option Name :=
  ty.consumeMData.getForallBody.consumeMData.getAppFn.constName?

/-- Heads of invariant facts that hold for every matching hypothesis (`HeapTyped`,
    `StaticsTyped` of `Jimple/Generic.lean`): instantiated for all matches, never consumed. -/
def persistentHeads : List Name := [`Jimple.ObjTyped, `Jimple.ValueTyped]

/-- Forward instantiation of quantified hypotheses `h : ∀ xs, P₁ → … → Pₖ → Q`: every premise
    must be matched — an equation with an uninstantiated variable on one side binds it, any other
    premise must unify with a hypothesis — and then `Q` (instantiated) is added. Equational
    rewrite rules (conclusion an equation) are left to `simp`. -/
def jForward : TacticM Unit := do
  let g ← getMainGoal
  let mut g := g
  let hs ← g.withContext do
    let mut acc := #[]
    let mc := jimple.modelContracts.get (← getOptions)
    for d in (← getLCtx) do
      if d.isImplementationDetail then continue
      -- (`jimple.modelContracts`: the type with its metavariables instantiated, and reduced when
      -- it is a callee's postcondition still matching on the outcome constructor)
      let ty ← if mc then instantiateMVars d.type else pure d.type
      let ty ← if !mc || ty.consumeMData.isForall then pure ty else
        if ← isProp ty then whnfD ty else pure ty
      if !ty.consumeMData.isForall then continue
      -- invariant facts are instantiated by `jPersistent`, for every match
      if let some c := forallConclHead ty then
        if persistentHeads.contains c then continue
      acc := acc.push d.fvarId
    return acc
  for hv in hs do
    let r ← g.withContext do
      let s ← saveState
      try
        let ty ← instantiateMVars (← hv.getType)
        let (ms, _, concl) ← forallMetaTelescopeReducing ty
        -- equational conclusions are rewrite rules: skip
        if concl.consumeMData.isAppOfArity ``Eq 3 then s.restore; return none
        let lctx ← getLCtx
        let mut ok := true
        for m in ms do
          let .mvar mid := m | continue
          if ← mid.isAssigned then continue
          let mty ← instantiateMVars (← inferType m)
          unless ← isProp mty do continue
          let solved ← (do
            -- ghost binding: `t = ?x` or `?x = t`
            match_expr mty with
            | Eq _ a b =>
              let a ← instantiateMVars a
              let b ← instantiateMVars b
              if let .mvar bid := b then
                if !(← bid.isAssigned) && !a.hasMVar then
                  if ← isDefEq b a then
                    mid.assign (← mkEqRefl a); return true
              if let .mvar aid := a then
                if !(← aid.isAssigned) && !b.hasMVar then
                  if ← isDefEq a b then
                    mid.assign (← mkEqRefl b); return true
              -- general case: unify the two sides (binds ghosts nested in lists, values, …)
              let s3 ← saveState
              if ← isDefEq a b then
                let a ← instantiateMVars a
                if !a.hasMVar then mid.assign (← mkEqRefl a); return true
              s3.restore
            | _ => pure ()
            for d in lctx do
              if d.isImplementationDetail || d.fvarId == hv then continue
              let s2 ← saveState
              if ← isDefEq mty d.type then
                mid.assign d.toExpr; return true
              s2.restore
            return false)
          if !solved then
            if jimple.debug.get (← getOptions) then
              dbgOut s!"[jForward] unmatched premise of {(← hv.getUserName)}: {(toString (← ppExpr mty)).take 300}"
            ok := false; break
        if !ok then s.restore; return none
        -- all binders must be determined
        for m in ms do
          if let .mvar mid := m then
            unless ← mid.isAssigned do s.restore; return none
        let pf ← instantiateMVars (mkAppN (.fvar hv) ms)
        let pty ← instantiateMVars concl
        if pty.hasMVar || (← getLCtx).any (fun d => d.type == pty) then
          if jimple.debug.get (← getOptions) then
            dbgOut s!"[jForward] {(← hv.getUserName)}: instance has mvars or exists"
          s.restore; return none
        return some (pf, pty)
      catch ex =>
        if jimple.debug.get (← getOptions) then
          dbgOut s!"[jForward] {(← hv.getUserName)}: exception {(toString (← ex.toMessageData.toString)).take 200}"
        s.restore; return none
    if let some (pf, pty) := r then
      let (_, g') ← (← g.assert `hfwd pty pf).intro1P
      -- the instance replaces the quantified hypothesis (avoids re-instantiation each round)
      g ← g'.tryClear hv
  replaceMainGoal [g]

/-- Instantiate every hypothesis `h : ∀ xs, l = r → C xs` whose conclusion is an invariant fact
    (`persistentHeads`) with every hypothesis matching its premise. -/
def jPersistent : TacticM Unit := do
  let g ← getMainGoal
  let mut g := g
  let cands ← g.withContext do
    let mut out := #[]
    for d in (← getLCtx) do
      if d.isImplementationDetail then continue
      unless d.type.consumeMData.isForall do continue
      if let some c := forallConclHead d.type then
        if persistentHeads.contains c then out := out.push d.fvarId
    return out
  for hv in cands do
    -- facts already used are renamed `hinst` (instances are later unfolded and destructured,
    -- so they cannot be recognized themselves)
    let facts ← g.withContext do return (← getLCtx).foldl (init := #[]) fun acc d =>
      if d.isImplementationDetail || d.fvarId == hv || d.userName == `hinst then acc
      else if d.type.consumeMData.isAppOfArity ``Eq 3 then acc.push d.fvarId else acc
    for fv in facts do
      let r ← g.withContext do
        let s ← saveState
        try
          let ty ← instantiateMVars (← hv.getType)
          let (ms, _, concl) ← forallMetaTelescopeReducing ty
          -- the first Prop premise must be the fact; every binder must be determined
          let mut done := false
          for m in ms do
            let .mvar mid := m | continue
            if ← mid.isAssigned then continue
            let mty ← instantiateMVars (← inferType m)
            if ← isProp mty then
              if !done then
                if ← isDefEq mty (← fv.getType) then
                  mid.assign (.fvar fv); done := true
                else s.restore; return none
              else s.restore; return none
          unless done do s.restore; return none
          for m in ms do
            if let .mvar mid := m then
              unless ← mid.isAssigned do s.restore; return none
          let pf ← instantiateMVars (mkAppN (.fvar hv) ms)
          let pty ← instantiateMVars concl
          if pty.hasMVar || (← getLCtx).any (fun d => d.type == pty) then s.restore; return none
          return some (pf, pty)
        catch _ => s.restore; return none
      if let some (pf, pty) := r then
        let (_, g') ← (← g.assert `hinv pty pf).intro1P
        g ← g'.rename fv `hinst
  replaceMainGoal [g]

/-- The witness of `∃ x, b` from a hypothesis: `b`'s inner existentials opened with
    metavariables, a conjunct mentioning `x` — a predicate such as a representation relation,
    whose ghost arguments no equation determines, or an equation with a known left side —
    unified with a hypothesis (reducible transparency). -/
partial def jExistsHyp (g : MVarId) (body : Lean.Expr) : MetaM (Option Lean.Expr) := g.withContext do
  let .lam _ ty b _ := body | return none
  let s ← saveState
  try
    let x ← mkFreshExprMVar ty
    let rec openEx (e : Lean.Expr) : Nat → MetaM Lean.Expr
      | 0 => return e
      | fuel + 1 => do
        let e := e.consumeMData
        if e.isAppOfArity ``Exists 2 then
          if let .lam _ ty' b' _ := e.appArg! then
            let y ← mkFreshExprMVar ty'
            return ← openEx (b'.instantiate1 y) fuel
        return e
    let rec conjs (e : Lean.Expr) : Nat → MetaM (List Lean.Expr)
      | 0 => return [e]
      | fuel + 1 => do
        let e ← openEx e 32
        if e.isAppOfArity ``And 2 then
          return (← conjs (e.getArg! 0) fuel) ++ (← conjs (e.getArg! 1) fuel)
        return [e]
    let cs ← conjs (b.instantiate1 x) 64
    let xm := x.mvarId!
    -- predicates, and equations whose left side is known (`σ.heap y = some (.str (f ?k))`)
    let cands := cs.filter fun c => !c.isAppOfArity ``Ne 3 && (c.find? (· == x)).isSome &&
      (!c.isAppOfArity ``Eq 3 || !(c.getArg! 1).hasMVar)
    let hyps := (← getLCtx).foldl (init := #[]) fun acc d =>
      if d.isImplementationDetail then acc else acc.push d.type
    for c in cands do
      for h in hyps do
        let s2 ← saveState
        if ← withReducible (isDefEq c h) then
          if ← xm.isAssigned then
            let w ← instantiateMVars x
            if !w.hasMVar then
              s.restore
              return some w
        s2.restore
    s.restore
    return none
  catch _ =>
    s.restore
    return none

/-- Existential goals: take a witness from an equation `x = t` among the conjuncts, else from a
    hypothesis matching a predicate conjunct (`jExistsHyp`). -/
partial def jExists : TacticM Bool := do
  let g ← getMainGoal
  let tgt ← instantiateMVars (← g.getType)
  let tgt := tgt.consumeMData
  unless tgt.isAppOfArity ``Exists 2 do return false
  let body := tgt.appArg!
  let .lam _ _ b _ := body | return false
  -- search conjuncts of b, also under further existentials (`∃ x y, (… = x ∧ … = y) ∧ …`),
  -- for `#k = t` or `t = #k` (`#k` the outer variable under `k` inner binders, `t` closed)
  let rec find (k : Nat) (e : Lean.Expr) : Option Lean.Expr :=
    match_expr e with
    | And p q => (find k p).orElse fun _ => find k q
    | Exists _ q => match q with
      | .lam _ _ b' _ => find (k + 1) b'
      | _ => none
    | Eq _ x t =>
      if x == .bvar k && !t.hasLooseBVars then some t
      else if t == .bvar k && !x.hasLooseBVars then some x
      else none
    | _ => none
  let w? ← match find 0 b with
    | some w => pure (some w)
    | none =>
      if jimple.modelContracts.get (← getOptions) then jExistsHyp g body else pure none
  match w? with
  | none =>
    if jimple.debug.get (← getOptions) then dbgOut "[jExists] no witness for the variable"
    return false
  | some w =>
    try
      let gs ← g.apply (← mkAppOptM ``Exists.intro #[none, body, w])
      replaceMainGoal gs
      return true
    catch ex =>
      if jimple.debug.get (← getOptions) then
        dbgOut s!"[jExists] apply failed: {(toString (← ex.toMessageData.toString)).take 300}"
      return false

/-- Length facts for omega: every `(List.filter p l).length` gets `≤ l.length`, every
    `(List.take n l).length` gets `= min n l.length`. -/
def jLengthFacts : TacticM Unit := do
  let g ← getMainGoal
  let mut g := g
  let terms ← g.withContext do
    let mut acc : Array Lean.Expr := #[]
    let rec go (t : Lean.Expr) (acc : Array Lean.Expr) : Array Lean.Expr :=
      let acc :=
        if t.isAppOfArity ``List.length 2 && !t.hasLooseBVars then
          let l := t.appArg!
          if (l.isAppOfArity ``List.filter 3 || l.isAppOfArity ``List.take 3) && !acc.contains t then
            acc.push t
          else acc
        else acc
      match t with
      | .app f a => go a (go f acc)
      | .lam _ ty b _ | .forallE _ ty b _ => go b (go ty acc)
      | .mdata _ b => go b acc
      | _ => acc
    acc := go (← instantiateMVars (← g.getType)) acc
    for h in (← getLCtx) do
      if !h.isImplementationDetail then acc := go (← instantiateMVars h.type) acc
    return acc
  for t in terms do
    let r ← g.withContext do
      try
        let l := t.appArg!
        let pf ← if l.isAppOfArity ``List.filter 3 then
            mkAppOptM ``List.length_filter_le #[none, l.getAppArgs[1]!, l.getAppArgs[2]!]
          else mkAppOptM ``List.length_take #[none, l.getAppArgs[1]!, l.getAppArgs[2]!]
        let ty ← instantiateMVars (← inferType pf)
        if (← getLCtx).any (fun d => d.type == ty) then return none
        return some (pf, ty)
      catch _ => return none
    if let some (pf, ty) := r then
      let (_, g') ← (← g.assert `hlen ty pf).intro1P
      g := g'
  replaceMainGoal [g]

/-- `tmod_facts` for every `Int.tmod a b` / `Int.tdiv a b` with a positive literal `b` in the
    goal or the context. -/
def jTmodFacts : TacticM Unit := do
  let g ← getMainGoal
  let mut g := g
  let terms ← g.withContext do
    let mut acc : Array (Lean.Expr × Lean.Expr) := #[]
    let rec go (t : Lean.Expr) (acc : Array (Lean.Expr × Lean.Expr)) : Array (Lean.Expr × Lean.Expr) :=
      let acc :=
        if (t.isAppOfArity ``Int.tmod 2 || t.isAppOfArity ``Int.tdiv 2) && !t.hasLooseBVars then
          let a := t.appFn!.appArg!
          let b := t.appArg!
          if (b.int?.isSome || b.nat?.isSome) && !acc.any (fun p => p.1 == a && p.2 == b) then
            acc.push (a, b)
          else acc
        else acc
      match t with
      | .app f a => go a (go f acc)
      | .lam _ ty b _ | .forallE _ ty b _ => go b (go ty acc)
      | .mdata _ b => go b acc
      | _ => acc
    acc := go (← instantiateMVars (← g.getType)) acc
    for h in (← getLCtx) do
      if !h.isImplementationDetail then acc := go (← instantiateMVars h.type) acc
    return acc
  for (a, b) in terms do
    let r ← g.withContext do
      try
        let hb ← mkDecideProof (← mkAppM ``LT.lt #[mkIntLit 0, b])
        let pf ← mkAppM ``tmod_facts #[a, b, hb]
        let ty ← instantiateMVars (← inferType pf)
        if (← getLCtx).any (fun d => d.type == ty) then return none
        return some (pf, ty)
      catch _ => return none
    if let some (pf, ty) := r then
      let (_, g') ← (← g.assert `htmod ty pf).intro1P
      g := g'
  replaceMainGoal [g]

/-- Shape facts `jShapeFields` has used (free variables are unique). -/
initialize jShapeDone : IO.Ref (Std.HashSet FVarId) ← IO.mkRef {}

/-- From a shape fact `h : d.erase = s` (a class of a `Shapes` fact) or `h : x.erase = y` (a
    method found in such a class): the equations of what erasure keeps — the class's name,
    hierarchy, flags and fields; the method's signature, modifiers and whether it has a body. The
    right-hand sides are closed, so lookups through `d` or `x` evaluate. -/
def jShapeFields : TacticM Unit := do
  let g ← getMainGoal
  let hs ← g.withContext do
    let mut out := #[]
    for d in (← getLCtx) do
      if d.isImplementationDetail then continue
      if (← jShapeDone.get).contains d.fvarId then continue
      let ty := (← instantiateMVars d.type).consumeMData
      let some (_, lhs, rhs) := ty.eq? | continue
      if (lhs.isAppOfArity ``ClassDecl.erase 1 || lhs.isAppOfArity ``MethodDecl.erase 1) &&
          !rhs.hasFVar then
        out := out.push (d.fvarId, lhs, rhs)
    return out
  if hs.isEmpty then return
  let mut g := g
  for (h, lhs, rhs) in hs do
    jShapeDone.modify (·.insert h)
    let x := lhs.appArg!
    let isClass := lhs.isAppOfArity ``ClassDecl.erase 1
    let projs : List Name := if isClass then
        [``ClassDecl.name, ``ClassDecl.isInterface, ``ClassDecl.isAbstract, ``ClassDecl.isEnum,
         ``ClassDecl.super, ``ClassDecl.interfaces, ``ClassDecl.fields]
      else [``MethodDecl.name, ``MethodDecl.params, ``MethodDecl.ret, ``MethodDecl.mods,
         ``MethodDecl.throws]
    let facts ← g.withContext do
      let mut out : Array (Lean.Expr × Lean.Expr) := #[]
      for pr in projs do
        let f := mkConst pr
        -- `congrArg f h : f (erase x) = f s`, which is `f x = f s` by unfolding `erase`
        let pf ← mkCongrArg f (.fvar h)
        let ty ← mkEq (mkApp f x) (mkApp f rhs)
        out := out.push (← mkExpectedTypeHint pf ty, ty)
      if isClass then
        let f := mkConst ``Program.ClassDecl.hasDefaultMethods
        let pf ← mkEqTrans (← mkEqSymm (mkApp (mkConst ``Program.hasDefaultMethods_erase) x))
          (← mkCongrArg f (.fvar h))
        out := out.push (pf, ← mkEq (mkApp f x) (mkApp f rhs))
      else
        let body : Lean.Expr → Lean.Expr := fun m =>
          mkApp2 (mkConst ``Option.isSome [.zero]) (mkConst ``Body) (mkApp (mkConst ``MethodDecl.body) m)
        let f ← withLocalDeclD `m (mkConst ``MethodDecl) fun m => mkLambdaFVars #[m] (body m)
        let pf ← mkEqTrans (← mkEqSymm (mkApp (mkConst ``MethodDecl.erase_body_isSome) x))
          (← mkCongrArg f (.fvar h))
        out := out.push (pf, ← mkEq (body x) (body rhs))
      return out
    for (pf, ty) in facts do
      let (_, g') ← (← g.assert `hshape ty pf).intro1P
      g := g'
  replaceMainGoal [g]

/-- Method lookups in a class known by its shape: for `ClassDecl.findMethod d sub st` or
    `ClassDecl.findClinit d` in the goal, with `h : d.erase = s`, evaluate the lookup in `s` and
    add `… = none`, or `… = some x` with `x.erase = y` for a fresh `x` (its body stays unknown:
    calls go through contracts). Returns whether facts were added. -/
def jShapeMethod1 (added : Array Lean.Expr) : TacticM (Option Lean.Expr) := do
  let g ← getMainGoal
  let r : Option (Lean.Expr × Lean.Expr × Lean.Expr × FVarId) ← g.withContext do
    let mut shapes : Array (Lean.Expr × Lean.Expr × FVarId) := #[]
    for d in (← getLCtx) do
      if d.isImplementationDetail then continue
      let ty := (← instantiateMVars d.type).consumeMData
      let some (_, lhs, rhs) := ty.eq? | continue
      if lhs.isAppOfArity ``ClassDecl.erase 1 && !rhs.hasFVar then
        shapes := shapes.push (lhs.appArg!, rhs, d.fvarId)
    if shapes.isEmpty then return none
    let tgt ← instantiateMVars (← g.getType)
    let known := (← getLCtx).foldl (init := #[]) fun acc d =>
      match d.type.consumeMData.eq? with
      | some (_, l, _) => acc.push l
      | none => acc
    -- the class argument of a lookup
    let clsOf : Lean.Expr → Lean.Expr := fun t =>
      if t.isAppOfArity ``Program.ClassDecl.findMethod 3 then t.getArg! 0 else t.appArg!
    let found := tgt.find? fun t =>
      (t.isAppOfArity ``Program.ClassDecl.findMethod 3 || t.isAppOfArity ``Program.ClassDecl.findClinit 1) &&
      !t.hasLooseBVars && !known.contains t && !added.contains t && shapes.any (·.1 == clsOf t) &&
      (t.getAppArgs.toList.drop 1).all (!·.hasFVar)
    match found with
    | none => return none
    | some t =>
      match shapes.find? (·.1 == clsOf t) with
      | some (d, s, h) => return some (t, d, s, h)
      | none => return none
  let some (t, _, s, h) := r | return none
  let isMethod := t.isAppOfArity ``Program.ClassDecl.findMethod 3
  let ts := if isMethod then mkApp3 t.getAppFn s (t.getArg! 1) (t.getArg! 2) else mkApp t.getAppFn s
  let g' ← g.withContext do
    let v ← groundEvalClean ts
    let optTy := mkApp (mkConst ``Option [.zero]) (mkConst ``MethodDecl)
    let hs ← mkExpectedTypeHint (← mkEqRefl v) (← mkEq ts v)
    if v.isAppOfArity ``Option.none 1 then
      let lem := if isMethod then ``Program.findMethod_none_of_erase else ``Program.findClinit_none_of_erase
      let pf ← mkAppM lem #[.fvar h, hs]
      let (_, g') ← (← g.assert `hshape (← mkEq t (mkApp (mkConst ``Option.none [.zero]) (mkConst ``MethodDecl))) pf).intro1P
      let _ := optTy
      return g'
    else
      let lem := if isMethod then ``Program.findMethod_some_of_erase else ``Program.findClinit_some_of_erase
      let pf ← mkAppM lem #[.fvar h, hs]
      let (_, g') ← (← g.assert `hshape (← inferType pf) pf).intro1P
      return g'
  replaceMainGoal [g']
  return some t

/-- `jShapeMethod1` for every lookup of the goal (at most 32); the existentials are then
    destructured and the new methods' facts derived. Returns whether facts were added. -/
def jShapeMethods : TacticM Bool := do
  let mut added : Array Lean.Expr := #[]
  for _ in [0:32] do
    match ← jShapeMethod1 added with
    | some t => added := added.push t
    | none => break
  if added.isEmpty then return false
  jDestruct
  unless (← getGoals).isEmpty do jShapeFields
  return true

/-- The facts generated from the goal's terms (element accesses, lengths, remainders); `true`
    when a hypothesis was added. -/
def jGoalFacts : TacticM Bool := do
  let n ← getMainGoal >>= fun g => g.withContext do return (← getLCtx).numIndices
  jInstMem
  jLengthFacts
  jTmodFacts
  -- method lookups in classes known by their shape (one per call; repeated by the loop)
  if !(← getGoals).isEmpty then discard jShapeMethods
  let n' ← getMainGoal >>= fun g => g.withContext do return (← getLCtx).numIndices
  return n' != n

/-- Run a tactic on `g`; on failure restore the state and return `none`. -/

register_option jimple.maxHeartbeats : Nat := {
  defValue := 0
  descr := "heartbeat budget (in thousands, 0 = unlimited) of one jvc/jverify call; the \
    symbolic execution itself is bounded by the exploration fuel" }

/-- Run with the `jimple.maxHeartbeats` budget instead of the declaration's `maxHeartbeats`. -/
def withJimpleHeartbeats {α} (x : TacticM α) : TacticM α := do
  let hb := jimple.maxHeartbeats.get (← getOptions)
  let now ← IO.getNumHeartbeats
  -- the budget counts from the start of this call
  withTheReader Core.Context (fun ctx => { ctx with maxHeartbeats := hb * 1000, initHeartbeats := now }) x

def tryOn (g : MVarId) (tac : TacticM Unit) : TacticM (Option (List MVarId)) := do
  let s ← saveState
  setGoals [g]
  tryCatchRuntimeEx
    (do tac; return some (← getGoals))
    (fun ex => do
      s.restore
      if jimple.trace.get (← getOptions) then
        logInfo m!"jvc: step failed: {ex.toMessageData}"
      if jimple.debug.get (← getOptions) then
        dbgOut s!"[jvc step failed] {(toString (← ex.toMessageData.toString)).take 300}"
      return none)

/-- `tryOn` returning the tactic's result too. -/
def tryOnR {α} (g : MVarId) (tac : TacticM α) : TacticM (Option (α × List MVarId)) := do
  let s ← saveState
  setGoals [g]
  tryCatchRuntimeEx
    (do let a ← tac; return some (a, ← getGoals))
    (fun ex => do
      s.restore
      if jimple.trace.get (← getOptions) then
        logInfo m!"jvc: step failed: {ex.toMessageData}"
      return none)

/-- `exfalso` for a propositional goal, by assigning `False.elim ?_` directly: the `exfalso`
    tactic elaborates `False.elim ?_` against the goal, which can `whnf` (that is, run) a whole
    symbolic execution goal. -/
def jExfalso : TacticM Unit := do
  let g ← getMainGoal
  let h ← g.withContext do
    let target ← instantiateMVars (← g.getType)
    let h ← mkFreshExprSyntheticOpaqueMVar (mkConst ``False) (← g.getTag)
    g.assign (mkApp2 (mkConst ``False.elim [levelZero]) target h)
    return h
  replaceMainGoal [h.mvarId!]

/-- Run `x` with a fresh budget of `hb` (in `maxHeartbeats` units) counted from now. -/
def withBudget {α} (hb : Nat) (x : TacticM α) : TacticM α := do
  let now ← IO.getNumHeartbeats
  withTheReader Core.Context (fun ctx => { ctx with maxHeartbeats := hb * 1000, initHeartbeats := now }) x

/-- Try to close `g` with `tac` within `hb` thousand heartbeats (timeouts are failures). -/
def tryClose (g : MVarId) (tac : TacticM Unit) (hb : Nat) : TacticM Bool := do
  let s ← saveState
  setGoals [g]
  tryCatchRuntimeEx
    (do
      withBudget hb tac
      if (← getGoals).isEmpty then return true
      s.restore; return false)
    (fun _ => do s.restore; return false)

/-- Leaf solving with bounded attempts (see `jauto`). -/
def jautoOn (g : MVarId) : TacticM Bool := do
  -- budgets in `maxHeartbeats` units (the option's default is 200000)
  let attempts : List (TacticM Unit × Nat) := [
    (do evalTactic (← `(tactic| with_reducible rfl)), 20000),
    (do evalTactic (← `(tactic| jomega_arith)), 100000),
    (do evalTactic (← `(tactic| simp_all [-BitVec.toInt_xor, -BitVec.toInt_and, -BitVec.toInt_or])), 100000),
    -- machine-word (in)equalities as equations of their values, for `omega`
    (do evalTactic (← `(tactic| simp only [← BitVec.toNat_inj, BitVec.toNat_ofNat] at *))
        evalTactic (← `(tactic| jomega_arith)), 50000),
    (do evalTactic (← `(tactic| simp (disch := jomega) only [bmod32_of_bounds, bmod64_of_bounds] at *));
        evalTactic (← `(tactic| first | jomega | grind)), 100000),
    (do evalTactic (← `(tactic| jdecide)), 50000),
    (do evalTactic (← `(tactic| grind)), 100000),
    (do evalTactic (← `(tactic| simp (disch := jbound) only [bmod32_of_bounds, bmod64_of_bounds] at *));
        evalTactic (← `(tactic| first | jomega | grind | (jnlin; grind))), 200000),
    (do evalTactic (← `(tactic| bv_decide)), 50000)]
  let dbg := jimple.debug.get (← getOptions)
  let mut k := 0
  for (tac, hb) in attempts do
    if dbg then
      dbgOut s!"[jauto {(← IO.monoMsNow)} ms] closer {k}"
    k := k + 1
    if ← tryClose g tac hb then return true
  return false

/-- Drop useless hypotheses: `True`, `a = a`, and repetitions of an earlier hypothesis
    (substitutions make distinct facts coincide). -/
def jCleanup : TacticM Unit := do
  let g ← getMainGoal
  let toClear ← g.withContext do
    let mut seen : Std.HashSet Lean.Expr := {}
    let mut out := #[]
    for d in (← getLCtx) do
      if d.isImplementationDetail then continue
      let ty ← instantiateMVars d.type
      unless ← isProp ty do continue
      let refl := ty.isAppOfArity ``Eq 3 && ty.appFn!.appArg! == ty.appArg!
      if ty.isConstOf ``True || refl || seen.contains ty then out := out.push d.fvarId
      else seen := seen.insert ty
    return out
  let mut g := g
  for fv in toClear.reverse do
    g ← g.tryClear fv
  replaceMainGoal [g]

/-- Hypotheses `jHypEval` has simplified without change (free variables are unique). -/
initialize jHypEvalDone : IO.Ref (Std.HashSet FVarId) ← IO.mkRef {}

/-- Evaluate hypotheses that mention closed program-structure terms or the definitions to
    unfold (typing facts of generic contracts, `c ∈ P.progSubclasses d`, ...). -/
def jHypEval (extra : Array Ident) : TacticM Unit := do
  let g ← getMainGoal
  let extraNames : List Name ← extra.toList.filterMapM fun (i : Ident) => do
    try return some (← realizeGlobalConstNoOverloadWithInfo i.raw) catch _ => return none
  -- instances of the typing invariants (`ObjTyped`, `ValueTyped` of `Jimple/Generic.lean`) are
  -- unfolded here, never under binders: the quantified invariants keep their heads for
  -- `jPersistent`
  let env ← getEnv
  let invNames := (persistentHeads ++ [`Jimple.RefTyped]).filter env.contains
  let unfoldNames := extraNames ++ invNames
  -- the facts of a per-method proof (`Jimple/Verify.lean`): `P.findClass c = …` equations
  -- rewrite the lookups in hypotheses too, and `NoShadow P` those of library classes
  -- (`jnoshadow`)
  let (facts, noShadow) ← g.withContext do
    let mut out : Array Lean.Expr := #[]
    let mut noShadow := false
    for d in (← getLCtx) do
      if d.isImplementationDetail then continue
      let ty := (← instantiateMVars d.type).consumeMData
      if ty.isAppOfArity ``NoShadow 1 then
        noShadow := true
      else if ty.isAppOfArity ``Eq 3 && (ty.getArg! 1).isAppOfArity ``Program.findClass 2 then
        out := out.push (.fvar d.fvarId)
    return (out, noShadow)
  let fvs ← g.withContext do
    let mut out := #[]
    for d in (← getLCtx) do
      if d.isImplementationDetail then continue
      let ty ← instantiateMVars d.type
      unless ← isProp ty do continue
      if facts.contains (.fvar d.fvarId) then continue
      -- the quantified typing invariants themselves stay folded; hypotheses already simplified
      -- without change are skipped
      if (← jHypEvalDone.get).contains d.fvarId then continue
      -- the cut facts and the postcondition (`jFoldCuts`) stay folded: they are used when the
      -- goal reaches a cut or a return, and unfolded there
      let un := d.userName.eraseMacroScopes
      if jimple.modelContracts.get (← getOptions) &&
          (un == `hcut || un == `hcutsNone || un == `hpost) then continue
      if ty.consumeMData.isForall then
        if let some c := forallConclHead ty then
          if persistentHeads.contains c then continue
      let found := (ty.find? fun t => match t.getAppFn with
        | .const c _ =>
          ((groundFns.contains c || (env.getProjectionFnInfo? c).isSome) && !t.hasFVar &&
            !t.hasLooseBVars) || unfoldNames.contains c ||
          (c == ``Program.findClass && (noShadow || !facts.isEmpty) && t.getAppNumArgs == 2 &&
            t.appArg!.isLit)
        | _ => false).isSome
      if found then out := out.push d.fvarId
    return out
  if fvs.isEmpty then return
  let extraL : Array (TSyntax `Lean.Parser.Tactic.simpLemma) ←
    (extra ++ invNames.toArray.map mkIdent).mapM fun i => `(Lean.Parser.Tactic.simpLemma| $i:ident)
  -- (`jimple.modelContracts`) `jdisch`: the conditional rewrite rules among the extra lemmas
  -- (`toInt (ofInt x) = x` for a bounded `x`, …) apply in the hypotheses as they do in the goal
  let stx ← if jimple.modelContracts.get (← getOptions) then
    `(tactic| simp (config := { decide := true, failIfUnchanged := false }) (disch := jdisch) only
      [jground, jnoshadow, List.forall_mem_cons, List.mem_cons, List.mem_singleton,
       List.not_mem_nil, or_false, false_or, and_true, true_and, implies_true, forall_const,
       ite_true, ite_false, Option.isSome_none, Option.isSome_some,
       false_implies, forall_eq_or_imp, forall_eq, forall_eq', Option.some.injEq, reduceCtorEq,
       $extraL,*])
  else
    `(tactic| simp (config := { decide := true, failIfUnchanged := false }) only
      [jground, jnoshadow, List.forall_mem_cons, List.mem_cons, List.mem_singleton,
       List.not_mem_nil, or_false, false_or, and_true, true_and, implies_true, forall_const,
       ite_true, ite_false, Option.isSome_none, Option.isSome_some,
       false_implies, forall_eq_or_imp, forall_eq, forall_eq', Option.some.injEq, reduceCtorEq,
       $extraL,*])
  let r ← g.withContext do
    let { ctx, simprocs, dischargeWrapper, .. } ← mkSimpContext stx (eraseLocal := false)
    let mut thms := ctx.simpTheorems
    for pf in facts do
      thms ← thms.addTheorem (.other `jfact) pf
    -- (opt-in) the heap facts of the context as rewrite rules: `argText σ (.ref a)`, `strOf …` in
    -- a hypothesis evaluate as they do in the goal
    if jimple.hypHeapFacts.get (← getOptions) then
      for d in (← getLCtx) do
        if d.isImplementationDetail || fvs.contains d.fvarId then continue
        let ty := (← instantiateMVars d.type).consumeMData
        if ty.isAppOfArity ``Eq 3 && (ty.getArg! 1).isAppOfArity ``State.heap 2 &&
            (ty.getArg! 2).isAppOfArity ``Option.some 2 then
          thms ← thms.addTheorem (.fvar d.fvarId) d.toExpr
    let ctx := ctx.setSimpTheorems thms
    -- the hypotheses only: the goal is simplified by the symbolic execution step
    jdischFailed.set {}
    let (r, _) ← try
        dischargeWrapper.with fun discharge? =>
          simpGoal g ctx simprocs discharge? (simplifyTarget := false) (fvarIdsToSimp := fvs)
      finally jdischFailed.set {}
    return r
  match r with
  | none => replaceMainGoal []
  | some (_, g') =>
    -- hypotheses that kept their identity did not change: never simplify them again
    let lctx ← g'.withContext getLCtx
    let kept : Array FVarId := fvs.filter fun fv => lctx.contains fv
    jHypEvalDone.modify fun st => kept.foldl (fun acc fv => acc.insert fv) st
    replaceMainGoal [g']

/-- Split one nullable reference fact `v = null ∨ …` (from the typing of a generic contract)
    into its two cases. -/
def jNullSplit : TacticM Unit := do
  let g ← getMainGoal
  let found ← g.withContext do
    for d in (← getLCtx) do
      if d.isImplementationDetail then continue
      let ty := (← instantiateMVars d.type).consumeMData
      if ty.isAppOfArity ``Or 2 then
        let lhs := ty.appFn!.appArg!
        if lhs.isAppOfArity ``Eq 3 && lhs.appArg!.isConstOf ``Value.null then return some d.fvarId
    return none
  if let some fv := found then
    -- `Or.elim h (fun h₁ => ?g₁) (fun h₂ => ?g₂)` built directly (`MVarId.cases` re-checks the
    -- whole goal and could take minutes on a goal with several nullable arguments)
    let gs ← g.withContext do
      let ty := (← instantiateMVars (← fv.getType)).consumeMData
      let a := ty.appFn!.appArg!
      let b := ty.appArg!
      let tgt ← g.getType
      let m1 ← mkFreshExprSyntheticOpaqueMVar (← mkArrow a tgt)
      let m2 ← mkFreshExprSyntheticOpaqueMVar (← mkArrow b tgt)
      g.assign (mkApp6 (mkConst ``Or.elim) a b tgt (.fvar fv) m1 m2)
      let (_, g1) ← m1.mvarId!.intro1P
      let (_, g2) ← m2.mvarId!.intro1P
      return [← g1.tryClear fv, ← g2.tryClear fv]
    replaceMainGoal gs

/-- Pairs (subclass fact, heap fact) `jSubFields` has used (free variables are unique). -/
initialize jSubFieldsDone : IO.Ref (Std.HashSet (FVarId × FVarId)) ← IO.mkRef {}

/-- Fields of an object whose class is only known to be a subclass: from
    `σ.heap a = some (.plain c' fs)` and `c' ∈ P.progSubclasses c` (the typing of a reference of
    class `c`), the fields `c` declares are present and typed (`fields_of_sub`,
    `Jimple/Generic.lean`). In a proof for every program, `c'` stays unknown. -/
def jSubFields : TacticM Unit := do
  unless (← getEnv).contains `Jimple.fields_of_sub do return
  let g ← getMainGoal
  let (heapFacts, subs, typed) ← g.withContext do
    let mut hs : Array (FVarId × Lean.Expr) := #[]
    let mut ss : Array (FVarId × Lean.Expr) := #[]
    let mut ts : Array FVarId := #[]
    for d in (← getLCtx) do
      if d.isImplementationDetail then continue
      let ty := (← instantiateMVars d.type).consumeMData
      if ty.isAppOfArity ``Eq 3 then
        let rhs := ty.appArg!
        if rhs.isAppOfArity ``Option.some 2 && rhs.appArg!.isAppOfArity ``Obj.plain 2 then
          hs := hs.push (d.fvarId, rhs.appArg!.appFn!.appArg!)
      else if ty.isAppOfArity ``Membership.mem 5 then
        if (ty.getArg! 3).isAppOfArity ``Program.progSubclasses 2 then
          ss := ss.push (d.fvarId, ty.getArg! 4)
      else if ty.isForall then
        if forallConclHead ty == some `Jimple.ObjTyped then ts := ts.push d.fvarId
    return (hs, ss, ts)
  if subs.isEmpty || typed.isEmpty then return
  let mut g := g
  for (hsub, c) in subs do
    for (hh, c') in heapFacts do
      unless c == c' do continue
      -- once per pair (the instance is simplified afterwards, so it cannot be recognized)
      if (← jSubFieldsDone.get).contains (hsub, hh) then continue
      jSubFieldsDone.modify (·.insert (hsub, hh))
      for hH in typed do
        let r ← g.withContext do
          try
            let pf ← mkAppM `Jimple.fields_of_sub #[.fvar hH, .fvar hh, .fvar hsub]
            let pty ← instantiateMVars (← inferType pf)
            if (← getLCtx).any (fun d => d.type == pty) then return none
            return some (pf, pty)
          catch _ => return none
        if let some (pf, pty) := r then
          let (_, g') ← (← g.assert `hsupf pty pf).intro1P
          g := g'
  replaceMainGoal [g]

/-- The symbolic machine integers `x` (`x : BitVec 32/64`) under `BitVec.toInt` in `e`. -/
partial def toIntAtoms (e : Lean.Expr) (acc : Array (Lean.Expr × Nat)) : Array (Lean.Expr × Nat) :=
  let acc :=
    if e.isAppOfArity ``BitVec.toInt 2 && !e.hasLooseBVars && e.appArg!.hasFVar then
      match (e.getArg! 0).nat? <|> (e.getArg! 0).rawNatLit? with
      | some 32 => if acc.any (·.1 == e.appArg!) then acc else acc.push (e.appArg!, 32)
      | some 64 => if acc.any (·.1 == e.appArg!) then acc else acc.push (e.appArg!, 64)
      | _ => acc
    else acc
  match e with
  | .app f a => toIntAtoms a (toIntAtoms f acc)
  | .lam _ t b _ | .forallE _ t b _ => toIntAtoms b (toIntAtoms t acc)
  | .letE _ t v b _ => toIntAtoms b (toIntAtoms v (toIntAtoms t acc))
  | .mdata _ b | .proj _ _ b => toIntAtoms b acc
  | _ => acc

/-- Machine integers seen by `omega`: for each symbolic `x.toInt` (`x : BitVec 32/64`) in the goal
    or the hypotheses, its range (`bv32_le_toInt`, `bv32_toInt_lt`, …), once. Loop invariants then
    need not restate that an `int` is an `int` (e.g. that `i + 1` does not overflow below `n`). -/
def jIntBounds : TacticM Unit := do
  let g ← getMainGoal
  let atoms ← g.withContext do
    let mut acc : Array (Lean.Expr × Nat) := toIntAtoms (← instantiateMVars (← g.getType)) #[]
    for d in (← getLCtx) do
      if d.isImplementationDetail then continue
      if ← isProp d.type then acc := toIntAtoms (← instantiateMVars d.type) acc
    return acc
  if atoms.isEmpty then return
  let mut g := g
  for (x, w) in atoms.toList.take 64 do
    let (lo, hi) := if w == 32 then (``bv32_le_toInt, ``bv32_toInt_lt) else (``bv64_le_toInt, ``bv64_toInt_lt)
    for lem in [lo, hi] do
      let pf := mkApp (mkConst lem) x
      let ty ← g.withContext do inferType pf
      let present ← g.withContext do return (← getLCtx).any fun d => d.type == ty
      unless present do
        let (_, g') ← (← g.assert `hrange ty pf).intro1P
        g := g'
  replaceMainGoal [g]

/-- A literal bound on an integer term from a hypothesis: `(t, lower?, value)`. -/
def intBoundOf (ty : Lean.Expr) : Option (Lean.Expr × Bool × Int) :=
  let ty := ty.consumeMData
  let lit (e : Lean.Expr) : Option Int := e.int?
  let isInt (e : Lean.Expr) := e.int?.isNone
  let (neg, ty) := if ty.isAppOfArity ``Not 1 then (true, ty.appArg!) else (false, ty)
  if (ty.isAppOfArity ``LE.le 4 || ty.isAppOfArity ``LT.lt 4) && (ty.getArg! 0).isConstOf ``Int then
    let strict := ty.isAppOfArity ``LT.lt 4
    let a := ty.getArg! 2
    let b := ty.getArg! 3
    -- `a ≤ b` / `a < b`, possibly negated: `¬ a ≤ b` is `b < a`, `¬ a < b` is `b ≤ a`
    let (a, b, strict) := if neg then (b, a, !strict) else (a, b, strict)
    match lit a, lit b with
    | some c, none => if isInt b then some (b, true, if strict then c + 1 else c) else none
    | none, some c => if isInt a then some (a, false, if strict then c - 1 else c) else none
    | _, _ => none
  else none

/-- An integer term the hypotheses pin to one value (`-1 ≤ i`, `i < 0` at a loop exit): add
    `t = c` (by `omega`), so that terms built from `t` evaluate. -/
def jPinInts : TacticM Unit := do
  let g ← getMainGoal
  let pins ← g.withContext do
    let mut lo : Array (Lean.Expr × Int) := #[]
    let mut hi : Array (Lean.Expr × Int) := #[]
    for d in (← getLCtx) do
      if d.isImplementationDetail then continue
      match intBoundOf (← instantiateMVars d.type) with
      | some (t, true, c) => lo := lo.push (t, c)
      | some (t, false, c) => hi := hi.push (t, c)
      | none => pure ()
    let mut out : Array (Lean.Expr × Int) := #[]
    for (t, c) in lo do
      let l := (lo.filter (·.1 == t)).foldl (fun m p => max m p.2) c
      let h? := (hi.filter (·.1 == t)).foldl (fun (m : Option Int) p => some (match m with | some x => min x p.2 | none => p.2)) none
      if h? == some l && !out.any (·.1 == t) then out := out.push (t, l)
    -- already known
    let known := (← getLCtx).foldl (init := (#[] : Array Lean.Expr)) fun acc d => acc.push d.type
    return out.filter fun (t, c) => !known.any fun ty =>
      ty.isAppOfArity ``Eq 3 && ty.appFn!.appArg! == t && ty.appArg!.int? == some c
  if pins.isEmpty then return
  let mut g := g
  for (t, c) in pins do
    let ty ← g.withContext do mkEq t (toExpr c)
    let m ← g.withContext do mkFreshExprSyntheticOpaqueMVar ty
    let saved ← getGoals
    let ok ← try
        setGoals [m.mvarId!]
        evalTactic (← `(tactic| omega))
        pure true
      catch _ => pure false
    setGoals saved
    if ok then
      let (_, g') ← (← g.assert `hpin ty m).intro1P
      g := g'
  replaceMainGoal [g]

/-- Frame conditions as rewrite rules: from `σ'.inits = σ.inits` (a callee contract's frame
    condition), `∀ c, σ'.initOf c = σ.initOf c`; likewise for the statics. -/
def jFrameFacts : TacticM Unit := do
  let g ← getMainGoal
  let todo ← g.withContext do
    let mut out : Array (Name × FVarId) := #[]
    for d in (← getLCtx) do
      if d.isImplementationDetail then continue
      let ty := (← instantiateMVars d.type).consumeMData
      let some (_, l, _) := ty.eq? | continue
      if l.isAppOfArity ``State.inits 1 then out := out.push (``State.initOf_eq_of_inits, d.fvarId)
      else if l.isAppOfArity ``State.statics 1 then out := out.push (``State.static_eq_of_statics, d.fvarId)
    return out
  if todo.isEmpty then return
  let mut g := g
  for (lem, h) in todo do
    let pf ← g.withContext do mkAppM lem #[.fvar h]
    let ty ← g.withContext do inferType pf
    let present ← g.withContext do return (← getLCtx).any fun d => d.type == ty
    unless present do
      let (_, g') ← (← g.assert `hframe ty pf).intro1P
      g := g'
  replaceMainGoal [g]

/-- The cut list and the postcondition of the method under verification become local functions
    `cuts` and `post` with defining equations (`hcuts : ∀ pc, cuts.lookup pc = …`, `hpost : ∀ o,
    post o = …`), used by `simp` at cut points and returns only: every symbolic step copies the
    `bodyWP` continuation, and written out each copy carries every invariant and the contract. -/
def jFoldCuts : TacticM Unit := do
  unless jimple.foldCuts.get (← getOptions) do return
  let mut g ← getMainGoal
  -- the cut list, when written out
  let r ← g.withContext do
    let tgt ← instantiateMVars (← g.getType)
    let some e := tgt.find? (fun e => e.isAppOfArity ``bodyWP 9 &&
        (e.getArg! 3).isAppOfArity ``List.cons 3 && !e.hasLooseBVars) | return none
    return some (e.getArg! 3)
  if let some I := r then
    -- the entries `(k, J)` of the literal cut list
    let mut entries : Array (Lean.Expr × Lean.Expr) := #[]
    let mut e := I
    while e.isAppOfArity ``List.cons 3 do
      let hd := e.getArg! 1
      if hd.isAppOfArity ``Prod.mk 4 then entries := entries.push (hd.getArg! 2, hd.getArg! 3)
      e := e.getArg! 2
    let (fvs, g1) ← g.generalize #[{ expr := I, xName? := some `cuts, hName? := some `hcutsEq }]
    g ← g1.withContext do
      let cuts := Lean.mkFVar fvs[0]!
      let heq := Lean.mkFVar fvs[1]!   -- `I = cuts`
      let cutsTy ← inferType cuts
      let lookupAt (pc : Lean.Expr) : MetaM Lean.Expr := do
        withLocalDeclD `l cutsTy fun l => do mkLambdaFVars #[l] (← mkAppM ``List.lookup #[pc, l])
      let mut g' := g1
      -- one fact per cut point, at its literal program counter (never under a binder, where the
      -- program counter is symbolic: a `∀ pc` equation unfolded the whole list there)
      for (k, J) in entries do
        let lhsEq ← mkCongrArg (← lookupAt k) (← mkEqSymm heq)   -- lookup k cuts = lookup k I
        let ty ← mkEq (← mkAppM ``List.lookup #[k, cuts]) (← mkAppM ``Option.some #[J])
        let pf ← mkExpectedTypeHint lhsEq ty
        let (_, g2) ← (← g'.assert `hcut ty pf).intro1P
        g' := g2
      -- every other literal program counter is no cut point
      let ks ← mkListLit (mkConst ``Nat) (entries.toList.map (·.1))
      let pcN ← mkFreshUserName `pc
      let ty ← withLocalDeclD pcN (mkConst ``Nat) fun pc => do
        let notMem ← mkAppM ``Not #[← mkAppM ``Membership.mem #[ks, pc]]
        mkForallFVars #[pc] (← mkArrow notMem (← mkEq (← mkAppM ``List.lookup #[pc, cuts])
          (← mkAppOptM ``Option.none #[cutsTy.appArg!.appArg!])))
      let pf ← withLocalDeclD pcN (mkConst ``Nat) fun pc => do
        let notMem ← mkAppM ``Not #[← mkAppM ``Membership.mem #[ks, pc]]
        withLocalDeclD `h notMem fun h => do
          let β := cutsTy.appArg!.appArg!
          let fstFn ← mkAppOptM ``Prod.fst #[some (mkConst ``Nat), some β]
          let hk ← mkExpectedTypeHint (← mkEqRefl ks) (← mkEq (← mkAppM ``List.map #[fstFn, I]) ks)
          let none' ← mkAppOptM ``lookup_none_of_keys #[none, I, ks, pc, hk, h]
          let lhsEq ← mkCongrArg (← lookupAt pc) (← mkEqSymm heq)
          mkLambdaFVars #[pc, h] (← mkEqTrans lhsEq none')
      let (_, g3) ← (← g'.assert `hcutsNone ty pf).intro1P
      g3.tryClear fvs[1]!
  -- the postcondition of the method itself (the `bodyWP` with a cut list), when written out
  let r2 ← g.withContext do
    let tgt ← instantiateMVars (← g.getType)
    -- (also under the binders of a pending step's continuation: the postcondition is closed)
    let some e := tgt.find? (fun e => e.isAppOfArity ``bodyWP 9 && (e.getArg! 4).isLambda &&
        ((e.getArg! 3).isFVar || (e.getArg! 3).isAppOfArity ``List.cons 3) &&
        !(e.getArg! 4).hasLooseBVars) | return none
    return some (e.getArg! 4)
  if let some Post := r2 then
    let (fvs, g3) ← g.generalize #[{ expr := Post, xName? := some `post, hName? := some `hpostEq }]
    g ← g3.withContext do
      let post := Lean.mkFVar fvs[0]!
      let heq := Lean.mkFVar fvs[1]!   -- `Post = post`
      let oTy := mkConst ``Outcome
      let ty ← withLocalDeclD `o oTy fun o => do
        mkForallFVars #[o] (← mkEq (mkApp post o) (mkApp Post o))
      let pf ← withLocalDeclD `o oTy fun o => do
        mkLambdaFVars #[o] (← mkCongrFun (← mkEqSymm heq) o)
      let (_, g') ← (← g3.assert `hpost ty pf).intro1P
      g'.tryClear fvs[1]!
  replaceMainGoal [g]

/-- `σ'` keeps every object of `σ`: the heaps agree below `σ.next` (a callee's `Grows`, the
    allocations and updates of fresh objects since). -/
def Agree (σ σ' : State) : Prop := ∀ y, y < σ.next → σ'.heap y = σ.heap y

/-- A premise `R … σ σ'` whose last two arguments are states: a frame relation between two
    states (`Agree`, `StrMono`, a contract's frame predicate). -/
def isFrameRel (ty : Lean.Expr) : MetaM Bool := do
  let ty := ty.consumeMData
  let some _ := ty.getAppFn.constName? | return false
  let args := ty.getAppArgs
  if args.size < 2 then return false
  let isState (e : Lean.Expr) : MetaM Bool := do
    return (← whnfR (← inferType e)).isConstOf ``State
  return (← isState args[args.size - 2]!) && (← isState args[args.size - 1]!)

/-- A leaf goal about a later state from a hypothesis about an earlier one, by a `jframe`
    lemma: its premises other than frame relations by assumption (which fixes the earlier
    state); a frame relation by assumption too when a hypothesis states it (a callee's frame,
    an invariant's), else unfolded and left to the jvc loop (`Agree σ σ'`: the heaps agree). -/
def jFrameStepMC : TacticM Unit := do
  let g ← getMainGoal
  let names ← labelled `jframe
  g.withContext do
  for n in names do
    let s ← saveState
    try
      let gs ← g.apply (← mkConstWithFreshMVarLevels n)
      let mut rest : Array MVarId := #[]
      for g' in gs do
        if ← g'.isAssigned then continue
        let ty ← instantiateMVars (← g'.getType)
        -- term arguments (the earlier state, …) are fixed by the premises' unification
        unless ← isProp ty do continue
        if ← isFrameRel ty then rest := rest.push g'
        else g'.assumption
      let mut out : Array MVarId := #[]
      for g' in rest do
        if ← g'.isAssigned then continue
        let done ← (do g'.assumption; pure true) <|> pure false
        if done then continue
        let ty ← instantiateMVars (← g'.getType)
        if ty.hasMVar then throwError "jFrameStep: frame premise with unknown states"
        let some c := ty.consumeMData.getAppFn.constName? | throwError "jFrameStep: no head"
        out := out.push (← g'.deltaTarget (· == c))
      for g' in gs do
        unless ← g'.isAssigned do
          unless ← isProp (← g'.getType) do throwError "jFrameStep: undetermined argument"
      replaceMainGoal out.toList
      return
    catch ex =>
      if jimple.debug.get (← getOptions) then
        dbgOut s!"[jFrameStep {n}] {(toString (← ex.toMessageData.toString)).take 300}"
      s.restore
  throwError "jFrameStep: no frame lemma applies"

/-- The frame step without `jimple.modelContracts`: the premises other than heap agreements by
    assumption, the heap agreements (at least one) unfolded. -/
def jFrameStepAgree : TacticM Unit := do
  let g ← getMainGoal
  let names ← labelled `jframe
  for n in names do
    let s ← saveState
    try
      let gs ← g.apply (← mkConstWithFreshMVarLevels n)
      let mut rest : Array MVarId := #[]
      for g' in gs do
        if ← g'.isAssigned then continue
        let ty ← instantiateMVars (← g'.getType)
        if ty.consumeMData.isAppOfArity ``Agree 2 then rest := rest.push g'
        else g'.assumption
      if rest.isEmpty then throwError "jFrameStep: no heap agreement premise"
      let out ← rest.mapM fun g' => g'.deltaTarget (· == ``Agree)
      replaceMainGoal out.toList
      return
    catch _ => s.restore
  throwError "jFrameStep: no frame lemma applies"

def jFrameStep : TacticM Unit := do
  if jimple.modelContracts.get (← getOptions) then jFrameStepMC else jFrameStepAgree

/-- `StrsAt σ' ys ss` from a hypothesis `StrsAt σ ys ss` with the same lists (the strings of an
    earlier state): what remains is `StrMono σ σ'`, unfolded. -/
def jStrsMono : TacticM Unit := do
  let g ← getMainGoal
  let g' ← g.withContext do
    let tgt := (← instantiateMVars (← g.getType)).consumeMData
    unless tgt.isAppOfArity ``StrsAt 3 do throwError "jStrsMono: not a StrsAt goal"
    let σ' := tgt.getArg! 0
    let ys := tgt.getArg! 1
    let ss := tgt.getArg! 2
    for d in (← getLCtx) do
      if d.isImplementationDetail then continue
      let ty := (← instantiateMVars d.type).consumeMData
      unless ty.isAppOfArity ``StrsAt 3 do continue
      let s ← saveState
      if (← withReducible (isDefEq (ty.getArg! 1) ys)) && (← withReducible (isDefEq (ty.getArg! 2) ss)) then
        let m ← mkFreshExprSyntheticOpaqueMVar (← mkAppM ``StrMono #[ty.getArg! 0, σ'])
        g.assign (← mkAppM ``StrsAt.mono #[d.toExpr, m])
        return [← m.mvarId!.deltaTarget (· == ``StrMono)]
      s.restore
    -- the same references, the texts written differently (`cardLines σ xs i` with `i = n`): the
    -- texts' equation is a goal too
    for d in (← getLCtx) do
      if d.isImplementationDetail then continue
      let ty := (← instantiateMVars d.type).consumeMData
      unless ty.isAppOfArity ``StrsAt 3 do continue
      let s ← saveState
      if ← withReducible (isDefEq (ty.getArg! 1) ys) then
        let he ← mkFreshExprSyntheticOpaqueMVar (← mkEq (ty.getArg! 2) ss)
        let m ← mkFreshExprSyntheticOpaqueMVar (← mkAppM ``StrMono #[ty.getArg! 0, σ'])
        g.assign (← mkAppM ``StrsAt.mono_eq #[d.toExpr, he, m])
        return [he.mvarId!, ← m.mvarId!.deltaTarget (· == ``StrMono)]
      s.restore
    throwError "jStrsMono: no StrsAt hypothesis for these lists"
  replaceMainGoal g'

/-- Constructor equations among the hypotheses (`[v] = [.ref a]`, from a contract's
    `args = [.ref a] → …` introduced before simplification): replaced by the equations of their
    components (`injection`, repeatedly); a mismatch closes the goal. -/
def jInjections : TacticM Unit := do
  let g ← getMainGoal
  let mut g := g
  let mut tried : Std.HashSet FVarId := {}
  for _ in [0:64] do
    let cand ← g.withContext do
      let env ← getEnv
      let isCtorApp (e : Lean.Expr) : Bool := match e.getAppFn with
        | .const c _ => env.isConstructor c
        | _ => false
      for d in (← getLCtx) do
        if d.isImplementationDetail || tried.contains d.fvarId then continue
        let ty := (← instantiateMVars d.type).consumeMData
        let some (_, l, r) := ty.eq? | continue
        if isCtorApp l && isCtorApp r then return some d.fvarId
      return none
    let some fv := cand | break
    tried := tried.insert fv
    let r ← try some <$> Lean.Meta.injection g fv catch _ => pure none
    match r with
    | some .solved => replaceMainGoal []; return
    | some (.subgoal g' _ _) => g := g'
    | none => pure ()
  replaceMainGoal [g]

/-- Context preprocessing: destructure, freshness, collection instantiation, forward
    instantiation, fact unification, substitution. Stops as soon as the goal is closed. -/
def jPrep (extra : Array Ident := #[]) : TacticM Unit := do
  let substVars : TacticM Unit := do evalTactic (← `(tactic| try subst_vars))
  let steps : List (String × TacticM Unit) := [("destruct", jDestruct), ("inj", jInjections),
    ("subst", substVars),
    ("fresh", jFresh), ("instMem", jInstMem), ("destruct", jDestruct), ("forward", jForward),
    ("persistent", jPersistent), ("subFields", jSubFields), ("hypEval", jHypEval extra),
    ("destruct", jDestruct),
    ("forward2", do if jimple.modelContracts.get (← getOptions) then jForward),
    ("shapes", jShapeFields),
    ("frameInst", do if jimple.modelContracts.get (← getOptions) then jFrameInst),
    ("unify", jUnifyFacts), ("destruct", jDestruct), ("subst", substVars), ("fresh", jFresh),
    -- facts destructured after the first unification (e.g. a collection quantifier instantiated
    -- again at the same element) are unified too
    ("unify", jUnifyFacts), ("destruct", jDestruct), ("inj", jInjections), ("subst", substVars),
    ("length", jLengthFacts), ("tmod", jTmodFacts), ("intBounds", jIntBounds), ("pin", jPinInts),
    ("frame", jFrameFacts),
    ("cleanup", jCleanup),
    ("nullSplit", jNullSplit)]
  let tr := jimple.trace.get (← getOptions)
  let dbg := jimple.debug.get (← getOptions)
  for (name, step) in steps do
    if (← getGoals).isEmpty then return
    let t0 ← IO.monoMsNow
    if dbg then dbgOut s!"[jprep {t0} ms] {name}"
    try step
    finally
      if tr then
        let dt := (← IO.monoMsNow) - t0
        if dt > 1000 then logInfo m!"jvc: preprocessing step {name} took {dt} ms"

/-- The verification condition loop on one goal; returns the goals it could not close. -/
partial def jvcGoal (extra : Array Ident) (fuel : Nat) (g : MVarId) (reprep : Bool := true) :
    TacticM (List MVarId) := do
  if fuel = 0 then
    if jimple.trace.get (← getOptions) then logInfo m!"jvc: out of fuel"
    return [g]
  -- trivial goals (`… → x = x`, a hypothesis restated) close at once
  if jimple.debug.get (← getOptions) then dbgOut s!"[jvc {(← IO.monoMsNow)} ms fuel {fuel}] enter"
  let isSymb ← isSymbolicGoal g
  if !isSymb then
    let closeTriv : TacticM Unit := do
      evalTactic (← `(tactic| intros))
      evalTactic (← `(tactic| try subst_vars))
      evalTactic (← `(tactic| first | rfl | assumption |
        (simp_all [-BitVec.toInt_xor, -BitVec.toInt_and, -BitVec.toInt_or]; done)))
    if ← tryClose g closeTriv 50000 then
      return []
  -- one preparation pass: expand the cut list `∀ p ∈ inst…` into one obligation per cut point,
  -- introduce and preprocess the context; then split a conjunction (each part is simplified on
  -- its own) or take a symbolic execution step
  let extraL : Array (TSyntax `Lean.Parser.Tactic.simpLemma) ←
    extra.mapM fun i => `(Lean.Parser.Tactic.simpLemma| $i:ident)
  let dbg := jimple.debug.get (← getOptions)
  let say (msg : String) : TacticM Unit := do
    if dbg then dbgOut s!"[jvc {(← IO.monoMsNow)} ms fuel {fuel}] {msg}"
  let prepStep : TacticM Bool := do
    say "cut list"
    evalTactic (← `(tactic| try simp only [Invariants.inst, List.map_cons, List.map_nil,
      List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, forall_const, and_true,
      $extraL,*]))
    if (← getGoals).isEmpty then return true
    evalTactic (← `(tactic| intros))
    jFoldCuts
    say "prep"
    jPrep extra
    if (← getGoals).length != 1 then return true
    let t ← instantiateMVars (← getMainTarget)
    if t.consumeMData.isAppOfArity ``And 2 then
      evalTactic (← `(tactic| constructor))
      return true
    say "jsym"
    let gBefore ← getMainGoal
    if dbg && jimple.dumpFuel.get (← getOptions) == fuel then
      let pp := toString (← gBefore.withContext do ppGoal gBefore)
      dbgOut s!"[jvc goal before jsym at fuel {fuel}]\n{pp.take 60000}"
    let t0 ← IO.monoMsNow
    jsym extra
    say "jsym done"
    if dbg && (← IO.monoMsNow) - t0 > 20000 then
      -- a slow step: the goal it started from
      let pp := toString (← gBefore.withContext do ppGoal gBefore)
      dbgOut s!"[jvc slow jsym, goal before]\n{pp.take 30000}"
    return false
  let some (isSplit, gs) ← tryOnR g prepStep
    | do
      if jimple.trace.get (← getOptions) then logInfo m!"jvc: first step failed at fuel {fuel}"
      return [g]
  if isSplit then
    let mut out := []
    for h in gs do out := out ++ (← jvcGoal extra (fuel - 1) h)
    return out
  let mut out := []
  for g' in gs do
    say s!"after step: {gs.length} goal(s); prune"
    -- prune infeasible branches early (contradictory arithmetic hypotheses)
    if ← tryClose g' (do jExfalso; evalTactic (← `(tactic| jomega))) 20000 then
      continue
    say "classify"
    let isAnd ← g'.withContext do return (← instantiateMVars (← g'.getType)).consumeMData.isAppOfArity ``And 2
    if isAnd then
      if let some gs' ← tryOn g' (evalTactic (← `(tactic| constructor))) then
        for h in gs' do out := out ++ (← jvcGoal extra (fuel - 1) h)
        continue
    -- implications produced by simplification: introduce and simplify again
    let isPi ← g'.withContext do return (← instantiateMVars (← g'.getType)).consumeMData.isForall
    if isPi then
      out := out ++ (← jvcGoal extra (fuel - 1) g')
      continue
    let symb ← isSymbolicGoal g'
    say s!"symbolic {symb}"
    if !symb then
      -- existential goals: instantiate from an equation, then continue
      if let some gs' ← tryOn g' (do unless ← jExists do throwError "no witness") then
        for h in gs' do out := out ++ (← jvcGoal extra (fuel - 1) h)
        continue
      -- strings of an earlier state (`StrsAt`): they are still there
      if let some gs' ← tryOn g' jStrsMono then
        for h in gs' do out := out ++ (← jvcGoal extra (fuel - 1) h)
        continue
      -- facts and values of an earlier state (`jframe` lemmas)
      if let some gs' ← tryOn g' jFrameStep then
        for h in gs' do out := out ++ (← jvcGoal extra (fuel - 1) h)
        continue
      -- method lookups in classes known by their shape (`staticDecl`, …) left in a leaf
      if let some (true, [g'']) ← tryOnR g' jShapeMethods then
        out := out ++ (← jvcGoal extra (fuel - 1) g'')
        continue
      if ← jautoOn g' then continue
    let mut g' := g'
    if symb && reprep then
      -- the step may have exposed new element accesses, lengths or remainders: their facts can
      -- unblock evaluation (the rest of the context is unchanged since the preparation pass)
      let tBefore ← instantiateMVars (← g'.getType)
      if let some (added, gs') ← tryOnR g' jGoalFacts then
        match gs' with
        | [g''] =>
          g' := g''
          if added then
            if let some gs'' ← tryOn g'' (jsym extra) then
              match gs'' with
              | [g3] =>
                let tAfter ← instantiateMVars (← g3.getType)
                if tAfter != tBefore then
                  -- evaluation progressed with the new facts: continue without re-preprocessing
                  out := out ++ (← jvcGoal extra (fuel - 1) g3 (reprep := false))
                  continue
                g' := g3
              | [] => continue
              | _ =>
                for h in gs'' do out := out ++ (← jvcGoal extra (fuel - 1) h)
                continue
        | [] => continue
        | _ =>
          for h in gs' do out := out ++ (← jvcGoal extra (fuel - 1) h)
          continue
    if symb then
      if let some gs' ← splitSwitchIndex g' then
        for h in gs' do out := out ++ (← jvcGoal extra (fuel - 1) h)
        continue
    if let some gs' ← splitBlocker g' symb then
      for h in gs' do
        -- a branch whose condition contradicts the context (e.g. `σ.next = σ.next + 2`) is
        -- closed before simplification (where such an equation would loop as a rewrite rule)
        if ← tryClose h (do jExfalso; evalTactic (← `(tactic| jomega))) 20000 then
          continue
        out := out ++ (← jvcGoal extra (fuel - 1) h)
      continue
    if jimple.trace.get (← getOptions) then
      logInfo m!"jvc: stuck (symbolic := {symb}) at fuel {fuel}"
    if dbg then
      -- the cut facts and the postcondition (large, unchanged since the start) left out
      let g'' ← g'.withContext do
        let fvs := (← getLCtx).foldl (init := #[]) fun acc d =>
          let un := d.userName.eraseMacroScopes
          if un == `hcut || un == `hcutsNone || un == `hpost then acc.push d.fvarId else acc
        try g'.tryClearMany fvs catch _ => pure g'
      let pp := toString (← g''.withContext do ppGoal g'')
      dbgOut s!"[jvc stuck at fuel {fuel}]\n{pp.take 30000}"
    out := out ++ [g']
  return out

/-- Constants to unfold: the heads of the contract, invariant and annotation arguments. -/
def vcConstants (tgt : Lean.Expr) : MetaM (Array Name) := do
  let tgt ← instantiateMVars tgt
  let mut out := #[]
  for a in tgt.getAppArgs do
    if let .const c _ := a.getAppFn then
      let env ← getEnv
      if let some info := env.find? c then
        if info.isDefinition && !(env.isConstructor c) && !(c.isPrefixOf ``Jimple.Program) then
          out := out.push c
  return out

/-- `jvc [f, g]`: symbolic execution and automatic discharge of verification conditions,
    unfolding the given definitions (specifications, invariants) as needed. -/
syntax (name := jvcTac) "jvc" (" [" ident,* "]")? : tactic

/-- Identifiers of an optional `[a, b, c]` argument. -/
def optIdents (s : Syntax) : Array Ident :=
  let s := if s.getNumArgs == 1 then s[0] else s
  if s.getNumArgs == 3 then s[1].getSepArgs.map (⟨·⟩) else #[]

@[tactic jvcTac] def evalJvc : Tactic := fun stx => do
  let extra : Array Ident := optIdents stx[1]
  withJimpleHeartbeats do
  let gs ← getGoals
  let mut out := []
  for g in gs do
    out := out ++ (← jvcGoal extra 400 g)
  setGoals out

/-- `jverify`: prove `MethodVC P Γ d m S A fuel` — selects the body, unfolds the contract and
    the invariants, and runs `jvc`. -/
syntax (name := jverifyTac) "jverify" (" [" ident,* "]")? : tactic

@[tactic jverifyTac] def evalJverify : Tactic := fun stx => do
  let extra : Array Ident := optIdents stx[1]
  let g ← getMainGoal
  let consts ← g.withContext do vcConstants (← g.getType)
  -- skip the program and the method reference (they are evaluated by `jground`)
  let tgt ← instantiateMVars (← g.getType)
  let args := tgt.getAppArgs
  let keep := consts.filter fun c =>
    (args.size == 7) && (match args[4]?.bind (·.getAppFn.constName?) with
      | some s => s == c | none => false) ||
    (match args[5]?.bind (·.getAppFn.constName?) with | some s => s == c | none => false) ||
    (match args[1]?.bind (·.getAppFn.constName?) with | some s => s == c | none => false)
  let ids := keep.map mkIdent ++ extra
  if jimple.trace.get (← getOptions) then logInfo m!"jverify: unfolding {ids}"
  let dbg := jimple.debug.get (← getOptions)
  if dbg then dbgOut s!"[jverify {(← IO.monoMsNow)} ms] select the body"
  withJimpleHeartbeats do
  evalTactic (← `(tactic| refine ⟨_, rfl, ?_⟩))
  if dbg then dbgOut s!"[jverify {(← IO.monoMsNow)} ms] body selected"
  let gs ← getGoals
  if jimple.trace.get (← getOptions) then logInfo m!"jverify: {gs.length} goal(s) after selecting the body"
  let mut out := []
  for g in gs do
    out := out ++ (← jvcGoal ids 400 g)
  setGoals out

end Jimple
