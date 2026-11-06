import EquivLean.Bridge.TS.Obs
import EquivLean.Bridge.TS.Tactic
import EquivLean.Demo.Gen.TS.ScaleOld
import EquivLean.Demo.Gen.TS.ScaleNew

/-!
# Demo: a refactoring that allocates differently (map fusion), modulo fresh allocation

`examples/ts/scale_old.ts`: `xs.map((x) => x + 1).map((x) => 2 * x)` (two allocations: an
intermediate array at `next`, the result at `next + 1`);
`examples/ts/scale_new.ts`: `xs.map((x) => 2 * (x + 1))` (one allocation, the result at
`next`).  Both translated by the pinned StrictTS front end (`Gen/TS/ScaleOld.lean`,
`Gen/TS/ScaleNew.lean`).

The two runs are *not* equal (`scale_runs_differ`: different result addresses, allocation
counters and heaps), but a caller cannot tell them apart: `scale_equiv` proves
`Equiv (ArrObs w.next)`, i.e. the same caller-visible cells and console, and fresh result arrays
with the same contents (`Bridge/TS/Obs.lean`).  The proof goes through one functional
specification per version (`scaleOld_spec`, `scaleNew_spec`, from StrictTS's `arrMap_pure'`).
-/

namespace EquivLean.Demo.TS.ScaleFresh
open EquivLean EquivLean.TS StrictTS JS
open EquivLean.Demo.Gen.TS

abbrev TT := ScaleOld.TT

def inc (v : Val TT .num) : Val TT .num := .num (v.toNum + 1)
def dbl (v : Val TT .num) : Val TT .num := .num (2 * v.toNum)

theorem scaleOld_spec (I : Impl) (a : Nat) (xs : Array (Val TT .num)) (w : World TT)
    (hw : w.heap.get? (.arr .num, a) = some xs) (ha : a < w.next) :
    JS.exec (callFun I ScaleOld.program ScaleOld.scaleRef (.cons (.arr a) .nil)) w =
      some (.ok (.arr (w.next + 1)), { w with
        heap := (w.heap.insert (.arr .num, w.next) (xs.map inc)).insert (.arr .num, w.next + 1)
          ((xs.map inc).map dbl),
        next := w.next + 1 + 1 }) := by
  rw [ScaleOld.scale_call]
  simp only [ScaleOld.scaleDef, ts_sym]
  rw [arrMap_pure' I _ a xs _ inc _ w hw (by omega)]
  · simp only [ts_sym]
    rw [arrMap_pure' I _ w.next (xs.map inc) _ dbl _
      { w with heap := w.heap.insert (.arr .num, w.next) (xs.map inc), next := w.next + 1 }
      (by simp) (by simp)]
    · simp only [ts_sym]
    · intro vs w'
      match vs with
      | .cons x (.cons i (.cons arr .nil)) => simp [ts_sym, dbl]
  · intro vs w'
    match vs with
    | .cons x (.cons i (.cons arr .nil)) => simp [ts_sym, inc]

theorem scaleNew_spec (I : Impl) (a : Nat) (xs : Array (Val TT .num)) (w : World TT)
    (hw : w.heap.get? (.arr .num, a) = some xs) (ha : a < w.next) :
    JS.exec (callFun I ScaleNew.program ScaleNew.scaleRef (.cons (.arr a) .nil)) w =
      some (.ok (.arr w.next), { w with
        heap := w.heap.insert (.arr .num, w.next) (xs.map (fun v => dbl (inc v))),
        next := w.next + 1 }) := by
  rw [ScaleNew.scale_call]
  simp only [ScaleNew.scaleDef, ts_sym]
  rw [arrMap_pure' I _ a xs _ (fun v => dbl (inc v)) _ w hw (by omega)]
  · simp only [ts_sym]
  · intro vs w'
    match vs with
    | .cons x (.cons i (.cons arr .nil)) => simp [ts_sym, inc, dbl]

/-- **Map fusion is invisible to callers**: for every array `xs` at a caller address `a` and
every world, the new and old `scale` are equivalent modulo fresh allocation. -/
theorem scale_equiv (I : Impl) (a : Nat) (xs : Array (Val TT .num)) (w : World TT)
    (hw : w.heap.get? (.arr .num, a) = some xs) (ha : a < w.next) :
    Equiv (ArrObs w.next) (call I ScaleNew.program ScaleNew.scaleRef (.cons (.arr a) .nil) w)
      (call I ScaleOld.program ScaleOld.scaleRef (.cons (.arr a) .nil) w) := by
  refine equiv_arrObs_of_runs (scaleNew_spec I a xs w hw ha) (scaleOld_spec I a xs w hw ha) ?_
  refine arrObs_of_specs (w := w) (xs := xs.map (fun v => dbl (inc v))) ?_ ?_
    (Nat.le_refl _) (Nat.le_succ _) (by simp) ?_
  · exact (WorldObs.refl _ w).insert_fresh (k := .arr .num) _ (Nat.le_refl _)
  · exact ((WorldObs.refl _ w).insert_fresh (k := .arr .num) _ (Nat.le_refl _)).insert_fresh
      (k := .arr .num) _ (Nat.le_succ _)
  · simp [Array.map_map, Function.comp_def]

/-- … although the runs differ (result address, allocation counter, heap): equality of
outcomes, the default relation, does not hold. -/
theorem scale_runs_differ (I : Impl) (a : Nat) (xs : Array (Val TT .num)) (w : World TT)
    (hw : w.heap.get? (.arr .num, a) = some xs) (ha : a < w.next) :
    call I ScaleNew.program ScaleNew.scaleRef (.cons (.arr a) .nil) w ≠
      call I ScaleOld.program ScaleOld.scaleRef (.cons (.arr a) .nil) w := by
  simp only [call, scaleNew_spec I a xs w hw ha, scaleOld_spec I a xs w hw ha, ne_eq,
    Option.some.injEq, Prod.mk.injEq, Except.ok.injEq, Val.arr.injEq]
  omega

end EquivLean.Demo.TS.ScaleFresh
