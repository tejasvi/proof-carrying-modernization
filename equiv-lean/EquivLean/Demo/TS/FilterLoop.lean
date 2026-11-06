import EquivLean.Bridge.TS.Obs
import EquivLean.Bridge.TS.Corr
import EquivLean.Bridge.TS.Tactic
import EquivLean.Demo.Gen.TS.PosOld
import EquivLean.Demo.Gen.TS.PosNew

/-!
# Demo: `filter` + `map` refactored into one loop (fresh allocation differs)

`examples/ts/pos_old.ts`: `xs.filter((x) => x > 0).map((x) => 2 * x)`, two allocations (the
filtered array at `next`, the result at `next + 1`);
`examples/ts/pos_new.ts`: one `for … of` loop pushing `2 * x` for every `x > 0` into a fresh
`out` array (one allocation, the result at `next`).  Both translated by the pinned StrictTS
front end (`Gen/TS/PosOld.lean`, `Gen/TS/PosNew.lean`).

`doublePositives_equiv`: the two versions are equivalent modulo fresh allocation
(`ArrObs w.next`: same caller-visible cells and console, fresh results with the same contents
`(xs.filter pos).map dbl`), for every array of numbers (NaN, ±0 included) at a caller address.
`doublePositives_runs_differ`: equality of outcomes fails (different result addresses).
The old version is computed with `arrFilter_pure` (Bridge/TS/Corr.lean) and StrictTS's
`arrMap_pure'`; the loop with StrictTS's index invariant rule (`ts_forof`).
-/

namespace EquivLean.Demo.TS.FilterLoop
open EquivLean EquivLean.TS StrictTS JS
open EquivLean.Demo.Gen.TS

abbrev TT := PosOld.TT

/-- The filter predicate `x > 0` and the map `2 * x` (IEEE semantics). -/
def pos (v : Val TT .num) : Bool := v.toNum.gt (F64.ofNat 0)
def dbl (v : Val TT .num) : Val TT .num := .num (F64.ofNat 2 * v.toNum)

theorem posOld_spec (I : Impl) (a : Nat) (xs : Array (Val TT .num)) (w : World TT)
    (hw : w.heap.get? (.arr .num, a) = some xs) (ha : a < w.next) :
    JS.exec (callFun I PosOld.program PosOld.doublePositivesRef (.cons (.arr a) .nil)) w =
      some (.ok (.arr (w.next + 1)), { w with
        heap := (w.heap.insert (.arr .num, w.next) (xs.filter pos)).insert (.arr .num, w.next + 1)
          ((xs.filter pos).map dbl),
        next := w.next + 1 + 1 }) := by
  rw [PosOld.doublePositives_call]
  simp only [PosOld.doublePositivesDef, ts_sym]
  rw [arrFilter_pure I _ a xs _ pos _ w hw (by omega)]
  · simp only [ts_sym]
    rw [arrMap_pure' I _ w.next (xs.filter pos) _ dbl _
      { w with heap := w.heap.insert (.arr .num, w.next) (xs.filter pos), next := w.next + 1 }
      (by simp) (by simp)]
    · simp only [ts_sym]
    · intro vs w'
      match vs with
      | .cons x (.cons i (.cons arr .nil)) => simp [ts_sym, dbl]
  · intro vs w'
    match vs with
    | .cons x (.cons i (.cons arr .nil)) => simp [ts_sym, pos]

theorem posNew_spec (I : Impl) (a : Nat) (xs : Array (Val TT .num)) (w : World TT)
    (hw : w.heap.get? (.arr .num, a) = some xs) (ha : a < w.next) :
    JS.exec (callFun I PosNew.program PosNew.doublePositivesRef (.cons (.arr a) .nil)) w =
      some (.ok (.arr w.next), { w with
        heap := w.heap.insert (.arr .num, w.next) ((xs.filter pos).map dbl),
        next := w.next + 1 }) := by
  rw [PosNew.doublePositives_call]
  simp only [PosNew.doublePositivesDef, ts_sym, Vals.toList]
  ts_forof xs using (fun i env w₁ => env = .cons (.arr w.next) (.cons (.arr a) .nil) ∧
    w₁ = { w with
      heap := w.heap.insert (.arr .num, w.next) (((xs.toList.take i).filter pos).map dbl).toArray,
      next := w.next + 1 })
  case cell =>
    rintro i env w₁ ⟨-, rfl⟩
    rw [heap_get_insert_addr_ne _ _ _ _ (by omega)]; exact hw
  case step =>
    rintro i env w₁ hi ⟨rfl, rfl⟩
    obtain ⟨x, hx⟩ : ∃ x, xs[i] = Val.num x := ⟨_, (Val.num_toNum _).symm⟩
    have htake : xs.toList.take (i + 1) = xs.toList.take i ++ [Val.num x] := by
      rw [List.take_add_one, List.getElem?_eq_getElem (by simpa using hi)]; simp [hx]
    by_cases hp : x.gt (F64.ofNat 0) = true
    · simp [ts_sym, hx, hp, htake, pos, dbl]
    · simp [ts_sym, hx, hp, htake, pos]
  case init => exact ⟨rfl, by simp⟩
  obtain ⟨rfl, rfl⟩ := hinv
  have harr : ((xs.toList.filter pos).map dbl).toArray = (xs.filter pos).map dbl := by
    apply Array.ext'; simp
  have htake : xs.toList.take xs.size = xs.toList := List.take_of_length_le (by simp)
  simp [ts_sym, htake, harr]
/-- **filter + map ≈ loop with push**, modulo fresh allocation. -/
theorem doublePositives_equiv (I : Impl) (a : Nat) (xs : Array (Val TT .num)) (w : World TT)
    (hw : w.heap.get? (.arr .num, a) = some xs) (ha : a < w.next) :
    Equiv (ArrObs w.next)
      (call I PosNew.program PosNew.doublePositivesRef (.cons (.arr a) .nil) w)
      (call I PosOld.program PosOld.doublePositivesRef (.cons (.arr a) .nil) w) := by
  refine equiv_arrObs_of_runs (posNew_spec I a xs w hw ha) (posOld_spec I a xs w hw ha) ?_
  refine arrObs_of_specs (w := w) (xs := (xs.filter pos).map dbl) ?_ ?_
    (Nat.le_refl _) (Nat.le_succ _) (by simp) (by simp)
  · exact (WorldObs.refl _ w).insert_fresh (k := .arr .num) _ (Nat.le_refl _)
  · exact ((WorldObs.refl _ w).insert_fresh (k := .arr .num) _ (Nat.le_refl _)).insert_fresh
      (k := .arr .num) _ (Nat.le_succ _)

/-- The runs are not equal: the results live at different addresses. -/
theorem doublePositives_runs_differ (I : Impl) (a : Nat) (xs : Array (Val TT .num))
    (w : World TT) (hw : w.heap.get? (.arr .num, a) = some xs) (ha : a < w.next) :
    call I PosNew.program PosNew.doublePositivesRef (.cons (.arr a) .nil) w ≠
      call I PosOld.program PosOld.doublePositivesRef (.cons (.arr a) .nil) w := by
  simp only [call, posNew_spec I a xs w hw ha, posOld_spec I a xs w hw ha, ne_eq,
    Option.some.injEq, Prod.mk.injEq, Except.ok.injEq, Val.arr.injEq]
  omega

end EquivLean.Demo.TS.FilterLoop
