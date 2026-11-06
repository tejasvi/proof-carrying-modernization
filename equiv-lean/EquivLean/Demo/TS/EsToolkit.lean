import EquivLean.Bridge.TS.Sets
import EquivLean.Bridge.TS.Obs
import EquivLean.Demo.Gen.TS.EsDifferenceOld
import EquivLean.Demo.Gen.TS.EsDifferenceNew
import EquivLean.Demo.Gen.TS.EsIntersectionOld
import EquivLean.Demo.Gen.TS.EsIntersectionNew

/-!
# Demo: es-toolkit's `difference` and `intersection` performance commits

Two real commits from the es-toolkit history (sources and `meta.json` in
`examples/ts/es-toolkit/`):

* `4ec747ea` "perf(difference): Optimize `difference` (#27)":
  `firstArr.filter(item => !secondArr.includes(item))` became
  `const secondSet = new Set(secondArr); firstArr.filter(item => !secondSet.has(item))`;
* `576b136a` "perf(intersection): Optimize `intersection` (#47)": the same with `includes`/`has`
  not negated.

`difference_equiv` and `intersection_equiv` prove, for the old and the new function,
`Equiv (ArrObs w.next)` with the old version as the first argument (the shape of
strictts-diff's observational statement): equivalence *modulo fresh allocation*.  The new
version allocates the `Set` (at `w.next`) before the result array (at `w.next + 1`); the old one
allocates only the result (at `w.next`).  So the final worlds differ, but a caller sees the same
cells below `w.next`, the same console output and oracle positions, and a fresh result array
with the same contents (`Bridge/TS/Obs.lean`).  Both use SameValueZero (`includes` and `Set`
keys), so NaN and `±0` behave identically.

Limits of the statement:
* es-toolkit's functions are generic (`<T>`).  The pinned StrictTS translator (a15926a)
  monomorphises generics at their call sites, so each version is translated through an
  agent-written wrapper `differenceNum`/`intersectionNum` (`examples/ts/es-toolkit/*/inst.ts`)
  that instantiates `T := number`.  The theorems are about the monomorphised es-toolkit
  functions `difference<number>`/`intersection<number>`, not about other instances.
* The two argument arrays are cells allocated below `w.next` (the caller's allocation
  counter), with any contents; they may be the same array (aliasing is allowed).  No length
  bound is needed.
-/

namespace EquivLean.Demo.TS.EsToolkit
open EquivLean EquivLean.TS StrictTS JS
open EquivLean.Demo.Gen.TS

abbrev TT := EsDifferenceOld.TT

/-- SameValueZero membership, the meaning of `ys.includes(x)`. -/
def svzIn (ys : Array (Val TT .num)) (x : Val TT .num) : Bool :=
  ys.any (fun y => Conv.svz .num y x)

/-- The set built by `new Set(ys)`. -/
abbrev setOf (ys : Array (Val TT .num)) : JSMap (Val TT .num) Unit :=
  ys.foldl (fun (m : JSMap (Val TT .num) Unit) y => m.set (Conv.svz .num) (normKey .num y) ()) {}

theorem setOf_has (ys : Array (Val TT .num)) (x : Val TT .num) :
    (setOf ys).has (Conv.svz .num) x = svzIn ys x :=
  setOfArr_has_num ys x

/-! ## `difference` (4ec747ea) -/

theorem differenceOld_spec (I : Impl) (w : World TT) (a0 a1 : Nat) (xs ys : Array (Val TT .num))
    (hw0 : w.heap.get? (.arr .num, a0) = some xs) (hn0 : a0 < w.next)
    (hw1 : w.heap.get? (.arr .num, a1) = some ys) (hn1 : a1 < w.next) :
    JS.exec (callFun I EsDifferenceOld.program EsDifferenceOld.difference_numberRef
        (.cons (.arr a0) (.cons (.arr a1) .nil))) w =
      some (.ok (.arr w.next), { w with
        heap := w.heap.insert (.arr .num, w.next) (xs.filter (fun x => !svzIn ys x)),
        next := w.next + 1 }) := by
  rw [EsDifferenceOld.difference_number_call]
  simp only [EsDifferenceOld.difference_numberDef, ts_sym]
  rw [arrFilter_pure_at I _ a0 xs _ (fun x => .bool (!svzIn ys x)) w hw0 (by omega)]
  · simp [ts_sym]
  · intro vs
    match vs with
    | .cons x (.cons i (.cons arr .nil)) =>
      have h1 : (w.heap.insert (.arr .num, w.next) (#[] : Array (Val TT .num))).get?
          (.arr .num, a1) = some ys := by
        rw [heap_get_insert_addr_ne _ _ _ _ (by omega)]; exact hw1
      simp [ts_sym, h1, svzIn, Ty.eqable]

theorem differenceNew_spec (I : Impl) (w : World TT) (a0 a1 : Nat) (xs ys : Array (Val TT .num))
    (hw0 : w.heap.get? (.arr .num, a0) = some xs) (hn0 : a0 < w.next)
    (hw1 : w.heap.get? (.arr .num, a1) = some ys) (_hn1 : a1 < w.next) :
    JS.exec (callFun I EsDifferenceNew.program EsDifferenceNew.difference_numberRef
        (.cons (.arr a0) (.cons (.arr a1) .nil))) w =
      some (.ok (.arr (w.next + 1)), { w with
        heap := (w.heap.insert (.set .num, w.next) (setOf ys)).insert (.arr .num, w.next + 1)
          (xs.filter (fun x => !(setOf ys).has (Conv.svz .num) x)),
        next := w.next + 1 + 1 }) := by
  rw [EsDifferenceNew.difference_number_call]
  simp only [EsDifferenceNew.difference_numberDef, ts_sym, hw1]
  rw [arrFilter_pure_at I _ a0 xs _ (fun x => .bool (!(setOf ys).has (Conv.svz .num) x)) _
    (by simp [hw0]) (by simp; omega)]
  · -- `ts_sym` unfolds `normKey` inside the fold: unfold `setOf` the same way
    simp [ts_sym, setOf]
  · intro vs
    match vs with
    | .cons x (.cons i (.cons arr .nil)) => simp [ts_sym, setOf]

/-- **es-toolkit 4ec747ea (`difference`)**: the old (`includes`) and the new (`Set.has`)
version at `T := number` are equivalent modulo fresh allocation, for all argument arrays
allocated below `w.next` (possibly the same array) and every world. -/
theorem difference_equiv (I : Impl) (w : World TT) (a0 a1 : Nat) (xs ys : Array (Val TT .num))
    (hw0 : w.heap.get? (.arr .num, a0) = some xs) (hn0 : a0 < w.next)
    (hw1 : w.heap.get? (.arr .num, a1) = some ys) (hn1 : a1 < w.next) :
    Equiv (ArrObs w.next)
      (JS.exec (callFun I EsDifferenceOld.program EsDifferenceOld.difference_numberRef
        (.cons (.arr a0) (.cons (.arr a1) .nil))) w)
      (JS.exec (callFun I EsDifferenceNew.program EsDifferenceNew.difference_numberRef
        (.cons (.arr a0) (.cons (.arr a1) .nil))) w) := by
  refine equiv_arrObs_of_runs (differenceOld_spec I w a0 a1 xs ys hw0 hn0 hw1 hn1)
    (differenceNew_spec I w a0 a1 xs ys hw0 hn0 hw1 hn1) ?_
  refine arrObs_of_specs (w := w) (xs := xs.filter (fun x => !svzIn ys x)) ?_ ?_
    (Nat.le_refl _) (Nat.le_succ _) (by simp) ?_
  · exact (WorldObs.refl _ w).insert_fresh (k := .arr .num) _ (Nat.le_refl _)
  · exact ((WorldObs.refl _ w).insert_fresh (k := .set .num) _ (Nat.le_refl _)).insert_fresh
      (k := .arr .num) _ (Nat.le_succ _)
  · simp only [setOf_has, heap_get_insert_self]

/-! ## `intersection` (576b136a) -/

theorem intersectionOld_spec (I : Impl) (w : World TT) (a0 a1 : Nat) (xs ys : Array (Val TT .num))
    (hw0 : w.heap.get? (.arr .num, a0) = some xs) (hn0 : a0 < w.next)
    (hw1 : w.heap.get? (.arr .num, a1) = some ys) (hn1 : a1 < w.next) :
    JS.exec (callFun I EsIntersectionOld.program EsIntersectionOld.intersection_numberRef
        (.cons (.arr a0) (.cons (.arr a1) .nil))) w =
      some (.ok (.arr w.next), { w with
        heap := w.heap.insert (.arr .num, w.next) (xs.filter (fun x => svzIn ys x)),
        next := w.next + 1 }) := by
  rw [EsIntersectionOld.intersection_number_call]
  simp only [EsIntersectionOld.intersection_numberDef, ts_sym]
  rw [arrFilter_pure_at I _ a0 xs _ (fun x => .bool (svzIn ys x)) w hw0 (by omega)]
  · simp [ts_sym]
  · intro vs
    match vs with
    | .cons x (.cons i (.cons arr .nil)) =>
      have h1 : (w.heap.insert (.arr .num, w.next) (#[] : Array (Val TT .num))).get?
          (.arr .num, a1) = some ys := by
        rw [heap_get_insert_addr_ne _ _ _ _ (by omega)]; exact hw1
      simp [ts_sym, h1, svzIn, Ty.eqable]

theorem intersectionNew_spec (I : Impl) (w : World TT) (a0 a1 : Nat) (xs ys : Array (Val TT .num))
    (hw0 : w.heap.get? (.arr .num, a0) = some xs) (hn0 : a0 < w.next)
    (hw1 : w.heap.get? (.arr .num, a1) = some ys) (_hn1 : a1 < w.next) :
    JS.exec (callFun I EsIntersectionNew.program EsIntersectionNew.intersection_numberRef
        (.cons (.arr a0) (.cons (.arr a1) .nil))) w =
      some (.ok (.arr (w.next + 1)), { w with
        heap := (w.heap.insert (.set .num, w.next) (setOf ys)).insert (.arr .num, w.next + 1)
          (xs.filter (fun x => (setOf ys).has (Conv.svz .num) x)),
        next := w.next + 1 + 1 }) := by
  rw [EsIntersectionNew.intersection_number_call]
  simp only [EsIntersectionNew.intersection_numberDef, ts_sym, hw1]
  rw [arrFilter_pure_at I _ a0 xs _ (fun x => .bool ((setOf ys).has (Conv.svz .num) x)) _
    (by simp [hw0]) (by simp; omega)]
  · simp [ts_sym, setOf]
  · intro vs
    match vs with
    | .cons x (.cons i (.cons arr .nil)) => simp [ts_sym, setOf]

/-- **es-toolkit 576b136a (`intersection`)**: the old (`includes`) and the new (`Set.has`)
version at `T := number` are equivalent modulo fresh allocation, for all argument arrays
allocated below `w.next` (possibly the same array) and every world. -/
theorem intersection_equiv (I : Impl) (w : World TT) (a0 a1 : Nat) (xs ys : Array (Val TT .num))
    (hw0 : w.heap.get? (.arr .num, a0) = some xs) (hn0 : a0 < w.next)
    (hw1 : w.heap.get? (.arr .num, a1) = some ys) (hn1 : a1 < w.next) :
    Equiv (ArrObs w.next)
      (JS.exec (callFun I EsIntersectionOld.program EsIntersectionOld.intersection_numberRef
        (.cons (.arr a0) (.cons (.arr a1) .nil))) w)
      (JS.exec (callFun I EsIntersectionNew.program EsIntersectionNew.intersection_numberRef
        (.cons (.arr a0) (.cons (.arr a1) .nil))) w) := by
  refine equiv_arrObs_of_runs (intersectionOld_spec I w a0 a1 xs ys hw0 hn0 hw1 hn1)
    (intersectionNew_spec I w a0 a1 xs ys hw0 hn0 hw1 hn1) ?_
  refine arrObs_of_specs (w := w) (xs := xs.filter (fun x => svzIn ys x)) ?_ ?_
    (Nat.le_refl _) (Nat.le_succ _) (by simp) ?_
  · exact (WorldObs.refl _ w).insert_fresh (k := .arr .num) _ (Nat.le_refl _)
  · exact ((WorldObs.refl _ w).insert_fresh (k := .set .num) _ (Nat.le_refl _)).insert_fresh
      (k := .arr .num) _ (Nat.le_succ _)
  · simp only [setOf_has, heap_get_insert_self]

end EquivLean.Demo.TS.EsToolkit
