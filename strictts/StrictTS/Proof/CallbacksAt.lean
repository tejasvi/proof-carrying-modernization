/-
StrictTS proof layer: array callbacks that read the heap.

`arrFilter_pure'` and its siblings (Arrays.lean) need a callback that is pure in every world
(`PureFn`). A callback that reads a cell (`ys.every(…)` inside a `filter` callback, a `Set` it
looks up) is pure only in the worlds where that cell holds what it holds. These methods call
their callback in one world: the call's world, or for `filter` the world after the result array
is allocated. Purity in that world is enough, so these variants take
`∀ vs, exec (applyFn I P f vs) w = some (.ok (g vs.a0), w)` for that world only (`ts_callbacks`
falls back to them when the callback is not pure in every world).
-/
import StrictTS.Proof.Arrays

namespace StrictTS
open JS

variable {TT : TypeTable}

/-- `arr.filter(f)` with a callback that is pure in the world after the result array is
allocated. -/
theorem arrFilter_pureAt (I : Impl) (P : Program TT) {t : Ty} (a : Nat) (xs : Array (Val TT t))
    (f : Val TT (.fn (.cons t (.cons .num (.cons (.arr t) .nil))) .bool))
    (g : Val TT t → Val TT .bool) (w : World TT)
    (hf : ∀ vs, exec (applyFn I P f vs)
        { w with heap := w.heap.insert (.arr t, w.next) (#[] : Array (Val TT t)), next := w.next + 1 } =
      some (.ok (g vs.a0),
        { w with heap := w.heap.insert (.arr t, w.next) (#[] : Array (Val TT t)), next := w.next + 1 }))
    (hw : w.heap.get? (.arr t, a) = some xs) (ha : a ≠ w.next) :
    exec (evalBuiltin I P (.arrFilter t) (.cons (.arr a) (.cons f .nil))) w =
      some (.ok (.arr w.next), { w with
        heap := w.heap.insert (.arr t, w.next) (xs.filter (fun x => (g x).toBool)),
        next := w.next + 1 }) := by
  rw [evalBuiltin.eq_def]
  simp only [exec_bind, exec_readArr, hw, Vals.a0_cons, Vals.a1_cons, Val.arrAddr_arr, exec_alloc]
  have hw1 : (w.heap.insert (.arr t, w.next) (#[] : Array (Val TT t))).get? (.arr t, a) = some xs := by
    rw [heap_get_insert_addr_ne _ _ _ _ (Ne.symm ha), hw]
  rw [foldlM_range_pure' xs _ (fun acc x => if (g x).toBool = true then acc.push x else acc) _]
  · rw [foldl_push_filter]
    simp only [exec_writeArr, heap_insert_insert, exec_pure, Array.empty_append, toArray_filter_toList]
  · intro acc k hk
    simp only [exec_bind, exec_readArr, hw1, hk, dite_true]
    rw [hf]; simp

/-- `arr.map(f)` with a callback that is pure in the world after the result array is
allocated. -/
theorem arrMap_pureAt (I : Impl) (P : Program TT) {t u : Ty} (a : Nat) (xs : Array (Val TT t))
    (f : Val TT (.fn (.cons t (.cons .num (.cons (.arr t) .nil))) u))
    (g : Val TT t → Val TT u) (w : World TT)
    (hf : ∀ vs, exec (applyFn I P f vs)
        { w with heap := w.heap.insert (.arr u, w.next) (#[] : Array (Val TT u)), next := w.next + 1 } =
      some (.ok (g vs.a0),
        { w with heap := w.heap.insert (.arr u, w.next) (#[] : Array (Val TT u)), next := w.next + 1 }))
    (hw : w.heap.get? (.arr t, a) = some xs) (ha : a ≠ w.next) :
    exec (evalBuiltin I P (.arrMap t u) (.cons (.arr a) (.cons f .nil))) w =
      some (.ok (.arr w.next), { w with
        heap := w.heap.insert (.arr u, w.next) (xs.map g),
        next := w.next + 1 }) := by
  rw [evalBuiltin.eq_def]
  simp only [exec_bind, exec_readArr, hw, Vals.a0_cons, Vals.a1_cons, Val.arrAddr_arr, exec_alloc]
  have hw1 : (w.heap.insert (.arr u, w.next) (#[] : Array (Val TT u))).get? (.arr t, a) = some xs := by
    rw [heap_get_insert_addr_ne _ _ _ _ (Ne.symm ha), hw]
  rw [foldlM_pure (List.range xs.size) _
    (fun acc k => if h : k < xs.size then acc.push (g xs[k]) else acc) _]
  · simp only [exec_writeArr, foldl_range_push xs (fun x _ => g x), heap_insert_insert, exec_pure,
      mapIdx_const]
  · intro acc k _
    simp only [exec_bind, exec_readArr, hw1]
    split
    · rw [exec_bind, hf]; rfl
    · exfalso; simp_all [List.mem_range]

/-- `arr.some(f)` with a callback that is pure in the call's world. -/
theorem arrSome_pureAt (I : Impl) (P : Program TT) {t : Ty} (a : Nat) (xs : Array (Val TT t))
    (f : Val TT (.fn (.cons t (.cons .num (.cons (.arr t) .nil))) .bool))
    (g : Val TT t → Val TT .bool) (w : World TT)
    (hf : ∀ vs, exec (applyFn I P f vs) w = some (.ok (g vs.a0), w))
    (hw : w.heap.get? (.arr t, a) = some xs) :
    exec (evalBuiltin I P (.arrSome t) (.cons (.arr a) (.cons f .nil))) w =
      some (.ok (.bool (xs.any (fun x => (g x).toBool))), w) := by
  rw [evalBuiltin.eq_def]
  simp only [exec_bind, exec_readArr, hw, Vals.a0_cons, Vals.a1_cons, Val.arrAddr_arr]
  rw [foldlM_range_pure' xs _ (fun st x => st || (g x).toBool) w]
  · rw [foldl_or_any]; simp
  · intro st k hk
    cases st
    · simp only [Bool.false_eq_true, ite_false, exec_bind, exec_readArr, hw, hk, dite_true]
      rw [hf]; simp
    · simp

/-- `arr.every(f)` with a callback that is pure in the call's world. -/
theorem arrEvery_pureAt (I : Impl) (P : Program TT) {t : Ty} (a : Nat) (xs : Array (Val TT t))
    (f : Val TT (.fn (.cons t (.cons .num (.cons (.arr t) .nil))) .bool))
    (g : Val TT t → Val TT .bool) (w : World TT)
    (hf : ∀ vs, exec (applyFn I P f vs) w = some (.ok (g vs.a0), w))
    (hw : w.heap.get? (.arr t, a) = some xs) :
    exec (evalBuiltin I P (.arrEvery t) (.cons (.arr a) (.cons f .nil))) w =
      some (.ok (.bool (xs.all (fun x => (g x).toBool))), w) := by
  rw [evalBuiltin.eq_def]
  simp only [exec_bind, exec_readArr, hw, Vals.a0_cons, Vals.a1_cons, Val.arrAddr_arr]
  rw [foldlM_range_pure' xs _ (fun st x => st && (g x).toBool) w]
  · rw [foldl_and_all]; simp
  · intro st k hk
    cases st
    · simp
    · simp only [Bool.not_true, Bool.false_eq_true, ite_false, exec_bind, exec_readArr, hw, hk, dite_true]
      rw [hf]; simp

/-- `arr.find(f)` with a callback that is pure in the call's world. -/
theorem arrFind_pureAt (I : Impl) (P : Program TT) {t : Ty} (a : Nat) (xs : Array (Val TT t))
    (f : Val TT (.fn (.cons t (.cons .num (.cons (.arr t) .nil))) .bool))
    (g : Val TT t → Val TT .bool) (w : World TT)
    (hf : ∀ vs, exec (applyFn I P f vs) w = some (.ok (g vs.a0), w))
    (hw : w.heap.get? (.arr t, a) = some xs) :
    exec (evalBuiltin I P (.arrFind t) (.cons (.arr a) (.cons f .nil))) w =
      some (.ok ((xs.find? (fun x => (g x).toBool)).elim .none .some), w) := by
  rw [evalBuiltin.eq_def]
  simp only [exec_bind, exec_readArr, hw, Vals.a0_cons, Vals.a1_cons, Val.arrAddr_arr]
  rw [foldlM_range_pure' xs _ (fun st x => st.or (if (g x).toBool = true then some x else none)) w]
  · rw [foldl_or_find]
    simp only [exec_pure, Option.none_or, Array.find?_toList]
    cases xs.find? (fun x => (g x).toBool) <;> rfl
  · intro st k hk
    cases st
    · simp only [exec_bind, exec_readArr, hw, hk, dite_true]
      rw [hf]; simp
    · simp

/-- `arr.findIndex(f)` with a callback that is pure in the call's world. -/
theorem arrFindIndex_pureAt (I : Impl) (P : Program TT) {t : Ty} (a : Nat) (xs : Array (Val TT t))
    (f : Val TT (.fn (.cons t (.cons .num (.cons (.arr t) .nil))) .bool))
    (g : Val TT t → Val TT .bool) (w : World TT)
    (hf : ∀ vs, exec (applyFn I P f vs) w = some (.ok (g vs.a0), w))
    (hw : w.heap.get? (.arr t, a) = some xs) :
    exec (evalBuiltin I P (.arrFindIndex t) (.cons (.arr a) (.cons f .nil))) w =
      some (.ok ((xs.findIdx? (fun x => (g x).toBool)).elim (.num (F64.ofInt (-1))) num), w) := by
  rw [evalBuiltin.eq_def]
  simp only [exec_bind, exec_readArr, hw, Vals.a0_cons, Vals.a1_cons, Val.arrAddr_arr]
  rw [foldlM_range_pure xs _ (fun st x k => st.or (if (g x).toBool = true then some k else none)) w]
  · rw [foldl_or_findIdx (fun x => (g x).toBool)]
    simp only [exec_pure, Option.none_or, Nat.add_zero, Option.map_id', Array.findIdx?_eq_toList]
    cases xs.toList.findIdx? (fun x => (g x).toBool) <;> rfl
  · intro st k hk
    cases st
    · simp only [exec_bind, exec_readArr, hw, hk, dite_true]
      rw [hf]; simp
    · simp

end StrictTS
