/-
StrictTS proof layer: Array library lemmas.

With a callback that has no effect on the world (`PureFn`), the array methods are the
corresponding `List` functions over the array's elements:
`reduce ↦ List.foldl`, `map ↦ List.map`, `filter ↦ List.filter`, `some ↦ List.any`, …
These lemmas are what makes refactorings between loops and array methods provable by
rewriting.
-/
import StrictTS.Proof.Loops

namespace StrictTS
open JS

variable {TT : TypeTable}

/-- `f` is a pure function value: applying it never changes the world and returns `g vs`. -/
def PureFn (I : Impl) (P : Program TT) {args : Tys} {ret : Ty} (f : Val TT (.fn args ret))
    (g : Vals TT args.toList → Val TT ret) : Prop :=
  ∀ vs w, exec (applyFn I P f vs) w = some (.ok (g vs), w)

/-- A monadic left fold whose steps do not change the world is the pure left fold. -/
theorem foldlM_pure {α β : Type} (l : List β) (step : α → β → JS TT α) (g : α → β → α) (w : World TT)
    (h : ∀ acc b, b ∈ l → exec (step acc b) w = some (.ok (g acc b), w)) :
    ∀ init, exec (l.foldlM step init) w = some (.ok (l.foldl g init), w) := by
  induction l with
  | nil => intro init; simp
  | cons b l ih =>
    intro init
    rw [List.foldlM_cons, exec_bind, h init b (List.mem_cons_self ..)]
    exact ih (fun acc b' hb' => h acc b' (List.mem_cons_of_mem _ hb')) (g init b)

/-- Iterating over the positions `0 … n-1` with a guard is iterating over `zipIdx`. -/
theorem foldl_range_dite {α β : Type} (l : List β) (G : α → β → Nat → α) (init : α) :
    (List.range l.length).foldl (fun acc k => if h : k < l.length then G acc l[k] k else acc) init
      = l.zipIdx.foldl (fun acc p => G acc p.1 p.2) init := by
  induction l generalizing G init with
  | nil => simp
  | cons x xs ih =>
    have h1 : List.range (x :: xs).length = 0 :: (List.range xs.length).map Nat.succ := by
      simp [List.range_succ_eq_map]
    rw [h1, List.foldl_cons, List.foldl_map]
    have hfun : (fun acc k => if h : Nat.succ k < (x :: xs).length then G acc (x :: xs)[Nat.succ k] (Nat.succ k) else acc)
        = (fun acc k => if h : k < xs.length then G acc xs[k] (k + 1) else acc) := by
      funext acc k
      simp [Nat.succ_lt_succ_iff]
    rw [hfun, ih (fun acc y k => G acc y (k + 1))]
    simp only [List.length_cons, Nat.zero_lt_succ, dite_true, List.getElem_cons_zero, List.zipIdx_cons,
      List.foldl_cons]
    rw [show xs.zipIdx (0 + 1) = (xs.zipIdx).map (fun p => (p.1, p.2 + 1)) by
      simpa using (List.zipIdx_succ (l := xs) (i := 0)), List.foldl_map]

/-- The callback arguments `(x, i, arr)` of array methods. -/
abbrev cbArgs {t : Ty} (x : Val TT t) (k : Nat) (a : Nat) :
    Vals TT [t, .num, .arr t] := .cons x (.cons (num k) (.cons (.arr a) .nil))

/-- `arr.reduce(f, init)` with a pure callback is a left fold over the elements. -/
theorem arrReduce_pure (I : Impl) (P : Program TT) {t u : Ty} (a : Nat) (xs : Array (Val TT t))
    (f : Val TT (.fn (.cons u (.cons t (.cons .num (.cons (.arr t) .nil)))) u)) (init : Val TT u)
    (g : Vals TT [u, t, .num, .arr t] → Val TT u) (hf : PureFn I P f g) (w : World TT)
    (hw : w.heap.get? (.arr t, a) = some xs) :
    exec (evalBuiltin I P (.arrReduce t u) (.cons (.arr a) (.cons f (.cons init .nil)))) w =
      some (.ok (xs.toList.zipIdx.foldl (fun acc p => g (.cons acc (cbArgs p.1 p.2 a))) init), w) := by
  rw [evalBuiltin.eq_def]
  simp only [exec_bind, exec_readArr, hw, Vals.a0_cons, Vals.a1_cons, Vals.a2_cons, Val.arrAddr_arr]
  rw [foldlM_pure (List.range xs.size) _
    (fun acc k => if h : k < xs.size then g (.cons acc (cbArgs xs[k] k a)) else acc) w]
  · have := foldl_range_dite xs.toList (fun acc x k => g (.cons acc (cbArgs x k a))) init
    simpa using this
  · intro acc k _
    simp only [exec_bind, exec_readArr, hw]
    split
    · rw [hf]
    · simp

/-- `arr.reduce(f, init)` when the callback ignores the index and the array. -/
theorem arrReduce_pure' (I : Impl) (P : Program TT) {t u : Ty} (a : Nat) (xs : Array (Val TT t))
    (f : Val TT (.fn (.cons u (.cons t (.cons .num (.cons (.arr t) .nil)))) u)) (init : Val TT u)
    (g : Val TT u → Val TT t → Val TT u)
    (hf : PureFn I P f (fun vs => g vs.a0 vs.a1)) (w : World TT)
    (hw : w.heap.get? (.arr t, a) = some xs) :
    exec (evalBuiltin I P (.arrReduce t u) (.cons (.arr a) (.cons f (.cons init .nil)))) w =
      some (.ok (xs.toList.foldl g init), w) := by
  rw [arrReduce_pure I P a xs f init _ hf w hw]
  congr 3
  simp only [Vals.a0_cons, Vals.a1_cons]
  generalize init = acc
  induction xs.toList generalizing acc with
  | nil => rfl
  | cons x l ih =>
    simp only [List.zipIdx_cons, List.foldl_cons]
    rw [show l.zipIdx (0 + 1) = (l.zipIdx).map (fun p => (p.1, p.2 + 1)) by
      simpa using (List.zipIdx_succ (l := l) (i := 0)), List.foldl_map]
    exact ih (g acc x)

/-- Folding `push` over a list appends the mapped list. -/
theorem foldl_push_toList {α β : Type} (L : List α) (H : α → β) (init : Array β) :
    (L.foldl (fun acc p => acc.push (H p)) init).toList = init.toList ++ L.map H := by
  induction L generalizing init with
  | nil => simp
  | cons p L ih => simp [List.foldl_cons]

/-- The pushes of a `map`-style loop build `mapIdx`. -/
theorem foldl_range_push {α β : Type} (xs : Array α) (G : α → Nat → β) :
    (List.range xs.size).foldl (fun acc k => if h : k < xs.size then acc.push (G xs[k] k) else acc) #[]
      = xs.mapIdx (fun k x => G x k) := by
  have h1 := foldl_range_dite xs.toList (fun acc x k => acc.push (G x k)) (#[] : Array β)
  simp only [Array.length_toList, Array.getElem_toList] at h1
  rw [h1]
  apply Array.ext'
  rw [foldl_push_toList, Array.toList_mapIdx, List.mapIdx_eq_zipIdx_map]
  simp

/-- `arr.map(f)` with a pure callback allocates `arr.mapIdx f` at the next free address. -/
theorem arrMap_pure (I : Impl) (P : Program TT) {t u : Ty} (a : Nat) (xs : Array (Val TT t))
    (f : Val TT (.fn (.cons t (.cons .num (.cons (.arr t) .nil))) u))
    (g : Vals TT [t, .num, .arr t] → Val TT u) (hf : PureFn I P f g) (w : World TT)
    (hw : w.heap.get? (.arr t, a) = some xs) (ha : a ≠ w.next) :
    exec (evalBuiltin I P (.arrMap t u) (.cons (.arr a) (.cons f .nil))) w =
      some (.ok (.arr w.next), { w with
        heap := w.heap.insert (.arr u, w.next) (xs.mapIdx (fun k x => g (cbArgs x k a))),
        next := w.next + 1 }) := by
  rw [evalBuiltin.eq_def]
  simp only [exec_bind, exec_readArr, hw, Vals.a0_cons, Vals.a1_cons, Val.arrAddr_arr, exec_alloc]
  have hw1 : (w.heap.insert (.arr u, w.next) (#[] : Array (Val TT u))).get? (.arr t, a) = some xs := by
    rw [heap_get_insert_addr_ne _ _ _ _ (Ne.symm ha), hw]
  rw [foldlM_pure (List.range xs.size) _
    (fun acc k => if h : k < xs.size then acc.push (g (cbArgs xs[k] k a)) else acc) _]
  · simp only [exec_writeArr, foldl_range_push xs (fun x k => g (cbArgs x k a)), heap_insert_insert, exec_pure]
  · intro acc k _
    simp only [exec_bind, exec_readArr, hw1]
    split
    · rw [exec_bind, hf]; rfl
    · exfalso; simp_all [List.mem_range]

/-- `mapIdx` with a function that ignores the index is `map`. -/
@[simp] theorem mapIdx_const {α β : Type} (xs : Array α) (g : α → β) :
    Array.mapIdx (fun _ x => g x) xs = Array.map g xs := by
  apply Array.ext'
  simp only [Array.toList_mapIdx, Array.toList_map]
  generalize xs.toList = l
  induction l with
  | nil => rfl
  | cons x l ih => simp [List.mapIdx_cons, ih]

/-- `arr.map(f)` when the callback ignores the index and the array. -/
theorem arrMap_pure' (I : Impl) (P : Program TT) {t u : Ty} (a : Nat) (xs : Array (Val TT t))
    (f : Val TT (.fn (.cons t (.cons .num (.cons (.arr t) .nil))) u))
    (g : Val TT t → Val TT u) (hf : PureFn I P f (fun vs => g vs.a0)) (w : World TT)
    (hw : w.heap.get? (.arr t, a) = some xs) (ha : a ≠ w.next) :
    exec (evalBuiltin I P (.arrMap t u) (.cons (.arr a) (.cons f .nil))) w =
      some (.ok (.arr w.next), { w with
        heap := w.heap.insert (.arr u, w.next) (xs.map g),
        next := w.next + 1 }) := by
  rw [arrMap_pure I P a xs f _ hf w hw ha]
  simp

/-! ### `filter`, `some`, `every`, `find`, `findIndex`, `findLast`, `findLastIndex`, `forEach`

The callback is a pure function of its element: `PureFn I P f (fun vs => g vs.a0)`. Each
method then denotes the standard `Array`/`List` function of the predicate `fun x => (g x).toBool`.
The proofs go through one pure fold over the positions (`foldlM_range_pure`, …) and a fold
lemma for the method's short-circuit state. -/

/-- A fold over `zipIdx` that ignores the index is a fold over the list. -/
theorem foldl_zipIdx_fst {α β : Type} (l : List β) (G : α → β → α) (init : α) (k : Nat) :
    (l.zipIdx k).foldl (fun acc p => G acc p.1) init = l.foldl G init := by
  induction l generalizing init k with
  | nil => rfl
  | cons x l ih => simp only [List.zipIdx_cons, List.foldl_cons]; exact ih _ _

/-- A monadic fold over the positions of an array whose steps are pure at every valid position. -/
theorem foldlM_range_pure {α β : Type} (xs : Array β) (step : α → Nat → JS TT α)
    (G : α → β → Nat → α) (w : World TT)
    (h : ∀ acc k (hk : k < xs.size), exec (step acc k) w = some (.ok (G acc xs[k] k), w)) (init : α) :
    exec ((List.range xs.size).foldlM step init) w =
      some (.ok (xs.toList.zipIdx.foldl (fun acc p => G acc p.1 p.2) init), w) := by
  rw [foldlM_pure (List.range xs.size) step (fun acc k => if h : k < xs.size then G acc xs[k] k else acc) w]
  · have := foldl_range_dite xs.toList G init
    simpa using this
  · intro acc k hk
    have hk' : k < xs.size := List.mem_range.mp hk
    simp only [hk', dite_true]
    exact h acc k hk'

/-- `foldlM_range_pure` when the step does not use the position. -/
theorem foldlM_range_pure' {α β : Type} (xs : Array β) (step : α → Nat → JS TT α)
    (G : α → β → α) (w : World TT)
    (h : ∀ acc k (hk : k < xs.size), exec (step acc k) w = some (.ok (G acc xs[k]), w)) (init : α) :
    exec ((List.range xs.size).foldlM step init) w = some (.ok (xs.toList.foldl G init), w) := by
  rw [foldlM_range_pure xs step (fun acc x _ => G acc x) w h init, foldl_zipIdx_fst]

/-- Iterating over the positions `n-1 … 0` with a guard is iterating over the reversed `zipIdx`. -/
theorem foldl_range_rev_dite {α β : Type} (l : List β) (G : α → β → Nat → α) (init : α) :
    (List.range l.length).reverse.foldl (fun acc k => if h : k < l.length then G acc l[k] k else acc) init
      = l.zipIdx.reverse.foldl (fun acc p => G acc p.1 p.2) init := by
  induction l generalizing G init with
  | nil => simp
  | cons x xs ih =>
    have h1 : List.range (x :: xs).length = 0 :: (List.range xs.length).map Nat.succ := by
      simp [List.range_succ_eq_map]
    rw [h1, List.reverse_cons, List.foldl_append, ← List.map_reverse, List.foldl_map]
    have hfun : (fun acc k => if h : Nat.succ k < (x :: xs).length then G acc (x :: xs)[Nat.succ k] (Nat.succ k) else acc)
        = (fun acc k => if h : k < xs.length then G acc xs[k] (k + 1) else acc) := by
      funext acc k
      simp [Nat.succ_lt_succ_iff]
    rw [hfun, ih (fun acc y k => G acc y (k + 1))]
    rw [List.zipIdx_cons, List.reverse_cons, List.foldl_append]
    rw [show xs.zipIdx (0 + 1) = (xs.zipIdx).map (fun p => (p.1, p.2 + 1)) by
      simpa using (List.zipIdx_succ (l := xs) (i := 0)), ← List.map_reverse, List.foldl_map]
    simp

/-- A monadic fold over the positions of an array, last to first, whose steps are pure at every
valid position. -/
theorem foldlM_range_rev_pure {α β : Type} (xs : Array β) (step : α → Nat → JS TT α)
    (G : α → β → Nat → α) (w : World TT)
    (h : ∀ acc k (hk : k < xs.size), exec (step acc k) w = some (.ok (G acc xs[k] k), w)) (init : α) :
    exec ((List.range xs.size).reverse.foldlM step init) w =
      some (.ok (xs.toList.zipIdx.reverse.foldl (fun acc p => G acc p.1 p.2) init), w) := by
  rw [foldlM_pure (List.range xs.size).reverse step
    (fun acc k => if h : k < xs.size then G acc xs[k] k else acc) w]
  · have := foldl_range_rev_dite xs.toList G init
    simpa using this
  · intro acc k hk
    have hk' : k < xs.size := List.mem_range.mp (List.mem_reverse.mp hk)
    simp only [hk', dite_true]
    exact h acc k hk'

/-- A fold over the reversed `zipIdx` that ignores the index is a fold over the reversed list. -/
theorem foldl_zipIdx_rev_fst {α β : Type} (l : List β) (G : α → β → α) (init : α) (k : Nat) :
    (l.zipIdx k).reverse.foldl (fun acc p => G acc p.1) init = l.reverse.foldl G init := by
  induction l generalizing init k with
  | nil => rfl
  | cons x l ih =>
    simp only [List.zipIdx_cons, List.reverse_cons, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [ih]

/-- `foldlM_range_rev_pure` when the step does not use the position. -/
theorem foldlM_range_rev_pure' {α β : Type} (xs : Array β) (step : α → Nat → JS TT α)
    (G : α → β → α) (w : World TT)
    (h : ∀ acc k (hk : k < xs.size), exec (step acc k) w = some (.ok (G acc xs[k]), w)) (init : α) :
    exec ((List.range xs.size).reverse.foldlM step init) w =
      some (.ok (xs.toList.reverse.foldl G init), w) := by
  rw [foldlM_range_rev_pure xs step (fun acc x _ => G acc x) w h init, foldl_zipIdx_rev_fst]

/-- A monadic `forM` whose steps leave the world unchanged and return normally. -/
theorem forM_pure {β : Type} (l : List β) (step : β → JS TT PUnit) (w : World TT)
    (h : ∀ b, b ∈ l → exec (step b) w = some (.ok ⟨⟩, w)) :
    exec (l.forM step) w = some (.ok ⟨⟩, w) := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    show exec (step b >>= fun _ => l.forM step) w = _
    rw [exec_bind, h b (List.mem_cons_self ..)]
    exact ih (fun b' hb' => h b' (List.mem_cons_of_mem _ hb'))

/-! Folds that compute standard list functions (the forms `ts_summarize` produces for loops). -/

/-- `some`'s short-circuit fold is `List.any`. -/
@[simp] theorem foldl_or_any {β : Type} (p : β → Bool) (l : List β) (init : Bool) :
    l.foldl (fun st x => st || p x) init = (init || l.any p) := by
  induction l generalizing init with
  | nil => simp
  | cons x l ih => simp [ih, Bool.or_assoc]

@[simp] theorem Array.foldl_or_any {β : Type} (p : β → Bool) (xs : Array β) (init : Bool) :
    xs.foldl (fun st x => st || p x) init = (init || xs.any p) := by
  rw [← Array.foldl_toList, StrictTS.foldl_or_any, Array.any_toList]

/-- `every`'s short-circuit fold is `List.all`. -/
@[simp] theorem foldl_and_all {β : Type} (p : β → Bool) (l : List β) (init : Bool) :
    l.foldl (fun st x => st && p x) init = (init && l.all p) := by
  induction l generalizing init with
  | nil => simp
  | cons x l ih => simp [ih, Bool.and_assoc]

@[simp] theorem Array.foldl_and_all {β : Type} (p : β → Bool) (xs : Array β) (init : Bool) :
    xs.foldl (fun st x => st && p x) init = (init && xs.all p) := by
  rw [← Array.foldl_toList, StrictTS.foldl_and_all, Array.all_toList]

/-- Pushing the elements that pass appends the filtered list (`filter` as a loop). -/
@[simp] theorem foldl_push_filter {β : Type} (p : β → Bool) (l : List β) (init : Array β) :
    l.foldl (fun acc x => if p x = true then acc.push x else acc) init = init ++ (l.filter p).toArray := by
  induction l generalizing init with
  | nil => simp
  | cons x l ih => by_cases hx : p x = true <;> simp [hx, ih]

@[simp] theorem toArray_filter_toList {β : Type} (p : β → Bool) (xs : Array β) :
    (xs.toList.filter p).toArray = xs.filter p := by
  apply Array.ext'; simp

@[simp] theorem Array.foldl_push_filter {β : Type} (p : β → Bool) (xs : Array β) (init : Array β) :
    xs.foldl (fun acc x => if p x = true then acc.push x else acc) init = init ++ xs.filter p := by
  rw [← Array.foldl_toList, StrictTS.foldl_push_filter, toArray_filter_toList]

/-- Pushing the images appends the mapped list (`map` as a loop). -/
@[simp] theorem foldl_push_map {β γ : Type} (f : β → γ) (l : List β) (init : Array γ) :
    l.foldl (fun acc x => acc.push (f x)) init = init ++ (l.map f).toArray := by
  induction l generalizing init with
  | nil => simp
  | cons x l ih => simp [ih]

@[simp] theorem toArray_map_toList {β γ : Type} (f : β → γ) (xs : Array β) :
    (xs.toList.map f).toArray = xs.map f := by
  apply Array.ext'; simp

@[simp] theorem Array.foldl_push_map {β γ : Type} (f : β → γ) (xs : Array β) (init : Array γ) :
    xs.foldl (fun acc x => acc.push (f x)) init = init ++ xs.map f := by
  rw [← Array.foldl_toList, StrictTS.foldl_push_map, toArray_map_toList]

/-- A flag set by `if (p(x)) flag = true` (`some` as a loop). -/
@[simp] theorem foldl_flag_true {β : Type} (p : β → Bool) (l : List β) (b : Bool) :
    l.foldl (fun acc x => if p x = true then (Val.bool true : Val TT .bool) else acc) (.bool b) =
      .bool (b || l.any p) := by
  induction l generalizing b with
  | nil => simp
  | cons x l ih => by_cases hx : p x = true <;> simp [hx, ih]

@[simp] theorem Array.foldl_flag_true {β : Type} (p : β → Bool) (xs : Array β) (b : Bool) :
    xs.foldl (fun acc x => if p x = true then (Val.bool true : Val TT .bool) else acc) (.bool b) =
      .bool (b || xs.any p) := by
  rw [← Array.foldl_toList, StrictTS.foldl_flag_true, Array.any_toList]

/-- A flag cleared by `if (p(x)) flag = false` (`every` of the negation, as a loop). -/
@[simp] theorem foldl_flag_false {β : Type} (p : β → Bool) (l : List β) (b : Bool) :
    l.foldl (fun acc x => if p x = true then (Val.bool false : Val TT .bool) else acc) (.bool b) =
      .bool (b && l.all (fun x => !p x)) := by
  induction l generalizing b with
  | nil => simp
  | cons x l ih => by_cases hx : p x = true <;> simp [hx, ih]

@[simp] theorem Array.foldl_flag_false {β : Type} (p : β → Bool) (xs : Array β) (b : Bool) :
    xs.foldl (fun acc x => if p x = true then (Val.bool false : Val TT .bool) else acc) (.bool b) =
      .bool (b && xs.all (fun x => !p x)) := by
  rw [← Array.foldl_toList, StrictTS.foldl_flag_false, Array.all_toList]

/-- The same folds for a negated test: `simp` turns `!p x` into `p x = false`, and a test on
`p x = false` into the test on `p x = true` with the branches swapped (`Merge.ite_eq_false_swap`). -/
@[simp] theorem foldl_push_filter_neg {β : Type} (p : β → Bool) (l : List β) (init : Array β) :
    l.foldl (fun acc x => if p x = true then acc else acc.push x) init =
      init ++ (l.filter (fun x => !p x)).toArray := by
  induction l generalizing init with
  | nil => simp
  | cons x l ih => cases hx : p x <;> simp [hx, ih]

@[simp] theorem Array.foldl_push_filter_neg {β : Type} (p : β → Bool) (xs : Array β) (init : Array β) :
    xs.foldl (fun acc x => if p x = true then acc else acc.push x) init = init ++ xs.filter (fun x => !p x) := by
  rw [← Array.foldl_toList, StrictTS.foldl_push_filter_neg, toArray_filter_toList]

@[simp] theorem foldl_flag_true_neg {β : Type} (p : β → Bool) (l : List β) (b : Bool) :
    l.foldl (fun acc x => if p x = true then acc else (Val.bool true : Val TT .bool)) (.bool b) =
      .bool (b || l.any (fun x => !p x)) := by
  induction l generalizing b with
  | nil => simp
  | cons x l ih => cases hx : p x <;> simp [hx, ih]

@[simp] theorem Array.foldl_flag_true_neg {β : Type} (p : β → Bool) (xs : Array β) (b : Bool) :
    xs.foldl (fun acc x => if p x = true then acc else (Val.bool true : Val TT .bool)) (.bool b) =
      .bool (b || xs.any (fun x => !p x)) := by
  rw [← Array.foldl_toList, StrictTS.foldl_flag_true_neg, Array.any_toList]

@[simp] theorem foldl_flag_false_neg {β : Type} (p : β → Bool) (l : List β) (b : Bool) :
    l.foldl (fun acc x => if p x = true then acc else (Val.bool false : Val TT .bool)) (.bool b) =
      .bool (b && l.all p) := by
  induction l generalizing b with
  | nil => simp
  | cons x l ih => cases hx : p x <;> simp [hx, ih]

@[simp] theorem Array.foldl_flag_false_neg {β : Type} (p : β → Bool) (xs : Array β) (b : Bool) :
    xs.foldl (fun acc x => if p x = true then acc else (Val.bool false : Val TT .bool)) (.bool b) =
      .bool (b && xs.all p) := by
  rw [← Array.foldl_toList, StrictTS.foldl_flag_false_neg, Array.all_toList]

/-- Array literals (`[]`, `[x, …]`) list their elements. -/
@[simp, ts_sym] theorem Vals.toList_nil {t : Ty} :
    (@Vals.toList TT t 0 .nil) = [] := rfl

@[simp, ts_sym] theorem Vals.toList_cons {t : Ty} {n : Nat} (v : Val TT t) (vs : Vals TT (List.replicate n t)) :
    (@Vals.toList TT t (n + 1) (.cons v vs)) = v :: vs.toList := rfl

/-- `find`'s fold: the first element that passes. -/
theorem foldl_or_find {β : Type} (p : β → Bool) (l : List β) (init : Option β) :
    l.foldl (fun st x => st.or (if p x = true then some x else none)) init = init.or (l.find? p) := by
  induction l generalizing init with
  | nil => simp
  | cons x l ih =>
    rw [List.foldl_cons, ih]
    cases init <;> by_cases hx : p x = true <;> simp [hx]

/-- `findIndex`'s fold over the positions: the first position that passes. -/
theorem foldl_or_findIdx {β : Type} (p : β → Bool) (l : List β) (k : Nat) (init : Option Nat) :
    (l.zipIdx k).foldl (fun st q => st.or (if p q.1 = true then some q.2 else none)) init =
      init.or ((l.findIdx? p).map (· + k)) := by
  induction l generalizing k init with
  | nil => simp
  | cons x l ih =>
    rw [List.zipIdx_cons, List.foldl_cons, ih]
    cases init <;> by_cases hx : p x = true <;> simp [hx, List.findIdx?_cons, Option.map_map, Function.comp_def,
      Nat.add_assoc, Nat.add_comm 1 k]

/-- `findLastIndex`'s fold over the positions, last to first. -/
theorem foldl_or_findIdx_rev {β : Type} (p : β → Bool) (l : List β) (k : Nat) (init : Option Nat) :
    (l.zipIdx k).reverse.foldl (fun st q => st.or (if p q.1 = true then some q.2 else none)) init =
      init.or ((l.reverse.findIdx? p).map (fun j => k + l.length - 1 - j)) := by
  induction l generalizing k init with
  | nil => simp
  | cons x l ih =>
    rw [List.zipIdx_cons, List.reverse_cons, List.foldl_append, ih, List.reverse_cons, List.findIdx?_append]
    by_cases hx : p x = true <;> cases l.reverse.findIdx? p <;> simp [hx, List.findIdx?_cons]

theorem Array.findIdx?_eq_toList {β : Type} (p : β → Bool) (xs : Array β) :
    xs.findIdx? p = xs.toList.findIdx? p := by
  rw [← List.findIdx?_toArray, Array.toArray_toList]

/-! The array methods. -/

/-- `arr.filter(f)` with a pure callback allocates the filtered array at the next free address. -/
theorem arrFilter_pure' (I : Impl) (P : Program TT) {t : Ty} (a : Nat) (xs : Array (Val TT t))
    (f : Val TT (.fn (.cons t (.cons .num (.cons (.arr t) .nil))) .bool))
    (g : Val TT t → Val TT .bool) (hf : PureFn I P f (fun vs => g vs.a0)) (w : World TT)
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

/-- `arr.some(f)` with a pure callback is `Array.any`. -/
theorem arrSome_pure' (I : Impl) (P : Program TT) {t : Ty} (a : Nat) (xs : Array (Val TT t))
    (f : Val TT (.fn (.cons t (.cons .num (.cons (.arr t) .nil))) .bool))
    (g : Val TT t → Val TT .bool) (hf : PureFn I P f (fun vs => g vs.a0)) (w : World TT)
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

/-- `arr.every(f)` with a pure callback is `Array.all`. -/
theorem arrEvery_pure' (I : Impl) (P : Program TT) {t : Ty} (a : Nat) (xs : Array (Val TT t))
    (f : Val TT (.fn (.cons t (.cons .num (.cons (.arr t) .nil))) .bool))
    (g : Val TT t → Val TT .bool) (hf : PureFn I P f (fun vs => g vs.a0)) (w : World TT)
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

/-- `arr.find(f)` with a pure callback is `Array.find?` (`undefined` when absent). -/
theorem arrFind_pure' (I : Impl) (P : Program TT) {t : Ty} (a : Nat) (xs : Array (Val TT t))
    (f : Val TT (.fn (.cons t (.cons .num (.cons (.arr t) .nil))) .bool))
    (g : Val TT t → Val TT .bool) (hf : PureFn I P f (fun vs => g vs.a0)) (w : World TT)
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

/-- `arr.findIndex(f)` with a pure callback is `Array.findIdx?` (`-1` when absent). -/
theorem arrFindIndex_pure' (I : Impl) (P : Program TT) {t : Ty} (a : Nat) (xs : Array (Val TT t))
    (f : Val TT (.fn (.cons t (.cons .num (.cons (.arr t) .nil))) .bool))
    (g : Val TT t → Val TT .bool) (hf : PureFn I P f (fun vs => g vs.a0)) (w : World TT)
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

/-- `arr.findLast(f)` with a pure callback is `find?` on the reversed array. -/
theorem arrFindLast_pure' (I : Impl) (P : Program TT) {t : Ty} (a : Nat) (xs : Array (Val TT t))
    (f : Val TT (.fn (.cons t (.cons .num (.cons (.arr t) .nil))) .bool))
    (g : Val TT t → Val TT .bool) (hf : PureFn I P f (fun vs => g vs.a0)) (w : World TT)
    (hw : w.heap.get? (.arr t, a) = some xs) :
    exec (evalBuiltin I P (.arrFindLast t) (.cons (.arr a) (.cons f .nil))) w =
      some (.ok ((xs.reverse.find? (fun x => (g x).toBool)).elim .none .some), w) := by
  rw [evalBuiltin.eq_def]
  simp only [exec_bind, exec_readArr, hw, Vals.a0_cons, Vals.a1_cons, Val.arrAddr_arr]
  rw [foldlM_range_rev_pure' xs _ (fun st x => st.or (if (g x).toBool = true then some x else none)) w]
  · rw [foldl_or_find]
    simp only [exec_pure, Option.none_or, ← Array.toList_reverse, Array.find?_toList]
    cases xs.reverse.find? (fun x => (g x).toBool) <;> rfl
  · intro st k hk
    cases st
    · simp only [exec_bind, exec_readArr, hw, hk, dite_true]
      rw [hf]; simp
    · simp

/-- `arr.findLastIndex(f)` with a pure callback: the position of the last element that passes
(`findIdx?` on the reversed array, counted from the end), `-1` when absent. -/
theorem arrFindLastIndex_pure' (I : Impl) (P : Program TT) {t : Ty} (a : Nat) (xs : Array (Val TT t))
    (f : Val TT (.fn (.cons t (.cons .num (.cons (.arr t) .nil))) .bool))
    (g : Val TT t → Val TT .bool) (hf : PureFn I P f (fun vs => g vs.a0)) (w : World TT)
    (hw : w.heap.get? (.arr t, a) = some xs) :
    exec (evalBuiltin I P (.arrFindLastIndex t) (.cons (.arr a) (.cons f .nil))) w =
      some (.ok (((xs.reverse.findIdx? (fun x => (g x).toBool)).map (fun j => xs.size - 1 - j)).elim
        (.num (F64.ofInt (-1))) num), w) := by
  rw [evalBuiltin.eq_def]
  simp only [exec_bind, exec_readArr, hw, Vals.a0_cons, Vals.a1_cons, Val.arrAddr_arr]
  rw [foldlM_range_rev_pure xs _ (fun st x k => st.or (if (g x).toBool = true then some k else none)) w]
  · rw [foldl_or_findIdx_rev (fun x => (g x).toBool)]
    simp only [exec_pure, Option.none_or, Nat.zero_add, Array.length_toList, Array.findIdx?_eq_toList,
      Array.toList_reverse]
    cases (xs.toList.reverse.findIdx? (fun x => (g x).toBool)) <;> rfl
  · intro st k hk
    cases st
    · simp only [exec_bind, exec_readArr, hw, hk, dite_true]
      rw [hf]; simp
    · simp

/-- `arr.forEach(f)` with a callback that has no effect does nothing. -/
theorem arrForEach_pure' (I : Impl) (P : Program TT) {t : Ty} (a : Nat) (xs : Array (Val TT t))
    (f : Val TT (.fn (.cons t (.cons .num (.cons (.arr t) .nil))) .undef))
    (hf : PureFn I P f (fun _ => .undef)) (w : World TT)
    (hw : w.heap.get? (.arr t, a) = some xs) :
    exec (evalBuiltin I P (.arrForEach t) (.cons (.arr a) (.cons f .nil))) w = some (.ok .undef, w) := by
  rw [evalBuiltin.eq_def]
  simp only [exec_bind, exec_readArr, hw, Vals.a0_cons, Vals.a1_cons, Val.arrAddr_arr]
  rw [forM_pure]
  · rfl
  · intro k hk
    have hk' : k < xs.size := List.mem_range.mp hk
    simp only [exec_bind, exec_readArr, hw, hk', dite_true]
    rw [hf]; rfl

/-! ### `sort` with a pure comparator -/

/-- The merge sort of `Array.prototype.sort` (`sortL`) as a pure function: split at
`length / 2`, sort both halves, stable `List.merge`. -/
def sortBy {α : Type} (le : α → α → Bool) (xs : List α) : List α :=
  if xs.length ≤ 1 then xs
  else List.merge (sortBy le (xs.take (xs.length / 2))) (sortBy le (xs.drop (xs.length / 2))) le
termination_by xs.length
decreasing_by
  all_goals simp only [List.length_take, List.length_drop]; omega

/-- `sortBy` permutes its input. -/
theorem sortBy_perm {α : Type} (le : α → α → Bool) (xs : List α) : (sortBy le xs).Perm xs := by
  obtain ⟨n, h⟩ : ∃ n, xs.length = n := ⟨_, rfl⟩
  induction n using Nat.strongRecOn generalizing xs with
  | _ n ih =>
    rw [sortBy]
    split
    · exact List.Perm.refl xs
    · refine (List.merge_perm_append le).trans ?_
      have h1 := ih _ (by simp only [List.length_take]; omega) (xs.take (xs.length / 2)) rfl
      have h2 := ih _ (by simp only [List.length_drop]; omega) (xs.drop (xs.length / 2)) rfl
      exact (h1.append h2).trans (by rw [List.take_append_drop])

/-- `sortBy` keeps the length. -/
@[simp] theorem sortBy_length {α : Type} (le : α → α → Bool) (xs : List α) :
    (sortBy le xs).length = xs.length :=
  (sortBy_perm le xs).length_eq

/-- For a total preorder, `sortBy` sorts. -/
theorem pairwise_sortBy {α : Type} (le : α → α → Bool)
    (trans : ∀ (a b c : α), le a b → le b c → le a c) (total : ∀ (a b : α), le a b || le b a)
    (xs : List α) : (sortBy le xs).Pairwise (fun a b => le a b) := by
  obtain ⟨n, h⟩ : ∃ n, xs.length = n := ⟨_, rfl⟩
  induction n using Nat.strongRecOn generalizing xs with
  | _ n ih =>
    rw [sortBy]
    split
    · match xs, (by omega : xs.length ≤ 1) with
      | [], _ => simp
      | [_], _ => simp
    · exact List.pairwise_merge trans total _ _
        (ih _ (by simp only [List.length_take]; omega) _ rfl)
        (ih _ (by simp only [List.length_drop]; omega) _ rfl)

/-- `mergeL` with a pure comparator is `List.merge`. -/
theorem mergeL_pure (I : Impl) (P : Program TT) {t : Ty} (cmp : Val TT (.fn (.cons t (.cons t .nil)) .num))
    (g : Val TT t → Val TT t → Val TT .num) (hf : PureFn I P cmp (fun vs => g vs.a0 vs.a1)) :
    ∀ (xs ys : List (Val TT t)) (w : World TT),
      exec (mergeL I P cmp xs ys) w = some (.ok (List.merge xs ys (fun x y => !Conv.isPos (g x y).toNum)), w) := by
  intro xs ys w
  obtain ⟨n, h⟩ : ∃ n, xs.length + ys.length = n := ⟨_, rfl⟩
  induction n using Nat.strongRecOn generalizing xs ys with
  | _ n ih =>
    rw [mergeL.eq_def]
    match xs, ys with
    | [], ys => simp
    | x :: xs', [] => simp
    | x :: xs', y :: ys' =>
      simp only [exec_bind]
      rw [hf]
      simp only [Vals.a0_cons, Vals.a1_cons]
      by_cases hc : Conv.isPos (g x y).toNum = true
      · simp only [hc, ite_true, exec_bind]
        rw [ih _ (by simp at h ⊢; omega) (x :: xs') ys' rfl]
        simp [hc]
      · simp only [hc, Bool.false_eq_true, ite_false, exec_bind]
        rw [ih _ (by simp at h ⊢; omega) xs' (y :: ys') rfl]
        simp [hc]

/-- `sortL` with a pure comparator is `sortBy`. -/
theorem sortL_pure (I : Impl) (P : Program TT) {t : Ty} (cmp : Val TT (.fn (.cons t (.cons t .nil)) .num))
    (g : Val TT t → Val TT t → Val TT .num) (hf : PureFn I P cmp (fun vs => g vs.a0 vs.a1)) :
    ∀ (xs : List (Val TT t)) (w : World TT),
      exec (sortL I P cmp xs) w = some (.ok (sortBy (fun x y => !Conv.isPos (g x y).toNum) xs), w) := by
  intro xs w
  obtain ⟨n, h⟩ : ∃ n, xs.length = n := ⟨_, rfl⟩
  induction n using Nat.strongRecOn generalizing xs with
  | _ n ih =>
    rw [sortL.eq_def, sortBy]
    split
    · rfl
    · simp only [exec_bind]
      rw [ih _ (by simp only [List.length_take]; omega) _ rfl]
      dsimp only
      rw [ih _ (by simp only [List.length_drop]; omega) _ rfl]
      dsimp only
      rw [mergeL_pure I P cmp g hf]

/-- `arr.sort(cmp)` with a pure comparator sorts the array in place with `sortBy`. -/
theorem arrSort_pure' (I : Impl) (P : Program TT) {t : Ty} (a : Nat) (xs : Array (Val TT t))
    (cmp : Val TT (.fn (.cons t (.cons t .nil)) .num)) (g : Val TT t → Val TT t → Val TT .num)
    (hf : PureFn I P cmp (fun vs => g vs.a0 vs.a1)) (w : World TT)
    (hw : w.heap.get? (.arr t, a) = some xs) :
    exec (evalBuiltin I P (.arrSort t) (.cons (.arr a) (.cons cmp .nil))) w =
      some (.ok (.arr a), { w with
        heap := w.heap.insert (.arr t, a) (sortBy (fun x y => !Conv.isPos (g x y).toNum) xs.toList).toArray }) := by
  rw [evalBuiltin.eq_def]
  simp only [exec_bind, exec_readArr, hw, Vals.a0_cons, Vals.a1_cons, Val.arrAddr_arr]
  rw [sortL_pure I P cmp g hf]
  rfl

end StrictTS
