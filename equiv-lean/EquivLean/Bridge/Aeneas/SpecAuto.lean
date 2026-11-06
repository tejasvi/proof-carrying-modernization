import EquivLean.Bridge.Aeneas.AutoCouple

/-!
# Aeneas (Rust) bridge: specifications of loops, with generated invariants

`aeneas_spec [defs] (with [lemmas])? (using (I) (V))?` proves that an Aeneas function meets a
specification given as a pure Lean function of its inputs: goals `wp (f xs) Q` (e.g.
`Q o := ∃ v, o = .ok v ∧ v.val = spec xs.val`), `∃ v, f xs = ok v ∧ P v` or `f xs = ok v`.  It
unfolds `defs`, runs the code before the loop symbolically, and proves each loop by the
one-sided rule `wp_loop` with an invariant and a variant it generates (`using`: the invariant `I`
and the variant `V` of the first loop, functions of its state, instead of the generated ones):

* the loop index `i` walks a list or counts up to a bound:
  - the `usize` loop variable that the body compares with the length of a slice (or `Vec`) `xs`
    the loop does not modify, or the `start` of a `Range` loop variable (`for i in 0..xs.len()`):
    the prefix after `i` iterations is `take i xs.val`;
  - a `usize` loop variable compared with a bound `n` (`while j < n`, `for j in 0..n`): the
    prefix of a term is the term at `i` instead of `n.val`.  When the head condition tests such a
    bound and the body also tests a length (a padded copy: `while i < width { if i < s.len() …`),
    the count walk on `n` is tried after the list walk;
  the invariant has `i.val ≤ xs.val.length` (or `≤ n.val`, and a `Range` keeps its `end`), and
  the variant is `xs.val.length - i.val`;
* every other loop variable `c` is "the specification on the prefix": `rep c = t[prefix i]` for a
  term `t` of the postcondition that mentions `xs.val` (or `n.val`): `List.map`, `List.filter`,
  `List.foldl`, `List.length`, … over `xs.val`, and the prefixes `a ++ … ++ b` of appends (e.g.
  `[header] ++ xs.val.map f` for `[header] ++ xs.val.map f ++ [trailer]`).  `rep c` is `c.val` for
  a `Vec` (or `c.val.map g` for a decoder `g` that the postcondition applies to the result), for a
  slice or an array written in place (a copy to an offset, `buf[pos + i] = src[i]`:
  `take pos buf ++ take i src ++ drop (pos + i) buf`) and for a scalar, and `c` itself otherwise.
  Candidates are filtered by type and by the entry value (`rep c₀ = t[empty prefix]` must not be
  refuted by `simp`).  A loop variable that no iteration changes keeps its entry value; each
  `Vec` grows by at most as many elements per iteration as a path through the body pushes;
* a search loop (no accumulator) gets `t[take i xs] = t[[]]` for an `Option` or `Bool` term `t`
  of the postcondition (e.g. `(take i xs).find? p = none`, `(take i xs).findIdx? p = none`,
  `(take i xs).any p = false`);
* a loop that a flag ends (the condition of the `if` at the head of the body does not test the
  index, e.g. `while !end_of_file` in a COBOL read loop whose body advances the position): while
  the loop goes on, the loop variables that the body tests (the flags) keep their entry values;
  once it stops, the index is at the end.  The invariant has `(cond ∧ flags = entry values) ∨
  (¬ cond ∧ i = len)` and the variant is `len - i + (if cond then 1 else 0)`.  The exit branch
  may run code (code after the loop that an early `return` in the loop moved into it).

The step and the initial state are closed by `spec_leaves`: symbolic execution (with value forms of
library functions: `for` ranges, `extend_from_slice`, `to_vec`, `vec![x; n]`, array indexing and
`==` on byte arrays, `&mut v[i]` on a `Vec`, writes to a slice, scalar literals), case splits, the
list lemmas that turn `take (i + 1)` into an append (`take_succ_of_lt`, `List.map_append`,
`List.filter_append`, `List.foldl_append`, …), writes at an offset (`set_drop_zero`) and into
padding (`set_replicate_zero`, `replicate_succ_sub`), `i = len` at the exit, `find?_of_take_none`
/ `findIdx?_of_take_none` / `any_of_getElem` for a search that stops at a match, length facts
for the bounds (`scalar_tac`, `omega`), and the given lemmas (definitions of the specification's
functions, specifications of called functions such as `lookup_eq`).  Each candidate invariant is
an attempt that either closes every goal or is undone; if none succeeds the goal is left
unchanged and the tactic fails with the invariants it tried.  Arithmetic invariants (digit loops
such as `zero_pad`) are not generated: prove those loops by hand (`wp_loop` with an invariant),
or give the invariant with `using`.
-/

open Aeneas Aeneas.Std

namespace EquivLean.Aeneas

open Lean Meta Elab Tactic

/-! ## Lemmas -/

theorem take_succ_of_lt {α : Type _} {l : List α} {i : Nat} (h : i < l.length) :
    l.take (i + 1) = l.take i ++ [l[i]] := by
  rw [List.take_add_one, List.getElem?_eq_getElem h]; rfl

/-- A search that found no match in the prefix stops at the first match. -/
theorem find?_of_take_none {α : Type _} {l : List α} {p : α → Bool} {j : Nat}
    (h : (l.take j).find? p = none) (hj : j < l.length) (hp : p l[j] = true) :
    l.find? p = some l[j] := by
  have hl : l.find? p = (l.take j ++ l.drop j).find? p := by rw [List.take_append_drop]
  rw [hl, List.drop_eq_getElem_cons hj, List.find?_append, h, Option.none_or, List.find?_cons, hp]

/-- A search for an index that found no match in the prefix stops at the first match. -/
theorem findIdx?_of_take_none {α : Type _} {l : List α} {p : α → Bool} {j : Nat}
    (h : (l.take j).findIdx? p = none) (hj : j < l.length) (hp : p l[j] = true) :
    l.findIdx? p = some j := by
  have hl : l.findIdx? p = (l.take j ++ l.drop j).findIdx? p := by rw [List.take_append_drop]
  rw [hl, List.findIdx?_append, h, List.drop_eq_getElem_cons hj, List.findIdx?_cons, hp]
  simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]

/-- A match at a position: the list has one. -/
theorem any_of_getElem {α : Type _} {l : List α} {p : α → Bool} {j : Nat} (hj : j < l.length)
    (hp : p l[j] = true) : l.any p = true :=
  List.any_eq_true.2 ⟨l[j], List.getElem_mem hj, hp⟩

/-- `∃ v, c = ok v ∧ P v` from its weakest precondition. -/
theorem exists_ok_of_wp {α : Type _} {c : Result α} {P : α → Prop}
    (h : wp c (fun o => ∃ v, o = .ok v ∧ P v)) : ∃ v, c = .ok v ∧ P v := by
  rcases (wp_iff _ _).1 h with ⟨s, hs, v, hv, hp⟩ | ⟨e, he, v, hv, hp⟩
  · cases hv; exact ⟨s, hs, hp⟩
  · cases hv

/-- `c = ok v` from its weakest precondition. -/
theorem eq_ok_of_wp {α : Type _} {c : Result α} {v : α} (h : wp c (fun o => o = .ok v)) :
    c = .ok v := by
  rcases (wp_iff _ _).1 h with ⟨s, hs, hok⟩ | ⟨e, he, herr⟩
  · cases hok; exact hs
  · cases herr

/-! ## Value forms of library functions -/

/-- `List.clone` with a `clone` that returns its argument (a `Copy` type). -/
theorem list_clone_ok {α : Type _} (clone : α → Result α) (hc : ∀ x, clone x = .ok x) :
    ∀ l : List α, List.clone clone l = .ok ⟨l, rfl⟩
  | [] => rfl
  | a :: l => by
    have ih := list_clone_ok clone hc l
    simp only [List.clone] at ih ⊢
    simp only [List.mapM_with_length, ih, hc, bind_tc_ok]
    rfl

theorem range_next_lt (r : core.ops.range.Range Usize) (h : r.start.val < r.end.val) :
    core.iter.range.IteratorRange.next core.iter.range.StepUsize r =
      .ok (some r.start, ⟨UScalar.ofNatCore (r.start.val + 1)
        (by have := r.end.hBounds; scalar_tac), r.end⟩) := by
  simp only [core.iter.range.IteratorRange.next, core.iter.range.UScalarStep,
    core.iter.range.UScalarStep.forward_checked]
  have h1 : core.cmp.impls.PartialOrdUsize.lt r.start r.end = true := by
    simp [core.cmp.impls.PartialOrdUsize.lt, h]
  have h2 : r.start.val < UScalar.max UScalarTy.Usize := by have := r.end.hBounds; scalar_tac
  simp only [liftFun2, h1]
  simp [liftFun1, core.clone.impls.CloneUsize.clone, h2]

theorem range_next_ge (r : core.ops.range.Range Usize) (h : ¬ r.start.val < r.end.val) :
    core.iter.range.IteratorRange.next core.iter.range.StepUsize r = .ok (none, r) := by
  simp only [core.iter.range.IteratorRange.next, core.iter.range.UScalarStep]
  have h1 : core.cmp.impls.PartialOrdUsize.lt r.start r.end = false := by
    simp [core.cmp.impls.PartialOrdUsize.lt, h]
  simp only [liftFun2, h1]
  simp

/-- One step of `for i in a..b` over `usize`. -/
theorem range_next (r : core.ops.range.Range Usize) :
    core.iter.range.IteratorRange.next core.iter.range.StepUsize r =
      if h : r.start.val < r.end.val then
        .ok (some r.start, ⟨UScalar.ofNatCore (r.start.val + 1)
          (by have := r.end.hBounds; scalar_tac), r.end⟩)
      else .ok (none, r) := by
  by_cases h : r.start.val < r.end.val
  · simp only [h, ↓reduceDIte]; exact range_next_lt r h
  · simp only [h, ↓reduceDIte]; exact range_next_ge r h

/-- `v.extend_from_slice(s)` for bytes. -/
theorem extend_from_slice_U8 (v : alloc.vec.Vec U8) (s : Slice U8)
    (h : v.val.length + s.val.length ≤ Usize.max) :
    alloc.vec.Vec.extend_from_slice core.clone.CloneU8 v s =
      .ok (alloc.vec.Vec.from (v.val ++ s.val) (by simp; omega)) := by
  have h' : v.length + s.length ≤ Usize.max := by simpa using h
  simp only [alloc.vec.Vec.extend_from_slice, h', _root_.dite_true]
  rw [list_clone_ok _ (fun x => rfl)]
  simp

theorem extend_from_slice_U8_eq (v : alloc.vec.Vec U8) (s : Slice U8) :
    alloc.vec.Vec.extend_from_slice core.clone.CloneU8 v s =
      if h : v.val.length + s.val.length ≤ Usize.max then
        .ok (alloc.vec.Vec.from (v.val ++ s.val) (by simp; omega))
      else .fail .panic := by
  by_cases h : v.val.length + s.val.length ≤ Usize.max
  · simp only [h, ↓reduceDIte]; exact extend_from_slice_U8 v s h
  · simp only [h, ↓reduceDIte]
    have h' : ¬ v.length + s.length ≤ Usize.max := by simpa using h
    simp only [alloc.vec.Vec.extend_from_slice, h', _root_.dite_false]

/-- `vec![x; n]` for bytes. -/
theorem from_elem_U8 (x : U8) (n : Usize) :
    alloc.vec.from_elem core.clone.CloneU8 x n =
      .ok (alloc.vec.Vec.from (List.replicate n.val x) (by simp; scalar_tac)) := by
  simp only [alloc.vec.from_elem]
  rw [list_clone_ok _ (fun x => rfl)]
  simp

/-- `a == b` for byte arrays. -/
theorem partialEqArray_eq_U8 {N : Usize} (a b : Array U8 N) :
    core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8 a b =
      .ok (decide (a.val = b.val)) := by
  have ha := a.property
  have hb := b.property
  simp only [core.array.equality.PartialEqArray.eq]
  rw [ite_eq_left (by simp only [Array.length, ha, hb])]
  generalize a.val = l1 at *
  generalize b.val = l2 at *
  have hl : l1.length = l2.length := by omega
  clear ha hb
  simp [liftFun2]
  induction l1 generalizing l2 with
  | nil =>
    cases l2 with
    | nil => rfl
    | cons y ys => simp at hl
  | cons x xs ih =>
    cases l2 with
    | nil => simp at hl
    | cons y ys =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
      simp only [List.zip_cons_cons, List.allM_cons]
      by_cases hxy : x = y
      · subst hxy; simp [ih ys hl]
      · have hv : ¬ x.val = y.val := fun h => hxy (UScalar.eq_of_val_eq h)
        first | (simp [hv, hxy]; done) | (simp [hv, hxy]; rfl)

/-- `a != b` for byte arrays. -/
theorem partialEqArray_ne_U8 {N : Usize} (a b : Array U8 N) :
    core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8 a b =
      .ok (decide (¬ a.val = b.val)) := by
  simp only [core.array.equality.PartialEqArray.ne, partialEqArray_eq_U8, bind_tc_ok,
    decide_eq_true_eq]

/-- `s.to_vec()` for bytes. -/
theorem slice_to_vec_U8 (s : Slice U8) :
    alloc.slice.Slice.to_vec core.clone.CloneU8 s =
      .ok (alloc.vec.Vec.from s.val (by scalar_tac)) := by
  simp only [alloc.slice.Slice.to_vec, Slice.clone]
  rw [list_clone_ok _ (fun x => rfl)]
  simp only [bind_tc_ok]
  rfl

/-- `a[i]` for an array. -/
theorem array_index_usize_eq {α : Type _} {n : Usize} (a : Array α n) (i : Usize) :
    Array.index_usize a i =
      if h : i.val < a.val.length then .ok (a.val[i.val]) else .fail .arrayOutOfBounds := by
  simp only [Array.index_usize, Array.getElem?_Usize_eq]
  have hl : a.val.length = n.val := a.property
  by_cases h : i.val < a.val.length
  · have h' : i.val < n.val := by omega
    simp [h']
  · have h' : ¬ i.val < n.val := by omega
    simp [h']

/-- `a[i] = x` for an array. -/
theorem array_update_eq {α : Type _} {n : Usize} (a : Array α n) (i : Usize) (x : α) :
    Array.update a i x = if _h : i.val < a.val.length then
      .ok (Array.from (a.val.set i.val x) (by simp [a.property])) else .fail .arrayOutOfBounds := by
  simp only [Array.update, Array.getElem?_Usize_eq]
  have hl : a.val.length = n.val := a.property
  by_cases h : i.val < a.val.length
  · have h' : i.val < n.val := by omega
    simp [h']
  · have h' : ¬ i.val < n.val := by omega
    simp [h']

/-- `s[i] = x` for a slice. -/
theorem slice_update_eq {α : Type _} (v : Slice α) (i : Usize) (x : α) :
    Slice.update v i x = if _h : i.val < v.val.length then
      .ok (Slice.from (v.val.set i.val x) (by have := v.property; simp))
      else .fail .arrayOutOfBounds := by
  simp only [Slice.update]
  by_cases h : i.val < v.val.length
  · simp [h]
  · simp [h]

/-- `&mut v[i]` for a vector (read the element, write it back). -/
theorem vec_index_mut_eq {α : Type _} (v : alloc.vec.Vec α) (i : Usize) :
    alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice α) v i =
      if h : i.val < v.val.length then .ok (v.val[i.val], alloc.vec.Vec.set v i)
      else .fail .arrayOutOfBounds := by
  rw [alloc.vec.Vec.index_mut_slice_index]
  simp only [alloc.vec.Vec.index_mut_usize, alloc.vec.Vec.index_usize]
  by_cases h : i.val < v.val.length
  · simp [h]
  · simp [h]

/-- Writing at the start of a suffix (a copy at an offset: `buf[pos + i] = src[i]`). -/
theorem set_drop_zero {α : Type _} (b : List α) (k : Nat) (x : α) (h : k < b.length) :
    (b.drop k).set 0 x = x :: b.drop (k + 1) := by
  rw [List.drop_eq_getElem_cons h, List.set_cons_zero]

/-- The suffix after an offset copy, in the form of the specification's prefix. -/
theorem drop_add_add_one {α : Type _} (l : List α) (a b : Nat) :
    l.drop (a + b + 1) = l.drop (a + (b + 1)) := by rw [Nat.add_assoc]

/-- Writing at the start of a run of copies (a padded copy: `r[i] = s[i]` into spaces). -/
theorem set_replicate_zero {α : Type _} (m : Nat) (a x : α) (h : 0 < m) :
    (List.replicate m a).set 0 x = x :: List.replicate (m - 1) a := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  simp [List.replicate_succ]

/-- The padding of a padded copy before the end of the source (`i < len`: none yet). -/
theorem replicate_sub_of_le {α : Type _} (a b : Nat) (x : α) (h : a ≤ b) :
    List.replicate (a - b) x = [] := by
  rw [Nat.sub_eq_zero_of_le h, List.replicate_zero]

/-- One more space of a padded copy past the end of the source (`len ≤ i`). -/
theorem replicate_succ_sub {α : Type _} (a b : Nat) (x : α) (h : b ≤ a) :
    List.replicate (a + 1 - b) x = List.replicate (a - b) x ++ [x] := by
  rw [show a + 1 - b = (a - b) + 1 by omega, List.replicate_succ']

/-- The value of a signed remainder (`x % y` on `i64`, …): truncated. -/
theorem iscalar_srem_val {ity : IScalarTy} (x y : IScalar ity) :
    (⟨BitVec.srem x.bv y.bv⟩ : IScalar ity).val = Int.tmod x.val y.val :=
  BitVec.toInt_srem _ _

/-- The value of a literal (`89#u8`). -/
theorem uscalar_ofNat_val {ty : UScalarTy} (x : Nat) (h : x ≤ UScalar.cMax ty) :
    (UScalar.ofNat x h).val = x := UScalar.ofNatCore_val_eq _

/-- The value of a literal (`16#i64`). -/
theorem iscalar_ofInt_val {ty : IScalarTy} (x : Int)
    (h : IScalar.cMin ty ≤ x ∧ x ≤ IScalar.cMax ty) :
    (IScalar.ofInt x h).val = x := IScalar.ofInt_val_eq _

/-- The value forms that the symbolic execution of the kit uses. -/
def specLib : MacroM SimpArgs := do
  let xs ← #[
    ← `(Parser.Tactic.simpArg| range_next),
    ← `(Parser.Tactic.simpArg| extend_from_slice_U8_eq),
    ← `(Parser.Tactic.simpArg| from_elem_U8),
    ← `(Parser.Tactic.simpArg| partialEqArray_eq_U8),
    ← `(Parser.Tactic.simpArg| partialEqArray_ne_U8),
    ← `(Parser.Tactic.simpArg| Array.make_val),
    ← `(Parser.Tactic.simpArg| Array.repeat_val),
    ← `(Parser.Tactic.simpArg| Array.to_slice),
    ← `(Parser.Tactic.simpArg| alloc.vec.Vec.deref),
    ← `(Parser.Tactic.simpArg| slice_to_vec_U8),
    ← `(Parser.Tactic.simpArg| array_index_usize_eq),
    ← `(Parser.Tactic.simpArg| array_update_eq),
    ← `(Parser.Tactic.simpArg| slice_update_eq),
    ← `(Parser.Tactic.simpArg| vec_index_mut_eq),
    ← `(Parser.Tactic.simpArg| alloc.vec.Vec.set_val_eq),
    ← `(Parser.Tactic.simpArg| Slice.from_val),
    ← `(Parser.Tactic.simpArg| Array.from_val),
    ← `(Parser.Tactic.simpArg| uscalar_ofNat_val),
    ← `(Parser.Tactic.simpArg| iscalar_ofInt_val),
    ← `(Parser.Tactic.simpArg| iscalar_srem_val),
    ← `(Parser.Tactic.simpArg| Bool.false_eq_true),
    ← `(Parser.Tactic.simpArg| Bool.true_eq_false),
    ← `(Parser.Tactic.simpArg| List.length_cons),
    ← `(Parser.Tactic.simpArg| List.length_nil),
    ← `(Parser.Tactic.simpArg| List.length_replicate),
    ← `(Parser.Tactic.simpArg| List.getElem_cons_zero),
    ← `(Parser.Tactic.simpArg| List.getElem_cons_succ),
    ← `(Parser.Tactic.simpArg| List.getElem_replicate),
    ← `(Parser.Tactic.simpArg| Nat.lt_irrefl),
    ← `(Parser.Tactic.simpArg| Nat.zero_lt_succ),
    ← `(Parser.Tactic.simpArg| Nat.one_lt_succ_succ),
    ← `(Parser.Tactic.simpArg| List.cons.injEq),
    ← `(Parser.Tactic.simpArg| Nat.reduceEqDiff),
    ← `(Parser.Tactic.simpArg| Nat.reduceAdd),
    ← `(Parser.Tactic.simpArg| Nat.reduceSub),
    ← `(Parser.Tactic.simpArg| Nat.reduceMul),
    ← `(Parser.Tactic.simpArg| Int.reduceEq),
    ← `(Parser.Tactic.simpArg| Int.reduceAdd),
    ← `(Parser.Tactic.simpArg| Int.reduceSub),
    ← `(Parser.Tactic.simpArg| Int.reduceMul),
    ← `(Parser.Tactic.simpArg| Int.reduceNeg),
    ← `(Parser.Tactic.simpArg| Int.reduceLE),
    ← `(Parser.Tactic.simpArg| Int.reduceLT)].mapM fun x => pure x
  return xs.map fun x => ⟨x.raw⟩

/-- The subterms of `e` without loose bound variables that satisfy `p`, added to `acc` (each shared
subterm is visited once: the proofs inside a goal are large DAGs). -/
def closedSubterms (p : Expr → Bool) (e : Expr) (acc : Array Expr) : MetaM (Array Expr) := do
  let r ← IO.mkRef acc
  e.forEach fun x => do
    if p x && !x.hasLooseBVars then
      let a ← r.get
      unless a.contains x do r.set (a.push x)
  r.get

/-- The `List.filter` terms of `e`. -/
def filterTerms (e : Expr) (acc : Array Expr) : MetaM (Array Expr) :=
  closedSubterms (·.isAppOfArity ``List.filter 3) e acc

/-- Length facts for `omega`/`scalar_tac`: `(l.filter q).length ≤ l.length` for the filters of
the goal and the hypotheses. -/
elab "spec_len_facts" : tactic => withMainContext do
  let mut terms : Array Expr ← filterTerms (← instantiateMVars (← getMainTarget)) #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    terms ← filterTerms (← instantiateMVars d.type) terms
  for t in terms do
    let pf ← mkAppM ``List.length_filter_le #[t.getArgD 1 t, t.getArgD 2 t]
    let g ← getMainGoal
    let g' ← g.assert `hlen (← inferType pf) pf
    let (_, g'') ← g'.intro1P
    replaceMainGoal [g'']

/-- Instances of the hypotheses `∀ x ∈ l, P x` at the elements `l[k]` that occur in the goal
(facts about the input records, e.g. field ranges, for the current record). -/
elab "spec_elem_facts" : tactic => withMainContext do
  let tgt ← instantiateMVars (← getMainTarget)
  let isGet (e : Expr) : Bool := e.isAppOfArity ``GetElem.getElem 8
  let mut gets : Array Expr ← closedSubterms isGet tgt #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    gets ← closedSubterms isGet (← instantiateMVars d.type) gets
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    -- ∀ x, x ∈ l → P x
    let .forallE _ _ (.forallE _ mem _ _) _ := ty | continue
    unless mem.isAppOfArity ``Membership.mem 5 do continue
    let l := mem.getArgD 3 mem
    for g in gets do
      -- GetElem.getElem coll idx elem valid inst xs i h
      unless (g.getArgD 5 g) == l do continue
      try
        let hm ← mkAppM ``List.getElem_mem #[g.getArgD 7 g]
        let pf := mkApp2 (mkFVar d.fvarId) g hm
        let pty ← instantiateMVars (← inferType pf)
        if (← getLCtx).any (fun d' => d'.type == pty) then continue
        let mg ← getMainGoal
        let mg' ← mg.assert `helem pty pf
        let (_, mg'') ← mg'.intro1P
        replaceMainGoal [mg'']
      catch _ => pure ()

/-- At the exit of a loop: `i = N` from `i ≤ N` and `¬ i < N` (by `omega`), rewritten in the
goal (the prefix at `i` is then the whole: `take N L`, or a counter's term at `N`). -/
elab "spec_count_exit" : tactic => withMainContext do
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    unless ty.isAppOfArity ``Not 1 do continue
    let p := ty.appArg!
    unless p.isAppOfArity ``LT.lt 4 && (p.getArgD 0 p).isConstOf ``Nat do continue
    let a := p.getArgD 2 p
    let b := p.getArgD 3 p
    if a.isRawNatLit || (a.nat?).isSome then continue
    let mv ← mkFreshExprMVar (← mkEq a b)
    let ok ← try
        let gs ← Tactic.run mv.mvarId! (evalTactic (← `(tactic| omega)))
        pure gs.isEmpty
      catch _ => pure false
    unless ok do continue
    let g ← getMainGoal
    let g' ← g.assert `spec_hex (← mkEq a b) (← instantiateMVars mv)
    let (_, g'') ← g'.intro1P
    replaceMainGoal [g'']
    evalTactic (← `(tactic| simp only [$(mkIdent `spec_hex):ident] at *))
    return

/-- The end of `spec_disch` after the symbolic-execution normalisation. -/
macro "spec_disch_close" : tactic =>
  `(tactic| first | assumption | omega | scalar_tac | simp only [and_self, and_true, true_and, *])

/-- The side conditions of the leaf lemmas: arithmetic, a hypothesis, or a key test that the
symbolic execution normalised (`decide (a.id = id) = true`). -/
syntax (name := specDisch) "spec_disch" " [" Parser.Tactic.simpArg,* "]" : tactic

macro_rules
  | `(tactic| spec_disch [$args,*]) => do
    let args : SimpArgs := args.getElems
    `(tactic| first
      | omega
      | assumption
      | (simp only [decide_eq_true_eq]; assumption)
      | (aeneas_wp [List.length_append, $args,*]; spec_disch_close)
      | (simp only [alloc.vec.Vec.from_val, Slice.from_val, List.length_append, List.length_take,
          List.length_drop, List.length_replicate, List.length_cons, List.length_nil, $args,*];
          scalar_tac))

/-- The list, logic and arithmetic normalisation of the leaves. -/
syntax (name := specBigSimp) "spec_big_simp" " [" Parser.Tactic.simpArg,* "]" : tactic

macro_rules
  | `(tactic| spec_big_simp [$args,*]) => `(tactic|
    simp (disch := spec_disch [$args,*])
        only [take_succ_of_lt, find?_of_take_none, findIdx?_of_take_none, any_of_getElem,
          List.findIdx?_append, List.findIdx?_nil, List.findIdx?_cons, Option.none_or,
          Option.getD_some, Option.getD_none, Option.isSome_some, Option.isSome_none,
          List.take_of_length_le, List.take_zero,
          List.replicate_succ', List.range_succ, List.replicate_zero, List.range_zero,
          List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
          List.set_append_left, List.set_append_right, set_drop_zero, List.take_append_drop,
          set_replicate_zero, List.take_take,
          Nat.min_eq_left, Nat.sub_self, Nat.add_sub_cancel_left, Nat.add_sub_cancel,
          drop_add_add_one, replicate_sub_of_le, replicate_succ_sub, Nat.zero_sub,
          List.map_append, List.map_cons, List.map_nil, List.filter_append, List.filter_cons,
          List.filter_nil, List.foldl_append, List.foldl_cons, List.foldl_nil, List.find?_append,
          List.any_append, List.any_cons, List.any_nil, List.all_append, List.all_cons,
          List.all_nil, Bool.or_false, Bool.or_true, Bool.false_or, Bool.true_or, Bool.and_true,
          Bool.and_false, Bool.true_and, Bool.false_and, decide_true, decide_false,
          List.append_assoc, List.append_nil, List.nil_append, List.cons_append,
          List.singleton_append, List.length_map, List.length_take, List.length_append,
          List.length_cons, List.length_nil, List.length_singleton, Nat.add_zero, Nat.zero_add,
          decide_eq_true_eq, ne_eq, not_true_eq_false, not_false_eq_true, _root_.ite_true,
          _root_.ite_false,
          ↓reduceIte, ↓reduceDIte, Bool.false_eq_true, false_and, and_false, true_and, and_true,
          exists_false, exists_const, false_or, or_false, Except.ok.injEq, Prod.mk.injEq,
          exists_eq_left', exists_eq_left, exists_and_left, exists_and_right, and_assoc,
          Option.map_some, Option.map_none, reduceCtorEq, $args,*, *])

/-- The leaves of a loop step or of the initial state (see the module doc). -/
syntax (name := specLeaves) "spec_leaves" " [" Parser.Tactic.simpArg,* "]" : tactic

macro_rules
  | `(tactic| spec_leaves [$args,*]) => do
    let user : SimpArgs := args.getElems ++ (← specLib)
    let base : SimpArgs ← #[
      ← `(Parser.Tactic.simpArg| alloc.vec.Vec.from_val),
      ← `(Parser.Tactic.simpArg| UScalar.ofNatCore_val_eq),
      ← `(Parser.Tactic.simpArg| Option.none_or),
      ← `(Parser.Tactic.simpArg| List.find?_cons),
      ← `(Parser.Tactic.simpArg| List.find?_nil),
      ← `(Parser.Tactic.simpArg| Option.some.injEq)].mapM fun x => pure ⟨x.raw⟩
    let all := base ++ user
    `(tactic| (
      (try split_ifs) <;>
      (try (contradiction; done)) <;>
      (try simp only [loopCls_cont, loopCls_done, loopCls_error]) <;>
      (try aeneas_wp [$user,*]) <;>
      (try spec_elem_facts) <;>
      (try iterate (simp (disch := spec_disch [$all,*]) only [$user,*]; try aeneas_wp [$user,*]))
        <;>
      (try split_ifs) <;>
      (try spec_count_exit) <;>
      (try simp (disch := omega) only [List.take_of_length_le] at *) <;>
      (try spec_big_simp [$all,*]) <;>
      (try (split_ifs <;> (try spec_big_simp [$all,*]))) <;>
      -- computations that the normalisation exposed (a call rewritten by its specification)
      (try (aeneas_wp [$user,*] <;> (try split_ifs) <;> (try spec_big_simp [$all,*]))) <;>
      (try simp only [alloc.vec.Vec.eq_iff, alloc.vec.Vec.from_val, Slice.eq_iff, Slice.from_val,
        *]) <;>
      (try spec_len_facts) <;>
      (try simp_all only [List.length_map, List.length_take, List.length_append,
        List.length_cons, List.length_nil, List.length_singleton]) <;>
      (try scalar_tac) <;> (try omega)))

namespace SpecAuto

/-- The list `xs.val` of a slice or vector length `Slice.len xs` / `Vec.len xs`. -/
def lenList? (b : Expr) : MetaM (Option Expr) := do
  let b := b.cleanupAnnotations
  if b.isAppOfArity ``Slice.len 2 then return some (← mkAppM ``Slice.val #[b.appArg!])
  if b.isAppOfArity ``alloc.vec.Vec.len 2 then
    return some (← mkAppM ``alloc.vec.Vec.val #[b.appArg!])
  return none

/-- The pieces of an append chain `a ++ b ++ …` (either association; `x :: l` is `[x] ++ l`). -/
partial def appendPieces (e : Expr) : MetaM (Array Expr) := do
  if e.isAppOfArity ``HAppend.hAppend 6 then
    return (← appendPieces (e.getArgD 4 e)) ++ (← appendPieces (e.getArgD 5 e))
  if e.isAppOfArity ``List.cons 3 && !(e.getArgD 2 e).isAppOf ``List.nil then
    let x := e.getArgD 1 e
    return #[← mkListLit (← inferType x) [x]] ++ (← appendPieces (e.getArgD 2 e))
  return #[e]

/-- The closed subterms of `e` that mention `L`, with the prefixes of append chains. -/
partial def specTerms (L e : Expr) (acc : Array Expr) : MetaM (Array Expr) := do
  let mut acc := acc
  let mentions (x : Expr) : Bool := (x.find? (· == L)).isSome
  if !e.hasLooseBVars && mentions e && !acc.contains e then
    acc := acc.push e
    if e.isAppOfArity ``HAppend.hAppend 6 || e.isAppOfArity ``List.cons 3 then
      let ps ← appendPieces e
      let mut pre := ps.getD 0 e
      for k in [1:ps.size] do
        unless acc.contains pre do
          if mentions pre then acc := acc.push pre
        pre ← mkAppM ``HAppend.hAppend #[pre, ps.getD k e]
  match e with
  | .app f a => specTerms L a (← specTerms L f acc)
  | .lam _ t b _ | .forallE _ t b _ => specTerms L b (← specTerms L t acc)
  | .mdata _ b => specTerms L b acc
  | .letE _ t v b _ => specTerms L b (← specTerms L v (← specTerms L t acc))
  | _ => return acc

/-- Decoders `g` applied to vector contents in `e` (`List.map g (Vec.val v)`). -/
partial def decoders (e : Expr) (acc : Array Expr) : Array Expr :=
  let acc := if e.isAppOfArity ``List.map 4 && (e.getArgD 3 e).isAppOf ``alloc.vec.Vec.val &&
      !(e.getArgD 2 e).hasLooseBVars && !acc.contains (e.getArgD 2 e) then
    acc.push (e.getArgD 2 e) else acc
  match e with
  | .app f a => decoders a (decoders f acc)
  | .lam _ t b _ | .forallE _ t b _ => decoders b (decoders t acc)
  | .mdata _ b => decoders b acc
  | _ => acc

/-- The representations of a loop variable `c` that a specification term can equal. -/
def reps (c : Expr) (decs : Array Expr) : MetaM (Array Expr) := do
  let ty ← whnfR (← inferType c)
  if ty.isAppOfArity ``alloc.vec.Vec 1 then
    let v ← mkAppM ``alloc.vec.Vec.val #[c]
    let mut out := #[v]
    for g in decs do
      try out := out.push (← mkAppM ``List.map #[g, v]) catch _ => pure ()
    return out
  -- a slice or an array (written in place): its contents
  if ty.isAppOfArity ``Slice 1 then return #[← mkAppM ``Slice.val #[c]]
  if ty.isAppOfArity ``Aeneas.Std.Array 2 then return #[← mkAppM ``Aeneas.Std.Array.val #[c]]
  if ty.isAppOfArity ``UScalar 1 then return #[c, ← mkAppM ``UScalar.val #[c]]
  if ty.isAppOfArity ``IScalar 1 then return #[c, ← mkAppM ``IScalar.val #[c]]
  return #[c]

/-- `simp` on `p`: `some true` if it proves `p`, `some false` if it proves `¬ p`. -/
def simpDecide (p : Expr) : TacticM (Option Bool) := do
  let attempt (q : Expr) : TacticM Bool := do
    let g ← mkFreshExprMVar q
    let s ← saveState
    try
      let gs ← Tactic.run g.mvarId! (evalTactic (← `(tactic| simp [alloc.vec.Vec.from_val])))
      let ok := gs.isEmpty
      s.restore
      return ok
    catch _ => s.restore; return false
  if ← attempt p then return some true
  if ← attempt (mkNot p) then return some false
  return none

/-- A loop index in a body already normalized by `aeneas_wp`: a comparison
`UScalar.val c_k OP List.length L` with `L` not depending on the loop state. -/
partial def valIndex? (cs : Array Expr) (fuel : Nat) (e : Expr) : MetaM (Option (Nat × Expr)) := do
  if fuel = 0 then return none
  let e ← AutoCouple.headNorm e
  if let some (a, _, b) := AutoCouple.cmpOf? e then
    let a ← AutoCouple.headNorm a
    let b ← AutoCouple.headNorm b
    let indexOf (x y : Expr) : MetaM (Option (Nat × Expr)) := do
      if x.isAppOfArity ``UScalar.val 2 && y.isAppOfArity ``List.length 2 then
        let L := y.getArgD 1 y
        if L.hasLooseBVars || cs.any (fun c => (L.find? (· == c)).isSome) then return none
        let c ← AutoCouple.headNorm (x.getArgD 1 x)
        return (cs.findIdx? (· == c)).map (·, L)
      return none
    if let some r ← indexOf a b then return some r
    if let some r ← indexOf b a then return some r
  match e with
  | .app .. =>
    for x in e.getAppArgs do
      if let some r ← valIndex? cs (fuel - 1) x then return some r
    return none
  | .lam _ _ b _ => valIndex? cs (fuel - 1) b
  | _ => return none

/-- How the loop index walks: the list `L` (the prefix after `i` iterations is `take i L`), or a
counter up to `N` (a `Nat`; the prefix of a term is the term at `i` instead of `N`). -/
inductive Walk where
  | list (L : Expr)
  | count (N : Expr)

/-- The loop index: loop variable `k`, or the `start` of loop variable `k` when it is a `Range`
(`for i in a..b`, whose `end` is `stop`). -/
structure LoopIndex where
  k : Nat
  range : Bool := false
  walk : Walk
  stop : Expr := mkConst ``Unit

/-- The term `t` at the prefix `i` of the walk. -/
def Walk.prefixAt (w : Walk) (t i : Expr) : MetaM Expr := do
  match w with
  | .list L =>
    let take ← mkAppM ``List.take #[i, L]
    return t.replace fun e => if e == L then some take else none
  | .count N => return t.replace fun e => if e == N then some i else none

/-- The term `t` at the empty prefix. -/
def Walk.prefixNil (w : Walk) (t : Expr) : MetaM Expr := do
  match w with
  | .list L =>
    let nil ← mkAppOptM ``List.nil #[(← inferType L).appArg!]
    return t.replace fun e => if e == L then some nil else none
  | .count N => return t.replace fun e => if e == N then some (mkNatLit 0) else none

/-- What the terms of the specification mention: `L` or `N`. -/
def Walk.anchor : Walk → Expr
  | .list L => L
  | .count N => N

/-- The number of iterations: `L.length` or `N`. -/
def Walk.total : Walk → MetaM Expr
  | .list L => mkAppM ``List.length #[L]
  | .count N => pure N

/-- A `Range usize` loop variable (`for i in a..b`), from its entry value `a..b`. -/
def rangeIndex? (side : AutoCouple.Side) : MetaM (Option LoopIndex) := do
  for j in [0:side.comps.size] do
    let ty ← whnfR (side.comps.getD j (mkConst ``Unit))
    unless ty.isAppOfArity ``core.ops.range.Range 1 do continue
    let x ← whnfR (← AutoCouple.headNorm (side.init.getD j (mkConst ``Unit)))
    unless x.isAppOfArity ``core.ops.range.Range.mk 3 do continue
    let stop := x.getArgD 2 x
    if let some L ← lenList? stop then return some { k := j, range := true, walk := .list L, stop }
    if let some N ← AutoCouple.scalarVal? stop then
      return some { k := j, range := true, walk := .count N, stop }
  return none

/-- `(a, b).1 = a` and `(a, b).2 = b` everywhere in `e` (the loop variables of a body applied to a
tuple). -/
def reduceTupleProjs (e : Expr) : MetaM Expr :=
  Meta.transform e (post := fun e => do
    if e.isAppOfArity ``Prod.fst 3 || e.isAppOfArity ``Prod.snd 3 then
      let a := e.appArg!
      if a.isAppOfArity ``Prod.mk 4 then
        return .visit (if e.isAppOfArity ``Prod.fst 3 then a.getArgD 2 a else a.getArgD 3 a)
    if let .proj ``Prod i a := e then
      if a.isAppOfArity ``Prod.mk 4 then return .visit (a.getArgD (2 + i) a)
    return .continue)

/-- The `if` at the head of the loop body whose other branch returns `done`: the condition under
which the loop goes on and its `Decidable` instance, the condition under which it stops (without a
double negation), as functions of the loop variables, and the loop variables they mention. -/
def headCond? (B : Expr) (comps : Array Expr) :
    MetaM (Option (Expr × Expr × Expr × Array Nat)) := do
  let mut decls : Array (Name × Expr) := #[]
  for ty in comps do decls := decls.push (Name.mkSimple s!"c{decls.size}", ty)
  withLocalDeclsDND decls fun cs => do
    let e ← reduceTupleProjs (← AutoCouple.headNorm (mkApp B (← AutoCouple.stateTuple cs)))
    unless e.isAppOfArity ``ite 5 do return none
    -- the exit: a branch that ends in `done` and never in `cont` (code after the loop that an
    -- early `return` in the loop moved into it)
    let isDone (x : Expr) : MetaM Bool := do
      let x ← instantiateMVars x
      return (x.find? (·.isConstOf ``ControlFlow.cont)).isNone &&
        (x.find? (·.isConstOf ``ControlFlow.done)).isSome
    let c := e.getArgD 1 e
    let inst := e.getArgD 2 e
    let vars := (List.range cs.size).toArray.filter fun j =>
      (c.find? (· == cs.getD j c)).isSome
    if ← isDone (e.getArgD 4 e) then
      return some (← mkLambdaFVars cs c, ← mkLambdaFVars cs inst, ← mkLambdaFVars cs (mkNot c),
        vars)
    if ← isDone (e.getArgD 3 e) then
      return some (← mkLambdaFVars cs (mkNot c),
        ← mkLambdaFVars cs (← mkAppOptM ``instDecidableNot #[c, inst]), ← mkLambdaFVars cs c, vars)
    return none

/-- The conditions of the `if`s of `e` that mention no bound variable. -/
def closedConds (e : Expr) : MetaM (Array Expr) := do
  let ifs ← closedSubterms (fun _ => false) e #[]
  let r ← IO.mkRef ifs
  e.forEach fun x => do
    if x.isAppOfArity ``ite 5 || x.isAppOfArity ``dite 5 then
      let c := x.getArgD 1 x
      if !c.hasLooseBVars then
        let a ← r.get
        unless a.contains c do r.set (a.push c)
  r.get

/-- The loop variables whose value at the head of the loop body is tested by an `if` of it. -/
def condVars (B : Expr) (comps : Array Expr) : MetaM (Array Nat) := do
  let mut decls : Array (Name × Expr) := #[]
  for ty in comps do decls := decls.push (Name.mkSimple s!"c{decls.size}", ty)
  withLocalDeclsDND decls fun cs => do
    let e ← reduceTupleProjs
      (← zetaReduce (← AutoCouple.headNorm (mkApp B (← AutoCouple.stateTuple cs))))
    let conds ← closedConds e
    return (List.range cs.size).toArray.filter fun j =>
      conds.any fun c => (c.find? (· == cs.getD j c)).isSome

/-- The most `Vec.push` calls on a vector of elements `T` along a path of a loop body that goes
on (`cont`) or of a computation inside it that returns: a bind adds, an `if` or a `match` takes
the larger branch, a path that ends in `done` or `fail` does not count, any other call counts 0.
`none` if no path goes on. -/
partial def pushCount (T : Expr) (e : Expr) : MetaM (Option Nat) := do
  let maxOpt : Option Nat → Option Nat → Option Nat
    | some a, some b => some (max a b)
    | some a, none | none, some a => some a
    | none, none => none
  let e := e.headBeta
  match e with
  | .letE _ _ _ b _ | .mdata _ b | .lam _ _ b _ => return ← pushCount T b
  | _ => pure ()
  let seq (m f : Expr) : MetaM (Option Nat) := do
    match ← pushCount T m, ← pushCount T f with
    | some a, some b => return some (a + b)
    | _, _ => return none
  if e.isAppOfArity ``Bind.bind 6 then return ← seq (e.getArgD 4 e) (e.getArgD 5 e)
  if e.isAppOfArity ``Aeneas.Std.bind 4 then return ← seq (e.getArgD 2 e) (e.getArgD 3 e)
  if e.isAppOfArity ``ite 5 || e.isAppOfArity ``dite 5 then
    return maxOpt (← pushCount T (e.getArgD 3 e)) (← pushCount T (e.getArgD 4 e))
  if e.isAppOfArity ``Result.ok 2 then
    return if e.appArg!.isAppOf ``ControlFlow.done then none else some 0
  if e.isAppOf ``Result.fail then return none
  -- a tuple pattern `let (a, b) ← m` (`uncurry fun a b => …`)
  if e.isAppOf ``Aeneas.Std.uncurry && e.getAppNumArgs ≥ 4 then
    return ← pushCount T (e.getArgD 3 e)
  if e.isAppOfArity ``alloc.vec.Vec.push 3 then
    let U := e.getArgD 0 e
    let same ← if U.hasLooseBVars then pure false else withNewMCtxDepth (isDefEq U T)
    return some (if same then 1 else 0)
  if let .const n _ := e.getAppFn then
    if let some info ← getMatcherInfo? n then
      let args := e.getAppArgs
      let mut best : Option Nat := none
      for a in args.extract info.getFirstAltPos (info.getFirstAltPos + info.numAlts) do
        best := maxOpt best (← pushCount T a)
      return best
  return some 0

/-- `pushCount` for the elements `T` in the body `B` of a loop with loop variables `comps`. -/
def pushesPerIteration (B : Expr) (comps : Array Expr) (T : Expr) : MetaM (Option Nat) := do
  let mut decls : Array (Name × Expr) := #[]
  for ty in comps do decls := decls.push (Name.mkSimple s!"c{decls.size}", ty)
  withLocalDeclsDND decls fun cs => do
    let e ← reduceTupleProjs (← AutoCouple.headNorm (mkApp B (← AutoCouple.stateTuple cs)))
    pushCount T e

/-- The candidate invariants for the loop `loop B x₀` (state type `σ`, `side`) with postcondition
`Q` and loop index `idx`, each with its variant. -/
def invariantsAt (σ B Q : Expr) (side : AutoCouple.Side) (idx : LoopIndex) :
    TacticM (Array (Expr × Expr)) := do
  let n := side.comps.size
  let k := idx.k
  let w := idx.walk
  -- a loop whose condition does not test the index: a flag (e.g. end of file) ends it
  let hc? ← headCond? B side.comps
  let flagLoop := match hc? with
    | some (_, _, _, vars) => !vars.contains k
    | none => false
  let flags ← if flagLoop then condVars B side.comps else pure #[]
  let Q ← instantiateMVars Q
  let mut terms ← specTerms w.anchor Q #[]
  -- the fields of structure-valued terms (e.g. the state of a `foldl` specification)
  for t in terms do
    let ty ← whnfR (← inferType t)
    let .const sn _ := ty.getAppFn | continue
    let some info := getStructureInfo? (← getEnv) sn | continue
    if sn == ``List then continue
    for f in info.fieldNames do
      try
        let pt ← mkProjection t f
        unless terms.contains pt do terms := terms.push pt
      catch _ => pure ()
  let decs := decoders Q #[]
  let total ← w.total
  -- candidate facts per loop variable, as functions of the state
  withLocalDeclD `s σ fun s => do
    let ps ← (List.range n).toArray.mapM fun j => AutoCouple.stateProj s n j
    let ci := ps.getD k s
    let iv ← if idx.range then mkAppM ``UScalar.val #[← mkAppM ``core.ops.range.Range.start #[ci]]
      else mkAppM ``UScalar.val #[ci]
    let mut perVar : Array (Array Expr) := #[]
    let mut flagFacts : Array Expr := #[]
    let mut accs := 0
    for j in [0:n] do
      if j == k then continue
      let cj := ps.getD j s
      let c0 := side.init.getD j cj
      if side.unchanged.getD j false then
        perVar := perVar.push #[← mkEq cj c0]
        continue
      if flags.contains j then
        flagFacts := flagFacts.push (← mkEq cj c0)
        continue
      accs := accs + 1
      let mut good : Array Expr := #[]
      let mut unknown : Array Expr := #[]
      let rs ← reps cj decs
      let rs0 ← reps c0 decs
      for ri in [0:rs.size] do
        let r := rs.getD ri cj
        let r0 := rs0.getD ri c0
        for t in terms do
          unless ← withNewMCtxDepth (isDefEq (← inferType t) (← inferType r)) do continue
          let fact ← mkEq r (← w.prefixAt t iv)
          match ← simpDecide (← mkEq r0 (← w.prefixNil t)) with
          | some true => good := good.push fact
          | some false => pure ()
          | none => unknown := unknown.push fact
      -- candidates whose entry value `simp` proves first; the undecided ones only if none is;
      -- the more structured terms first (`(take i xs).filter p` before `take i xs`)
      let byDepth (a b : Expr) : Bool := a.approxDepth > b.approxDepth
      perVar := perVar.push (if good.isEmpty then unknown.qsort byDepth else good.qsort byDepth)
    -- a search loop: facts on `Option` terms, the smallest first (`find? p (take i xs) = none`
    -- before a term built on it)
    let mut extra : Array Expr := #[]
    if accs == 0 then
      let mut opts : Array Expr := #[]
      for t in terms do
        let ty ← whnfR (← inferType t)
        if ty.isAppOf ``Option || ty.isConstOf ``Bool then opts := opts.push t
      opts := opts.qsort fun a b => a.approxDepth < b.approxDepth
      for t in opts do
        extra := extra.push (← mkEq (← w.prefixAt t iv) (← w.prefixNil t))
    -- combinations (at most 12)
    let mut combos : Array (Array Expr) := #[#[]]
    for cands in perVar do
      if cands.isEmpty then continue
      let mut next : Array (Array Expr) := #[]
      for c in combos do
        for f in cands do
          if next.size < 12 then next := next.push (c.push f)
      combos := next
    if !extra.isEmpty then
      combos := combos.flatMap fun c => extra.map (c.push ·) |>.push c
    let mut bound : Array Expr := #[← mkAppM ``LE.le #[iv, total]]
    -- a range keeps its end
    if idx.range then
      bound := bound.push (← mkEq (← mkAppM ``core.ops.range.Range.end #[ci]) idx.stop)
    -- each vector grows by at most one element per iteration
    let mut lens : Array Expr := #[]
    for j in [0:n] do
      if j == k || side.unchanged.getD j false then continue
      let cj := ps.getD j s
      let ty ← whnfR (← inferType cj)
      if ty.isAppOfArity ``alloc.vec.Vec 1 then
        let c0 := side.init.getD j cj
        let l ← mkAppM ``List.length #[← mkAppM ``alloc.vec.Vec.val #[cj]]
        let l0 ← mkAppM ``List.length #[← mkAppM ``alloc.vec.Vec.val #[c0]]
        -- `k` pushes per iteration at most (`k * i`; `i` when `k ≤ 1`)
        let k := (← pushesPerIteration B side.comps (ty.getArgD 0 ty)).getD 1
        let grow ← if k ≤ 1 then pure iv else mkAppM ``HMul.hMul #[mkNatLit k, iv]
        lens := lens.push (← mkAppM ``LE.le #[l, ← mkAppM ``HAdd.hAdd #[l0, grow]])
    -- the flag loop: while it goes on, the flags keep their entry values; it stops at the end
    let mut phase : List Expr := []
    let mut V ← mkAppM ``HSub.hSub #[total, iv]
    if flagLoop then
      if let some (cL, instL, sL, _) := hc? then
        let c := cL.beta ps
        let inst := instL.beta ps
        let going := mkAndN (c :: flagFacts.toList)
        let stopped := mkAnd (sL.beta ps) (← mkEq iv total)
        phase := [mkOr going stopped]
        let one ← mkAppOptM ``ite #[mkConst ``Nat, c, inst, mkNatLit 1, mkNatLit 0]
        V ← mkAppM ``HAdd.hAdd #[V, one]
    let Vl ← mkLambdaFVars #[s] V
    let mut invs : Array (Expr × Expr) := #[]
    for c in combos do
      invs := invs.push
        (← mkLambdaFVars #[s] (mkAndN (bound.toList ++ (c ++ lens).toList ++ phase)), Vl)
      unless lens.isEmpty do
        invs := invs.push (← mkLambdaFVars #[s] (mkAndN (bound.toList ++ c.toList ++ phase)), Vl)
    -- each failed attempt costs heartbeats of the declaration: at most 8
    return invs.extract 0 8

/-- The candidate invariants for the loop `loop B x₀` (state type `σ`) with postcondition
`Q`, each with its variant. -/
def invariants (σ B x₀ Q : Expr) : TacticM (Array (Expr × Expr)) := do
  let side ← AutoCouple.side σ B x₀ #[]
  -- the index and what it walks
  let mut idx? : Option LoopIndex ← rangeIndex? side
  if idx?.isNone then
    for bd in side.bounds do
      if bd.lower || idx?.isSome then continue
      if let some L ← lenList? bd.rhs then idx? := some { k := bd.comp, walk := .list L }
  if idx?.isNone then
    let mut decls : Array (Name × Expr) := #[]
    for ty in side.comps do decls := decls.push (Name.mkSimple s!"c{decls.size}", ty)
    let r ← withLocalDeclsDND decls fun cs => do
      valIndex? cs 512 (mkApp B (← AutoCouple.stateTuple cs))
    if let some (k, L) := r then idx? := some { k, walk := .list L }
  if idx?.isNone then
    for bd in side.bounds do
      if bd.lower || idx?.isSome then continue
      let ty ← whnfR (side.comps.getD bd.comp (mkConst ``Unit))
      unless ty.isAppOfArity ``UScalar 1 && (ty.getArgD 0 ty).isConstOf ``UScalarTy.Usize do
        continue
      if let some N ← AutoCouple.scalarVal? bd.rhs then
        idx? := some { k := bd.comp, walk := .count N }
  let some idx := idx?
    | throwError "aeneas_spec: no loop index (a `usize` compared with the length of a slice or \
        with a bound, or a `for` range)"
  -- a counter loop that also reads a slice (a padded copy: `while i < width`, `if i < s.len()`):
  -- the count walk of the bound of its head condition too, after the list walk
  let mut alt? : Option LoopIndex := none
  if !idx.range then
    if let .list _ := idx.walk then
      if let some (cL, _, _, _) ← headCond? B side.comps then
        for bd in side.bounds do
          if bd.lower || alt?.isSome || bd.comp != idx.k then continue
          if (← lenList? bd.rhs).isSome then continue
          unless (cL.find? (· == bd.rhs)).isSome do continue
          if let some N ← AutoCouple.scalarVal? bd.rhs then
            alt? := some { k := bd.comp, walk := .count N }
  let invs ← invariantsAt σ B Q side idx
  match alt? with
  | some a => return invs ++ (← invariantsAt σ B Q side a)
  | none => return invs

end SpecAuto

/-- One loop `wp (loop B x₀) Q` with a generated invariant (see the module doc). -/
syntax (name := specLoop) "spec_loop" " [" ident,* "]" " [" Parser.Tactic.simpArg,* "]" : tactic

/-- Debugging: the first candidate invariant of `spec_loop`, with its error. -/
syntax (name := specLoopDbg) "spec_loop!" " [" ident,* "]" " [" Parser.Tactic.simpArg,* "]" :
  tactic

/-- Shrink the postcondition of a loop goal: the branches that the symbolic execution of the code
around the loop made trivially false (`error = ok _`), and `∃ v, ok x = ok v ∧ …`. -/
macro "spec_shrink_post" : tactic => `(tactic|
  simp only [reduceCtorEq, false_and, and_false, exists_false, exists_const, false_or, or_false,
    Except.ok.injEq, exists_eq_left', exists_eq_left, exists_and_left, exists_and_right, and_assoc,
    true_and, and_true, _root_.dite_false, _root_.ite_false, _root_.dite_true, _root_.ite_true,
    uscalar_ofNat_val, iscalar_ofInt_val, Int.reduceSub, Int.reduceAdd, Int.reduceNeg, Int.reduceLE,
    Int.reduceLT, Int.reduceEq, Nat.reduceEqDiff, eq_self_iff_true, not_true_eq_false,
    not_false_eq_true, and_self])

/-- The invariant at the entry of a search: `find? p [] = none`, … -/
macro "spec_nil_simp" : tactic => `(tactic|
  simp only [List.find?_nil, List.findIdx?_nil, List.any_nil, List.map_nil, List.filter_nil,
    List.foldl_nil, List.length_nil, List.append_nil, List.nil_append] at *)

def runSpecLoop (defs : Array Ident) (args : SimpArgs) (debug : Bool)
    (user? : Option (Syntax.Term × Syntax.Term) := none) : TacticM Unit := do
  evalTactic (← `(tactic| try spec_shrink_post))
  let g ← getMainGoal
  g.withContext do
  let ty := (← instantiateMVars (← g.getType)).cleanupAnnotations
  unless ty.isAppOfArity ``EquivLean.wp 5 do throwError "spec_loop: the goal is not `wp c Q`"
  let some (σ, B, x₀) := AutoCouple.loopOf? (ty.getArgD 3 ty)
    | throwError "spec_loop: the goal is not `wp (loop body init) Q`"
  let invs ← match user? with
    | some (i, v) => do
      -- the user's invariant and variant, on the loop state
      let I ← instantiateMVars (← elabTermEnsuringType i (← mkArrow σ (mkSort Level.zero)))
      let V ← instantiateMVars (← elabTermEnsuringType v (← mkArrow σ (mkConst ``Nat)))
      pure #[(I, V)]
    | none => SpecAuto.invariants σ B x₀ (ty.getArgD 4 ty)
  let defArgs : SimpArgs := defs.map identSimpArg
  let lib ← liftMacroM specLib
  let stepArgs : SimpArgs := defArgs ++ args ++ lib
  -- the hypotheses are normalised without the user's lemmas (a lemma among the hypotheses would
  -- rewrite itself to `True`)
  let hypArgs : SimpArgs := defArgs ++ lib
  let errors : TacticM Nat := do
    return (← Core.getMessageLog).toList.countP (·.severity == .error)
  let e1 ← errors
  let s0 ← saveState
  for (I, V) in invs do
    if debug then
      let Is ← Term.exprToSyntax I
      let Vs ← Term.exprToSyntax V
      evalTactic (← `(tactic| refine wp_loop (loop_shape _) $Is $Vs ?_ _ ?_))
      evalTactic (← `(tactic| case refine_1 =>
                                  try simp only [Prod.forall]
                                  intros
                                  try casesm* _ ∧ _
                                  try casesm* _ ∨ _
                                  all_goals (try casesm* _ ∧ _)
                                  all_goals (try subst_vars)
                                  all_goals (try spec_nil_simp)
                                  all_goals (try (aeneas_wp [rust_loop_body, $hypArgs,*] at *))
                                  all_goals (try (aeneas_wp [rust_loop_body, $stepArgs,*]))
                                  all_goals (spec_leaves [$args,*])
                                  all_goals (try spec_loop [$defs,*] [$args,*])))
      evalTactic (← `(tactic| case refine_2 => spec_leaves [$args,*]))
      return
    try
      withoutRecover <| focus do
        let Is ← Term.exprToSyntax I
        let Vs ← Term.exprToSyntax V
        evalTactic (← `(tactic| refine wp_loop (loop_shape _) $Is $Vs ?_ _ ?_))
        evalTactic (← `(tactic| · try simp only [Prod.forall]
                                  intros
                                  try casesm* _ ∧ _
                                  try casesm* _ ∨ _
                                  all_goals (try casesm* _ ∧ _)
                                  all_goals (try subst_vars)
                                  all_goals (try spec_nil_simp)
                                  all_goals (try (aeneas_wp [rust_loop_body, $hypArgs,*] at *))
                                  all_goals (try (aeneas_wp [rust_loop_body, $stepArgs,*]))
                                  all_goals (spec_leaves [$args,*])
                                  all_goals (try spec_loop [$defs,*] [$args,*])))
        evalTactic (← `(tactic| · spec_leaves [$args,*]))
        done
      if (← instantiateMVars (mkMVar g)).hasSorry || (← errors) > e1 then
        throwError "spec_loop: the attempt left an error"
      return
    catch ex =>
      if debug then throw ex
      s0.restore
  throwError "spec_loop: no generated invariant closes this loop; tried{indentD
    (MessageData.joinSep (invs.toList.map (MessageData.ofExpr ·.1)) Format.line)}"

/-- One loop `wp (loop B x₀) Q` with the given invariant `I` and variant `V` (functions of the
loop state, the tuple of the loop variables in the order of the generated `loop` call); the kit
proves the step and the entry. -/
syntax (name := specLoopUsing) "spec_loop_using" " [" ident,* "]" " [" Parser.Tactic.simpArg,* "]"
  " (" term ")" " (" term ")" : tactic

/-- Debugging: `spec_loop_using` with the errors of its attempt. -/
syntax (name := specLoopUsingDbg) "spec_loop_using!" " [" ident,* "]"
  " [" Parser.Tactic.simpArg,* "]" " (" term ")" " (" term ")" : tactic

elab_rules : tactic
  | `(tactic| spec_loop [$defs,*] [$args,*]) => runSpecLoop defs.getElems args.getElems false
  | `(tactic| spec_loop! [$defs,*] [$args,*]) => runSpecLoop defs.getElems args.getElems true
  | `(tactic| spec_loop_using [$defs,*] [$args,*] ($i) ($v)) =>
    runSpecLoop defs.getElems args.getElems false (some (i, v))
  | `(tactic| spec_loop_using! [$defs,*] [$args,*] ($i) ($v)) =>
    runSpecLoop defs.getElems args.getElems true (some (i, v))

/-- Split an `if` at the head of the goal (a condition of the code before the loop), not one
inside the postcondition. -/
elab "spec_split_head" : tactic => withMainContext do
  let t := (← instantiateMVars (← getMainTarget)).cleanupAnnotations
  unless t.isAppOfArity ``ite 5 || t.isAppOfArity ``dite 5 do
    throwError "spec_split_head: no `if` at the head of the goal"
  evalTactic (← `(tactic| split))

/-- `aeneas_spec [defs] (with [lemmas])? (using (I) (V))?` (see the module doc; `using`: the
invariant and the variant of the (first) loop, instead of the generated ones). -/
syntax (name := aeneasSpec) "aeneas_spec" (" [" ident,* "]")?
  (" with" " [" Parser.Tactic.simpArg,* "]")? (" using" " (" term ")" " (" term ")")? :
  tactic

/-- The symbolic execution of `aeneas_spec` up to the loop. -/
syntax (name := specPrelude) "spec_prelude" " [" ident,* "]" " [" Parser.Tactic.simpArg,* "]" :
  tactic

macro_rules
  | `(tactic| spec_prelude [$defs,*] [$args,*]) => do
    let defArgs : SimpArgs := defs.getElems.map identSimpArg
    let wpArgs : SimpArgs := args.getElems ++ (← specLib)
    `(tactic| (
      (try rw [spec_iff_wp])
      (try refine exists_ok_of_wp ?_)
      (try refine eq_ok_of_wp ?_)
      (try simp only [$defArgs,*])
      (try aeneas_wp [$wpArgs,*])
      -- calls before the loop whose specifications have side conditions
      (try iterate (simp (disch := spec_disch [$wpArgs,*]) only [$wpArgs,*]; try aeneas_wp [$wpArgs,*]))
      iterate 8 (all_goals (try spec_split_head))))

macro_rules
  | `(tactic| aeneas_spec $[[$defs,*]]? $[with [$args,*]]? $[using ($i) ($v)]?) => do
    let defs : Array Ident := (defs.map (·.getElems)).getD #[]
    let args : SimpArgs := (args.map (·.getElems)).getD #[]
    match i, v with
    | some i, some v =>
      `(tactic| (
        spec_prelude [$defs,*] [$args,*]
        all_goals (first | spec_loop_using [$defs,*] [$args,*] ($i) ($v) | spec_leaves [$args,*])))
    | _, _ =>
      `(tactic| (
        spec_prelude [$defs,*] [$args,*]
        all_goals (first | spec_loop [$defs,*] [$args,*] | spec_leaves [$args,*])))

end EquivLean.Aeneas
