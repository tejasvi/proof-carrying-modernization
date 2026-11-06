import EquivLean.Bridge.Jimple.Auto

/-!
# Jimple bridge: proving Java methods against functional specifications (`jspec_auto`)

The Java side of a COBOL → Java modernization is a contract of one static method: every
terminating run of `run(records…)` returns `spec(inputs)`, where `spec` is a pure Lean function of
the input records (`List.map`/`filter`/`foldl` over them).  `jspec_auto [defs]` proves such a goal,
`Sat P m S`, for a method whose loop walks an input array and appends to lists, with no loop
invariant written: the invariant is generated, then the verification conditions are proved by
JimpleLean's `jvc` and the kit's closers, and the kernel checks everything (standard axioms).

**Kit** (`EquivLean.Jimple.Spec`): `Pairs R xs ys` (an input array's elements related to the ghost
records, `R` the user's record predicate), `StrAt σ v s`, `StrsAt σ vs ss := strsOf σ vs = some ss`
(the strings a list of references holds, as a function of the heap, so that appending is list
append), `Grows σ σ'` (existing objects unchanged), `Hide` (a fact kept from `jvc`), frame lemmas
(`strsOf_alloc_of`, `strsOf_setObj_of`, `grows_alloc_of`, `grows_setObj_of`, …), index lemmas,
`jlong_cmp_toInt`, and the `jstrLit` simproc (`JStr.ofString "…"` on a literal as its UTF-16 units,
so that string constants and `makeConcatWithConstants` recipes compute).

**Contract shape.**  `S` is a `Spec.of pre post` with the ghost values as parameters (as
`Demo/Jimple/Cbact04c/JavaRunDefs.lean`'s `runSpecG`): `pre args σ` says `args = [.ref a, …]`,
`σ.heap a = some (.array t xs)`, `Pairs (R σ) xs rs`, and which classes are initialized; `post`
says, for each field of the returned object holding a list, `StrsAt σ' ys T` with `T` a function
of `rs`.

**The invariant** (`specAnalyze` + `jspecAuto`):
* `SpecAlign.specAnalyze` runs the method on sampled inputs through JimpleLean's interpreter
  (Align's machinery: loop heads, liveness, `traceHeads`; inputs: arrays of objects with sampled
  primitive and `String` fields) and finds, at the loop head, the index (an `int` local counting the
  iterations), the walked array argument, the locals holding arguments, the locals holding lists
  allocated by the run (with the field of the returned object that holds each list at the end,
  matched by address) and the scalar locals the loop assigns;
* the candidates come from the postcondition: for the output `T` of a list's field, the prefix of
  `T`'s append chain up to its first part built element by element from `rs` (`map`, `filterMap`,
  `flatMap`, `filter`), on `rs.take i` (`[start] ++ (rs.take i).map line`); for a scalar, the fold
  over `rs` inside the outputs, on `rs.take i`;
* the invariant at the head: the index in `[0, rs.length]`, the argument locals, each list local
  holding a fresh `ArrayList` with `StrsAt` of its candidate, each scalar equal to its fold, the
  heap grown from the entry state, the classes initialized; an auxiliary definition
  `<theorem>._jinv0`.

**The proof**: `MethodVC.sat_of_valid` (callees inlined); the entry path by `jvc`; at the loop
head, the exit (the prefix is the whole list) and one more element (`pairs_getElem?'`, the record's
heap facts carried to the current state) by `jvc`, with the string lists, the heap frame and the
folds hidden from it and closed afterwards (`jspecClose`).

Limits (first version): one loop, over one input array with the loop's own index (no flag-driven
`while` loop, no callee loops: a callee is inlined); outputs are lists of strings (`StrsAt`);
scalars whose spec is a `foldl`; `jvc` must close the loop body (a running total in `long` and a
`long` comparison hit a `simp` loop / slow case splits in this version); samples ignore the
precondition.  `set_option jspec.trace true` logs the analysis, the invariant and the goals left by
`jvc`.
-/

open Jimple


namespace EquivLean.Jimple.SpecAlign
open EquivLean.Jimple.Align

/-- A random string (narrow: from two letters). -/
def sampleStr (narrow : Bool) (σ : State) (r : Rng) : Value × State × Rng :=
  let (n, r) := r.range 0 4
  let (cs, r) := (List.range n.toNat).foldl (fun (acc, r) _ =>
    let (c, r) := if narrow then r.range 97 98 else r.range 97 122
    (acc ++ [BitVec.ofInt 16 c], r)) ([], r)
  let (a, σ) := σ.alloc (.str cs)
  (.ref a, σ, r)

/-- A random object of application class `c`: primitive and `String` fields sampled, other
reference fields `null`. -/
def sampleObj (P : Program) (c : ClassName) (narrow : Bool) (σ : State) (r : Rng) :
    Option (Value × State × Rng) := Id.run do
  let some d := P.findClass c | return none
  if d.isAbstract || d.isInterface then return none
  let mut r := r
  let mut σ := σ
  let mut fs : Array (FieldKey × Value) := #[]
  for (key, ft) in P.instanceFields c do
    match ft with
    | .prim p =>
      match samplePrim p narrow r with
      | some (v, r') => fs := fs.push (key, v); r := r'
      | none => return none
    | .cls "java.lang.String" =>
      let (v, σ', r') := sampleStr narrow σ r
      fs := fs.push (key, v); σ := σ'; r := r'
    | _ => fs := fs.push (key, ft.default)
  let (a, σ') := σ.alloc (.plain c fs.toList)
  return some (.ref a, σ', r)

/-- A random argument of type `t` for sample `k`: `Align.sampleArg`, and also arrays of objects
of application classes and objects with `String` fields. -/
def sampleArgS (P : Program) (t : JType) (k : Nat) (σ : State) (r : Rng) :
    Option (Value × State × Rng) :=
  let narrow := k % 2 == 1
  match t with
  | .array (.cls c) => Id.run do
    let len := sampleLengths.getD (k % sampleLengths.length) 3
    let mut r := r
    let mut σ := σ
    let mut xs : Array Value := #[]
    for _ in [0:len] do
      let o := if c == "java.lang.String" then some (sampleStr narrow σ r) else sampleObj P c narrow σ r
      match o with
      | some (v, σ', r') => xs := xs.push v; σ := σ'; r := r'
      | none => return none
    let (a, σ') := σ.alloc (.array (.cls c) xs.toList)
    return some (.ref a, σ', r)
  | .cls "java.lang.String" => some (sampleStr narrow σ r)
  | .cls c => sampleObj P c narrow σ r
  | _ => sampleArg P t k σ r

/-- Arguments of a call of `m` (the receiver first for an instance method), in a fresh heap. -/
def sampleArgsS (P : Program) (m : MethodRef) (k : Nat) (seed : Nat) :
    Option (List Value × State) := Id.run do
  let mut r : Rng := ⟨seed * 7919 + k * 104729 + 17⟩
  let mut σ : State := State.empty
  let mut vs : Array Value := #[]
  let ts := (if m.decl.mods.isStatic then [] else [JType.cls m.cls]) ++ m.decl.params
  for t in ts do
    match sampleArgS P t k σ r with
    | some (v, σ', r') => vs := vs.push v; σ := σ'; r := r'
    | none => return none
  return some (vs.toList, σ)

/-- The roles of the locals at the loop head. -/
structure SpecAnalysis where
  head : Nat
  /-- the index local and the argument (an array) it walks -/
  idx : Nat
  walked : Nat
  /-- `(local, argument)`: the local holds the argument at every visit -/
  argLocals : List (Nat × Nat)
  /-- `(local, field)`: the local holds a list allocated by the run, which the returned object
  holds in this field at the end (`""`: not returned) -/
  listLocals : List (Nat × String)
  /-- `(local, isLong)`: other `int`/`long` locals the loop assigns -/
  scalarLocals : List (Nat × Bool)
  fuel : Nat
  depth : Nat
  isStatic : Bool
  samples : Nat
  deriving Inhabited, Repr

/-- The list object a value refers to. -/
def listAt (σ : State) : Value → Option Addr
  | .ref a => match σ.heap a with
    | some (.list ..) => some a
    | _ => none
  | _ => none

/-- **The analysis** of method `m` (one loop): samples, runs, roles of the head locals. -/
def specAnalyze (P : Program) (m : MethodRef) (nSamples seed : Nat) : Except String SpecAnalysis := do
  let some b := m.decl.body | throw "the method has no body"
  let hs := loopHeads b
  let [h] := hs | throw s!"one loop expected, the loop heads are {hs}"
  let isStatic := m.decl.mods.isStatic
  let live := liveIn b h
  let mods := loopDefs b h
  -- per sample: arguments, entry state, head visits, final state and returned object's fields
  let mut runs : Array (List Value × State × List (Frame × State) × List (FieldKey × Value) × State) := #[]
  for k in [0:nSamples] do
    let some (args, σ0) := sampleArgsS P m k seed
      | throw s!"unsupported parameter types {repr m.decl.params}"
    let (o, tr) := traceHeads P b [h] 1000000 0 (Frame.init isStatic args) σ0 #[]
    match o with
    | some (.normal (some (.ref res)) σf) =>
      let fs := match σf.heap res with
        | some (.plain _ fs) => fs
        | _ => []
      runs := runs.push (args, σ0, tr.toList.map (fun (_, f, s) => (f, s)), fs, σf)
    | _ => pure ()
  if runs.isEmpty then throw "no sample returned an object"
  let allVisits := runs.toList.flatMap fun (args, σ0, vs, _, _) =>
    (vs.zipIdx).map fun ((f, s), j) => (args, σ0, f, s, j)
  let nargs := m.decl.params.length + (if isStatic then 0 else 1)
  -- the index: `int` local = number of iterations done; the walked array: as many elements as
  -- the loop has iterations
  let idxs := live.filter fun x => allVisits.all fun (_, _, f, _, j) =>
    f.get x == some (.int (BitVec.ofNat 32 j))
  let walkedArgs := (List.range nargs).filter fun i => runs.toList.all fun (args, σ0, vs, _, _) =>
    (args[i]?.bind (arrLen σ0)) == some (vs.length - 1)
  let some idx := idxs.head? | throw "no index local (an int local counting the iterations)"
  let some walked := walkedArgs.head? | throw "no array argument with one element per iteration"
  -- argument locals
  let argLocals := live.filterMap fun x =>
    if mods.contains x then none else
    ((List.range nargs).find? fun i => allVisits.all fun (args, _, f, _, _) =>
      f.get x == args[i]? ∧ (f.get x).isSome).map (x, ·)
  -- list locals: a list allocated by the run, the same at every visit of a run
  let listLocals := live.filterMap fun x =>
    if mods.contains x then none else
    let ok := runs.toList.all fun (_, σ0, vs, _, _) => vs.all fun (f, s) =>
      match (f.get x).bind (listAt s) with
      | some a => σ0.next ≤ a
      | none => false
    if !ok then none else
    -- the field of the returned object holding this list (same in every run)
    let fieldOf := fun (fs : List (FieldKey × Value)) (a : Addr) =>
      (fs.find? fun (_, v) => v == .ref a).map (·.1.2)
    let names := runs.toList.filterMap fun (_, _, vs, fs, _) =>
      match vs.head? with
      | some (f, s) => ((f.get x).bind (listAt s)).bind (fieldOf fs)
      | none => none
    let name := match names.eraseDups with
      | [n] => if names.length == runs.size then n else ""
      | _ => ""
    some (x, name)
  -- scalar locals
  let scalarLocals := live.filterMap fun x =>
    if x == idx || !mods.contains x then none
    else if allVisits.all fun (_, _, f, _, _) => match f.get x with | some (.int _) => true | _ => false
    then some (x, false)
    else if allVisits.all fun (_, _, f, _, _) => match f.get x with | some (.long _) => true | _ => false
    then some (x, true)
    else none
  return { head := h, idx, walked, argLocals, listLocals, scalarLocals,
           fuel := segFuel b [h] + 1, depth := if hasCalls b then 4 else 0, isStatic,
           samples := runs.size }

end EquivLean.Jimple.SpecAlign


namespace EquivLean.Jimple.Spec

/-! ## Representation predicates -/

/-- Two lists related element by element. -/
def Pairs {α β : Type} (R : α → β → Prop) : List α → List β → Prop
  | [], [] => True
  | a :: as1, b :: bs1 => R a b ∧ Pairs R as1 bs1
  | _, _ => False

/-- `v` is a reference to a `String` holding `s`. -/
def StrAt (σ : State) (v : Value) (s : JStr) : Prop :=
  ∃ x, v = .ref x ∧ σ.heap x = some (.str s)

/-- The heap only grows: existing objects are unchanged. -/
def Grows (σ σ' : State) : Prop := σ.next ≤ σ'.next ∧ ∀ x, x < σ.next → σ'.heap x = σ.heap x

/-- A hypothesis hidden from `jvc`'s preprocessing. -/
@[irreducible] def Hide (p : Prop) : Prop := p

theorem Hide.intro {p : Prop} (h : p) : Hide p := by unfold Hide; exact h
theorem Hide.elim {p : Prop} (h : Hide p) : p := by unfold Hide at h; exact h
theorem hide_iff (p : Prop) : Hide p ↔ p := by unfold Hide; exact Iff.rfl

/-- Objects that are not strings. -/
def notStr : Obj → Bool
  | .str _ => false
  | _ => true

/-- No contracts: nothing to establish (methods are verified by inlining their callees). -/
theorem valid_none (P : Program) : Valid P (fun _ => none) := fun _ _ h => by cases h

/-! ## `Pairs` -/

@[simp] theorem pairs_nil {α β : Type} (R : α → β → Prop) : Pairs R [] [] := trivial

theorem pairs_length {α β : Type} {R : α → β → Prop} :
    ∀ {xs : List α} {ys : List β}, Pairs R xs ys → xs.length = ys.length
  | [], [], _ => rfl
  | _ :: _, _ :: _, h => by simp [Pairs] at h; simp [pairs_length h.2]
  | [], _ :: _, h => by simp [Pairs] at h
  | _ :: _, [], h => by simp [Pairs] at h

theorem pairs_get {α β : Type} {R : α → β → Prop} :
    ∀ {xs : List α} {ys : List β} (h : Pairs R xs ys) (n : Nat) (hn : n < xs.length),
      R xs[n] (ys[n]'(by rw [← pairs_length h]; exact hn))
  | [], [], _, n, hn => by simp at hn
  | x :: xs, y :: ys, h, 0, _ => by simp [Pairs] at h; simpa using h.1
  | x :: xs, y :: ys, h, n + 1, hn => by
      simp [Pairs] at h
      simpa using pairs_get h.2 n (by simpa using hn)
  | [], _ :: _, h, _, _ => by simp [Pairs] at h
  | _ :: _, [], h, _, _ => by simp [Pairs] at h

theorem pairs_mono {α β : Type} {R R' : α → β → Prop} (hR : ∀ x y, R x y → R' x y) :
    ∀ {xs : List α} {ys : List β}, Pairs R xs ys → Pairs R' xs ys
  | [], [], _ => trivial
  | _ :: _, _ :: _, h => ⟨hR _ _ h.1, pairs_mono hR h.2⟩
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

theorem pairs_append_iff {α β : Type} {R : α → β → Prop} {x : α} {y : β} :
    ∀ {xs : List α} {ys : List β}, Pairs R (xs ++ [x]) (ys ++ [y]) ↔ Pairs R xs ys ∧ R x y
  | [], [] => by simp [Pairs]
  | a :: as1, b :: bs1 => by
      simp only [List.cons_append, Pairs]
      rw [pairs_append_iff]; exact and_assoc.symm
  | [], b :: bs1 => by
      simp only [List.nil_append, List.cons_append, Pairs]
      cases bs1 <;> simp [Pairs]
  | a :: as1, [] => by
      simp only [List.nil_append, List.cons_append, Pairs]
      cases as1 <;> simp [Pairs]

theorem pairs_append_nil {α β : Type} {R : α → β → Prop} {xs : List α} {ys : List β} :
    Pairs R xs (ys ++ []) ↔ Pairs R xs ys := by simp

/-! ## The heap grows -/

theorem grows_refl (σ : State) : Grows σ σ := ⟨Nat.le_refl _, fun _ _ => rfl⟩

theorem grows_trans {σ1 σ2 σ3 : State} (h1 : Grows σ1 σ2) (h2 : Grows σ2 σ3) : Grows σ1 σ3 :=
  ⟨Nat.le_trans h1.1 h2.1, fun x hx => by rw [h2.2 x (Nat.lt_of_lt_of_le hx h1.1), h1.2 x hx]⟩

theorem heap_of_grows {σ0 σ : State} {x : Addr} {o : Obj} (hg : Grows σ0 σ)
    (h : σ0.heap x = some o) : σ.heap x = some o := by
  rw [hg.2 x (State.lt_next_of_heap h), h]

theorem next_of_grows {σ0 σ : State} (hg : Grows σ0 σ) : σ0.next ≤ σ.next := hg.1

theorem grows_alloc (σ : State) (o : Obj) : Grows σ (σ.alloc o).2 := by
  refine ⟨by rw [State.next_alloc]; exact Nat.le_succ _, fun x hx => ?_⟩
  rw [State.heap_alloc, ite_eq_right (Nat.ne_of_lt hx)]

theorem grows_alloc_of {σ0 σ : State} (o : Obj) (h : Grows σ0 σ) : Grows σ0 (σ.alloc o).2 :=
  grows_trans h (grows_alloc σ o)

theorem grows_setObj_of {σ0 σ : State} {l : Addr} {o : Obj} (hg : Grows σ0 σ) (hl : σ0.next ≤ l) :
    Grows σ0 (σ.setObj l o) := by
  refine ⟨by rw [State.next_setObj]; exact hg.1, fun x hx => ?_⟩
  have hxl : x ≠ l := by intro h; subst h; exact absurd hx (Nat.not_lt.mpr hl)
  rw [State.heap_setObj, ite_eq_right hxl, hg.2 x hx]

theorem grows_setInit_of {σ0 σ : State} {c : ClassName} {s : InitSt} (hg : Grows σ0 σ) :
    Grows σ0 (σ.setInit c s) := ⟨hg.1, fun x hx => by rw [State.heap_setInit]; exact hg.2 x hx⟩

theorem grows_setStatic_of {σ0 σ : State} {k : FieldKey} {v : Value} (hg : Grows σ0 σ) :
    Grows σ0 (σ.setStatic k v) := ⟨hg.1, fun x hx => by rw [State.heap_setStatic]; exact hg.2 x hx⟩

/-! ## Strings survive allocation and the update of other objects -/

theorem strAt_alloc_of {σ : State} {v : Value} {s : JStr} (o : Obj) (h : StrAt σ v s) :
    StrAt (σ.alloc o).2 v s := by
  obtain ⟨x, rfl, hx⟩ := h
  exact ⟨x, rfl, heap_of_grows (grows_alloc σ o) hx⟩

theorem strAt_setObj_of {σ : State} {l : Addr} {o o' : Obj} {v : Value} {s : JStr}
    (hl : σ.heap l = some o') (hno : notStr o' = true) (h : StrAt σ v s) :
    StrAt (σ.setObj l o) v s := by
  obtain ⟨x, rfl, hx⟩ := h
  have hxl : x ≠ l := by
    intro h; subst h; rw [hl] at hx; cases hx; simp [notStr] at hno
  exact ⟨x, rfl, by rw [State.heap_setObj, ite_eq_right hxl, hx]⟩

theorem strAt_setInit_of {σ : State} {c : ClassName} {st : InitSt} {v : Value} {s : JStr}
    (h : StrAt σ v s) : StrAt (σ.setInit c st) v s := by
  obtain ⟨x, rfl, hx⟩ := h
  exact ⟨x, rfl, by rw [State.heap_setInit]; exact hx⟩

theorem strAt_of_grows {σ0 σ : State} {v : Value} {s : JStr} (hg : Grows σ0 σ)
    (h : StrAt σ0 v s) : StrAt σ v s := by
  obtain ⟨x, rfl, hx⟩ := h
  exact ⟨x, rfl, heap_of_grows hg hx⟩

theorem strAt_setObj_of' {σ : State} {l : Addr} {o : Obj} {v : Value} {s : JStr}
    (hl : ∀ t, σ.heap l ≠ some (.str t)) (h : StrAt σ v s) : StrAt (σ.setObj l o) v s := by
  obtain ⟨x, rfl, hx⟩ := h
  have hxl : x ≠ l := by intro h; subst h; exact hl s hx
  exact ⟨x, rfl, by rw [State.heap_setObj, ite_eq_right hxl, hx]⟩

theorem strs_setObj_of' {σ : State} {l : Addr} {o : Obj} {vs : List Value} {ss : List JStr}
    (hl : ∀ t, σ.heap l ≠ some (.str t)) (h : Pairs (StrAt σ) vs ss) :
    Pairs (StrAt (σ.setObj l o)) vs ss :=
  pairs_mono (fun _ _ => strAt_setObj_of' hl) h

theorem strs_alloc_of {σ : State} {vs : List Value} {ss : List JStr} (o : Obj)
    (h : Pairs (StrAt σ) vs ss) : Pairs (StrAt (σ.alloc o).2) vs ss :=
  pairs_mono (fun _ _ => strAt_alloc_of o) h

theorem strs_setObj_of {σ : State} {l : Addr} {o o' : Obj} {vs : List Value} {ss : List JStr}
    (hl : σ.heap l = some o') (hno : notStr o' = true) (h : Pairs (StrAt σ) vs ss) :
    Pairs (StrAt (σ.setObj l o)) vs ss :=
  pairs_mono (fun _ _ => strAt_setObj_of hl hno) h

theorem strs_setInit_of {σ : State} {c : ClassName} {st : InitSt} {vs : List Value}
    {ss : List JStr} (h : Pairs (StrAt σ) vs ss) : Pairs (StrAt (σ.setInit c st)) vs ss :=
  pairs_mono (fun _ _ => strAt_setInit_of) h

/-! ## Lists of strings, as a function of the heap -/

/-- The string a value refers to. -/
def strOfV (σ : State) : Value → Option JStr
  | .ref x => match σ.heap x with
    | some (.str s) => some s
    | _ => none
  | _ => none

/-- The strings a list of values refers to (`none` if one is not a string). -/
def strsOf (σ : State) : List Value → Option (List JStr)
  | [] => some []
  | v :: vs => match strOfV σ v, strsOf σ vs with
    | some s, some ss => some (s :: ss)
    | _, _ => none

/-- `vs` are references to strings holding `ss`, in order. -/
def StrsAt (σ : State) (vs : List Value) (ss : List JStr) : Prop := strsOf σ vs = some ss

@[simp] theorem strsOf_nil (σ : State) : strsOf σ [] = some [] := rfl

theorem strsOf_cons (σ : State) (v : Value) (vs : List Value) :
    strsOf σ (v :: vs) = (strOfV σ v).bind fun s => (strsOf σ vs).map (s :: ·) := by
  simp only [strsOf]
  cases strOfV σ v <;> cases strsOf σ vs <;> rfl

theorem strsOf_append (σ : State) :
    ∀ (xs ys : List Value),
      strsOf σ (xs ++ ys) = (strsOf σ xs).bind fun a => (strsOf σ ys).map (a ++ ·)
  | [], ys => by cases h : strsOf σ ys <;> simp [h]
  | x :: xs, ys => by
    rw [List.cons_append, strsOf_cons, strsOf_cons, strsOf_append σ xs ys]
    cases strOfV σ x <;> cases strsOf σ xs <;> cases strsOf σ ys <;> rfl

theorem strsOf_singleton (σ : State) (v : Value) : strsOf σ [v] = (strOfV σ v).map ([·]) := by
  rw [strsOf_cons]; cases strOfV σ v <;> rfl

theorem strOfV_ref (σ : State) (x : Addr) :
    strOfV σ (.ref x) = match σ.heap x with | some (.str s) => some s | _ => none := rfl

theorem strOfV_alloc_of {σ : State} {v : Value} {s : JStr} (o : Obj) (h : strOfV σ v = some s) :
    strOfV (σ.alloc o).2 v = some s := by
  cases v with
  | ref x =>
    simp only [strOfV] at h ⊢
    cases hx : σ.heap x with
    | none => rw [hx] at h; cases h
    | some ob =>
      rw [heap_of_grows (grows_alloc σ o) hx]; rw [hx] at h; exact h
  | _ => simp [strOfV] at h

theorem strOfV_setObj_of {σ : State} {l : Addr} {o : Obj} {v : Value} {s : JStr}
    (hl : ∀ t, σ.heap l ≠ some (.str t)) (h : strOfV σ v = some s) :
    strOfV (σ.setObj l o) v = some s := by
  cases v with
  | ref x =>
    simp only [strOfV] at h ⊢
    have hx : σ.heap x = some (.str s) := by
      cases hx : σ.heap x with
      | none => rw [hx] at h; cases h
      | some ob => rw [hx] at h; cases ob <;> simp at h; subst h; rfl
    have hxl : x ≠ l := by intro e; subst e; exact hl s hx
    rw [State.heap_setObj, ite_eq_right hxl, hx]
  | _ => simp [strOfV] at h

theorem strOfV_setInit_of {σ : State} {c : ClassName} {st : InitSt} {v : Value} {s : JStr}
    (h : strOfV σ v = some s) : strOfV (σ.setInit c st) v = some s := by
  cases v <;> simp_all [strOfV, State.heap_setInit]

theorem strsOf_mono {σ σ' : State} (hv : ∀ v s, strOfV σ v = some s → strOfV σ' v = some s) :
    ∀ {vs : List Value} {ss : List JStr}, strsOf σ vs = some ss → strsOf σ' vs = some ss
  | [], _, h => h
  | v :: vs, ss, h => by
    rw [strsOf_cons] at h ⊢
    cases hs : strOfV σ v with
    | none => rw [hs] at h; cases h
    | some s =>
      rw [hs] at h
      cases hss : strsOf σ vs with
      | none => rw [hss] at h; cases h
      | some ss' =>
        rw [hss] at h
        rw [hv v s hs, strsOf_mono hv hss]
        exact h

theorem strsOf_alloc_of {σ : State} {vs : List Value} {ss : List JStr} (o : Obj)
    (h : strsOf σ vs = some ss) : strsOf (σ.alloc o).2 vs = some ss :=
  strsOf_mono (fun _ _ => strOfV_alloc_of o) h

theorem strsOf_setObj_of {σ : State} {l : Addr} {o : Obj} {vs : List Value} {ss : List JStr}
    (hl : ∀ t, σ.heap l ≠ some (.str t)) (h : strsOf σ vs = some ss) :
    strsOf (σ.setObj l o) vs = some ss :=
  strsOf_mono (fun _ _ => strOfV_setObj_of hl) h

theorem strsOf_setInit_of {σ : State} {c : ClassName} {st : InitSt} {vs : List Value}
    {ss : List JStr} (h : strsOf σ vs = some ss) : strsOf (σ.setInit c st) vs = some ss :=
  strsOf_mono (fun _ _ => strOfV_setInit_of) h

/-! ## Comparisons of `long` values (`lcmp`) -/

theorem jlong_cmp_toInt (a b : I64) :
    (JLong.cmp a b).toInt = if a.toInt < b.toInt then -1 else if a.toInt = b.toInt then 0 else 1 := by
  unfold JLong.cmp
  by_cases h1 : a.toInt < b.toInt
  · have hs : a.slt b = true := by simp [BitVec.slt, h1]
    rw [if_pos hs, if_pos h1]; decide
  · have hs : a.slt b = false := by simp [BitVec.slt, h1]
    rw [if_neg (by simp [hs]), if_neg h1]
    by_cases h2 : a = b
    · subst h2; simp
    · have h2' : a.toInt ≠ b.toInt := fun h => h2 (BitVec.toInt_inj.mp h)
      rw [if_neg h2, if_neg h2']; decide

/-! ## Loop indices -/

/-- `i + 1` on `int` without overflow. -/
theorem i32_toInt_add_one (i : I32) (h0 : 0 ≤ i.toInt) (h1 : i.toInt < 2147483647) :
    (i + 1#32).toInt = i.toInt + 1 := by
  rw [BitVec.toInt_add]
  have : (1#32).toInt = 1 := by decide
  rw [this]
  rw [Int.bmod_def]; split <;> omega

theorem i32_toNat_eq (i : I32) (h0 : 0 ≤ i.toInt) : i.toNat = i.toInt.toNat := by
  rw [BitVec.toInt_eq_toNat_cond] at *
  split at h0 <;> omega

theorem i32_toNat_add_one (i : I32) (h0 : 0 ≤ i.toInt) (h1 : i.toInt < 2147483647) :
    (i + 1#32).toNat = i.toNat + 1 := by
  have h2 := i32_toInt_add_one i h0 h1
  rw [i32_toNat_eq i h0, i32_toNat_eq (i + 1#32) (by omega), h2]
  omega

/-- The `n`-th elements of two related lists, as optional lookups. -/
theorem pairs_getElem? {α β : Type} {R : α → β → Prop} {xs : List α} {ys : List β}
    (h : Pairs R xs ys) {n : Nat} (hn : n < xs.length) :
    ∃ x y, xs[n]? = some x ∧ ys[n]? = some y ∧ R x y :=
  ⟨xs[n], ys[n]'(by rw [← pairs_length h]; exact hn), List.getElem?_eq_getElem hn,
    List.getElem?_eq_getElem _, pairs_get h n hn⟩

/-- `pairs_getElem?` with the bound on the second list. -/
theorem pairs_getElem?' {α β : Type} {R : α → β → Prop} {xs : List α} {ys : List β}
    (h : Pairs R xs ys) {n : Nat} (hn : n < ys.length) :
    ∃ x y, xs[n]? = some x ∧ ys[n]? = some y ∧ R x y :=
  pairs_getElem? h (by rw [pairs_length h]; exact hn)

/-- One more element of the prefix, from an optional lookup. -/
theorem take_succ_of_getElem? {α : Type} {l : List α} {n : Nat} {y : α} (h : l[n]? = some y) :
    l.take (n + 1) = l.take n ++ [y] := by
  rw [List.take_add_one, h]; rfl

/-- One more element of the prefix. -/
theorem take_succ_eq {α : Type} (l : List α) (n : Nat) (h : n < l.length) :
    l.take (n + 1) = l.take n ++ [l[n]] := by
  rw [List.take_add_one, List.getElem?_eq_getElem h]; rfl

open Lean Meta Elab Tactic in
/-- The head of a state term: allocation, object update, class initialization, static field. -/
def stateStep? (τ : Lean.Expr) : Option (Name × Lean.Expr) :=
  let τ := τ.consumeMData
  if τ.isAppOfArity ``Prod.snd 3 && (τ.getArg! 2).isAppOfArity ``State.alloc 2 then
    some (``State.alloc, (τ.getArg! 2).getArg! 0)
  else if τ.isAppOfArity ``State.setObj 3 then some (``State.setObj, τ.getArg! 0)
  else if τ.isAppOfArity ``State.setInit 3 then some (``State.setInit, τ.getArg! 0)
  else if τ.isAppOfArity ``State.setStatic 3 then some (``State.setStatic, τ.getArg! 0)
  else none

open Lean Meta Elab Tactic in
/-- Address side conditions: heap lookups through allocations and updates, decided with the
disequalities of the context. -/
def addrSide : TacticM Unit := do
  evalTactic (← `(tactic| first
    | jomega
    | (simp (disch := jomega) only [State.heap_alloc, State.heap_setObj, State.next_alloc,
        State.next_setObj, State.heap_setInit, State.next_setInit, ite_eq_left, ite_eq_right,
        ite_true, ite_false, ne_eq, reduceCtorEq, Option.some.injEq, not_false_eq_true, *]
       all_goals first | jomega | simp_all)))

open Lean Meta Elab Tactic in
/-- `Pairs (StrAt τ) vs ss` from `Pairs (StrAt σ) vs ss` (a hypothesis) for `τ` built from `σ`
by allocations, class initializations and updates of objects that are not strings. -/
partial def jstrsFrameCore (g : MVarId) : TacticM Unit := do
  setGoals [g]
  let ok ← try evalTactic (← `(tactic| assumption)); pure true catch _ => pure false
  if ok then return
  let t := (← instantiateMVars (← g.getType)).consumeMData
  -- Pairs (StrAt τ) vs ss
  let some τ := (do
      guard (t.isAppOfArity ``Pairs 5)
      let R := t.getArg! 2
      guard (R.isAppOfArity ``StrAt 1)
      pure (R.getArg! 0)) | throwError "jstrs_frame: not `Pairs (StrAt σ) vs ss`: {t}"
  match stateStep? τ with
  | some (``State.alloc, _) =>
    let [g'] ← g.apply (← mkConstWithFreshMVarLevels ``strs_alloc_of) | throwError "jstrs_frame: alloc"
    jstrsFrameCore g'
  | some (``State.setInit, _) =>
    let [g'] ← g.apply (← mkConstWithFreshMVarLevels ``strs_setInit_of) | throwError "jstrs_frame: init"
    jstrsFrameCore g'
  | some (``State.setObj, _) =>
    let gs ← g.apply (← mkConstWithFreshMVarLevels ``strs_setObj_of')
    let [ghl, gh] := gs | throwError "jstrs_frame: setObj goals {gs.length}"
    setGoals [ghl]
    evalTactic (← `(tactic| intro t))
    addrSide
    unless (← getGoals).isEmpty do throwError "jstrs_frame: side condition not closed"
    jstrsFrameCore gh
  | _ => throwError "jstrs_frame: no hypothesis for {t}"

open Lean Meta Elab Tactic in
/-- `strsOf τ vs = some ss` from `strsOf σ vs = some ss` (a hypothesis) for `τ` built from `σ`
by allocations, class initializations and updates of objects that are not strings. -/
partial def jstrsOfFrameCore (g : MVarId) : TacticM Unit := do
  setGoals [g]
  let ok ← try evalTactic (← `(tactic| assumption)); pure true catch _ => pure false
  if ok then return
  let t := (← instantiateMVars (← g.getType)).consumeMData
  let some τ := (do
      guard (t.isAppOfArity ``Eq 3)
      let l := t.getArg! 1
      guard (l.isAppOfArity ``strsOf 2)
      pure (l.getArg! 0)) | throwError "jstrs_frame: not `strsOf σ vs = some ss`: {t}"
  match stateStep? τ with
  | some (``State.alloc, _) =>
    let [g'] ← g.apply (← mkConstWithFreshMVarLevels ``strsOf_alloc_of) | throwError "jstrs_frame: alloc"
    jstrsOfFrameCore g'
  | some (``State.setInit, _) =>
    let [g'] ← g.apply (← mkConstWithFreshMVarLevels ``strsOf_setInit_of) | throwError "jstrs_frame: init"
    jstrsOfFrameCore g'
  | some (``State.setObj, _) =>
    let gs ← g.apply (← mkConstWithFreshMVarLevels ``strsOf_setObj_of)
    let [ghl, gh] := gs | throwError "jstrs_frame: setObj goals {gs.length}"
    setGoals [ghl]
    evalTactic (← `(tactic| intro t))
    addrSide
    unless (← getGoals).isEmpty do throwError "jstrs_frame: side condition not closed"
    jstrsOfFrameCore gh
  | _ => throwError "jstrs_frame: no hypothesis for {t}"

open Lean Elab Tactic in
/-- The frame of a list of string references (`jstrsFrameCore`). -/
elab "jstrs_frame" : tactic => do jstrsFrameCore (← getMainGoal)

open Lean Meta Elab Tactic in
/-- `Grows σ0 τ` from `Grows σ0 σ` (a hypothesis) for `τ` built from `σ` by allocations, class
initializations, static fields and updates of objects allocated after `σ0`. -/
partial def jgrowsCore (g : MVarId) : TacticM Unit := do
  setGoals [g]
  let ok ← try evalTactic (← `(tactic| first | assumption | exact grows_refl _)); pure true
    catch _ => pure false
  if ok then return
  let t := (← instantiateMVars (← g.getType)).consumeMData
  unless t.isAppOfArity ``Grows 2 do throwError "jgrows: not `Grows σ0 τ`: {t}"
  match stateStep? (t.getArg! 1) with
  | some (``State.alloc, _) =>
    let [g'] ← g.apply (← mkConstWithFreshMVarLevels ``grows_alloc_of) | throwError "jgrows: alloc"
    jgrowsCore g'
  | some (``State.setInit, _) =>
    let [g'] ← g.apply (← mkConstWithFreshMVarLevels ``grows_setInit_of) | throwError "jgrows: init"
    jgrowsCore g'
  | some (``State.setStatic, _) =>
    let [g'] ← g.apply (← mkConstWithFreshMVarLevels ``grows_setStatic_of) | throwError "jgrows: static"
    jgrowsCore g'
  | some (``State.setObj, _) =>
    let gs ← g.apply (← mkConstWithFreshMVarLevels ``grows_setObj_of)
    let [gg, ghl] := gs | throwError "jgrows: setObj goals {gs.length}"
    setGoals [ghl]
    evalTactic (← `(tactic| first | jomega | (simp only [State.next_alloc, State.next_setObj, State.next_setInit, State.next_setStatic]; jomega)))
    jgrowsCore gg
  | _ => throwError "jgrows: no hypothesis for {t}"

open Lean Elab Tactic in
/-- `Grows σ0 τ` (`jgrowsCore`). -/
elab "jgrows" : tactic => do jgrowsCore (← getMainGoal)

open Lean Meta in
/-- `JStr.ofString "…"` on a literal as its explicit list of UTF-16 code units (as `JStr.ofChar`
builds it), so that string constants and concatenation recipes compute. -/
dsimproc jstrLit (JStr.ofString _) := fun e => do
  let_expr JStr.ofString s := e | return .continue
  let .lit (.strVal str) := s.consumeMData | return .continue
  let units := JStr.ofString str
  let elems := units.map fun (c : BitVec 16) =>
    mkApp2 (mkConst ``BitVec.ofNat) (mkNatLit 16) (mkNatLit c.toNat)
  return .done (← mkListLit (mkApp (mkConst ``BitVec) (mkNatLit 16)) elems)

end EquivLean.Jimple.Spec


namespace EquivLean.Jimple.Spec

open Lean Meta Elab Tactic

/-! ## Reading the contract -/

/-- Library modules: their definitions are never unfolded as user specifications. -/
def specLibraryRoots : List Name :=
  [`Init, `Lean, `Std, `Jimple, `Mathlib, `Aeneas, `Batteries, `Qq, `Aesop, `EquivLean.Core,
   `EquivLean.Repr, `EquivLean.Tactic, `EquivLean.Bridge]

/-- A definition of the user (current file or a non-library module). -/
def isUserDef (c : Name) : MetaM Bool := do
  let env ← getEnv
  let user := match env.getModuleIdxFor? c with
    | none => true
    | some i => !specLibraryRoots.any (·.isPrefixOf (env.header.moduleNames[i.toNat]!))
  unless user do return false
  match env.find? c with
  | some (.defnInfo _) => return true
  | _ => return false

/-- Unfold user definitions at the head (and beta), a bounded number of times. -/
partial def unfoldUserHead (e : Lean.Expr) (fuel : Nat := 16) : MetaM Lean.Expr := do
  let e := (← instantiateMVars e).headBeta.consumeMData
  if fuel = 0 then return e
  match e.getAppFn with
  | .const c _ =>
    if ← isUserDef c then
      match ← unfoldDefinition? e with
      | some e' => unfoldUserHead e' (fuel - 1)
      | none => return e
    else return e
  | _ => return e

/-- The conjuncts of a proposition (user definitions unfolded at the heads), existential binders
replaced by fresh metavariables (so that conjuncts sharing a binder share it). -/
partial def conjuncts (e : Lean.Expr) : MetaM (Array Lean.Expr) := do
  let e ← unfoldUserHead e
  if e.isAppOfArity ``And 2 then
    return (← conjuncts (e.getArg! 0)) ++ (← conjuncts (e.getArg! 1))
  if e.isAppOfArity ``Exists 2 then
    match e.appArg!.consumeMData with
    | .lam _ ty b _ =>
      let m ← mkFreshExprMVar ty
      return ← conjuncts (b.instantiate1 m)
    | _ => return #[e]
  return #[e]

/-- What the precondition says about the walked array. -/
structure PreInfo where
  /-- the arguments (`args = [...]`) -/
  argEs : Array Lean.Expr
  /-- `(address, element list)` of `σ.heap a = some (.array t xs)` -/
  arrays : Array (Lean.Expr × Lean.Expr)
  /-- `(element list, record predicate applied to σ, ghost list)` of `Pairs (R σ) xs rs` -/
  pairs : Array (Lean.Expr × Lean.Expr × Lean.Expr)
  /-- classes initialized -/
  inits : Array Lean.Expr

def readPre (pre : Lean.Expr) (args σ : Lean.Expr) : MetaM PreInfo := do
  let cs ← conjuncts (mkApp2 pre args σ)
  let mut info : PreInfo := ⟨#[], #[], #[], #[]⟩
  for c in cs do
    let c ← instantiateMVars c
    if c.isAppOfArity ``Eq 3 then
      let l := c.getArg! 1
      let r := c.getArg! 2
      if l == args then
        if let some (es, _) ← explicitList r then info := { info with argEs := es }
      else if l.isAppOfArity ``State.heap 2 && l.getArg! 0 == σ && r.isAppOfArity ``Option.some 2 &&
          (r.getArg! 1).isAppOfArity ``Obj.array 2 then
        info := { info with arrays := info.arrays.push (l.getArg! 1, (r.getArg! 1).getArg! 1) }
      else if l.isAppOfArity ``State.initOf 2 && l.getArg! 0 == σ && r.isConstOf ``InitSt.done then
        info := { info with inits := info.inits.push (l.getArg! 1) }
    else if c.isAppOfArity ``Pairs 5 then
      info := { info with pairs := info.pairs.push (c.getArg! 3, c.getArg! 2, c.getArg! 4) }
  return info

/-- What the postcondition (applied, normal outcome) says about the returned object: for each
field, the list of strings it holds (`StrsAt σ' ys T`). -/
def readPost (postApplied : Lean.Expr) : MetaM (Array (String × Lean.Expr)) := do
  let cs ← conjuncts postApplied
  let cs ← cs.mapM instantiateMVars
  -- field name ↦ list address, list address ↦ elements, elements ↦ strings
  let mut fieldL : Array (String × Lean.Expr) := #[]
  let mut listYs : Array (Lean.Expr × Lean.Expr) := #[]
  let mut ysT : Array (Lean.Expr × Lean.Expr) := #[]
  for c in cs do
    if c.isAppOfArity ``Eq 3 then
      let l := c.getArg! 1
      let rhs := c.getArg! 2
      if l.isAppOfArity ``Fields.get 2 && rhs.isAppOfArity ``Option.some 2 &&
          (rhs.getArg! 1).isAppOfArity ``Value.ref 1 then
        let key ← whnfD (l.getArg! 1)
        if key.isAppOfArity ``Prod.mk 4 then
          if let .lit (.strVal f) := (← whnfD (key.getArg! 3)).consumeMData then
            fieldL := fieldL.push (f, (rhs.getArg! 1).getArg! 0)
      else if l.isAppOfArity ``State.heap 2 && rhs.isAppOfArity ``Option.some 2 &&
          (rhs.getArg! 1).isAppOfArity ``Obj.list 3 then
        listYs := listYs.push (l.getArg! 1, (rhs.getArg! 1).getArg! 1)
    else if c.isAppOfArity ``Pairs 5 && (c.getArg! 2).isAppOfArity ``StrAt 1 then
      ysT := ysT.push (c.getArg! 3, c.getArg! 4)
    else if c.isAppOfArity ``StrsAt 3 then
      ysT := ysT.push (c.getArg! 1, c.getArg! 2)
  let mut out := #[]
  for (f, l) in fieldL do
    if let some (_, ys) := listYs.find? (·.1 == l) then
      if let some (_, t) := ysT.find? (·.1 == ys) then out := out.push (f, t)
  return out

/-! ## Candidates on a prefix -/

/-- The components of an append chain (`a ++ b`, `x :: l` as `[x] ++ l`), user definitions
unfolded. -/
partial def appendChain (e : Lean.Expr) : MetaM (Array Lean.Expr) := do
  let e ← unfoldUserHead e
  if e.isAppOfArity ``HAppend.hAppend 6 then
    return (← appendChain (e.getArg! 4)) ++ (← appendChain (e.getArg! 5))
  if e.isAppOfArity ``List.cons 3 then
    let x := e.getArg! 1
    let ty := e.getArg! 0
    let single := mkApp3 (mkConst ``List.cons [Level.zero]) ty x (mkApp (mkConst ``List.nil [Level.zero]) ty)
    return #[single] ++ (← appendChain (e.getArg! 2))
  return #[e]

/-- A component built element by element from the ghost list (`map`, `filterMap`, `flatMap`,
`filter`, possibly composed). -/
partial def perElement (e : Lean.Expr) (rs : Lean.Expr) : MetaM Bool := do
  let e ← unfoldUserHead e
  let fns := [``List.map, ``List.filterMap, ``List.flatMap, ``List.filter]
  match e.getAppFn with
  | .const c _ =>
    if fns.contains c then
      let l := e.appArg!
      return l == rs || (← perElement l rs)
    return false
  | _ => return false

/-- `fun n => e[rs := rs.take n]`. -/
def prefixFn (e rs : Lean.Expr) : MetaM Lean.Expr := do
  withLocalDeclD `n (mkConst ``Nat) fun n => do
    let tk ← mkAppM ``List.take #[n, rs]
    mkLambdaFVars #[n] (e.replace fun t => if t == rs then some tk else none)

/-- The list a loop has built after `n` iterations, for the output `T`: the components of `T`
before its first component built element by element from `rs`, and that component on the
prefix (`none`: no such component). -/
def listCandidate (t rs : Lean.Expr) : MetaM (Option Lean.Expr) := do
  let comps ← appendChain t
  let mut acc : Array Lean.Expr := #[]
  for c in comps do
    if ← perElement c rs then
      acc := acc.push c
      let mut e := acc.back!
      for c' in acc.pop.reverse do e ← mkAppM ``HAppend.hAppend #[c', e]
      return some (← prefixFn e rs)
    acc := acc.push c
  return none

/-- The folds over the ghost list inside `e` (user definitions unfolded, bounded depth). -/
partial def foldTerms (e rs : Lean.Expr) (depth : Nat := 32) : MetaM (Array Lean.Expr) := do
  if depth = 0 then return #[]
  let e ← unfoldUserHead e
  let mut out := #[]
  if (e.isAppOfArity ``List.foldl 5 || e.isAppOfArity ``List.foldr 5) && (e.getArg! 4).containsFVar rs.fvarId! then
    out := out.push e
  for a in e.getAppArgs do
    if a.containsFVar rs.fvarId! then out := out ++ (← foldTerms a rs (depth - 1))
  return out

/-! ## The tactic -/

unsafe def evalSpecAnalysisImpl (e : Lean.Expr) : MetaM (Except String SpecAlign.SpecAnalysis) :=
  Meta.evalExpr (Except String SpecAlign.SpecAnalysis)
    (mkApp2 (mkConst ``Except [Level.zero, Level.zero]) (mkConst ``String)
      (mkConst ``SpecAlign.SpecAnalysis)) e

/-- Evaluate `SpecAlign.specAnalyze …` (compiled code: JimpleLean's interpreter on samples). -/
@[implemented_by evalSpecAnalysisImpl]
opaque evalSpecAnalysis (e : Lean.Expr) : MetaM (Except String SpecAlign.SpecAnalysis)

register_option jspec.trace : Bool := {
  defValue := false
  descr := "log the analysis and the generated invariant of jspec_auto" }

/-- The user definitions (current file or non-library modules) occurring in `e`. -/
def userConsts (e : Lean.Expr) : MetaM (Array Name) := do
  let mut out := #[]
  for c in e.getUsedConstants do
    if (← isUserDef c) && !out.contains c then out := out.push c
  return out

/-- The subterms of `e` satisfying `p`. -/
partial def subtermsWith (p : Lean.Expr → Bool) (e : Lean.Expr) : Array Lean.Expr :=
  let here := if p e then #[e] else #[]
  match e with
  | .app f a => here ++ subtermsWith p f ++ subtermsWith p a
  | .lam _ t b _ => here ++ subtermsWith p t ++ subtermsWith p b
  | .forallE _ t b _ => here ++ subtermsWith p t ++ subtermsWith p b
  | .letE _ t v b _ => here ++ subtermsWith p t ++ subtermsWith p v ++ subtermsWith p b
  | .mdata _ b => here ++ subtermsWith p b
  | .proj _ _ b => here ++ subtermsWith p b
  | _ => here

/-- The first local hypothesis whose type satisfies `p`. -/
def findHyp (p : Lean.Expr → MetaM Bool) : TacticM (Option FVarId) := withMainContext do
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    if ← p (← instantiateMVars d.type) then return some d.fvarId
  return none

/-- `σ.heap x = some o` facts about `σ0`, restated about `σ` (the heap grows). -/
def transferHeapFacts (σ0 σ : Lean.Expr) (hg : Lean.Expr) : TacticM Unit := withMainContext do
  let mut g ← getMainGoal
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    if ty.isAppOfArity ``Eq 3 && (ty.getArg! 1).isAppOfArity ``State.heap 2 &&
        (ty.getArg! 1).getArg! 0 == σ0 && (ty.getArg! 2).isAppOfArity ``Option.some 2 then
      let pf ← mkAppM ``heap_of_grows #[hg, d.toExpr]
      let pty ← inferType pf
      let exists_ := (← getLCtx).any fun d' => d'.type == pty
      unless exists_ do
        let (_, g') ← (← g.assert `hσ pty pf).intro1P
        g := g'
  replaceMainGoal [g]

/-- The closer of the leaves left by `jvc`: hidden facts revealed, witnesses of list objects
taken from equations, string lists and the heap frame through the kit's lemmas, list equations
by `simp` with the user's definitions unfolded. -/
def jspecClose (userDefs : Array Name) : TacticM Unit := do
  let ud : Array (TSyntax `Lean.Parser.Tactic.simpLemma) ←
    (userDefs.push ``jstrLit).mapM fun n => `(Lean.Parser.Tactic.simpLemma| $(mkCIdent n):ident)
  evalTactic (← `(tactic| all_goals (try simp only [EquivLean.Jimple.Spec.hide_iff] at *)))
  evalTactic (← `(tactic| all_goals (try simp only [and_assoc, exists_and_left, exists_eq_left'])))
  let gs ← getGoals
  let mut out := []
  for g in gs do
    setGoals [g]
    let t := (← instantiateMVars (← g.getType)).consumeMData
    if t.isConstOf ``True then
      evalTactic (← `(tactic| trivial)); continue
    if t.isAppOfArity ``Grows 2 then
      evalTactic (← `(tactic| jgrows)); continue
    if t.isAppOfArity ``StrsAt 3 then
      -- the list as the old list and new strings; the old list by the frame lemmas
      evalTactic (← `(tactic| (
        simp only [EquivLean.Jimple.Spec.StrsAt, EquivLean.Jimple.Spec.strsOf_append,
          EquivLean.Jimple.Spec.strsOf_singleton] at *)))
      -- frame: every `strsOf τ ys` from a hypothesis `strsOf σ ys = some L`
      let hyps ← withMainContext do
        let mut acc := #[]
        for d in (← getLCtx) do
          let ty ← instantiateMVars d.type
          if ty.isAppOfArity ``Eq 3 && (ty.getArg! 1).isAppOfArity ``strsOf 2 then
            acc := acc.push ((ty.getArg! 1).getArg! 1, ty.getArg! 2)
        return acc
      let tgt ← instantiateMVars (← getMainTarget)
      for (ys, L) in hyps do
        -- occurrences `strsOf τ ys` in the goal
        let occs := (subtermsWith (fun e => e.isAppOfArity ``strsOf 2 && e.getArg! 1 == ys) tgt).filter
          fun e => !(e.getArg! 0).isFVar
        for o in occs.toList.eraseDups do
          let gEq ← withMainContext do mkFreshExprMVar (← mkEq o L)
          let saved ← getGoals
          try
            jstrsOfFrameCore gEq.mvarId!
          catch ex =>
            if jspec.trace.get (← getOptions) then
              logInfo m!"jspec_auto: frame of {o} failed: {ex.toMessageData}"
          setGoals saved
          if (← instantiateMVars gEq).hasMVar then continue
          let main ← getMainGoal
          let main' ← main.withContext do main.rewrite (← main.getType) gEq
          let mg ← main.replaceTargetEq main'.eNew main'.eqProof
          replaceMainGoal (mg :: main'.mvarIds)
      -- new strings: their heap cells; then the list equation
      evalTactic (← `(tactic| all_goals (try simp (disch := jomega) only [EquivLean.Jimple.Spec.strOfV_ref,
          State.heap_alloc, State.heap_setObj, State.next_alloc, State.next_setObj, ite_eq_left,
          ite_eq_right, ite_true, ite_false, Option.map_some, Option.bind_some, Option.some.injEq])))
      evalTactic (← `(tactic| all_goals (try simp (config := { decide := true }) [$ud,*, List.append_assoc,
        Jimple.bv32_toNat_of_nonneg] at *)))
      out := out ++ (← getGoals)
      continue
    -- other goals (fold values, arithmetic): one more element of the prefix, then simp
    evalTactic (← `(tactic| all_goals (try simp (config := { decide := true }) [$ud,*, List.append_assoc,
        Jimple.bv32_toNat_of_nonneg, List.take_succ, List.foldl_append, List.foldl_cons, List.foldl_nil] at *)))
    evalTactic (← `(tactic| all_goals (try jomega)))
    out := out ++ (← getGoals)
  setGoals out

/-- The entry state `σ0`, the current state `σ`, the hidden `Grows σ0 σ` fact and the index `i`
(`fr.get idx = some (.int i)`) of the loop-head goal, looked up afresh (substitutions renew
local variables). -/
def headCtx (idx : Nat) : TacticM (Lean.Expr × Lean.Expr × Lean.Expr × Lean.Expr) := withMainContext do
  let lctx ← getLCtx
  let some σ0 := lctx.findFromUserName? `σ0 | throwError "jspec_auto: σ0 not found"
  let some σ := lctx.findFromUserName? `σ | throwError "jspec_auto: σ not found"
  let mut hgo := none
  let mut iEo := none
  for d in lctx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    if ty.isAppOfArity ``Hide 1 && (ty.getArg! 0).isAppOfArity ``Grows 2 then hgo := some d.toExpr
    if ty.isAppOfArity ``Eq 3 && (ty.getArg! 1).isAppOfArity ``Frame.get 2 then
      let k ← instantiateMVars ((ty.getArg! 1).getArg! 1)
      if k.nat? == some idx || k.rawNatLit? == some idx then
        let rhs := ty.getArg! 2
        if rhs.isAppOfArity ``Option.some 2 && (rhs.getArg! 1).isAppOfArity ``Value.int 1 then
          iEo := some ((rhs.getArg! 1).getArg! 0)
  let some hg := hgo | throwError "jspec_auto: no Grows fact"
  let some iE := iEo | throwError "jspec_auto: no index fact"
  return (σ0.toExpr, σ.toExpr, ← mkAppM ``Hide.elim #[hg], iE)

set_option hygiene false in
/-- `jspec_auto [defs]`: prove `Sat P m S` for a method whose loop walks an input array (see the
module documentation). -/
def jspecAuto (defs : Array Name) : TacticM Unit := withMainContext do
  let g ← getMainGoal
  let tgt := (← instantiateMVars (← g.getType)).consumeMData
  unless tgt.isAppOfArity ``Sat 3 do throwError "jspec_auto: the goal is not `Sat P m S`"
  let P := tgt.getArg! 0; let m := tgt.getArg! 1; let S := tgt.getArg! 2
  if P.hasFVar || m.hasFVar then throwError "jspec_auto: the program and the method must be closed"
  let an ← match ← evalSpecAnalysis (mkAppN (mkConst ``SpecAlign.specAnalyze)
      #[P, m, mkNatLit 8, mkNatLit 1]) with
    | .ok an => pure an
    | .error e => throwError "jspec_auto: {e}"
  if jspec.trace.get (← getOptions) then logInfo m!"jspec_auto: analysis {repr an}"
  -- the contract
  let preFn ← whnfD (mkApp (mkConst ``Spec.pre) S)
  let (preInfo, rc) ← withLocalDeclD `args (← mkAppM ``List #[mkConst ``Jimple.Value]) fun args =>
    withLocalDeclD `σ (mkConst ``Jimple.State) fun σ => do
      let info ← readPre preFn args σ
      let some a := info.argEs[an.walked]?
        | throwError "jspec_auto: the precondition does not give argument {an.walked}"
      let a := (← instantiateMVars a).consumeMData
      unless a.isAppOfArity ``Value.ref 1 do throwError "jspec_auto: argument {an.walked} is not `.ref a`"
      let some (_, xs) := info.arrays.find? (·.1 == a.appArg!)
        | throwError "jspec_auto: no `σ.heap a = some (.array t xs)` for the walked array"
      let some (_, R, rs) := info.pairs.find? (·.1 == xs)
        | throwError "jspec_auto: no `Pairs (R σ) xs rs` for the walked array"
      let some rc := R.getAppFn.constName? | throwError "jspec_auto: record predicate {R}"
      -- argument expressions and inits must not mention the local σ, args
      return ((info.argEs, rs, info.inits), rc)
  let (argEs, rs, inits) := preInfo
  if argEs.any (·.hasLooseBVars) || !rs.isFVar then throwError "jspec_auto: ghost list must be a variable"
  let listV ← mkAppM ``List #[mkConst ``Jimple.Value]
  let optV ← mkAppM ``Option #[mkConst ``Jimple.Value]
  let outs ← withLocalDeclD `args listV fun args =>
    withLocalDeclD `σ (mkConst ``Jimple.State) fun σx => withLocalDeclD `r optV fun r =>
      withLocalDeclD `σ' (mkConst ``Jimple.State) fun σ' => do
        let post ← whnfD (mkAppN (mkConst ``Spec.post) #[S, args, σx, mkApp2 (mkConst ``Outcome.normal) r σ'])
        readPost post
  -- candidates
  let mut listCs : Array (Nat × Lean.Expr) := #[]
  for (x, f) in an.listLocals do
    let some (_, t) := outs.find? (·.1 == f) | throwError "jspec_auto: no output for field {f}"
    let some c ← listCandidate t rs | throwError "jspec_auto: no element-wise part in the output {t}"
    listCs := listCs.push (x, c)
  let folds ← outs.foldlM (fun acc (_, t) => do return acc ++ (← foldTerms t rs)) #[]
  let mut scalarCs : Array (Nat × Bool × Lean.Expr) := #[]
  for (x, isLong) in an.scalarLocals do
    let w := if isLong then 64 else 32
    let cands ← folds.filterM fun f => do
      return (← isDefEq (← inferType f) (mkApp (mkConst ``BitVec) (mkNatLit w)))
    match cands.toList.eraseDups with
    | [c] => scalarCs := scalarCs.push (x, isLong, ← prefixFn c rs)
    | [] => throwError "jspec_auto: no fold of the outputs for the {w}-bit local {x}"
    | _ => throwError "jspec_auto: several folds of the outputs for local {x}"
  -- the invariant
  let fr := mkIdent `fr; let σ := mkIdent `σ; let σ0 := mkIdent `σ0; let i := mkIdent `i
  let rsS ← Term.exprToSyntax rs
  let mut facts : Array Term := #[
    ← `(Jimple.Frame.get $fr $(natStx an.idx) = some (Jimple.Value.int $i)),
    ← `(0 ≤ BitVec.toInt $i), ← `(BitVec.toInt $i ≤ ((List.length $rsS : Nat) : Int))]
  for (x, ai) in an.argLocals do
    if let some a := argEs[ai]? then
      facts := facts.push (← `(Jimple.Frame.get $fr $(natStx x) = some $(← Term.exprToSyntax a)))
  let mut binders : Array (Ident × Term) := #[(i, ← `(Jimple.I32))]
  let mut k := 0
  for (x, c) in listCs do
    let l := mkIdent (Name.mkSimple s!"l{k}"); let ys := mkIdent (Name.mkSimple s!"ys{k}")
    let mm := mkIdent (Name.mkSimple s!"m{k}")
    k := k + 1
    binders := binders ++ #[(l, ← `(Jimple.Addr)), (ys, ← `(List Jimple.Value)), (mm, ← `(Nat))]
    let cS ← Term.exprToSyntax c
    let xS := natStx x
    let f1 ← `(Jimple.Frame.get $fr $xS = some (Jimple.Value.ref $l))
    let f2 ← `(Jimple.State.heap $σ $l = some (Jimple.Obj.list Jimple.ListKind.arrayList $ys $mm))
    let f3 ← `(Jimple.State.next $σ0 ≤ $l)
    let f4 ← `(EquivLean.Jimple.Spec.Hide (EquivLean.Jimple.Spec.StrsAt $σ $ys ($cS (Int.toNat (BitVec.toInt $i)))))
    facts := facts ++ #[f1, f2, f3, f4]
  let mut ks := 0
  for (x, isLong, c) in scalarCs do
    let cS ← Term.exprToSyntax c
    let t := mkIdent (Name.mkSimple s!"t{ks}")
    ks := ks + 1
    binders := binders.push (t, ← if isLong then `(Jimple.I64) else `(Jimple.I32))
    let xS := natStx x
    facts := facts.push (← if isLong then
        `(Jimple.Frame.get $fr $xS = some (Jimple.Value.long $t))
      else `(Jimple.Frame.get $fr $xS = some (Jimple.Value.int $t)))
    -- the fold's value, hidden from symbolic execution (the closer proves it)
    facts := facts.push (← `(EquivLean.Jimple.Spec.Hide ($t = $cS (Int.toNat (BitVec.toInt $i)))))
  facts := facts ++ #[← `(Jimple.State.next $σ0 ≤ Jimple.State.next $σ),
    ← `(EquivLean.Jimple.Spec.Hide (EquivLean.Jimple.Spec.Grows $σ0 $σ))]
  for c in inits do
    facts := facts.push (← `(Jimple.State.initOf $σ $(← Term.exprToSyntax c) = Jimple.InitSt.done))
  let mut body := facts.back!
  for f in facts.pop.reverse do body ← `($f ∧ $body)
  for (b, ty) in binders.reverse do body ← `(∃ $b:ident : $ty, $body)
  let invStx ← `(fun (_args : List Jimple.Value) ($σ0 : Jimple.State) ($fr : Jimple.Frame)
      ($σ : Jimple.State) => $body)
  let invTy ← mkArrow (← mkAppM ``List #[mkConst ``Jimple.Value]) (← mkArrow (mkConst ``Jimple.State)
    (← mkArrow (mkConst ``Jimple.Frame) (← mkArrow (mkConst ``Jimple.State) (mkSort Level.zero))))
  let inv ← Term.withoutErrToSorry <| Term.elabTermEnsuringType invStx invTy
  Term.synthesizeSyntheticMVarsNoPostponing
  let inv ← instantiateMVars inv
  let base := (← Term.getDeclName?).getD `jspec_auto
  let invName ← freshAuxName base "jinv"
  let invE ← mkAuxDefinition invName invTy inv (compile := false)
  enableRealizationsForConst invName
  if jspec.trace.get (← getOptions) then
    let some (.defnInfo d) := (← getEnv).find? invName | pure ()
    logInfo m!"jspec_auto: invariant at statement {an.head}: {d.value}"
  -- definitions to unfold
  let specDefs := (← userConsts S) ++ (← userConsts preFn)
  let sDef ← match S.getAppFn.constName? with
    | some c => pure #[c]
    | none => pure #[]
  let sBody ← match S.getAppFn.constName? with
    | some _ => do pure (← userConsts ((← unfoldDefinition? S).getD S))
    | none => pure #[]
  let specDefs := (sDef ++ specDefs ++ sBody).toList.eraseDups.toArray.filter (· != rc)
  let invS ← Term.exprToSyntax invE
  let headS := natStx an.head
  let depthS := natStx an.depth
  let fuelS := natStx (an.fuel + 4)
  let st ← `(tactic| refine Jimple.MethodVC.sat_of_valid (Γ := fun _ => none) (d := $depthS)
      (fuel := $fuelS) (A := [Prod.mk $headS $invS]) (EquivLean.Jimple.Spec.valid_none _) ?_)
  evalTactic st
  let tr := jspec.trace.get (← getOptions)
  let jvcIds : Array Ident := (specDefs ++ #[invName, ``inlineFuel, ``fields_get_cons, ``fields_get_nil,
    ``evalDynamic, ``concatRecipe, ``Native.valueOfArg, ``Native.valueOfObj, ``Native.valueOfObjN,
    ``Native.nObjStr, ``Native.primStr, ``JType.isRef, ``jstrLit, ``jlong_cmp_toInt] ++ defs).map mkCIdent
  -- the user's functions (unfolded by the closer only)
  let closeDefs := (← (outs.foldlM (fun acc (_, t) => do return acc ++ (← userConsts t)) #[])) ++ defs
  evalTactic (← `(tactic| refine ⟨_, rfl, ?_⟩))
  evalTactic (← `(tactic| intro args σ0 hpre))
  evalTactic (← `(tactic| refine ⟨?_, ?_⟩))
  let [gEntry, gHead] ← getGoals | throwError "jspec_auto: VC shape"
  -- entry path
  setGoals [gEntry]
  evalTactic (← `(tactic| jvc [$jvcIds,*]))
  if tr then logInfo m!"jspec_auto: entry jvc left {(← getGoals).length}: {goalsToMessageData (← getGoals)}"
  jspecClose closeDefs
  let entryLeft ← getGoals
  unless entryLeft.isEmpty do
    throwError "jspec_auto: entry path not closed:\n{goalsToMessageData entryLeft}"
  -- the loop head
  setGoals [gHead]
  let invIds : Array (TSyntax `Lean.Parser.Tactic.simpLemma) ← #[``Invariants.inst, ``List.map_cons,
    ``List.map_nil, ``List.forall_mem_cons, ``List.not_mem_nil, ``false_implies, ``implies_true,
    ``and_true].mapM fun n => `(Lean.Parser.Tactic.simpLemma| $(mkCIdent n):ident)
  evalTactic (← `(tactic| simp only [$invIds,*]))
  evalTactic (← `(tactic| intro fr σ hJ))
  let preIds : Array (TSyntax `Lean.Parser.Tactic.simpLemma) ← (specDefs.push ``Spec.of).mapM fun n =>
    `(Lean.Parser.Tactic.simpLemma| $(mkCIdent n):ident)
  evalTactic (← `(tactic| simp only [$preIds,*] at hpre))
  evalTactic (← `(tactic| simp only [$(mkCIdent invName):ident] at hJ))
  Jimple.jDestruct
  evalTactic (← `(tactic| try subst_vars))
  -- the facts the head needs
  let (σ0E, σE, hgE, iE) ← headCtx an.idx
  transferHeapFacts σ0E σE hgE
  let some hpv ← findHyp fun t => return t.isAppOfArity ``Pairs 5 && t.getArg! 4 == rs
    | throwError "jspec_auto: no Pairs fact for the ghost list"
  withMainContext do
    let g ← getMainGoal
    let ty ← inferType (.fvar hpv)
    let (_, g') ← (← g.assert `hpairs ty (.fvar hpv)).intro1P
    replaceMainGoal [g']
  let iS ← withMainContext (Term.exprToSyntax iE)
  evalTactic (← `(tactic| have hxlen := EquivLean.Jimple.Spec.pairs_length hpairs))
  evalTactic (← `(tactic| have hi0 : 0 ≤ BitVec.toInt $iS := by assumption))
  -- the index as jvc writes it (`(BitVec.toInt i).toNat`)
  evalTactic (← `(tactic| try simp only [EquivLean.Jimple.Spec.i32_toNat_eq _ hi0] at *))
  evalTactic (← `(tactic| by_cases hc : ((List.length $rsS : Nat) : Int) ≤ BitVec.toInt $iS))
  let [gExit, gCont] ← getGoals | throwError "jspec_auto: case split"
  -- exit: the prefix is the whole list
  setGoals [gExit]
  evalTactic (← `(tactic| have htk := List.take_of_length_le (l := $rsS) (i := (BitVec.toInt $iS).toNat)
      (by omega)))
  evalTactic (← `(tactic| simp only [htk] at *))
  evalTactic (← `(tactic| have hp' := EquivLean.Jimple.Spec.Hide.intro hpairs))
  evalTactic (← `(tactic| clear hpairs))
  evalTactic (← `(tactic| jvc [$jvcIds,*]))
  if tr then logInfo m!"jspec_auto: exit jvc left {goalsToMessageData (← getGoals)}"
  jspecClose closeDefs
  let exitLeft ← getGoals
  if tr then logInfo m!"jspec_auto: exit closed, left {exitLeft.length}"
  -- continue: one more element
  setGoals [gCont]
  evalTactic (← `(tactic| have hn : BitVec.toNat $iS < List.length $rsS := by
      rw [EquivLean.Jimple.Spec.i32_toNat_eq _ hi0]; omega))
  evalTactic (← `(tactic| obtain ⟨xv, rv, hxget, hrget, hrec⟩ := EquivLean.Jimple.Spec.pairs_getElem?' hpairs hn))
  evalTactic (← `(tactic| simp only [$(mkCIdent rc):ident, EquivLean.Jimple.Spec.StrAt] at hrec))
  Jimple.jDestruct
  evalTactic (← `(tactic| try subst_vars))
  let (σ0E', σE', hgE', _) ← headCtx an.idx
  transferHeapFacts σ0E' σE' hgE'
  evalTactic (← `(tactic| rw [EquivLean.Jimple.Spec.i32_toNat_eq _ hi0] at hxget hrget))
  evalTactic (← `(tactic| obtain ⟨hxb, hxget'⟩ := List.getElem?_eq_some_iff.mp hxget))
  evalTactic (← `(tactic| have hrget' := List.getElem?_eq_some_iff.mp hrget))
  evalTactic (← `(tactic| obtain ⟨hrb, hrget''⟩ := hrget'))
  evalTactic (← `(tactic| have hp' := EquivLean.Jimple.Spec.Hide.intro hpairs))
  evalTactic (← `(tactic| clear hpairs))
  evalTactic (← `(tactic| jvc [$jvcIds,*]))
  if tr then logInfo m!"jspec_auto: cont jvc left {goalsToMessageData (← getGoals)}"
  jspecClose closeDefs
  let contLeft ← getGoals
  setGoals (exitLeft ++ contLeft)
  unless (exitLeft ++ contLeft).isEmpty do
    throwError "jspec_auto: {(exitLeft ++ contLeft).length} goal(s) not closed:\n{goalsToMessageData (exitLeft ++ contLeft)}"

/-- `jspec_auto [defs]` (module documentation). -/
syntax (name := jspecAutoTac) "jspec_auto" (" [" ident,* "]")? : tactic

@[tactic jspecAutoTac] def evalJspecAuto : Tactic := fun stx => do
  let ids := Jimple.optIdents stx[1]
  let defs ← ids.mapM fun i => realizeGlobalConstNoOverloadWithInfo i
  withJimpleHeartbeats (jspecAuto defs)

end EquivLean.Jimple.Spec

/-! ## Helper methods: class initialization, characters, repeated characters -/

namespace EquivLean.Jimple.Spec

/-- Classes initialized stay initialized. -/
def InitMono (σ σ' : Jimple.State) : Prop := ∀ c, σ.initOf c = .done → σ'.initOf c = .done

theorem initMono_refl (σ : State) : InitMono σ σ := fun _ h => h

theorem initMono_alloc_of {σ0 σ : State} (o : Obj) (h : InitMono σ0 σ) :
    InitMono σ0 (σ.alloc o).2 := fun c hc => by rw [State.initOf_alloc]; exact h c hc

theorem initMono_setObj_of {σ0 σ : State} {a : Addr} {o : Obj} (h : InitMono σ0 σ) :
    InitMono σ0 (σ.setObj a o) := fun c hc => by rw [State.initOf_setObj]; exact h c hc

theorem initMono_setStatic_of {σ0 σ : State} {k : FieldKey} {v : Value} (h : InitMono σ0 σ) :
    InitMono σ0 (σ.setStatic k v) := fun c hc => by rw [State.initOf_setStatic]; exact h c hc

theorem initMono_setInit_done_of {σ0 σ : State} {c' : ClassName} (h : InitMono σ0 σ) :
    InitMono σ0 (σ.setInit c' .done) := fun c hc => by
  rw [State.initOf_setInit]; split
  · rfl
  · exact h c hc

theorem initMono_trans {σ1 σ2 σ3 : State} (h1 : InitMono σ1 σ2) (h2 : InitMono σ2 σ3) :
    InitMono σ1 σ3 := fun c hc => h2 c (h1 c hc)

open Lean Meta Elab Tactic in
/-- `InitMono σ0 τ` from `InitMono σ0 σ` (a hypothesis) for `τ` built from `σ` by allocations,
object updates, static fields and initializations that end `done`. -/
partial def jinitMonoCore (g : MVarId) : TacticM Unit := do
  setGoals [g]
  let ok ← try evalTactic (← `(tactic| first | assumption | exact initMono_refl _)); pure true
    catch _ => pure false
  if ok then return
  let t := (← instantiateMVars (← g.getType)).consumeMData
  unless t.isAppOfArity ``InitMono 2 do throwError "jinit_mono: not `InitMono σ0 τ`: {t}"
  let next (lem : Name) : TacticM Unit := do
    let [g'] ← g.apply (← mkConstWithFreshMVarLevels lem) | throwError "jinit_mono: {lem}"
    jinitMonoCore g'
  match stateStep? (t.getArg! 1) with
  | some (``State.alloc, _) => next ``initMono_alloc_of
  | some (``State.setObj, _) => next ``initMono_setObj_of
  | some (``State.setStatic, _) => next ``initMono_setStatic_of
  | some (``State.setInit, _) => next ``initMono_setInit_done_of
  | _ => throwError "jinit_mono: no hypothesis for {t}"

open Lean Elab Tactic in
/-- `InitMono σ0 τ` (`jinitMonoCore`). -/
elab "jinit_mono" : tactic => do jinitMonoCore (← getMainGoal)

/-- A character through `int` and back (`charAt`, then `append(char)`). -/
@[simp] theorem jchar_roundtrip (c : BitVec 16) : (c.zeroExtend 32).setWidth 16 = c := by
  apply BitVec.eq_of_toNat_eq
  simp

/-- The frame closers on the goals left by `jvc` in a helper's proof: hidden facts revealed,
`Grows`/`InitMono` through the state steps, the rest by `simp` and `jomega`. -/
macro "jhelper_close" : tactic => `(tactic| (
  all_goals (try simp only [EquivLean.Jimple.Spec.hide_iff] at *)
  all_goals first
    | done
    | trivial
    | jgrows
    | jinit_mono
    | jomega
    | (simp_all; done)))

end EquivLean.Jimple.Spec
