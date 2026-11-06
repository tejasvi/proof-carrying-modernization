import EquivLean.Modernize.Cbact04c.JavaRunRunDefs
import EquivLean.Modernize.Cbact04c.JavaRunRecFacts

/-!
# CBACT04C → Java: lemmas for the segments of `run`

* `grows_chain`: the heap after a stretch of statements that only allocate and call methods
  whose contracts say the heap grew (the state terms `jvc` leaves behind);
* the heap invariants carried along such a stretch.
-/

open Jimple EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbact04c.Java

/-! ## String constants and `String.valueOf` (from `Cbtrn01c/JavaRunLib.lean`) -/

open Lean Meta in
/-- `JStr.ofString "…"` on a literal as its explicit list of UTF-16 code units, so that string
constants and concatenation recipes compute. -/
dsimproc jstrLit04 (JStr.ofString _) := fun e => do
  let_expr JStr.ofString s := e | return .continue
  let .lit (.strVal str) := s.consumeMData | return .continue
  let units := JStr.ofString str
  let elems := units.map fun (c : BitVec 16) =>
    mkApp2 (mkConst ``BitVec.ofNat) (mkNatLit 16) (mkNatLit c.toNat)
  return .done (← mkListLit (mkApp (mkConst ``BitVec) (mkNatLit 16)) elems)

/-- `valueOfObjN` folded: the cases other than a string object. -/
@[irreducible] def vobjSlow (P : Program) (n : Nat) (v : Value) (σ : State)
    (k : JStr → State → NRes) : NRes := Native.valueOfObjN P n v σ k

/-- `String.valueOf` of a reference: a string object's text; every other case folded into
`vobjSlow`. -/
theorem valueOfObjN_ref (P : Program) (n : Nat) (a : Addr) (σ : State)
    (k : JStr → State → NRes) :
    Native.valueOfObjN P (n + 1) (.ref a) σ k =
      match σ.heap a with
      | some (.str s) => k s σ
      | _ => vobjSlow P (n + 1) (.ref a) σ k := by
  unfold vobjSlow
  cases h : σ.heap a with
  | none => rfl
  | some o =>
    cases o <;> first | rfl | (simp only [Native.valueOfObjN, h, Native.nObjStr])

theorem valueOfObj_eq (P : Program) (v : Value) (σ : State) (k : JStr → State → NRes) :
    Native.valueOfObj P v σ k = Native.valueOfObjN P 8 v σ k := rfl

theorem nat_mod_2_32 {i : Nat} (h : i < 4294967296) : i % 4294967296 = i := Nat.mod_eq_of_lt h
theorem addr_eq_false {a b : Nat} (h : a ≠ b) : (a = b) = False := eq_false h
theorem addr_lt_true {a b : Nat} (h : a < b) : (a < b) = True := eq_true h

/-- A heap read through the states of a stretch: the frame conditions of the callees, allocations
and updates; address (dis)equalities by `jomega` (`trn_chain` of `Cbtrn01c/JavaRunState.lean`). -/
macro "chain_simp" : tactic => `(tactic| (
  try simp only [State.next_alloc, State.next_setObj] at *
  simp (config := { decide := true }) (disch := jomega) only [State.heap_alloc, State.heap_setObj,
    State.next_alloc, State.next_setObj, ite_true, ite_false, reduceIte, addr_eq_false, addr_lt_true,
    jstrLit04, State.initOf_alloc, State.initOf_setObj, List.cons_append, List.nil_append,
    List.append_assoc, Frame.get_setLocal, *]
  try rfl))

/-- The usual small facts of a cut point: frames, heap reads, address arithmetic. -/
macro "resid_close" : tactic => `(tactic| first
  | (chain_simp; done)
  | jomega
  | (simp only [State.next_alloc, State.next_setObj]; jomega)
  | (intro x hx; chain_simp; done)
  | decide
  | skip)

/-! ## Chains of heap growth -/

theorem grows_alloc' {σ0 σ : State} (h : Grows σ0 σ) (o : Obj) : Grows σ0 (σ.alloc o).2 :=
  grows_trans h (grows_alloc σ o)

theorem grows_setObj' {σ0 σ : State} {a : Addr} (h : Grows σ0 σ) (ha : σ0.next ≤ a) (o : Obj) :
    Grows σ0 (σ.setObj a o) :=
  grows_setObj h ha

theorem grows_post {σ0 σ σ' : State} (h : Grows σ0 σ) (h1 : σ.next ≤ σ'.next)
    (h2 : ∀ x, x < σ.next → σ'.heap x = σ.heap x) : Grows σ0 σ' :=
  grows_trans h ⟨h1, h2⟩

theorem grows_ctor {σ0 σ σ' : State} {a : Addr} (h : Grows σ0 σ) (ha : σ0.next ≤ a)
    (h1 : ∀ y, y ≠ a → σ'.heap y = σ.heap y) (h2 : σ'.next = σ.next) : Grows σ0 σ' :=
  ⟨by rw [h2]; exact h.1, fun x hx => by
    rw [h1 x (Nat.ne_of_lt (Nat.lt_of_lt_of_le hx ha)), h.2 x hx]⟩

/-- `Grows σ0 σ` for a state `σ` built from `σ0` by allocations, writes to fresh objects and
callee post-states (whose growth facts are hypotheses). -/
macro "grows_chain" : tactic => `(tactic| repeat (first
  | exact grows_refl _
  | assumption
  | (apply grows_alloc')
  | (refine grows_setObj' ?_ (by simp only [State.next_alloc] at *; omega) _)
  | (refine grows_post ?_ ‹_› ‹_›)
  | (refine grows_ctor ?_ (by simp only [State.next_alloc] at *; omega) ‹_› ‹_›)))

/-- `fr'.get k = some v` for a frame built by `setLocal`s, from facts about the old frame. -/
macro "frame_simp" " [" hs:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| simp (config := { decide := true }) only [Frame.get_setLocal, ite_true, ite_false,
    reduceIte, $hs,*])

theorem initOf_alloc' (σ : State) (o : Obj) (c : ClassName) : (σ.alloc o).2.initOf c = σ.initOf c :=
  State.initOf_alloc σ o c

/-! ## Record objects: presence of fields, copies -/

/-- Every field of a record object holds a value. -/
theorem jrec_present {s : Schema} {cls : ClassName} {σ : State} {fs : List (FieldKey × Value)}
    {vals : List FV} (h : Forall2 (fun f val => jFieldAt σ cls fs f val) s.fields vals) :
    ∀ f ∈ s.fields, ∃ w, Fields.get fs (cls, f.jname) = some w := by
  generalize s.fields = fields at h
  induction h with
  | nil => intro f hf; simp at hf
  | @cons f val fs' vals' hfv _ ih =>
    intro f' hf'
    rcases List.mem_cons.1 hf' with rfl | hm
    · cases val with
      | num n => exact ⟨_, hfv⟩
      | str bs => obtain ⟨sv, hs, -⟩ := hfv; exact ⟨sv, hs⟩
    · exact ih f' hm

/-- Strings are kept. -/
def StrKeep (σ σ' : State) : Prop := ∀ a s, σ.heap a = some (.str s) → σ'.heap a = some (.str s)

theorem strKeep_of_grows {σ σ' : State} (h : Grows σ σ') : StrKeep σ σ' :=
  fun _ _ hs => heap_of_grows h hs

theorem jfieldAt_copy {σ σ' : State} {cls : ClassName} {fs fs' : List (FieldKey × Value)}
    {f : Field} {val : FV} (h : jFieldAt σ cls fs f val)
    (he : Fields.get fs' (cls, f.jname) = Fields.get fs (cls, f.jname)) (hk : StrKeep σ σ') :
    jFieldAt σ' cls fs' f val := by
  cases val with
  | num n => exact he.trans h
  | str bs =>
    obtain ⟨sv, hs, x, rfl, hx⟩ := h
    exact ⟨.ref x, he.trans hs, x, rfl, hk x _ hx⟩

theorem forall2_jfield_copy {σ σ' : State} {cls : ClassName} {fs fs' : List (FieldKey × Value)}
    (hk : StrKeep σ σ') :
    ∀ {fields : List Field} {vals : List FV},
      Forall2 (fun f val => jFieldAt σ cls fs f val) fields vals →
      (∀ f ∈ fields, Fields.get fs' (cls, f.jname) = Fields.get fs (cls, f.jname)) →
      Forall2 (fun f val => jFieldAt σ' cls fs' f val) fields vals
  | [], [], .nil, _ => .nil
  | _ :: _, _ :: _, .cons h hs, he =>
    .cons (jfieldAt_copy h (he _ (List.mem_cons_self ..)) hk)
      (forall2_jfield_copy hk hs (fun f hf => he f (List.mem_cons_of_mem _ hf)))

/-- A copy of a record object holds the same record. -/
theorem jrecAt_copy {s : Schema} {cls : ClassName} {σ σ' : State} {y y' : Addr}
    {fs fs' : List (FieldKey × Value)} {vals : List FV} (h : JRecAt s cls σ (.ref y) vals)
    (hy : σ.heap y = some (.plain cls fs)) (hy' : σ'.heap y' = some (.plain cls fs'))
    (he : ∀ f ∈ s.fields, Fields.get fs' (cls, f.jname) = Fields.get fs (cls, f.jname))
    (hk : StrKeep σ σ') : JRecAt s cls σ' (.ref y') vals := by
  obtain ⟨x, fs0, hx, hheap, hf⟩ := h
  cases hx
  rw [hy] at hheap
  cases hheap
  exact ⟨y', fs', rfl, hy', forall2_jfield_copy hk hf he⟩

theorem accountRecord_jnames : AccountRecord.fields.map (·.jname) = keysAC := by decide
theorem tranCatBalRecord_jnames : TranCatBalRecord.fields.map (·.jname) = keysTC := by decide
theorem cardXrefRecord_jnames : CardXrefRecord.fields.map (·.jname) = keysXC := by decide
theorem disGroupRecord_jnames : DisGroupRecord.fields.map (·.jname) = keysDC := by decide
theorem tranRecord_jnames : TranRecord.fields.map (·.jname) = keysRC := by decide

theorem present_keys {s : Schema} {cls : ClassName} {σ : State} {fs : List (FieldKey × Value)}
    {vals : List FV} {keys : List String} (hk : s.fields.map (·.jname) = keys)
    (h : Forall2 (fun f val => jFieldAt σ cls fs f val) s.fields vals) :
    ∀ k ∈ keys, ∃ w, Fields.get fs (cls, k) = some w := by
  intro k hk'
  rw [← hk] at hk'
  obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hk'
  exact jrec_present h f hf

theorem same_keys {s : Schema} {cls : ClassName} {fs fs' : List (FieldKey × Value)}
    {keys : List String} (hk : s.fields.map (·.jname) = keys)
    (h : ∀ k ∈ keys, Fields.get fs' (cls, k) = Fields.get fs (cls, k)) :
    ∀ f ∈ s.fields, Fields.get fs' (cls, f.jname) = Fields.get fs (cls, f.jname) := by
  intro f hf
  exact h f.jname (hk ▸ List.mem_map_of_mem hf)

/-! ## The heap invariants along a stretch that writes only the objects `W` -/

theorem resAt_agree {σ σ' : State} {h : Hp} {W : List Addr} (hr : ResAt σ h) (ha : Agree σ σ' W)
    (hw : h.res ∉ W) : ResAt σ' h := by
  obtain ⟨fs, h1, h2⟩ := hr
  exact ⟨fs, by rw [ha.2 _ (State.lt_next_of_heap h1) hw, h1], h2⟩

theorem dispAt_agree {σ σ' : State} {ld : Addr} {d : List (List Nat)} {W : List Addr}
    (hd : DispAt σ ld d) (ha : Agree σ σ' W) (hn : NoStr σ W) (hw : ld ∉ W) : DispAt σ' ld d := by
  obtain ⟨xs, m, h1, h2⟩ := hd
  exact ⟨xs, m, by rw [ha.2 _ (State.lt_next_of_heap h1) hw, h1], forall2_jstrAt_agree ha hn h2⟩

theorem recsAt_agree {s : Schema} {cls : ClassName} {σ σ' : State} {l : Addr} {vals : List (List FV)}
    {M W : List Addr} (hr : RecsAt s cls σ l vals M) (ha : Agree σ σ' W) (hn : NoStr σ W)
    (hw : l ∉ W) (hMW : ∀ a ∈ W, a ∈ M ∨ ∀ fs, σ.heap a ≠ some (.plain cls fs)) :
    RecsAt s cls σ' l vals M := by
  obtain ⟨xs, m, h1, h2, h3⟩ := hr
  refine ⟨xs, m, by rw [ha.2 _ (State.lt_next_of_heap h1) hw, h1],
    forall2_jrecAt_agree ha hn h2 (fun v hv a hva haW => ?_), h3⟩
  rcases hMW a haW with hm | hc
  · exact h3 v hv a hva hm
  · obtain ⟨vals', hrel⟩ := forall2_mem_rel h2 v hv
    obtain ⟨b, fs, hb, hbh, -⟩ := jrec_obj hrel
    rw [hva] at hb; cases hb
    exact hc fs hbh

theorem tableAt_agree {σ σ' : State} {A : Addr} {accts : List (List FV)} {M W : List Addr}
    (ht : TableAt σ A accts M) (ha : Agree σ σ' W) (hn : NoStr σ W) (hw : A ∉ W)
    (hMW : ∀ a ∈ W, a ∈ M ∨ ∀ fs, σ.heap a ≠ some (.plain "Cbact04c$AccountRecord" fs)) :
    TableAt σ' A accts M := by
  obtain ⟨xs, h1, h2, h3⟩ := ht
  refine ⟨xs, by rw [ha.2 _ (State.lt_next_of_heap h1) hw, h1],
    forall2_jrecAt_agree ha hn h2 (fun v hv a hva haW => ?_), h3⟩
  rcases hMW a haW with hm | hc
  · exact h3 v hv a hva hm
  · obtain ⟨vals', hrel⟩ := forall2_mem_rel h2 v hv
    obtain ⟨b, fs, hb, hbh, -⟩ := jrec_obj hrel
    rw [hva] at hb; cases hb
    exact hc fs hbh

/-! ## The inputs -/

theorem RunPreG.lens {g : G} {args : List Value} {σ0 : State} (h : RunPreG g args σ0) :
    g.tcat.length < 2147483648 ∧ g.xrefs.length < 2147483648 ∧ g.accts.length < 2147483648 ∧
      g.discs.length < 2147483648 := by
  obtain ⟨hargs, ⟨b1, b2, b3, b4, q1, c1, hargs', ⟨et1, xs1, h1, hb1, hp1⟩, ⟨et2, xs2, h2, hb2, hp2⟩,
    ⟨et3, xs3, h3, hb3, hp3⟩, ⟨et4, xs4, h4, hb4, hp4⟩, -⟩, -⟩ := h
  rw [← Forall2.length_eq hp1, ← Forall2.length_eq hp2, ← Forall2.length_eq hp3,
    ← Forall2.length_eq hp4]
  exact ⟨hb1, hb2, hb3, hb4⟩

/-! ## Message lines -/

theorem startLine_eq :
    jline (Model.txt "START OF EXECUTION OF PROGRAM CBACT04C") =
      JStr.ofString "START OF EXECUTION OF PROGRAM CBACT04C" := by decide

theorem endLine_eq :
    jline (Model.txt "END OF EXECUTION OF PROGRAM CBACT04C") =
      JStr.ofString "END OF EXECUTION OF PROGRAM CBACT04C" := by decide

/-! ## Closing the facts of a cut point after a stretch of statements -/

theorem resAt_congr {σ : State} {res ld lw lr a a' t t' : Addr} {p p' c c' : Value}
    (h : ResAt σ ⟨res, ld, lw, lr, a, t, p, c⟩) : ResAt σ ⟨res, ld, lw, lr, a', t', p', c'⟩ := h

theorem dispAt_start {σ : State} {ld sv : Addr} (accts : List (List FV))
    (hld : σ.heap ld = some (.list .arrayList [.ref sv] 1))
    (hsv : σ.heap sv = some (.str (JStr.ofString "START OF EXECUTION OF PROGRAM CBACT04C"))) :
    DispAt σ ld (Model.init accts).disp :=
  ⟨[.ref sv], 1, hld, .cons ⟨sv, rfl, by rw [hsv]; simp only [Model.init, List.map_cons, startLine_eq]⟩ .nil⟩

/-- Small facts about a state built by allocations and writes. -/
macro "state_simp" : tactic => `(tactic| first
  | (simp only [State.initOf_alloc, State.initOf_setObj]; assumption)
  | (simp only [State.next_alloc, State.next_setObj] at *; omega)
  | (simp only [State.heap_alloc, State.heap_setObj, State.next_alloc, State.next_setObj];
     simp_all; done))

/-! ## The model state along the loop -/

theorem G.st_zero (g : G) : g.st 0 = Model.init g.accts := by simp [G.st]

theorem G.st_succ (g : G) {n : Nat} (hn : n < g.tcat.length) :
    g.st (n + 1) = g.step (g.st n) g.tcat[n] := by
  simp only [G.st]
  rw [List.take_succ, List.getElem?_eq_getElem hn, Option.toList_some, List.foldl_append]
  rfl

theorem G.st_full (g : G) {n : Nat} (hn : g.tcat.length ≤ n) :
    g.st n = g.tcat.foldl g.step (Model.init g.accts) := by
  simp only [G.st]
  rw [List.take_of_length_le hn]

theorem G.out_eq (g : G) :
    g.out = { disp := (g.st g.tcat.length).disp ++ [Model.txt "END OF EXECUTION OF PROGRAM CBACT04C"],
              writes := (g.st g.tcat.length).writes,
              rewrites := (g.st g.tcat.length).rewrites } := by
  rw [G.st_full g (Nat.le_refl _)]
  rfl

end EquivLean.Modernize.Cbact04c.Java
