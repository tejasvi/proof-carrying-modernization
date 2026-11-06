import EquivLean.Modernize.Cbtrn02c.Any.JavaRunRunDefs

/-!
# CBTRN02C → Java: `run` before the main loop

The cut points 35, 44 and 48 (after each work-storage record is built) and the facts that give the
main loop's invariant at its first visit (`W_init`: `W` for `Model.init`).
-/

open Jimple EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbtrn02c.Java

/-- The account table at `σ0.next + 8` complete: copies of the accounts, allocated below `b`. -/
def TabDone (g : G) (σ0 σ : State) (b : Nat) : Prop :=
  ∃ ys, σ.heap (σ0.next + 8) = some (.array (.cls "Cbtrn02c$AccountRecord") ys) ∧
    Forall2 (JRecAt AccountRecord "Cbtrn02c$AccountRecord" σ) ys g.accts ∧
    ∀ v ∈ ys, ∀ a, v = .ref a → σ0.next + 9 ≤ a ∧ a < b

/-- The category list at `lC` complete: copies of the category records, allocated below `b`. -/
def CatDone (g : G) (σ0 σ : State) (lC b : Nat) : Prop :=
  ∃ xs m, σ.heap lC = some (.list .arrayList xs m) ∧
    Forall2 (JRecAt TranCatBalRecord "Cbtrn02c$TranCatBalRecord" σ) xs g.cats ∧
    ∀ v ∈ xs, ∀ a, v = .ref a → σ0.next + 9 ≤ a ∧ a < b

/-- After the copy loops: the `Result` and its lists, the account table, the category list `lC`,
the empty key list `lK` (allocated after all the copies). -/
def PreL (g : G) (σ0 σ : State) (lC lK : Addr) : Prop :=
  ResInit σ0 σ ∧ ListsInit σ0 σ ∧ TabDone g σ0 σ lK ∧ CatDone g σ0 σ lC lK ∧
  (∃ m, σ.heap lK = some (.list .arrayList [] m)) ∧ σ0.next + 9 ≤ lC ∧ lC < lK

/-- The locals that hold the inputs, the `Result`, the account table and the two lists. -/
def LocsP (g : G) (σ0 : State) (fr : Frame) (lC lK : Addr) : Prop :=
  fr.get 32 = some (.ref g.a1) ∧ fr.get 0 = some (.ref g.a2) ∧ fr.get 16 = some (.ref g.cs) ∧
  fr.get 31 = some (.ref σ0.next) ∧ fr.get 8 = some (.ref (σ0.next + 8)) ∧
  fr.get 11 = some (.ref lC) ∧ fr.get 12 = some (.ref lK)

/-- The heap grown from the entry state, the classes as they were. -/
def StateP (σ0 σ : State) : Prop :=
  Grows σ0 σ ∧ σ.inits = σ0.inits ∧ σ.statics = σ0.statics ∧
  σ.initOf "Cbtrn02c" = σ0.initOf "Cbtrn02c"

abbrev xrCls : ClassName := "Cbtrn02c$CardXrefRecord"
abbrev acCls : ClassName := "Cbtrn02c$AccountRecord"
abbrev tcCls : ClassName := "Cbtrn02c$TranCatBalRecord"
abbrev trCls : ClassName := "Cbtrn02c$TranRecord"

/-- Statement 35: `xrefWs` built. -/
def J35 (g : G) (_args : List Value) (σ0 : State) (fr : Frame) (σ : State) : Prop :=
  ∃ (lC lK wX : Addr), LocsP g σ0 fr lC lK ∧ fr.get 6 = some (.ref wX) ∧
    Hide (PreL g σ0 σ lC lK ∧ WSObj σ wX xrCls (keysOf CardXrefRecord xrCls)) ∧
    lK < wX ∧ StateP σ0 σ

/-- Statement 44: `acctWs` built. -/
def J44 (g : G) (_args : List Value) (σ0 : State) (fr : Frame) (σ : State) : Prop :=
  ∃ (lC lK wX wA : Addr), LocsP g σ0 fr lC lK ∧ fr.get 6 = some (.ref wX) ∧
    fr.get 13 = some (.ref wA) ∧
    Hide (PreL g σ0 σ lC lK ∧ WSObj σ wX xrCls (keysOf CardXrefRecord xrCls) ∧
      WSObj σ wA acCls (keysOf AccountRecord acCls)) ∧
    lK < wX ∧ wX < wA ∧ StateP σ0 σ

/-- Statement 48: `tcatWs` built (its `FILLER` of spaces). -/
def J48 (g : G) (_args : List Value) (σ0 : State) (fr : Frame) (σ : State) : Prop :=
  ∃ (lC lK wX wA wC : Addr), LocsP g σ0 fr lC lK ∧ fr.get 6 = some (.ref wX) ∧
    fr.get 13 = some (.ref wA) ∧ fr.get 29 = some (.ref wC) ∧
    Hide (PreL g σ0 σ lC lK ∧ WSObj σ wX xrCls (keysOf CardXrefRecord xrCls) ∧
      WSObj σ wA acCls (keysOf AccountRecord acCls) ∧
      WSObj σ wC tcCls (keysOf TranCatBalRecord tcCls) ∧ WSFill σ wC tcCls (Model.sp 22)) ∧
    lK < wX ∧ wX < wA ∧ wA < wC ∧ StateP σ0 σ

/-! ## Along the heap growth -/

theorem ResInit.grows {σ0 σ σ' : State} (h : ResInit σ0 σ) (hg : Grows σ σ') : ResInit σ0 σ' := by
  obtain ⟨fs, h1, h2⟩ := h
  exact ⟨fs, heap_of_grows hg h1, h2⟩

theorem ListsInit.grows {σ0 σ σ' : State} (h : ListsInit σ0 σ) (hg : Grows σ σ') :
    ListsInit σ0 σ' := by
  obtain ⟨⟨m1, h1⟩, h7, ⟨m2, h2⟩, ⟨m3, h3⟩, ⟨m4, h4⟩, ⟨m5, h5⟩, ⟨m6, h6⟩⟩ := h
  exact ⟨⟨m1, heap_of_grows hg h1⟩, heap_of_grows hg h7, ⟨m2, heap_of_grows hg h2⟩,
    ⟨m3, heap_of_grows hg h3⟩, ⟨m4, heap_of_grows hg h4⟩, ⟨m5, heap_of_grows hg h5⟩,
    ⟨m6, heap_of_grows hg h6⟩⟩

theorem TabDone.grows {g : G} {σ0 σ σ' : State} {b : Nat} (h : TabDone g σ0 σ b) (hg : Grows σ σ') :
    TabDone g σ0 σ' b := by
  obtain ⟨ys, h1, h2, h3⟩ := h
  exact ⟨ys, heap_of_grows hg h1, forall2_imp (fun _ _ h => jrecAt_grows h hg) h2, h3⟩

theorem CatDone.grows {g : G} {σ0 σ σ' : State} {lC b : Nat} (h : CatDone g σ0 σ lC b)
    (hg : Grows σ σ') : CatDone g σ0 σ' lC b := by
  obtain ⟨xs, m, h1, h2, h3⟩ := h
  exact ⟨xs, m, heap_of_grows hg h1, forall2_imp (fun _ _ h => jrecAt_grows h hg) h2, h3⟩

theorem PreL.grows {g : G} {σ0 σ σ' : State} {lC lK : Addr} (h : PreL g σ0 σ lC lK)
    (hg : Grows σ σ') : PreL g σ0 σ' lC lK := by
  obtain ⟨h1, h2, h3, h4, ⟨m, h5⟩, h6, h7⟩ := h
  exact ⟨h1.grows hg, h2.grows hg, h3.grows hg, h4.grows hg, ⟨m, heap_of_grows hg h5⟩, h6, h7⟩

/-! ## The copy loops -/

/-- One more element stored in a partly filled array. -/
theorem set_fill {α : Type} (ys : List α) (n : Nat) (v w : α) :
    (ys ++ List.replicate (n + 1) v).set ys.length w = (ys ++ [w]) ++ List.replicate n v := by
  induction ys with
  | nil => simp [List.replicate_succ]
  | cons y ys ih => simp [ih]

/-- The addresses of record objects are below `σ.next`. -/
theorem rec_lt_next {s : Schema} {cls : ClassName} {σ : State} {xs : List Value}
    {vals : List (List EquivLean.Cobol.Rec.FVal)} (h : Forall2 (JRecAt s cls σ) xs vals) :
    ∀ v ∈ xs, ∀ a, v = .ref a → a < σ.next := by
  intro v hv a hva
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hv
  have hr := forall2_get h i hi (by rw [← forall2_length h]; exact hi)
  obtain ⟨x, fs, hx, hxh, -⟩ := hr
  rw [hva] at hx
  cases hx
  exact State.lt_next_of_heap hxh

/-- The table complete: its records lie below the next allocation. -/
theorem tabDone_of_init {g : G} {σ0 σ : State} (h : TabInit g σ0 σ g.accts.length) :
    TabDone g σ0 σ σ.next := by
  obtain ⟨ys, h1, h2, h3⟩ := h
  rw [Nat.sub_self, List.replicate_zero, List.append_nil] at h1
  rw [List.take_length] at h2
  exact ⟨ys, h1, h2, fun v hv a hva => ⟨h3 v hv a hva, rec_lt_next h2 v hv a hva⟩⟩

/-! ## The main loop's first visit -/

/-- The addresses of `run`'s objects. -/
def A0 (σ0 : State) (lC lK wX wA wC wT : Addr) : Addrs :=
  ⟨σ0.next, σ0.next + 1, σ0.next + 2, σ0.next + 3, σ0.next + 4, σ0.next + 5, σ0.next + 6,
    σ0.next + 8, lC, lK, wX, wA, wC, wT⟩

theorem not_ws {σ0 : State} {lC lK wX wA wC wT : Addr} {a : Addr} (ha : a < lK) (h1 : lK < wX)
    (h2 : wX < wA) (h3 : wA < wC) (h4 : wC < wT) :
    ∀ w ∈ (A0 σ0 lC lK wX wA wC wT).ws, Value.ref a ≠ .ref w := by
  intro w hw
  simp only [Addrs.ws, A0, List.mem_cons, List.not_mem_nil, or_false] at hw
  intro h
  cases h
  jomega

theorem arec_input {s : Schema} {cls : ClassName} {σ0 σ : State} {a : Addr} {ws : List Addr}
    {vals : List (List EquivLean.Cobol.Rec.FVal)}
    (h : ∃ et xs, σ0.heap a = some (.array et xs) ∧ xs.length < 2147483648 ∧
      Forall2 (JRecAt s cls σ0) xs vals)
    (hg : Grows σ0 σ) (hws : ∀ w ∈ ws, σ0.next ≤ w) : ARec σ a s cls ws vals := by
  obtain ⟨et, xs, h1, h2, h3⟩ := h
  refine ⟨et, xs, heap_of_grows hg h1, forall2_imp (fun _ _ h => jrecAt_grows h hg) h3, ?_, h2⟩
  intro v hv w hw hvw
  have := rec_lt_next h3 v hv w hvw
  have := hws w hw
  jomega

set_option maxRecDepth 4000 in
/-- **`W` at the first visit of the main loop**: the state holds `Model.init`. -/
theorem W_init {g : G} {σ0 σ : State} {lC lK wX wA wC wT : Addr}
    (hin : RunIn g.args σ0 g.trans g.xrefs g.accts g.cats g.clk) (hP : PreL g σ0 σ lC lK)
    (hX : WSObj σ wX xrCls (keysOf CardXrefRecord xrCls))
    (hA : WSObj σ wA acCls (keysOf AccountRecord acCls))
    (hC : WSObj σ wC tcCls (keysOf TranCatBalRecord tcCls))
    (hT : WSObj σ wT trCls (keysOf TranRecord trCls))
    (hFC : WSFill σ wC tcCls (Model.sp 22)) (hFT : WSFill σ wT trCls (Model.sp 20))
    (h1 : lK < wX) (h2 : wX < wA) (h3 : wA < wC) (h4 : wC < wT) (hg : Grows σ0 σ) :
    W σ (A0 σ0 lC lK wX wA wC wT) (Model.init g.accts g.cats) ∧
      Inp σ g (A0 σ0 lC lK wX wA wC wT) ∧ MV (Model.init g.accts g.cats) := by
  obtain ⟨a1, a2, a3, a4, cs, hargs, hd, hx, ha, hc, hcs, -, hv1, hv2, hv3, hv4, -⟩ := hin
  simp only [G.args, List.cons.injEq, Value.ref.injEq, and_true] at hargs
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hargs
  obtain ⟨hR, ⟨⟨mD, hD⟩, hS, ⟨mT, hT0⟩, ⟨mR, hR0⟩, ⟨mCW, hCW0⟩, ⟨mAR, hAR0⟩, ⟨mCR, hCR0⟩⟩,
    ⟨ys, hys, hysf, hysa⟩, ⟨xs, m, hxs, hxsf, hxsa⟩, ⟨mK, hK⟩, hlC, hlCK⟩ := hP
  obtain ⟨et3, xs3, -, hl3, hf3⟩ := ha
  obtain ⟨et4, xs4, -, hl4, hf4⟩ := hc
  have hlen3 := forall2_length hf3
  have hlen4 := forall2_length hf4
  have hlenys := forall2_length hysf
  have hlenxs := forall2_length hxsf
  have hws : ∀ w ∈ (A0 σ0 lC lK wX wA wC wT).ws, σ0.next ≤ w := by
    intro w hw
    simp only [Addrs.ws, A0, List.mem_cons, List.not_mem_nil, or_false] at hw
    jomega
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hX, hA, hC, hT, hFC, hFT, ?_⟩,
    ⟨arec_input hd hg hws, arec_input hx hg hws, jstrAt_grows hcs hg⟩, hv3, hv4, ?_⟩
  · exact hR
  · exact ⟨[.ref (σ0.next + 7)], mD, hD, .cons ⟨σ0.next + 7, rfl, hS⟩ .nil, by simp⟩
  · exact ⟨[], mT, hT0, .nil, by simp, by decide⟩
  · exact ⟨[], mR, hR0, .nil, by simp, by decide⟩
  · exact ⟨[], mCW, hCW0, .nil, by simp, by decide⟩
  · exact ⟨[], mAR, hAR0, .nil, by simp, by decide⟩
  · exact ⟨[], mCR, hCR0, .nil, by simp, by decide⟩
  · exact ⟨_, ys, hys, hysf, fun v hv w hw => by
      intro hvw
      subst hvw
      exact not_ws (hysa _ hv w rfl).2 h1 h2 h3 h4 w hw rfl, by omega⟩
  · exact ⟨xs, m, hxs, hxsf, fun v hv w hw => by
      intro hvw
      subst hvw
      exact not_ws (hxsa _ hv w rfl).2 h1 h2 h3 h4 w hw rfl, by omega⟩
  · exact ⟨[], mK, hK, .nil, by decide⟩
  · simp only [A0, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil, not_false_eq_true, and_true]
    repeat' constructor
    all_goals jomega
  · simp [Model.init, Model.sp]

end EquivLean.Modernize.Cbtrn02c.Java
