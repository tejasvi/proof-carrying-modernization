import EquivLean.Modernize.Cbstm03b.Java.TrnxFin

/-!
# CBSTM03B → Java: `call`, the dispatch on the DD name

`call(openErrors, st, area)` reads the area's DD name and operation strings, compares the DD name with
`"TRNXFILE"`, `"XREFFILE"`, `"CUSTFILE"` and `"ACCTFILE"` (`String.equals`, each literal a new string object) and
calls the file procedure of the first match with the operation string, or does nothing. Verified against the
procedures' contracts `procSpec dd` (`callCallees`): the procedure's precondition holds in the heap after the
literals' allocations, its postcondition for the same ghost values is `call`'s.
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open CardDemo.Cbstm03b (ddTrnx ddXref ddCust ddAcct opOpen opRead opReadK opClose stBytes intoBuf)

namespace EquivLean.Modernize.Cbstm03b.Java

/-- `call`'s paths from `pc`, against `runSpecG` (folded: the defeq checks must not run the method). -/
@[irreducible] def callWPd (oe st q : Addr) (oeM : Model.OpenErrs) (s : Model.StM)
    (a : List EquivLean.Cobol.Rec.FVal) (args : List Value) (σ0 : State) (pc : Nat) (fr : Frame) (σ : State) : Prop :=
  bodyWP Gen.prog (callWP Gen.prog callCallees.env 1)
    Gen.Cbstm03b.«call(java.lang.Integer[],Cbstm03b$State,Cbstm03b$LkM03bArea)»
    (Invariants.inst [] args σ0) ((runSpecG oe st q oeM s a).post args σ0) 100 pc fr σ

theorem grows_alloc (σ : State) (o : Obj) : Grows σ (σ.alloc o).2 :=
  ⟨by rw [State.next_alloc]; exact Nat.le_succ _, fun _ hy => State.heap_alloc_of_lt hy o⟩

theorem grows_alloc' {σ0 σ : State} (h : Grows σ0 σ) (o : Obj) : Grows σ0 (σ.alloc o).2 :=
  grows_trans h (grows_alloc σ o)

theorem initsDone_alloc {σ : State} (h : InitsDone σ) (o : Obj) : InitsDone (σ.alloc o).2 := h

theorem opAt_grows {σ σ' : State} {q : Addr} {opv : Value} (h : OpAt σ q opv) (hg : Grows σ σ') :
    OpAt σ' q opv := by
  obtain ⟨fs, h1, h2⟩ := h
  exact ⟨fs, heap_grows hg h1, h2⟩

/-- The model's call for an area whose DD name is none of the four. -/
theorem call_none {oeM : Model.OpenErrs} {s : Model.StM} {a : List EquivLean.Cobol.Rec.FVal}
    (h1 : ¬ Model.aDd a = ddTrnx) (h2 : ¬ Model.aDd a = ddXref) (h3 : ¬ Model.aDd a = ddCust)
    (h4 : ¬ Model.aDd a = ddAcct) : Model.call oeM s a = (s, a) := by
  simp only [Model.call, h1, h2, h3, h4, ↓reduceIte]

/-- The text of a DD name other than `d`'s is not `d`'s text. -/
theorem dd_ne_text {dd d : List UInt8} {t : String} (ht : cp037Str d = JStr.ofString t) (h : ¬ dd = d) :
    ¬ (cp037Str dd = JStr.ofString t) := fun e => h (cp037Str_inj (e.trans ht.symm))

/-- A heap after the literals' allocations. -/
macro "grows_tac" : tactic => `(tactic| repeat (first | exact grows_refl _ | refine grows_alloc' ?_ _))

macro "inits_tac" : tactic => `(tactic| repeat (first | assumption | refine initsDone_alloc ?_ _))

set_option hygiene false in
/-- The leaves of a path through a procedure call: its precondition (the ghost values of `call`'s, in the heap
after the literals), and `call`'s postcondition from the procedure's (`hpost`, the last inaccessible hypothesis). -/
macro "call_close" : tactic => `(tactic| first | exact ⟨oeM, envAtM_grows hE (by grows_tac)⟩ | exact ⟨s, stateAtM_grows hS (by grows_tac), sepM_grows hS hsep (by grows_tac), a, jRecAt_grows hA (by grows_tac), hV, hVa, hK, hdd, opAt_grows hop (by grows_tac), by inits_tac⟩ | (rename_i hpost; exact (hpost oe st q sop oeM s a rfl rfl rfl rfl (envAtM_grows hE (by grows_tac)) (stateAtM_grows hS (by grows_tac)) (sepM_grows hS hsep (by grows_tac)) (jRecAt_grows hA (by grows_tac)) hV hVa hK hdd (opAt_grows hop (by grows_tac)) (by inits_tac)).2.1) | (rename_i hpost; exact (hpost oe st q sop oeM s a rfl rfl rfl rfl (envAtM_grows hE (by grows_tac)) (stateAtM_grows hS (by grows_tac)) (sepM_grows hS hsep (by grows_tac)) (jRecAt_grows hA (by grows_tac)) hV hVa hK hdd (opAt_grows hop (by grows_tac)) (by inits_tac)).2.2.1) | (rename_i hpost; exact (hpost oe st q sop oeM s a rfl rfl rfl rfl (envAtM_grows hE (by grows_tac)) (stateAtM_grows hS (by grows_tac)) (sepM_grows hS hsep (by grows_tac)) (jRecAt_grows hA (by grows_tac)) hV hVa hK hdd (opAt_grows hop (by grows_tac)) (by inits_tac)).2.2.2))

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem call_entry (oe st q : Addr) (oeM : Model.OpenErrs) (s : Model.StM)
    (a : List EquivLean.Cobol.Rec.FVal) (args : List Value) (σ0 : State)
    (hpre : (runSpecG oe st q oeM s a).pre args σ0) :
    callWPd oe st q oeM s a args σ0 0 (Frame.init true args) σ0 := by
  obtain ⟨rfl, hE, hS, hsep, hA, hV, hVa, hK, hI⟩ := hpre
  obtain ⟨q', fsq, dd, op, rc, key, kl, fldt, sdd, sop, src, skey, sfl, hqq, hq, ha, -, -, -, -, -, -, -,
    gdd, jdd, gop, -, -, -, -, -, -, -, -⟩ := areaAt_of hA hVa
  cases hqq
  obtain ⟨xdd, rfl, hxdd⟩ := jdd
  have hdd : Model.aDd a = dd := by rw [ha]; rfl
  have hkept : Kept (EnvAtM σ0 oe oeM ∧ StateAtM σ0 st s ∧ SepM σ0 st ∧
      JRecAt Model.LkM03bArea "Cbstm03b$LkM03bArea" σ0 (.ref q) a ∧ Glue.ValidSt s ∧ Model.LkM03bArea.Valid a ∧
      Glue.KeyOk a ∧ Model.aDd a = dd ∧ OpAt σ0 q sop ∧ InitsDone σ0) :=
    Kept.intro ⟨hE, hS, hsep, hA, hV, hVa, hK, hdd, ⟨fsq, hq, gop⟩, hI⟩
  have hI0 : σ0.initOf "Cbstm03b" = .done := hI.1
  clear hE hS hsep hA hV hVa hK hI ha
  by_cases hT : dd = ddTrnx
  · subst hT
    clear hdd
    rw [dd_texts.1] at hxdd
    simp only [callWPd, runSpecG, Spec.of]
    jvc [callCallees, trnxProcSig, xrefProcSig, custProcSig, acctProcSig, procParams]
    all_goals obtain ⟨hE, hS, hsep, hA, hV, hVa, hK, hdd, hop, hI⟩ := Kept.elim ‹Kept _›
    all_goals call_close
  by_cases hX : dd = ddXref
  · subst hX
    clear hdd
    rw [dd_texts.2.1] at hxdd
    have hn1 : ¬ (JStr.ofString "XREFFILE" = JStr.ofString "TRNXFILE") := by decide +kernel
    simp only [callWPd, runSpecG, Spec.of]
    jvc [callCallees, trnxProcSig, xrefProcSig, custProcSig, acctProcSig, procParams]
    all_goals obtain ⟨hE, hS, hsep, hA, hV, hVa, hK, hdd, hop, hI⟩ := Kept.elim ‹Kept _›
    all_goals call_close
  by_cases hC : dd = ddCust
  · subst hC
    clear hdd
    rw [dd_texts.2.2.1] at hxdd
    have hn1 : ¬ (JStr.ofString "CUSTFILE" = JStr.ofString "TRNXFILE") := by decide +kernel
    have hn2 : ¬ (JStr.ofString "CUSTFILE" = JStr.ofString "XREFFILE") := by decide +kernel
    simp only [callWPd, runSpecG, Spec.of]
    jvc [callCallees, trnxProcSig, xrefProcSig, custProcSig, acctProcSig, procParams]
    all_goals obtain ⟨hE, hS, hsep, hA, hV, hVa, hK, hdd, hop, hI⟩ := Kept.elim ‹Kept _›
    all_goals call_close
  by_cases hAc : dd = ddAcct
  · subst hAc
    clear hdd
    rw [dd_texts.2.2.2] at hxdd
    have hn1 : ¬ (JStr.ofString "ACCTFILE" = JStr.ofString "TRNXFILE") := by decide +kernel
    have hn2 : ¬ (JStr.ofString "ACCTFILE" = JStr.ofString "XREFFILE") := by decide +kernel
    have hn3 : ¬ (JStr.ofString "ACCTFILE" = JStr.ofString "CUSTFILE") := by decide +kernel
    simp only [callWPd, runSpecG, Spec.of]
    jvc [callCallees, trnxProcSig, xrefProcSig, custProcSig, acctProcSig, procParams]
    all_goals obtain ⟨hE, hS, hsep, hA, hV, hVa, hK, hdd, hop, hI⟩ := Kept.elim ‹Kept _›
    all_goals call_close
  -- no match: `call` returns, the model's call changes nothing
  have hcall : Model.call oeM s a = (s, a) :=
    call_none (by rw [hdd]; exact hT) (by rw [hdd]; exact hX) (by rw [hdd]; exact hC) (by rw [hdd]; exact hAc)
  have hn1 := dd_ne_text dd_texts.1 hT
  have hn2 := dd_ne_text dd_texts.2.1 hX
  have hn3 := dd_ne_text dd_texts.2.2.1 hC
  have hn4 := dd_ne_text dd_texts.2.2.2 hAc
  clear hdd hT hX hC hAc
  simp only [callWPd, runSpecG, Spec.of, hcall]
  jvc [callCallees, trnxProcSig, xrefProcSig, custProcSig, acctProcSig, procParams]
  all_goals obtain ⟨hE, hS, hsep, hA, hV, hVa, hK, hdd, hop, hI⟩ := Kept.elim ‹Kept _›
  all_goals first
    | exact stateAtM_grows hS (by grows_tac)
    | exact sepM_grows hS hsep (by grows_tac)
    | exact jRecAt_grows hA (by grows_tac)

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
/-- **`call`'s verification conditions** against the file procedures' contracts, for fixed ghost values. -/
theorem call_vc (oe st q : Addr) (oeM : Model.OpenErrs) (s : Model.StM) (a : List EquivLean.Cobol.Rec.FVal) :
    MethodVC Gen.prog callCallees.env 1 callRef (runSpecG oe st q oeM s a) [] 100 := by
  refine ⟨_, rfl, fun args σ0 hpre => ⟨?_, fun p hp => by simp [Invariants.inst] at hp⟩⟩
  have h := call_entry oe st q oeM s a args σ0 hpre
  unfold callWPd at h
  exact h

end EquivLean.Modernize.Cbstm03b.Java

#print axioms EquivLean.Modernize.Cbstm03b.Java.call_vc
