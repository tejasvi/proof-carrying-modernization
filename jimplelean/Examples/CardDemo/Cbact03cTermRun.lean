/-
  Examples/CardDemo/Cbact03cTermRun.lean

  Termination of CBACT03C's `run` (the read loop) by the split VC, and its total correctness. The
  loop's counters live in the state object: the variant `c3RunVar` reads `pos` and `atEof` there
  (twice the records left, plus one until the end-of-file flag is set). One lemma per segment, as for
  `c3_run_vc`.
-/
import Examples.CardDemo.Cbact03cTermHelpers

open Jimple

namespace Examples.CardDemo

/-- Twice the records left, plus one until `atEof` is set; `pos` and `atEof` are fields of the state
    object (local `$r1`, 2), the records the entry array's. -/
def c3RunVar (args : List Value) (σ0 : State) (fr : Frame) (σ : State) : Nat :=
  match args, fr.get 2 with
  | [.ref a], some (.ref st) =>
    match σ0.heap a, σ.heap st with
    | some (.array _ xs), some (.plain _ sfs) =>
      match Fields.get sfs (stCls, "pos"), Fields.get sfs (stCls, "atEof") with
      | some (.int i), some (.int z) => 2 * (xs.length - i.toInt.toNat) + (if z = 0 then 1 else 0)
      | _, _ => 0
    | _, _ => 0
  | _, _ => 0

/-- The thin paths of `run` from statement `pc`, cut assertions `I`. -/
def c3RunThinWP (I : Cuts) (pc : Nat) (fr : Frame) (σ : State) : Prop :=
  bodyWP C3.prog (callWPThin C3.prog c3RunCallees.env 1) C3.Cbact03c.«run(Cbact03c$CardXrefRecord[])» I
    (fun _ => True) 200 pc fr σ

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem c3_run_thin_entry (args : List Value) (σ0 : State) (hpre : c3RunSpecJ.pre args σ0) :
    c3RunThinWP (c3RunInv.map fun p => (p.1, fun _ _ => True)) 0 (Frame.init true args) σ0 := by
  jvc [ite_nat_ne, c3RunThinWP, c3RunSpecJ, c3RunInv, c3RunInv29, C3RunAt, c3RunCallees, c3SpacesSig,
    c3FixLenSig, c3RecordTextSig, c3StartText, c3EndText, xrefLines, xrecLineV, xrefLine, xfieldOf, xfieldLong,
    XrefOk, XStrField, XLongField, xrefCls, StateRecOk, stateLine, sfieldOf, sfieldLong, stCls,
    StrOk, argText, textN, textY, Grows, spacesSpec, fixLenSpec, recordTextSpec]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem c3_run_thin_read (args : List Value) (σ0 : State) (hpre : c3RunSpecJ.pre args σ0)
    (fr : Frame) (σ : State) (a : Addr) (et : JType) (xs : List Value) (ha : args = [.ref a])
    (harr : σ0.heap a = some (.array et xs)) (st : Addr) (sfs : List (FieldKey × Value)) (res : Addr)
    (fs : List (FieldKey × Value)) (l : Addr) (ys : List Value) (m : Nat) (i z : I32) (e : Addr)
    (sv ap rc rcu rac rf : Value)
    (h : C3RunAt σ0 fr σ a xs st sfs res fs l ys m i z e sv ap rc rcu rac rf) (hz : z = 0)
    (hi : i.toInt < xs.length) :
    c3RunThinWP (c3RunInv.map fun q => (q.1, fun fr' σ' => c3RunVar args σ0 fr' σ' < c3RunVar args σ0 fr σ))
      29 fr σ := by
  jvc [ite_nat_ne, c3RunThinWP, c3RunVar, c3RunSpecJ, c3RunInv, c3RunInv29, C3RunAt, c3RunCallees, c3SpacesSig,
    c3FixLenSig, c3RecordTextSig, c3StartText, c3EndText, xrefLines, xrecLineV, xrefLine, xfieldOf, xfieldLong,
    XrefOk, XStrField, XLongField, xrefCls, StateRecOk, stateLine, sfieldOf, sfieldLong, stCls,
    StrOk, argText, textN, textY, Grows, spacesSpec, fixLenSpec, recordTextSpec]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem c3_run_thin_eof (args : List Value) (σ0 : State) (hpre : c3RunSpecJ.pre args σ0)
    (fr : Frame) (σ : State) (a : Addr) (et : JType) (xs : List Value) (ha : args = [.ref a])
    (harr : σ0.heap a = some (.array et xs)) (st : Addr) (sfs : List (FieldKey × Value)) (res : Addr)
    (fs : List (FieldKey × Value)) (l : Addr) (ys : List Value) (m : Nat) (i z : I32) (e : Addr)
    (sv ap rc rcu rac rf : Value)
    (h : C3RunAt σ0 fr σ a xs st sfs res fs l ys m i z e sv ap rc rcu rac rf) (hz : z = 0)
    (hi : (xs.length : Int) ≤ i.toInt) :
    c3RunThinWP (c3RunInv.map fun q => (q.1, fun fr' σ' => c3RunVar args σ0 fr' σ' < c3RunVar args σ0 fr σ))
      29 fr σ := by
  jvc [ite_nat_ne, c3RunThinWP, c3RunVar, c3RunSpecJ, c3RunInv, c3RunInv29, C3RunAt, c3RunCallees, c3SpacesSig,
    c3FixLenSig, c3RecordTextSig, c3StartText, c3EndText, xrefLines, xrecLineV, xrefLine, xfieldOf, xfieldLong,
    XrefOk, XStrField, XLongField, xrefCls, StateRecOk, stateLine, sfieldOf, sfieldLong, stCls,
    StrOk, argText, textN, textY, Grows, spacesSpec, fixLenSpec, recordTextSpec]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem c3_run_thin_exit (args : List Value) (σ0 : State) (hpre : c3RunSpecJ.pre args σ0)
    (fr : Frame) (σ : State) (a : Addr) (et : JType) (xs : List Value) (ha : args = [.ref a])
    (harr : σ0.heap a = some (.array et xs)) (st : Addr) (sfs : List (FieldKey × Value)) (res : Addr)
    (fs : List (FieldKey × Value)) (l : Addr) (ys : List Value) (m : Nat) (i z : I32) (e : Addr)
    (sv ap rc rcu rac rf : Value)
    (h : C3RunAt σ0 fr σ a xs st sfs res fs l ys m i z e sv ap rc rcu rac rf) (hz : z ≠ 0) :
    c3RunThinWP (c3RunInv.map fun q => (q.1, fun fr' σ' => c3RunVar args σ0 fr' σ' < c3RunVar args σ0 fr σ))
      29 fr σ := by
  jvc [ite_nat_ne, c3RunThinWP, c3RunVar, c3RunSpecJ, c3RunInv, c3RunInv29, C3RunAt, c3RunCallees, c3SpacesSig,
    c3FixLenSig, c3RecordTextSig, c3StartText, c3EndText, xrefLines, xrecLineV, xrefLine, xfieldOf, xfieldLong,
    XrefOk, XStrField, XLongField, xrefCls, StateRecOk, stateLine, sfieldOf, sfieldLong, stCls,
    StrOk, argText, textN, textY, Grows, spacesSpec, fixLenSpec, recordTextSpec]

theorem c3_run_thin : ThinVC C3.prog c3RunCallees.env 1 c3RunRef c3RunSpecJ c3RunInv (fun _ => c3RunVar) 200 := by
  refine ⟨_, rfl, fun args σ0 hpre => ⟨?_, ?_⟩⟩
  · show c3RunThinWP (c3RunInv.map fun p => (p.1, fun _ _ => True)) 0 (Frame.init true args) σ0
    exact c3_run_thin_entry args σ0 hpre
  · intro p hp fr σ hI
    simp only [c3RunInv, List.mem_cons, List.not_mem_nil, or_false] at hp
    subst hp
    show c3RunThinWP (c3RunInv.map fun q => (q.1, fun fr' σ' => c3RunVar args σ0 fr' σ' < c3RunVar args σ0 fr σ))
      29 fr σ
    have hpre' := hpre
    obtain ⟨a, et, xs, ha, harr, -⟩ := hpre'
    obtain ⟨st, sfs, res, fs, l, ys, m, i, z, e, sv, ap, rc, rcu, rac, rf, h⟩ := hI a et xs ha harr
    by_cases hz : z = 0
    · rcases Int.lt_or_le i.toInt xs.length with hi | hi
      · exact c3_run_thin_read args σ0 hpre fr σ a et xs ha harr st sfs res fs l ys m i z e sv ap rc rcu
          rac rf h hz hi
      · exact c3_run_thin_eof args σ0 hpre fr σ a et xs ha harr st sfs res fs l ys m i z e sv ap rc rcu
          rac rf h hz hi
    · exact c3_run_thin_exit args σ0 hpre fr σ a et xs ha harr st sfs res fs l ys m i z e sv ap rc rcu
        rac rf h hz

/-- **CBACT03C, Java side, termination**: every call of `run` on an array of cross-reference records
    terminates. -/
theorem c3_run_term : ∀ args σ, c3RunSpecJ.pre args σ → MTerm C3.prog c3RunRef args σ :=
  TermVC.mterm (rank := fun _ => 0) (r := 1)
    (Contracts.valid_of_ok (by
      intro p hp
      simp only [c3RunCallees, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl
      · exact c3_spaces_ok
      · exact c3_fixLen_ok
      · exact c3_recordText_ok))
    (Contracts.term_of_ok (by
      intro p hp
      simp only [c3RunCallees, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl
      · exact c3_spaces_cterm
      · exact c3_fixLen_cterm
      · exact c3_recordText_cterm) _ _)
    (TermVC.of_thin (SpecEnv.below_const _ _ (by decide)) c3_run_vc c3_run_thin)

/-- **CBACT03C, Java side, total correctness.** -/
theorem c3_run_total : ∀ args σ, c3RunSpecJ.pre args σ →
    (∃ o, MExec C3.prog c3RunRef args σ o) ∧ ∀ o, MExec C3.prog c3RunRef args σ o → c3RunSpecJ.post args σ o :=
  total_of_sat_mterm c3_run_sat c3_run_term

end Examples.CardDemo

#print axioms Examples.CardDemo.c3_run_term
#print axioms Examples.CardDemo.c3_run_total
