-- Copied from JimpleLean (frozen snapshot ~/jimplelean_work/snapshots/JimpleLean-20261025T2312Z,
-- Examples/CardDemo/Cbcus01cTermRun.lean); proved by JimpleLean's own session.  Only the imports, the
-- program (`CU`, the same Jimple files, is equiv-lean's generated
-- `EquivLean.Modernize.Cbcus01c.Java.Gen`) and the namespace differ (tools/modernize/import_jl.py).
/-
  Examples/CardDemo/Cbcus01cTermRun.lean

  Termination of CBCUS01C's `run` (the read loop) by the split VC, and its total correctness. The
  thin VC takes the correctness invariant of the loop head (`cuRunInv`) with the variant `cuRunVar`:
  twice the records left, plus one until the end-of-file flag is set. One lemma per segment, as for
  `cu_run_vc`.
-/
import EquivLean.Modernize.JL.Cbcus01cTermHelpers

open Jimple

namespace EquivLean.Modernize.JL

/-- Twice the records left, plus one until the end-of-file flag `z` (local `$z0`, 10) is set:
    the read path takes a record (−2), the end-of-file path sets the flag (−1). The records are the
    entry array's; `i` is local `i5` (7). -/
def cuRunVar (args : List Value) (σ0 : State) (fr : Frame) (_ : State) : Nat :=
  match args with
  | [.ref a] =>
    match σ0.heap a, fr.get 7, fr.get 10 with
    | some (.array _ xs), some (.int i), some (.int z) =>
      2 * (xs.length - i.toInt.toNat) + (if z = 0 then 1 else 0)
    | _, _, _ => 0
  | _ => 0

/-- The thin paths of `run` from statement `pc`, cut assertions `I`. -/
def cuRunThinWP (I : Cuts) (pc : Nat) (fr : Frame) (σ : State) : Prop :=
  bodyWP EquivLean.Modernize.Cbcus01c.Java.Gen.prog (callWPThin EquivLean.Modernize.Cbcus01c.Java.Gen.prog cuRunCallees.env 1) EquivLean.Modernize.Cbcus01c.Java.Gen.Cbcus01c.«run(Cbcus01c$CustomerRecord[])» I
    (fun _ => True) 200 pc fr σ

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem cu_run_thin_entry (args : List Value) (σ0 : State) (hpre : cuRunSpecJ.pre args σ0) :
    cuRunThinWP (cuRunInv.map fun p => (p.1, fun _ _ => True)) 0 (Frame.init true args) σ0 := by
  jvc [ite_nat_ne, cuRunThinWP, cuRunSpecJ, cuRunInv, cuRunInv26, CuRunAt, cuRunCallees, cuFmtRecordInitialSig,
    cuFmtRecordSig, cuStartText, cuEndText, custLines, crecLineV, Grows, fmtRecordInitialSpec, fmtRecordSpec]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem cu_run_thin_read (args : List Value) (σ0 : State) (hpre : cuRunSpecJ.pre args σ0)
    (fr : Frame) (σ : State) (a : Addr) (et : JType) (xs : List Value) (ha : args = [.ref a])
    (harr : σ0.heap a = some (.array et xs)) (res : Addr) (fs : List (FieldKey × Value)) (l : Addr)
    (ys : List Value) (m : Nat) (i z : I32) (h : CuRunAt σ0 fr σ a xs res fs l ys m i z) (hz : z = 0)
    (hi : i.toInt < xs.length) :
    cuRunThinWP (cuRunInv.map fun q => (q.1, fun fr' σ' => cuRunVar args σ0 fr' σ' < cuRunVar args σ0 fr σ))
      26 fr σ := by
  jvc [ite_nat_ne, cuRunThinWP, cuRunVar, cuRunSpecJ, cuRunInv, cuRunInv26, CuRunAt, cuRunCallees,
    cuFmtRecordInitialSig, cuFmtRecordSig, cuStartText, cuEndText, custLines, crecLineV, Grows,
    fmtRecordInitialSpec, fmtRecordSpec]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem cu_run_thin_eof (args : List Value) (σ0 : State) (hpre : cuRunSpecJ.pre args σ0)
    (fr : Frame) (σ : State) (a : Addr) (et : JType) (xs : List Value) (ha : args = [.ref a])
    (harr : σ0.heap a = some (.array et xs)) (res : Addr) (fs : List (FieldKey × Value)) (l : Addr)
    (ys : List Value) (m : Nat) (i z : I32) (h : CuRunAt σ0 fr σ a xs res fs l ys m i z) (hz : z = 0)
    (hi : xs.length ≤ i.toInt) :
    cuRunThinWP (cuRunInv.map fun q => (q.1, fun fr' σ' => cuRunVar args σ0 fr' σ' < cuRunVar args σ0 fr σ))
      26 fr σ := by
  jvc [ite_nat_ne, cuRunThinWP, cuRunVar, cuRunSpecJ, cuRunInv, cuRunInv26, CuRunAt, cuRunCallees,
    cuFmtRecordInitialSig, cuFmtRecordSig, cuStartText, cuEndText, custLines, crecLineV, Grows,
    fmtRecordInitialSpec, fmtRecordSpec]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem cu_run_thin_exit (args : List Value) (σ0 : State) (hpre : cuRunSpecJ.pre args σ0)
    (fr : Frame) (σ : State) (a : Addr) (et : JType) (xs : List Value) (ha : args = [.ref a])
    (harr : σ0.heap a = some (.array et xs)) (res : Addr) (fs : List (FieldKey × Value)) (l : Addr)
    (ys : List Value) (m : Nat) (i z : I32) (h : CuRunAt σ0 fr σ a xs res fs l ys m i z) (hz : z ≠ 0) :
    cuRunThinWP (cuRunInv.map fun q => (q.1, fun fr' σ' => cuRunVar args σ0 fr' σ' < cuRunVar args σ0 fr σ))
      26 fr σ := by
  jvc [ite_nat_ne, cuRunThinWP, cuRunVar, cuRunSpecJ, cuRunInv, cuRunInv26, CuRunAt, cuRunCallees,
    cuFmtRecordInitialSig, cuFmtRecordSig, cuStartText, cuEndText, custLines, crecLineV, Grows,
    fmtRecordInitialSpec, fmtRecordSpec]

theorem cu_run_thin : ThinVC EquivLean.Modernize.Cbcus01c.Java.Gen.prog cuRunCallees.env 1 cuRunRef cuRunSpecJ cuRunInv (fun _ => cuRunVar) 200 := by
  refine ⟨_, rfl, fun args σ0 hpre => ⟨?_, ?_⟩⟩
  · show cuRunThinWP (cuRunInv.map fun p => (p.1, fun _ _ => True)) 0 (Frame.init true args) σ0
    exact cu_run_thin_entry args σ0 hpre
  · intro p hp fr σ hI
    simp only [cuRunInv, List.mem_cons, List.not_mem_nil, or_false] at hp
    subst hp
    show cuRunThinWP (cuRunInv.map fun q => (q.1, fun fr' σ' => cuRunVar args σ0 fr' σ' < cuRunVar args σ0 fr σ))
      26 fr σ
    have hpre' := hpre
    obtain ⟨a, et, xs, ha, harr, -⟩ := hpre'
    obtain ⟨res, fs, l, ys, m, i, z, h⟩ := hI a et xs ha harr
    by_cases hz : z = 0
    · rcases Int.lt_or_le i.toInt xs.length with hi | hi
      · exact cu_run_thin_read args σ0 hpre fr σ a et xs ha harr res fs l ys m i z h hz hi
      · exact cu_run_thin_eof args σ0 hpre fr σ a et xs ha harr res fs l ys m i z h hz hi
    · exact cu_run_thin_exit args σ0 hpre fr σ a et xs ha harr res fs l ys m i z h hz

/-- **CBCUS01C, Java side, termination**: every call of `run` on an array of records as `fmtRecord`
    reads them terminates. -/
theorem cu_run_term : ∀ args σ, cuRunSpecJ.pre args σ → MTerm EquivLean.Modernize.Cbcus01c.Java.Gen.prog cuRunRef args σ :=
  TermVC.mterm (rank := fun _ => 0) (r := 1)
    (Contracts.valid_of_ok (by
      intro p hp
      simp only [cuRunCallees, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · exact cu_fmtRecordInitial_ok
      · exact cu_fmtRecord_ok))
    (Contracts.term_of_ok (by
      intro p hp
      simp only [cuRunCallees, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · exact cu_fmtRecordInitial_cterm
      · exact cu_fmtRecord_cterm) _ _)
    (TermVC.of_thin (SpecEnv.below_const _ _ (by decide)) cu_run_vc cu_run_thin)

/-- **CBCUS01C, Java side, total correctness.** -/
theorem cu_run_total : ∀ args σ, cuRunSpecJ.pre args σ →
    (∃ o, MExec EquivLean.Modernize.Cbcus01c.Java.Gen.prog cuRunRef args σ o) ∧ ∀ o, MExec EquivLean.Modernize.Cbcus01c.Java.Gen.prog cuRunRef args σ o → cuRunSpecJ.post args σ o :=
  total_of_sat_mterm cu_run_sat cu_run_term

end EquivLean.Modernize.JL

#print axioms EquivLean.Modernize.JL.cu_run_term
#print axioms EquivLean.Modernize.JL.cu_run_total
