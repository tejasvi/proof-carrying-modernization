-- Copied from JimpleLean (frozen snapshot ~/jimplelean_work/snapshots/JimpleLean-20261025T2312Z,
-- Examples/CardDemo/Cbact02cTermRun.lean); proved by JimpleLean's own session.  Only the imports, the
-- program (`CB`, the same Jimple files, is equiv-lean's generated
-- `EquivLean.Modernize.Cbact02c.Java.Gen`) and the namespace differ (tools/modernize/import_jl.py).
/-
  Examples/CardDemo/Cbact02cTermRun.lean

  Termination of CBACT02C's `run` (the read loop) and its total correctness: the correctness
  invariant of the loop head with the variant `runVar`, the entry segment and the three cases at the
  loop head checked one lemma each, as for `run_vc`.
-/
import EquivLean.Modernize.JL.Cbact02cTermHelpers

open Jimple

namespace EquivLean.Modernize.JL

/-! ### `run`: the read loop -/

/-- Twice the records left, plus one until the end-of-file flag `z` is set: the read path takes a
    record (−2), the end-of-file path sets the flag (−1). -/
def runVar (_ : List Value) (_ : State) (fr : Frame) (_ : State) : Nat :=
  match fr.get 7, fr.get 8, fr.get 15 with
  | some (.int i), some (.int n), some (.int z) => 2 * (n.toInt - i.toInt).toNat + (if z = 0 then 1 else 0)
  | _, _, _ => 0

def runTerm : TermCuts := runInv.withVariant runVar

/-- The termination paths of `run` from statement `pc`, cut assertions `I`. -/
def runTWP (I : Cuts) (pc : Nat) (fr : Frame) (σ : State) : Prop :=
  bodyWP EquivLean.Modernize.Cbact02c.Java.Gen.prog (callWPT EquivLean.Modernize.Cbact02c.Java.Gen.prog (runCallees.env.below (fun _ => 0) 1) 1)
    EquivLean.Modernize.Cbact02c.Java.Gen.Cbact02c.«run(Cbact02c$CardRecord[])» I (fun _ => True) 200 pc fr σ

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem run_tentry (args : List Value) (σ0 : State) (hpre : runSpecJ.pre args σ0) :
    runTWP (runTerm.inv args σ0) 0 (Frame.init true args) σ0 := by
  jvc [ite_nat_ne, runTWP, runTerm, runVar, runSpecJ, runInv, runInv32, RunAt, runCallees, formatCardSig,
    spacesSig, startText, endText, textN, textY, cardLines, recLineV, Grows, CardOk, StrField, LongField, StrOk,
    cardLine, fieldOf, fieldLong, argText, cardCls, formatCardSpec, spacesSpec]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem run_tloop_read (args : List Value) (σ0 : State) (hpre : runSpecJ.pre args σ0)
    (fr : Frame) (σ : State) (a : Addr) (et : JType) (xs : List Value) (ha : args = [.ref a])
    (harr : σ0.heap a = some (.array et xs)) (res : Addr) (fs : List (FieldKey × Value)) (l : Addr)
    (ys : List Value) (m : Nat) (i n : I32) (r5 : Addr) (z : I32)
    (h : RunAt σ0 fr σ a xs res fs l ys m i n r5 z) (hz : z = 0) (hi : i.toInt < n.toInt) :
    runTWP (runTerm.dec args σ0 (runVar args σ0 fr σ)) 32 fr σ := by
  jvc [ite_nat_ne, runTWP, runTerm, runVar, runSpecJ, runInv, runInv32, RunAt, runCallees, formatCardSig,
    spacesSig, startText, endText, textN, textY, cardLines, recLineV, Grows, CardOk, StrField, LongField, StrOk,
    cardLine, fieldOf, fieldLong, argText, cardCls, formatCardSpec, spacesSpec]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem run_tloop_eof (args : List Value) (σ0 : State) (hpre : runSpecJ.pre args σ0)
    (fr : Frame) (σ : State) (a : Addr) (et : JType) (xs : List Value) (ha : args = [.ref a])
    (harr : σ0.heap a = some (.array et xs)) (res : Addr) (fs : List (FieldKey × Value)) (l : Addr)
    (ys : List Value) (m : Nat) (i n : I32) (r5 : Addr) (z : I32)
    (h : RunAt σ0 fr σ a xs res fs l ys m i n r5 z) (hz : z = 0) (hi : n.toInt ≤ i.toInt) :
    runTWP (runTerm.dec args σ0 (runVar args σ0 fr σ)) 32 fr σ := by
  jvc [ite_nat_ne, runTWP, runTerm, runVar, runSpecJ, runInv, runInv32, RunAt, runCallees, formatCardSig,
    spacesSig, startText, endText, textN, textY, cardLines, recLineV, Grows, CardOk, StrField, LongField, StrOk,
    cardLine, fieldOf, fieldLong, argText, cardCls, formatCardSpec, spacesSpec]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem run_tloop_exit (args : List Value) (σ0 : State) (hpre : runSpecJ.pre args σ0)
    (fr : Frame) (σ : State) (a : Addr) (et : JType) (xs : List Value) (ha : args = [.ref a])
    (harr : σ0.heap a = some (.array et xs)) (res : Addr) (fs : List (FieldKey × Value)) (l : Addr)
    (ys : List Value) (m : Nat) (i n : I32) (r5 : Addr) (z : I32)
    (h : RunAt σ0 fr σ a xs res fs l ys m i n r5 z) (hz : z ≠ 0) :
    runTWP (runTerm.dec args σ0 (runVar args σ0 fr σ)) 32 fr σ := by
  jvc [ite_nat_ne, runTWP, runTerm, runVar, runSpecJ, runInv, runInv32, RunAt, runCallees, formatCardSig,
    spacesSig, startText, endText, textN, textY, cardLines, recLineV, Grows, CardOk, StrField, LongField, StrOk,
    cardLine, fieldOf, fieldLong, argText, cardCls, formatCardSpec, spacesSpec]

theorem run_tvc : TermVC EquivLean.Modernize.Cbact02c.Java.Gen.prog runCallees.env (fun _ => 0) 1 1 runRef runSpecJ runTerm 200 := by
  refine ⟨_, rfl, fun args σ0 hpre => ⟨?_, ?_⟩⟩
  · show runTWP (runTerm.inv args σ0) 0 (Frame.init true args) σ0
    exact run_tentry args σ0 hpre
  · intro p hp fr σ hI
    simp only [runTerm, runInv, Invariants.withVariant, List.map_cons, List.map_nil, List.mem_cons,
      List.not_mem_nil, or_false] at hp
    subst hp
    show runTWP (runTerm.dec args σ0 (runVar args σ0 fr σ)) 32 fr σ
    have hpre' := hpre
    obtain ⟨a, et, xs, ha, harr, -⟩ := hpre'
    obtain ⟨res, fs, l, ys, m, i, n, r5, z, h⟩ := hI a et xs ha harr
    by_cases hz : z = 0
    · rcases Int.lt_or_le i.toInt n.toInt with hi | hi
      · exact run_tloop_read args σ0 hpre fr σ a et xs ha harr res fs l ys m i n r5 z h hz hi
      · exact run_tloop_eof args σ0 hpre fr σ a et xs ha harr res fs l ys m i n r5 z h hz hi
    · exact run_tloop_exit args σ0 hpre fr σ a et xs ha harr res fs l ys m i n r5 z h hz

/-- **CBACT02C, Java side, termination**: every call of `run` on an array of records as
    `formatCard` reads them terminates. With `run_sat`, `run` is totally correct
    (`total_of_sat_mterm`). -/
theorem run_term : ∀ args σ, runSpecJ.pre args σ → MTerm EquivLean.Modernize.Cbact02c.Java.Gen.prog runRef args σ :=
  TermVC.mterm (Contracts.valid_of_ok (by
      intro p hp
      simp only [runCallees, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · exact formatCard_ok
      · exact spaces_ok))
    (Contracts.term_of_ok (by
      intro p hp
      simp only [runCallees, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · exact formatCard_cterm
      · exact spaces_cterm) _ _) run_tvc

/-- **CBACT02C, Java side, total correctness.** -/
theorem run_total : ∀ args σ, runSpecJ.pre args σ →
    (∃ o, MExec EquivLean.Modernize.Cbact02c.Java.Gen.prog runRef args σ o) ∧ ∀ o, MExec EquivLean.Modernize.Cbact02c.Java.Gen.prog runRef args σ o → runSpecJ.post args σ o :=
  total_of_sat_mterm run_sat run_term

end EquivLean.Modernize.JL

#print axioms EquivLean.Modernize.JL.run_term
#print axioms EquivLean.Modernize.JL.run_total
