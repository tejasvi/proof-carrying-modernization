-- Termination package by JimpleLean's session: TermPk/Cbact04c/Every/JavaTermSeg125.lean (sha256 6850c57a0d0bae3b...); only the module root renamed.
import EquivLean.Modernize.Cbact04c.Every.JavaRunSeg125
import EquivLean.Modernize.Cbact04c.Every.JavaTermDefs

/-!
# CBACT04C → Java, termination: thin twins of `JavaRunSeg125`

The statements and preambles of the originals; the cut assertions the variants (`runVs`),
calls by `callWPThin` (`callWPT` without the callee preconditions, which `MethodVC` checks).
-/

open Jimple EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbact04c.Java

set_option maxHeartbeats 0 in
set_option maxRecDepth 8000 in
set_option jimple.trace true in
theorem run_tseg125 (g : G) (σ0 : State) (fr : Frame) (σ : State) (cuts : Cuts) (B : Nat) (hB1 : 2147483648 < B) (hB2 : B < 8589934576)
    (hpre : RunPreG g g.args σ0) (h : J125 g g.args σ0 fr σ)
    (c126 : cuts.lookup 126 = none) (c127 : cuts.lookup 127 = none) (c128 : cuts.lookup 128 = none)
    (c129 : cuts.lookup 129 = some (fun fr' σ' => runVs B 129 g.args σ0 fr' σ' < runVs B 125 g.args σ0 fr σ)) : RunThinWPc g σ0 cuts 125 fr σ := by
  obtain ⟨i, hp, tcbV, ⟨hn, hi0, hlocs, f22, f6, f4, f5, htcb, hstop⟩, hne, f3, f14, hcore⟩ := h
  have hvt := trec_valid hpre hn
  clear hpre
  obtain ⟨y, fs, hy, -, -⟩ := jrec_obj (Hide.elim htcb)
  subst hy
  have hlocs' := Hide.intro hlocs
  obtain ⟨f1, f36, f40, f8, f37, f10, f19, f20, f21, f41, f38, f26, f24⟩ := hlocs
  obtain ⟨fsy, tyA, fiA, hyh, ht0, -, -, -, -, -, -, hr0, hr1, -, -, -, -, -, -⟩ :=
    tcb_facts (Hide.elim htcb) hvt
  have hta := toInt_ofInt64 (v := Model.tAcct (g.trec i.toInt.toNat)) (by omega) (by omega)
  have ba : -9223372036854775808 < (BitVec.ofInt 64 (Model.tAcct (g.trec i.toInt.toNat))).toInt := by
    rw [hta]; omega
  have hinit : Inits σ := (Hide.elim hcore).2.1
  obtain ⟨i1, i2, i3, i4, i5, i6, i7, i8⟩ := hinit
  have hta' := Hide.intro hta
  clear hvt hr0 hr1 hta
  generalize haE : BitVec.ofInt 64 (Model.tAcct (g.trec i.toInt.toNat)) = a at ht0 ba
  have haE' := Hide.intro haE
  clear haE
  have hneH := Hide.intro hne
  clear hne
  unfold RunThinWPc
  jvc [runSpecG, runC, fmtUSig, Grows, runVs, upAt]
  all_goals first
    | exact ⟨Or.inl rfl, rfl⟩
    | skip

end EquivLean.Modernize.Cbact04c.Java
