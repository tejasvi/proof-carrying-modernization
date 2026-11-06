import EquivLean.Modernize.Cbact04c.JavaRunRes97

/-!
# CBACT04C → Java, `run`: statements 97–107, case the same account as the previous record
-/

open Jimple EquivLean.Cobol.Rec


namespace EquivLean.Modernize.Cbact04c.Java

set_option maxHeartbeats 0 in
set_option maxRecDepth 8000 in
set_option jimple.trace true in
theorem run_seg97_same (g : G) (σ0 : State) (fr : Frame) (σ : State) (cuts : Cuts) (hpre : RunPreG g g.args σ0)
    (h : J97 g g.args σ0 fr σ)
    (hc : ∀ i : I32, fr.get 22 = some (.int (i + 1#32)) → (g.st i.toInt.toNat).lastId = some (Model.tAcct (g.trec i.toInt.toNat)))
    (c98 : cuts.lookup 98 = none) (c99 : cuts.lookup 99 = none) (c100 : cuts.lookup 100 = none)
    (c101 : cuts.lookup 101 = none) (c172 : cuts.lookup 172 = some (J172 g g.args σ0)) :
    RunWPc g σ0 cuts 97 fr σ := by
  obtain ⟨i, hp, tcbV, acctV, xrefV, lastV, ⟨hn, hi0, hlocs, f22, f6, f4, f5, htcb⟩, f12, f3, f14,
    f25, f16, f17, hheap⟩ := h
  have hl := hc i f22
  clear hc
  have hvt := trec_valid hpre hn
  have hst := stInv_st (inFacts_of_pre hpre) i.toInt.toNat
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
  obtain ⟨la, hlaV, hla⟩ := (Hide.elim hheap).2.2.2.1
  subst hlaV
  have hinit : Inits σ := (Hide.elim hheap).1.2.1
  obtain ⟨i1, i2, i3, i4, i5, i6, i7, i8⟩ := hinit
  have f3o := Hide.intro f3
  simp only [disp1, hl, lastText] at hla
  rw [← hta] at hla
  simp only [hl, Option.isSome_some, ↓reduceIte] at f3
  clear hta hr0 hr1 hvt hst
  generalize BitVec.ofInt 64 (Model.tAcct (g.trec i.toInt.toNat)) = a at ht0 ba hla
  unfold RunWPc
  jvc [runSpecG, runC, fmtUSig, truncSig, Grows]
  first
    | exact j172_of_same hn hi0 (Hide.elim hlocs') f22 f6 f4 f5 f12 (Hide.elim f3o) f14 f25 f16 f17 htcb hheap hl
        ⟨‹_›, ‹_›⟩ ‹_›
    | skip

end EquivLean.Modernize.Cbact04c.Java
