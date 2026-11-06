import EquivLean.Modernize.Cbact04c.JavaRunRes89

/-!
# CBACT04C → Java, `run`: record `i` displayed (statements 90–96), callee contracts of `CallSpecs`
-/

open Jimple EquivLean.Cobol.Rec


namespace EquivLean.Modernize.Cbact04c.Java

set_option maxHeartbeats 0 in
set_option maxRecDepth 8000 in
set_option jimple.trace true in
theorem run_seg90 (g : G) (σ0 : State) (fr : Frame) (σ : State) (cuts : Cuts) (hpre : RunPreG g g.args σ0)
    (h : J89 g g.args σ0 fr σ)
    (c93 : cuts.lookup 93 = none) (c94 : cuts.lookup 94 = none) (c95 : cuts.lookup 95 = none)
    (c96 : cuts.lookup 96 = none) (c97 : cuts.lookup 97 = some (J97 g g.args σ0)) :
    RunWPc g σ0 cuts 90 fr σ := by
  obtain ⟨i, hp, tcbV, acctV, xrefV, lastV, ⟨hn, hi0, hlocs, f22, f6, f4, f5, htcb⟩, f12, f3, f14,
    f25, f16, f17, hheap⟩ := h
  have hvt := Hide.intro (trec_valid hpre hn)
  clear hpre
  obtain ⟨y, fs, hy, -, -⟩ := jrec_obj (Hide.elim htcb)
  subst hy
  have hlocs' := Hide.intro hlocs
  obtain ⟨f1, f36, f40, f8, f37, f10, f19, f20, f21, f41, f38, f26, f24⟩ := hlocs
  -- what `displayTcb` reads, the field values as opaque variables
  obtain ⟨fsy, tyA, fiA, hyh, ht0, ht1, htyA, ht2, ht3, ht4, hfiA, hr0, hr1, hr2, hr3, hr4, hr5,
    -, -⟩ := tcb_facts (Hide.elim htcb) (Hide.elim hvt)
  have ba : -9223372036854775808 < (BitVec.ofInt 64 (Model.tAcct (g.trec i.toInt.toNat))).toInt := by
    rw [toInt_ofInt64 (by omega) (by omega)]; omega
  have bc : -9223372036854775808 < (BitVec.ofInt 64 (Model.tCat (g.trec i.toInt.toNat))).toInt := by
    rw [toInt_ofInt64 (by omega) (by omega)]; omega
  have bb : -9223372036854775808 < (BitVec.ofInt 64 (Model.tBal (g.trec i.toInt.toNat))).toInt := by
    rw [toInt_ofInt64 (by omega) (by omega)]; omega
  clear hr0 hr1 hr2 hr3 hr4 hr5
  generalize BitVec.ofInt 64 (Model.tAcct (g.trec i.toInt.toNat)) = a at ht0 ba
  generalize BitVec.ofInt 64 (Model.tCat (g.trec i.toInt.toNat)) = c at ht2 bc
  generalize BitVec.ofInt 64 (Model.tBal (g.trec i.toInt.toNat)) = b at ht3 bb
  generalize cp037Str (Model.tType (g.trec i.toInt.toNat)) = ty at htyA
  generalize cp037Str (tFill (g.trec i.toInt.toNat)) = fl at hfiA
  -- the display list and the `Result`
  have hres : ResAt σ hp := (Hide.elim hheap).1.2.2.2.1
  have hdisp : DispAt σ hp.ld (g.st i.toInt.toNat).disp := (Hide.elim hheap).1.2.2.2.2.1
  have hinit : Inits σ := (Hide.elim hheap).1.2.1
  obtain ⟨fsR, hR, hRd, hRw, hRr, hRa⟩ := hres
  obtain ⟨dxs, dm, hld, -⟩ := hdisp
  obtain ⟨i1, i2, i3, i4, i5, i6, i7, i8⟩ := hinit
  unfold RunWPc
  jvc [runSpecG, runC, displayTcbSig, Grows]
  -- the cut point 97: `displayTcb`'s line added to the display list
  first
    | exact j97_of_disp hn hi0 (Hide.elim hlocs') f22 f6 f4 f5 f12 f3 f14 f25 f16 f17 htcb hvt hheap
        hld ⟨‹_›, ‹_›⟩ ‹_› ‹_›
    | skip

end EquivLean.Modernize.Cbact04c.Java
