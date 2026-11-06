-- Termination package by JimpleLean's session: TermPk/Cbact04c/JavaTermSeg97p.lean (sha256 b5c8596280092ed0...); only the module root renamed.
import EquivLean.Modernize.Cbact04c.JavaRunSeg97p
import EquivLean.Modernize.Cbact04c.JavaTermDefs

/-!
# CBACT04C → Java, termination: thin twins of `JavaRunSeg97p`

The statements and preambles of the originals; the cut assertions the variants (`runVs`),
calls by `callWPThin` (`callWPT` without the callee preconditions, which `MethodVC` checks).
-/

open Jimple EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbact04c.Java

set_option maxHeartbeats 0 in
set_option maxRecDepth 8000 in
set_option jimple.trace true in
theorem run_tseg97_post (g : G) (σ0 : State) (fr : Frame) (σ : State) (cuts : Cuts) (B : Nat) (hB1 : 2147483648 < B) (hB2 : B < 8589934576) (hpre : RunPreG g g.args σ0)
    (h : J97 g g.args σ0 fr σ)
    (hc : ∀ i : I32, fr.get 22 = some (.int (i + 1#32)) → (g.st i.toInt.toNat).lastId.isSome ∧
      (g.st i.toInt.toNat).lastId ≠ some (Model.tAcct (g.trec i.toInt.toNat)))
    (c98 : cuts.lookup 98 = none) (c99 : cuts.lookup 99 = none) (c100 : cuts.lookup 100 = none)
    (c101 : cuts.lookup 101 = none) (c102 : cuts.lookup 102 = some (fun fr' σ' => runVs B 102 g.args σ0 fr' σ' < runVs B 97 g.args σ0 fr σ))
    (c172 : cuts.lookup 172 = some (fun fr' σ' => runVs B 172 g.args σ0 fr' σ' < runVs B 97 g.args σ0 fr σ)) (c124 : cuts.lookup 124 = none) :
    RunThinWPc g σ0 cuts 97 fr σ := by
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
  obtain ⟨id, hid⟩ := Option.isSome_iff_exists.1 hl.1
  have hne : id ≠ Model.tAcct (g.trec i.toInt.toNat) := fun h => hl.2 (by rw [hid, h])
  obtain ⟨-, -, -, hid0, hid1⟩ := hst.2.2.2.1 id hid
  simp only [disp1, hid, lastText] at hla
  simp only [hid, Option.isSome_some, ↓reduceIte] at f3
  have hne1 : ∀ n, zpadJ id.natAbs 11 ≠
      zpadJ (BitVec.ofInt 64 (Model.tAcct (g.trec i.toInt.toNat))).toInt.natAbs n := by
    rw [hta]
    exact zpadJ_ne_of_ne (by simp only [Nat.reducePow]; omega) (by simp only [Nat.reducePow]; omega)
      (by omega)
  have hne2 : ∀ n, zpadJ (BitVec.ofInt 64 (Model.tAcct (g.trec i.toInt.toNat))).toInt.natAbs n ≠
      zpadJ id.natAbs 11 := fun n h => hne1 n h.symm
  have hl' := Hide.intro hl
  clear hta hr0 hr1 hvt hst hl hid hne hid0 hid1
  generalize BitVec.ofInt 64 (Model.tAcct (g.trec i.toInt.toNat)) = a at ht0 ba hne1 hne2
  unfold RunThinWPc
  jvc [runSpecG, runC, fmtUSig, Grows, runVs, upAt]
  all_goals first
    | exact ⟨Or.inl rfl, rfl⟩
    | skip

end EquivLean.Modernize.Cbact04c.Java
