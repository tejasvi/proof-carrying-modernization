-- Termination package by JimpleLean's session: TermPk/Cbact04c/JavaTermSeg102.lean (sha256 d7c6eb9fb8f38559...); only the module root renamed.
import EquivLean.Modernize.Cbact04c.JavaRunSeg102
import EquivLean.Modernize.Cbact04c.JavaTermDefs

/-!
# CBACT04C → Java, termination: thin twins of `JavaRunSeg102`

The statements and preambles of the originals; the cut assertions the variants (`runVs`),
calls by `callWPThin` (`callWPT` without the callee preconditions, which `MethodVC` checks).
-/

open Jimple EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbact04c.Java

set_option maxHeartbeats 0 in
set_option maxRecDepth 8000 in
set_option jimple.trace true in
theorem run_tseg102 (g : G) (σ0 : State) (fr : Frame) (σ : State) (cuts : Cuts) (B : Nat) (hB1 : 2147483648 < B) (hB2 : B < 8589934576) (hpre : RunPreG g g.args σ0)
    (h : J102 g g.args σ0 fr σ)
    (c103 : cuts.lookup 103 = none) (c104 : cuts.lookup 104 = none)
    (c105 : cuts.lookup 105 = none) (c106 : cuts.lookup 106 = none)
    (c107 : cuts.lookup 107 = none) (c108 : cuts.lookup 108 = some (fun fr' σ' => runVs B 108 g.args σ0 fr' σ' < runVs B 102 g.args σ0 fr σ)) :
    RunThinWPc g σ0 cuts 102 fr σ := by
  obtain ⟨i, hp, tcbV, acctV, xrefV, lastV, ⟨hn, hi0, hlocs, f22, f6, f4, f5, htcb⟩, hsome, hne, f3,
    f12, f14, f16, hheap⟩ := h
  have hst := stInv_st (inFacts_of_pre hpre) i.toInt.toNat
  clear hpre
  obtain ⟨id, hid⟩ := Option.isSome_iff_exists.1 hsome
  have hne' : id ≠ Model.tAcct (g.trec i.toInt.toNat) := fun h => hne (by rw [hid, h])
  obtain ⟨y, fs, hy, -, -⟩ := jrec_obj (Hide.elim htcb)
  subst hy
  -- the current account object: what statements 102–107 read and write
  obtain ⟨ac, fsa, hacc⟩ := acct_facts (Hide.elim hheap) (stInv_disp1 hst _) hid
  have hacc' := Hide.intro hacc
  obtain ⟨hacV, hac, hbal, ⟨w1, hw1⟩, ⟨w2, hw2⟩, h0⟩ := hacc
  subst hacV
  simp only [disp1] at hbal
  have hbr := aBal_range (acct_valid hst hid)
  have ht1 := hst.2.2.2.2.1
  have ht2 := hst.2.2.2.2.2.1
  have hinit : Inits σ := (Hide.elim hheap).1.2.1
  obtain ⟨i1, i2, i3, i4, i5, i6, i7, i8⟩ := hinit
  have hlocs' := Hide.intro hlocs
  obtain ⟨f1, f36, f40, f8, f37, f10, f19, f20, f21, f41, f38, f26, f24⟩ := hlocs
  generalize hbalE : BitVec.ofInt 64 (Model.aBal (g.st i.toInt.toNat).acct) = bal at hbal
  generalize hTE : BitVec.ofInt 64 (g.st i.toInt.toNat).total = T at f12
  have hbalE' := Hide.intro hbalE
  have hTE' := Hide.intro hTE
  have hid' := Hide.intro hid
  have hne'' := Hide.intro hne'
  have hrng := Hide.intro (And.intro hbr (And.intro ht1 ht2))
  clear hbalE hTE hst hid hsome hne hne' hbr ht1 ht2
  unfold RunThinWPc
  jvc [runSpecG, runC, truncSig, fields_get_set, narrow_long, runVs, upAt]
  all_goals first
    | exact ⟨Or.inl rfl, rfl⟩
    | skip

end EquivLean.Modernize.Cbact04c.Java
