-- Termination package by JimpleLean's session: TermPk/Cbact04c/JavaTermSeg196z.lean (sha256 60ca3c654d25b127...); only the module root renamed.
import EquivLean.Modernize.Cbact04c.JavaRunSeg196z
import EquivLean.Modernize.Cbact04c.JavaTermDefs

/-!
# CBACT04C → Java, termination: thin twins of `JavaRunSeg196z`

The statements and preambles of the originals; the cut assertions the variants (`runVs`),
calls by `callWPThin` (`callWPT` without the callee preconditions, which `MethodVC` checks).
-/

open Jimple EquivLean.Cobol.Rec
attribute [-jsimp] JLong.cmp_eq

namespace EquivLean.Modernize.Cbact04c.Java

set_option maxHeartbeats 0 in
set_option maxRecDepth 8000 in
set_option jimple.trace true in
theorem run_tseg196_zero (g : G) (σ0 : State) (fr : Frame) (σ : State) (cuts : Cuts) (B : Nat) (hB1 : 2147483648 < B) (hB2 : B < 8589934576)
    (hpre : RunPreG g g.args σ0) (h : J196 g g.args σ0 fr σ)
    (hc : ∀ i : I32, fr.get 22 = some (.int (i + 1#32)) →
      Model.dRate (discOf g (stSel g.xrefs (g.st i.toInt.toNat) (g.trec i.toInt.toNat))
        (g.trec i.toInt.toNat)) = 0)
    (c197 : cuts.lookup 197 = none) (c198 : cuts.lookup 198 = none)
    (cT : cuts.lookup 85 = some (fun fr' σ' => runVs B 85 g.args σ0 fr' σ' < runVs B 196 g.args σ0 fr σ)) :
    RunThinWPc g σ0 cuts 196 fr σ := by
  obtain ⟨i, hp, tcbV, acctV, xrefV, lastV, disV, ⟨hn, hi0, hlocs, f22, f6, f4, f5, htcb⟩, f3, f12,
    f14, f25, f16, f17, f7, hheap, hdis⟩ := h
  have hrate := hc i f22
  clear hc
  have hin := inFacts_of_pre hpre
  obtain ⟨et4, xs4, -, -, -, hv4⟩ := discArr_of_pre hpre (Hide.elim hheap).1.1
  clear hpre
  have hst := stInv_st hin i.toInt.toNat
  have hmemT : g.trec i.toInt.toNat ∈ g.tcat := by rw [trec_eq hn]; exact List.getElem_mem hn
  have hvt := hin.tcat_valid _ hmemT
  have hst2 := stInv_stSel hst hvt (hin.dom.2 _ hmemT).1
  have hl2 := stSel_lastId g.xrefs (g.st i.toInt.toNat) (g.trec i.toInt.toNat)
  have hvd := discOf_valid hv4 _ _ (disc_exists hin hst2 hmemT hl2)
  obtain ⟨dc, fsd, hdV, hdc, hrf, hr1, hr2⟩ := disRate_field (Hide.elim hdis) hvd
  subst hdV
  have hlenT : g.tcat.length < 2147483647 := by have := hin.dom.1; omega
  have hinit : Inits σ := (Hide.elim hheap).1.2.1
  obtain ⟨i1, i2, i3, i4, i5, i6, i7, i8⟩ := hinit
  have hlocs' := Hide.intro hlocs
  obtain ⟨f1, f36, f40, f8, f37, f10, f19, f20, f21, f41, f38, f26, f24⟩ := hlocs
  have hR : BitVec.ofInt 64 (Model.dRate (discOf g (stSel g.xrefs (g.st i.toInt.toNat)
      (g.trec i.toInt.toNat)) (g.trec i.toInt.toNat))) = 0#64 := by rw [hrate]; rfl
  have hstE : g.st (i.toInt.toNat + 1) = stSel g.xrefs (g.st i.toInt.toNat) (g.trec i.toInt.toNat) := by
    rw [st_succ_eq g hn, hrate]
    simp [stFin]
  have hstE' := Hide.intro hstE
  clear hstE
  have hrate' := Hide.intro hrate
  have hl2' := Hide.intro hl2
  clear hrate hst hst2 hin hvt hmemT hv4 hvd hl2 hr1 hr2
  generalize hRE : BitVec.ofInt 64 (Model.dRate (discOf g (stSel g.xrefs (g.st i.toInt.toNat)
    (g.trec i.toInt.toNat)) (g.trec i.toInt.toNat))) = R at hrf hR
  clear hRE
  unfold RunThinWPc
  jvc [runSpecG, runC, jlong_cmp_eq_zero_iff, runVs, upAt]
  all_goals first
    | exact ⟨Or.inl rfl, rfl⟩
    | skip

end EquivLean.Modernize.Cbact04c.Java
