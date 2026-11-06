-- Termination package by JimpleLean's session: TermPk/Cbact04c/Every/JavaTermSeg199.lean (sha256 aae73dbb3df04d53...); only the module root renamed.
import EquivLean.Modernize.Cbact04c.Every.JavaRunSeg199
import EquivLean.Modernize.Cbact04c.Every.JavaTermDefs

/-!
# CBACT04C → Java, termination: thin twins of `JavaRunSeg199`

The statements and preambles of the originals; the cut assertions the variants (`runVs`),
calls by `callWPThin` (`callWPT` without the callee preconditions, which `MethodVC` checks).
-/

open Jimple EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbact04c.Java

set_option maxHeartbeats 0 in
set_option maxRecDepth 8000 in
set_option jimple.trace true in
theorem run_tseg199 (g : G) (σ0 : State) (fr : Frame) (σ : State) (cuts : Cuts) (B : Nat) (hB1 : 2147483648 < B) (hB2 : B < 8589934576)
    (hpre : RunPreG g g.args σ0) (h : J199 g g.args σ0 fr σ)
    (c200 : cuts.lookup 200 = none) (c201 : cuts.lookup 201 = none) (c202 : cuts.lookup 202 = none)
    (c203 : cuts.lookup 203 = none) (c204 : cuts.lookup 204 = none) (c205 : cuts.lookup 205 = none)
    (c206 : cuts.lookup 206 = none) (c207 : cuts.lookup 207 = none) (c208 : cuts.lookup 208 = none)
    (c209 : cuts.lookup 209 = none) (c210 : cuts.lookup 210 = some (fun fr' σ' => runVs B 210 g.args σ0 fr' σ' < runVs B 199 g.args σ0 fr σ)) :
    RunThinWPc g σ0 cuts 199 fr σ := by
  obtain ⟨i, hp, tcbV, acctV, xrefV, lastV, disV, ⟨hn, hi0, hlocs, f22, f6, f4, f5, htcb, hstop⟩, f3, f12,
    f14, f25, f16, f17, f7, hheap, hdis, hrate⟩ := h
  have hin := inFacts_of_pre hpre
  obtain ⟨et4, xs4, -, -, -, hv4⟩ := discArr_of_pre hpre (Hide.elim hheap).1.1
  have hvt := trec_valid hpre hn
  clear hpre
  have hst := stInv_st hin i.toInt.toNat hstop
  have hmemT : g.trec i.toInt.toNat ∈ g.tcat := by rw [trec_eq hn]; exact List.getElem_mem hn
  have hst2 := stInv_stSel hst hvt
    (hex_of_found hin hstop (found_of_loopHeap (Hide.elim hheap)).1)
  have hl2 := stSel_lastId g.xrefs (g.st i.toInt.toNat) (g.trec i.toInt.toNat)
  have hd0 := jrecAt_ne_nil (Hide.elim hdis) (by decide)
  have hvd := discD_valid hv4 hd0
  obtain ⟨dc, fsd, hdV, hdc, hrf, hr1, hr2⟩ := disRate_field (Hide.elim hdis) hvd
  subst hdV
  obtain ⟨y, fs, hy, -, -⟩ := jrec_obj (Hide.elim htcb)
  subst hy
  obtain ⟨fsy, tyA, fiA, hyh, -, -, -, -, ht3, -, -, -, -, -, -, hb1, hb2, -, -⟩ :=
    tcb_facts (Hide.elim htcb) hvt
  -- the strings of `PARM-DATE` and the clock
  have hcore := (Hide.elim hheap).1
  obtain ⟨-, hinit, -, -, -, -, -, -, -, ⟨pa, hpaV, hpa⟩, -⟩ := hcore
  obtain ⟨i1, i2, i3, i4, i5, i6, i7, i8⟩ := hinit
  have hlocs' := Hide.intro hlocs
  obtain ⟨f1, f36, f40, f8, f37, f10, f19, f20, f21, f41, f38, f26, f24⟩ := hlocs
  rw [hpaV] at f26
  have hst2' := Hide.intro hst2
  have hrng := Hide.intro (And.intro (And.intro hb1 hb2) (And.intro hr1 hr2))
  clear hst hst2 hin hvt hmemT hv4 hvd hl2 hb1 hb2 hr1 hr2
  generalize hbE : BitVec.ofInt 64 (Model.tBal (g.trec i.toInt.toNat)) = tb at ht3
  generalize hRE : BitVec.ofInt 64 (Model.dRate (discD g (stSel g.xrefs (g.st i.toInt.toNat)
    (g.trec i.toInt.toNat)) (g.trec i.toInt.toNat))) = R at hrf
  generalize hTE : BitVec.ofInt 64 (stSel g.xrefs (g.st i.toInt.toNat) (g.trec i.toInt.toNat)).total = T
    at f12
  generalize hKE : BitVec.ofNat 64 (stSel g.xrefs (g.st i.toInt.toNat) (g.trec i.toInt.toNat)).k = K
    at f14
  have hbE' := Hide.intro hbE
  have hRE' := Hide.intro hRE
  have hTE' := Hide.intro hTE
  have hKE' := Hide.intro hKE
  clear hbE hRE hTE hKE
  unfold RunThinWPc
  jvc [runSpecG, runC, truncSig, fmtUSig, Grows, evalDynamic, concatRecipe, Native.valueOfArg, runVs, upAt]
  all_goals first
    | exact ⟨Or.inl rfl, rfl⟩
    | skip

end EquivLean.Modernize.Cbact04c.Java
