-- Termination package by JimpleLean's session: TermPk/Cbact04c/JavaTermSeg210.lean (sha256 77d8c5b8d3a9729c...); only the module root renamed.
import EquivLean.Modernize.Cbact04c.JavaRunSeg210
import EquivLean.Modernize.Cbact04c.JavaTermDefs

/-!
# CBACT04C → Java, termination: thin twins of `JavaRunSeg210`

The statements and preambles of the originals; the cut assertions the variants (`runVs`),
calls by `callWPThin` (`callWPT` without the callee preconditions, which `MethodVC` checks).
-/

open Jimple EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbact04c.Java

set_option maxHeartbeats 0 in
set_option maxRecDepth 8000 in
set_option jimple.trace true in
theorem run_tseg210 (g : G) (σ0 : State) (fr : Frame) (σ : State) (cuts : Cuts) (B : Nat) (hB1 : 2147483648 < B) (hB2 : B < 8589934576)
    (hpre : RunPreG g g.args σ0) (h : J210 g g.args σ0 fr σ)
    (c211 : cuts.lookup 211 = none) (c212 : cuts.lookup 212 = none) (c213 : cuts.lookup 213 = none)
    (c214 : cuts.lookup 214 = none) (c215 : cuts.lookup 215 = none) (c216 : cuts.lookup 216 = none)
    (c217 : cuts.lookup 217 = some (fun fr' σ' => runVs B 217 g.args σ0 fr' σ' < runVs B 210 g.args σ0 fr σ)) :
    RunThinWPc g σ0 cuts 210 fr σ := by
  obtain ⟨i, hp, tcbV, acctV, xrefV, lastV, tidV, ⟨⟨hn, hi0, hlocs, f22, f6, f4, f5, htcb⟩, f3, f11,
    f12, f14, f25, f16, f17, hheap, hrate⟩, f27, htid⟩ := h
  have hin := inFacts_of_pre hpre
  have hvt := trec_valid hpre hn
  clear hpre
  have hst := stInv_st hin i.toInt.toNat
  have hmemT : g.trec i.toInt.toNat ∈ g.tcat := by rw [trec_eq hn]; exact List.getElem_mem hn
  have hst2 := stInv_stSel hst hvt (hin.dom.2 _ hmemT).1
  have hl2 := stSel_lastId g.xrefs (g.st i.toInt.toNat) (g.trec i.toInt.toNat)
  -- the transaction object
  simp only [sel] at hheap hrate f11 f12 f14 htid
  have hL := Hide.elim hheap
  obtain ⟨⟨-, hinit, -, -, -, -, -, -, ⟨fsT, hT, hTk, -⟩, -⟩, hacc, -⟩ := id hL
  obtain ⟨i1, i2, i3, i4, i5, i6, i7, i8⟩ := hinit
  obtain ⟨w0, hw0⟩ := hTk "tranId" (by decide)
  obtain ⟨w1, hw1⟩ := hTk "tranTypeCd" (by decide)
  obtain ⟨w2, hw2⟩ := hTk "tranCatCd" (by decide)
  obtain ⟨w3, hw3⟩ := hTk "tranSource" (by decide)
  -- the account object's id
  have hsome : (stSel g.xrefs (g.st i.toInt.toNat) (g.trec i.toInt.toNat)).lastId.isSome := by
    rw [hl2]; rfl
  have hva := acct_valid hst2 hl2
  obtain ⟨ac, fsa, hacV, hac, hfa⟩ := jrec_obj (hacc hsome)
  have hid := jfield_num hfa hva (i := 0) (by decide) (fmt := {digits := 11}) (by decide)
  rw [show (AccountRecord.fields.getD 0 default).jname = "acctId" from rfl] at hid
  have hidr := aId_range hva
  subst hacV
  have hida : -9223372036854775808 < (BitVec.ofInt 64 (Model.numOf
      ((stSel g.xrefs (g.st i.toInt.toNat) (g.trec i.toInt.toNat)).acct.getD 0 default))).toInt := by
    rw [toInt_ofInt64 (by simp only [Model.aId] at hidr; omega) (by simp only [Model.aId] at hidr; omega)]
    simp only [Model.aId] at hidr; omega
  have hlocs' := Hide.intro hlocs
  obtain ⟨f1, f36, f40, f8, f37, f10, f19, f20, f21, f41, f38, f26, f24⟩ := hlocs
  have hst2' := Hide.intro hst2
  have hTk' := Hide.intro hTk
  have hT' := Hide.intro hT
  have hidr' := Hide.intro hidr
  clear hst hst2 hin hvt hmemT hl2 hsome hva hfa hacc hidr hTk
  unfold RunThinWPc
  jvc [runSpecG, runC, fmtUSig, Grows, evalDynamic, concatRecipe, Native.valueOfArg, fields_get_set,
    narrow_cls, narrow_long, runVs, upAt]
  all_goals first
    | exact ⟨Or.inl rfl, rfl⟩
    | skip

end EquivLean.Modernize.Cbact04c.Java
