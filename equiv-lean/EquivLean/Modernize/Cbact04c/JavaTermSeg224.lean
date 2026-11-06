-- Termination package by JimpleLean's session: TermPk/Cbact04c/JavaTermSeg224.lean (sha256 f27b6f5aa8fa11f2...); only the module root renamed.
import EquivLean.Modernize.Cbact04c.JavaRunSeg224
import EquivLean.Modernize.Cbact04c.JavaTermDefs

/-!
# CBACT04C → Java, termination: thin twins of `JavaRunSeg224`

The statements and preambles of the originals; the cut assertions the variants (`runVs`),
calls by `callWPThin` (`callWPT` without the callee preconditions, which `MethodVC` checks).
-/

open Jimple EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbact04c.Java

set_option maxHeartbeats 0 in
set_option maxRecDepth 8000 in
theorem run_tseg224 (g : G) (σ0 : State) (fr : Frame) (σ : State) (cuts : Cuts) (B : Nat) (hB1 : 2147483648 < B) (hB2 : B < 8589934576)
    (hpre : RunPreG g g.args σ0) (h : J224 g g.args σ0 fr σ)
    (c225 : cuts.lookup 225 = none) (c226 : cuts.lookup 226 = none) (c227 : cuts.lookup 227 = none)
    (c228 : cuts.lookup 228 = none) (c229 : cuts.lookup 229 = none) (c230 : cuts.lookup 230 = none)
    (c231 : cuts.lookup 231 = none) (c232 : cuts.lookup 232 = some (fun fr' σ' => runVs B 232 g.args σ0 fr' σ' < runVs B 224 g.args σ0 fr σ)) :
    RunThinWPc g σ0 cuts 224 fr σ := by
  obtain ⟨i, hp, tcbV, acctV, xrefV, lastV, ⟨⟨hn, hi0, hlocs, f22, f6, f4, f5, htcb⟩, f3, f11,
    f12, f14, f25, f16, f17, hheap, hrate⟩, hset⟩ := h
  have hin := inFacts_of_pre hpre
  have hvt := trec_valid hpre hn
  have hxv := xrefs_valid_of_pre hpre
  clear hpre
  have hst := stInv_st hin i.toInt.toNat
  have hmemT : g.trec i.toInt.toNat ∈ g.tcat := by rw [trec_eq hn]; exact List.getElem_mem hn
  have hst2 := stInv_stSel hst hvt (hin.dom.2 _ hmemT).1
  have hl2 := stSel_lastId g.xrefs (g.st i.toInt.toNat) (g.trec i.toInt.toNat)
  simp only [sel] at hheap hrate f11 f12 f14 hset
  -- the transaction object
  obtain ⟨fsT, hT, hset7⟩ := Hide.elim hset
  have htr : TranOk σ hp.T := by
    obtain ⟨-, -, -, -, -, -, -, -, htr, -⟩ := (Hide.elim hheap).1
    exact htr
  obtain ⟨fs0, hT0, hTk, -, -⟩ := id htr
  rw [hT] at hT0
  cases hT0
  obtain ⟨w7, hw7⟩ := hTk "tranMerchantName" (by decide)
  obtain ⟨w8, hw8⟩ := hTk "tranMerchantCity" (by decide)
  obtain ⟨w9, hw9⟩ := hTk "tranMerchantZip" (by decide)
  obtain ⟨w10, hw10⟩ := hTk "tranCardNum" (by decide)
  -- the cross-reference object's card number
  have hsome : (stSel g.xrefs (g.st i.toInt.toNat) (g.trec i.toInt.toNat)).lastId.isSome := by
    rw [hl2]; rfl
  have hxr := (Hide.elim hheap).2.2.1 hsome
  have hvx : CardXrefRecord.Valid (stSel g.xrefs (g.st i.toInt.toNat) (g.trec i.toInt.toNat)).xref := by
    obtain ⟨-, -, -, hcur, -⟩ := hst2
    obtain ⟨-, hxx, -, -, -⟩ := hcur _ hl2
    rw [hxx]
    exact findXref_valid hxv (hin.dom.2 _ hmemT).2.1
  obtain ⟨xc, fsx, hxV, hxh, hfx⟩ := jrec_obj hxr
  obtain ⟨cs, hcs, hcss⟩ := jfield_str hfx hvx (i := 0) (by decide) (j := false) (by decide)
  rw [show (CardXrefRecord.fields.getD 0 default).jname = "xrefCardNum" from rfl] at hcs
  subst hxV
  have hinit : Inits σ := (Hide.elim hheap).1.2.1
  obtain ⟨i1, i2, i3, i4, i5, i6, i7, i8⟩ := hinit
  have hxT : xc ≠ hp.T := by intro e; rw [e, hT] at hxh; simp at hxh
  have hlocs' := Hide.intro hlocs
  obtain ⟨f1, f36, f40, f8, f37, f10, f19, f20, f21, f41, f38, f26, f24⟩ := hlocs
  have hT' := Hide.intro hT
  have hset7' := Hide.intro hset7
  have htr' := Hide.intro htr
  have hcss' := Hide.intro hcss
  clear hset7 htr hTk hset hst hst2 hin hvt hmemT hl2 hsome hxr hvx hfx hxv
  unfold RunThinWPc
  jvc [runSpecG, runC, spacesSig, Grows, fields_get_set, narrow_cls, narrow_long, runVs, upAt]
  all_goals first
    | exact ⟨Or.inl rfl, rfl⟩
    | skip

end EquivLean.Modernize.Cbact04c.Java
