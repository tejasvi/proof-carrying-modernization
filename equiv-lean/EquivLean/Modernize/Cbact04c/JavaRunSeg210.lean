import EquivLean.Modernize.Cbact04c.JavaRunRes210

/-!
# CBACT04C → Java, `run`: statements 210–216 (id, type, category, source; the description's head)
-/

open Jimple EquivLean.Cobol.Rec


namespace EquivLean.Modernize.Cbact04c.Java

set_option maxHeartbeats 0 in
set_option maxRecDepth 8000 in
set_option jimple.trace true in
theorem run_seg210 (g : G) (σ0 : State) (fr : Frame) (σ : State) (cuts : Cuts)
    (hpre : RunPreG g g.args σ0) (h : J210 g g.args σ0 fr σ)
    (c211 : cuts.lookup 211 = none) (c212 : cuts.lookup 212 = none) (c213 : cuts.lookup 213 = none)
    (c214 : cuts.lookup 214 = none) (c215 : cuts.lookup 215 = none) (c216 : cuts.lookup 216 = none)
    (c217 : cuts.lookup 217 = some (J217 g g.args σ0)) :
    RunWPc g σ0 cuts 210 fr σ := by
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
  unfold RunWPc
  jvc [runSpecG, runC, fmtUSig, Grows, evalDynamic, concatRecipe, Native.valueOfArg, fields_get_set,
    narrow_cls, narrow_long]
  -- the cut point 217
  have hTlt : hp.T < σ.next := State.lt_next_of_heap (Hide.elim hT')
  apply j217_of' hn hi0
  all_goals (try (first | exact htcb | exact hheap | exact hrate | exact htid | exact Hide.elim hT'))
  case hlocs => locs_tac
  case f22 => frame_simp [f22]
  case f6 => frame_simp [f6]
  case f4 => frame_simp [f4]
  case f5 => frame_simp [f5]
  case f3 => frame_simp [f3]
  case f11 => frame_simp [f11]
  case f12 => frame_simp [f12]
  case f14 => frame_simp [f14]
  case f25 => frame_simp [f25]
  case f16 => frame_simp [f16]
  case f17 => frame_simp [f17]
  case f27 => frame_simp []
  case hle => assumption
  case hR => assumption
  case hi2 => assumption
  case hHo =>
    intro x hx hxT
    simp [hxT, Nat.ne_of_lt hx, Nat.ne_of_lt (Nat.lt_succ_of_lt hx)]
  case hHT => simp
  case hH0 => simp [Nat.ne_of_gt hTlt]
  case hHs =>
    simp [Nat.ne_of_gt (Nat.lt_succ_of_lt hTlt)]
    try decide
  case hHEAD =>
    have hr := Hide.elim hidr'
    have hb : (Model.numOf ((stSel g.xrefs (g.st i.toInt.toNat) (g.trec i.toInt.toNat)).acct[0]?.getD
        (Cobol.Rec.FVal.num 0))).bmod 18446744073709551616 =
        Model.aId (sel g i.toInt.toNat).acct := by
      have hd : (default : Cobol.Rec.FVal) = Cobol.Rec.FVal.num 0 := rfl
      simp only [Model.aId, sel, List.getD_eq_getElem?_getD, hd] at hr ⊢
      rw [Int.bmod_def]
      split <;> omega
    rw [hb]
    rfl

end EquivLean.Modernize.Cbact04c.Java
