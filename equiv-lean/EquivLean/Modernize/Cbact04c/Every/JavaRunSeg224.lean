import EquivLean.Modernize.Cbact04c.Every.JavaRunRes224

/-!
# CBACT04C → Java, `run`: statements 224–231 (merchant name, city, zip; card number)
-/

open Jimple EquivLean.Cobol.Rec


namespace EquivLean.Modernize.Cbact04c.Java

set_option maxHeartbeats 0 in
set_option maxRecDepth 8000 in
theorem run_seg224 (g : G) (σ0 : State) (fr : Frame) (σ : State) (cuts : Cuts)
    (hpre : RunPreG g g.args σ0) (h : J224 g g.args σ0 fr σ)
    (c225 : cuts.lookup 225 = none) (c226 : cuts.lookup 226 = none) (c227 : cuts.lookup 227 = none)
    (c228 : cuts.lookup 228 = none) (c229 : cuts.lookup 229 = none) (c230 : cuts.lookup 230 = none)
    (c231 : cuts.lookup 231 = none) (c232 : cuts.lookup 232 = some (J232 g g.args σ0)) :
    RunWPc g σ0 cuts 224 fr σ := by
  obtain ⟨i, hp, tcbV, acctV, xrefV, lastV, ⟨⟨hn, hi0, hlocs, f22, f6, f4, f5, htcb, hstop⟩, f3, f11,
    f12, f14, f25, f16, f17, hheap, hrate⟩, hset⟩ := h
  have hin := inFacts_of_pre hpre
  have hvt := trec_valid hpre hn
  have hxv := xrefs_valid_of_pre hpre
  clear hpre
  have hst := stInv_st hin i.toInt.toNat hstop
  have hmemT : g.trec i.toInt.toNat ∈ g.tcat := by rw [trec_eq hn]; exact List.getElem_mem hn
  have hfnd := found_of_loopHeap (Hide.elim hheap)
  have hst2 := stInv_stSel hst hvt (hex_of_found hin hstop hfnd.1)
  have hl2 := stSel_lastId g.xrefs (g.st i.toInt.toNat) (g.trec i.toInt.toNat)
  have hxrS := loopHeap_xref_sel (Hide.elim hheap)
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
  have hxr := hxrS
  have hvx : CardXrefRecord.Valid (stSel g.xrefs (g.st i.toInt.toNat) (g.trec i.toInt.toNat)).xref := by
    obtain ⟨-, -, -, hcur, -⟩ := hst2
    obtain ⟨-, hxx, -, -, -⟩ := hcur _ hl2
    have hxr0 := hfnd.2
    rw [hxx] at hxr0 ⊢
    exact hxv _ (getD_find_mem hxr0)
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
  clear hset7 htr hTk hset hst hst2 hin hvt hmemT hl2 hsome hxr hvx hfx hxv hxrS hfnd
  unfold RunWPc
  jvc [runSpecG, runC, spacesSig, Grows, fields_get_set, narrow_cls, narrow_long]
  apply j232_of hn hi0 hstop
  case hheap => exact hheap
  case htcb => exact htcb
  case hT => exact Hide.elim hT'
  case h1h => assumption
  case h1n => assumption
  case h1f => assumption
  case h2h => assumption
  case h2n => assumption
  case h2f => assumption
  case h3h => assumption
  case h3n => assumption
  case h3f => assumption
  case h3i => assumption
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
  case hrate => exact hrate
  case hset => exact Hide.intro ⟨fsT, Hide.elim hT', Hide.elim hset7'⟩
  case hcs =>
    have h := Hide.elim hcss'
    unfold sel
    rw [selD_xref]
    exact h

end EquivLean.Modernize.Cbact04c.Java
