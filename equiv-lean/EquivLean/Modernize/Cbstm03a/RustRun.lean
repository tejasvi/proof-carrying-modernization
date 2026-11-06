import EquivLean.Modernize.Cbstm03a.RustRun1
import EquivLean.Modernize.Cbstm03a.RustRun2
import EquivLean.Modernize.Cbstm03a.RustRun3
import EquivLean.Modernize.Cbstm03a.RustRun4
import EquivLean.Modernize.Cbstm03a.RustRun4b
import EquivLean.Modernize.Cbstm03a.RustRun5
import EquivLean.Modernize.Cbstm03a.RustProof

/-!
# CBSTM03A → Rust: top-level proof of `run_spec : RunSpec` and `rust : Statement`

Links `RustRun1`–`RustRun5` and `RustProof.statement_of_run` to close `rust : Statement`.
-/

open Aeneas Aeneas.Std Result EquivLean EquivLean.Aeneas
open Cobol Cobol.StmCore EquivLean.Cobol.Rec
open EquivLean.Modernize.Cbstm03a.StmBridge EquivLean.Modernize.Cbstm03a.Model

namespace EquivLean.Modernize.Cbstm03a.Rust

open ML

theorem mainlineDeps_inst
    (s1 : Slice cbstm03a.TrnxRecord) (s2 : Slice cbstm03a.CardXrefRecord)
    (s3 : Slice cbstm03a.CustomerRecord) (s4 : Slice cbstm03a.AccountRecord)
    (vals1 vals2 vals3 vals4 : List (List FVal))
    (hs2 : s2.val.map CardXrefRecord.vals = vals2)
    (hs3 : s3.val.map CustomerRecord.vals = vals3)
    (hs4 : s4.val.map AccountRecord.vals = vals4)
    (hv1 : ∀ v ∈ vals1, TrnxRecord.Valid v)
    (hv3 : ∀ v ∈ vals3, CustomerRecord.Valid v)
    (hv4 : ∀ v ∈ vals4, AccountRecord.Valid v)
    (hD : EquivLean.Modernize.Cbstm03a.Domain vals1 vals2 vals3 vals4)
    (tbl : Array U8 256#usize)
    (htbl : ∀ x : UInt8, tbl.val.getD (cp037Code x) 0#u8 = byteOf x.toNat)
    (mem : cbstm03a.Mem)
    (hmem : MemLoaded mem (grp (vals1.map TrnxRecord.encode)))
    (cr_cnt : Std.I64)
    (hcr_cnt : cr_cnt.val = ((grp (vals1.map TrnxRecord.encode)).length : Int)) :
    MainlineDeps s1 s2 s3 s4 vals1 vals2 vals3 vals4 tbl mem cr_cnt where
  put_eq := put_eq
  eq_bytes_eq := eq_bytes_eq
  set_dd_8 := set_dd_8
  err_abend_cust c hd hrc := err_abend_cust c hd (by rw [hrc]; rfl)
  err_abend_acct c hd hrc := err_abend_acct c hd (by rw [hrc]; rfl)
  m03b_xref_some c idx hdd hop heof hpos hlt := by
    obtain ⟨c', hc', hrc, _, hpos', heof', hfldt, hd, hs, hh, ha⟩ :=
      call_m03b_xref_read_lt c s1 s2 s3 s4 vals2 (by rw [hdd]; rfl) hop heof hs2 (by omega)
    rw [hpos] at hpos' hfldt
    exact ⟨c', hc', hrc, hpos', heof', hfldt, hd, hs, hh, ha⟩
  m03b_xref_eof c hdd hop heof hpos := by
    exact ⟨_, call_m03b_xref_read_eof c s1 s2 s3 s4 vals2 (by rw [hdd]; rfl) hop heof hs2 (by omega),
      rfl, rfl, rfl, rfl, rfl, rfl⟩
  m03b_cust_key c cid hdd hop hkln hcid0 hcid9 hkey :=
    call_m03b_cust_key c s1 s2 s3 s4 vals3 cid (by rw [hdd]; rfl) hop hkln hcid0 hcid9 hkey hs3 hv3
  m03b_acct_key c aid hdd hop hkln haid0 haid11 hkey :=
    call_m03b_acct_key c s1 s2 s3 s4 vals4 aid (by rw [hdd]; rfl) hop hkln haid0 haid11 hkey hs4 hv4
  create_and_trnx_get c st cust_rec acct_rec xref_rec trnx_rec xval cval aval
      hx hc ha hxref hcust hacct hcaps hcaph := by
    obtain ⟨c1, st1, hcs, hs1_eq, hs1_len, hh1_eq, hh1_len, hd1, hab1, hxp1, hxe1⟩ :=
      CS.create_statement_spec c st cust_rec acct_rec cval aval hc ha hcust hacct
        (by omega) (by omega)
    obtain ⟨c2, st2, trnx_rec', htg, hs2_eq, hh2_eq, hd2, hab2, hxp2, hxe2⟩ :=
      trnx_get_spec hv1 hD hmem hcr_cnt htbl c1 st1 xref_rec trnx_rec xval hx hxref
        (by omega) (by omega)
    refine ⟨c1, st1, c2, st2, trnx_rec', hcs, htg, ?_, ?_,
      hd2.trans hd1, hab2.trans hab1, hxp2.trans hxp1, hxe2.trans hxe1⟩
    · simp only [linesOfVec, hs2_eq, hs1_eq, modelStmtOf, List.append_assoc]
    · simp only [linesOfVec, hh2_eq, hh1_eq, modelHtmlOf, List.append_assoc]

theorem close_file_any
    (s1 : Slice cbstm03a.TrnxRecord) (s2 : Slice cbstm03a.CardXrefRecord)
    (s3 : Slice cbstm03a.CustomerRecord) (s4 : Slice cbstm03a.AccountRecord)
    (c0 : cbstm03a.Ctx) (dd msg : Slice U8)
    (hdd : dd.val = ddTrnxArr.val ∨ dd.val = ddXrefArr.val ∨
           dd.val = ddCustArr.val ∨ dd.val = ddAcctArr.val) :
    ∃ c0', cbstm03a.close_file c0 dd msg s1 s2 s3 s4 = .ok (true, c0') ∧
      c0'.displays = c0.displays ∧ c0'.stmt = c0.stmt ∧
      c0'.html = c0.html ∧ c0'.abended = c0.abended := by
  rcases hdd with h | h | h | h
  · exact ⟨_, close_file_trnx c0 dd msg s1 s2 s3 s4 h, rfl, rfl, rfl, rfl⟩
  · exact ⟨_, close_file_xref c0 dd msg s1 s2 s3 s4 h, rfl, rfl, rfl, rfl⟩
  · exact ⟨_, close_file_cust c0 dd msg s1 s2 s3 s4 h, rfl, rfl, rfl, rfl⟩
  · exact ⟨_, close_file_acct c0 dd msg s1 s2 s3 s4 h, rfl, rfl, rfl, rfl⟩

/-- **Main specification of `cbstm03a.run`.** -/
theorem run_spec : RunSpec := by
  intro s1 s2 s3 s4 vals1 vals2 vals3 vals4 hs1 hs2 hs3 hs4 hv1 hv2 hv3 hv4 hD _hLen
  obtain ⟨tbl, htbl_ok, htbl⟩ := lat2ebc_table_eq
  let c0 : cbstm03a.Ctx :=
    { initCtx0 with
      m_dd := ddTrnxArr
      m_oper := 79#u8
      m_rc := Array.make 2#usize [48#u8, 48#u8]
      trnx_pos := 0#usize
      trnx_eof := false
      trnx_status := Array.make 2#usize [48#u8, 48#u8] }
  have hop1 : ∀ msg : Slice U8,
      cbstm03a.open_file initCtx0 ddTrnxArr.to_slice msg s1 s2 s3 s4 = .ok (true, c0) :=
    fun msg => open_file_trnx initCtx0 ddTrnxArr.to_slice msg s1 s2 s3 s4 rfl
  obtain ⟨c1, c2, s4_sl, s7_sl, mem, mem1, trnx_rec2, cr_cnt, tr_cnt,
      hm0, hrc1, hp350, hp16, hl0, hwtrct, hloaded, hcr, _htr, _hpos2, _heof2,
      _hxp2, _hxe2, hd2, hs2_stmt, hh2_html, ha2⟩ :=
    @run_load_phase_spec s1 s2 s3 s4 vals1 vals2 vals3 vals4 hs1 hv1 hD c0 rfl rfl rfl
  let c3 : cbstm03a.Ctx :=
    { c2 with
      m_dd := ddXrefArr
      m_oper := 79#u8
      m_rc := Array.make 2#usize [48#u8, 48#u8]
      xref_pos := 0#usize
      xref_eof := false
      xref_status := Array.make 2#usize [48#u8, 48#u8] }
  let c4 : cbstm03a.Ctx :=
    { c3 with
      m_dd := ddCustArr
      m_oper := 79#u8
      m_rc := Array.make 2#usize [48#u8, 48#u8]
      cust_status := Array.make 2#usize [48#u8, 48#u8] }
  let c5 : cbstm03a.Ctx :=
    { c4 with
      m_dd := ddAcctArr
      m_oper := 79#u8
      m_rc := Array.make 2#usize [48#u8, 48#u8]
      acct_status := Array.make 2#usize [48#u8, 48#u8] }
  have hop2 : ∀ msg : Slice U8,
      cbstm03a.open_file c2 ddXrefArr.to_slice msg s1 s2 s3 s4 = .ok (true, c3) :=
    fun msg => open_file_xref c2 ddXrefArr.to_slice msg s1 s2 s3 s4 rfl
  have hop3 : ∀ msg : Slice U8,
      cbstm03a.open_file c3 ddCustArr.to_slice msg s1 s2 s3 s4 = .ok (true, c4) :=
    fun msg => open_file_cust c3 ddCustArr.to_slice msg s1 s2 s3 s4 rfl
  have hop4 : ∀ msg : Slice U8,
      cbstm03a.open_file c4 ddAcctArr.to_slice msg s1 s2 s3 s4 = .ok (true, c5) :=
    fun msg => open_file_acct c4 ddAcctArr.to_slice msg s1 s2 s3 s4 rfl
  have hD_deps :=
    mainlineDeps_inst s1 s2 s3 s4 vals1 vals2 vals3 vals4 hs2 hs3 hs4 hv1 hv3 hv4 hD
      tbl htbl mem1 hloaded cr_cnt hcr
  exact run_eq_of_parts htbl_ok hop1 hm0 hrc1 hp350 hp16 hl0 hwtrct hop2 hop3 hop4
    rfl rfl
    (by change c2.displays.val = []; rw [hd2]; rfl)
    (by change c2.abended = false; rw [ha2]; rfl)
    (by change c2.stmt.val = []; rw [hs2_stmt]; rfl)
    (by change c2.html.val = []; rw [hh2_html]; rfl)
    (close_file_any s1 s2 s3 s4)
    hD_deps hv2 hv3 hv4 hD

/-- **CBSTM03A → Rust (`Statement`).** -/
theorem rust : Statement :=
  statement_of_run run_spec

#print axioms rust

end EquivLean.Modernize.Cbstm03a.Rust
