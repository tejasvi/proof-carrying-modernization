import EquivLean.Modernize.Cbstm03a.RustDefs

/-!
# CBSTM03A → Rust, part 5: `1000-MAINLINE` (`run_loop1`), `close_file`, and `run_spec : RunSpec`

Connects the entry point `cbstm03a.run` and its mainline loop `cbstm03a.run_loop1` to `Model.loop`
and `Model.run`, proving `run_spec : RunSpec` and `rust : Statement` (`statement_of_run`).
-/

open Aeneas Aeneas.Std Result ControlFlow Error EquivLean EquivLean.Aeneas
open Cobol Cobol.StmCore EquivLean.Cobol.Rec
open EquivLean.Modernize.Cbstm03a.StmBridge EquivLean.Modernize.Cbstm03a.Model

namespace EquivLean.Modernize.Cbstm03a.Rust.ML

/-! ## 1. Output line-count bounds (`Usize.max`) -/

theorem usize_max_ge : 4294967295 ≤ Usize.max := by
  rcases Usize.bounds_eq with h | h <;> rw [h] <;> simp only [U32.max_eq, U64.max_eq] <;> omega

theorem length_modelHeadStmt (c a : List FVal) : (modelHeadStmt c a).length = 16 := rfl
theorem length_modelHeadHtml (c a : List FVal) : (modelHeadHtml c a).length = 56 := rfl
theorem length_modelTranHtml (r : List FVal) : (modelTranHtml r).length = 11 := rfl
theorem length_modelTailStmt (t : Int) : (modelTailStmt t).length = 3 := rfl
theorem length_modelTailHtml : modelTailHtml.length = 8 := rfl

theorem length_flatMap_modelTranHtml : ∀ ts : List (List FVal),
    (ts.flatMap modelTranHtml).length = 11 * ts.length
  | [] => rfl
  | _ :: rs => by
    simp only [List.flatMap_cons, List.length_append, length_modelTranHtml,
      length_flatMap_modelTranHtml rs, List.length_cons]
    omega

theorem length_flatten_le_10 {α : Type} : ∀ {gs : List (List α)},
    (∀ g ∈ gs, g.length ≤ 10) → gs.flatten.length ≤ 10 * gs.length
  | [], _ => by simp
  | g :: gs, h => by
    have hg := h g (List.mem_cons_self ..)
    have hgs := length_flatten_le_10 (fun x hx => h x (List.mem_cons_of_mem _ hx))
    simp only [List.flatten_cons, List.length_append, List.length_cons]
    omega

theorem trs_length_le_500 {vals1 vals2 vals3 vals4 : List (List FVal)}
    (hD : EquivLean.Modernize.Cbstm03a.Domain vals1 vals2 vals3 vals4) :
    vals1.length ≤ 500 := by
  obtain ⟨_, _, hG, hT, _⟩ := hD
  have hf := (grp_props (vals1.map TrnxRecord.encode)).1
  have hlen : (vals1.map TrnxRecord.encode).length = vals1.length := List.length_map _
  have hfl := length_flatten_le_10 hT
  rw [hf, hlen] at hfl
  omega

theorem length_modelStmtOf_le {vals1 vals2 vals3 vals4 : List (List FVal)}
    (hD : EquivLean.Modernize.Cbstm03a.Domain vals1 vals2 vals3 vals4)
    (card : List UInt8) (c a : List FVal) :
    (modelStmtOf vals1 card c a).length ≤ 519 := by
  have h500 := trs_length_le_500 hD
  have hof : (ofCardF card vals1).length ≤ vals1.length := List.length_filter_le _ _
  unfold modelStmtOf
  simp only [List.length_append, length_modelHeadStmt, List.length_map, length_modelTailStmt]
  omega

theorem length_modelHtmlOf_le {vals1 vals2 vals3 vals4 : List (List FVal)}
    (hD : EquivLean.Modernize.Cbstm03a.Domain vals1 vals2 vals3 vals4)
    (card : List UInt8) (c a : List FVal) :
    (modelHtmlOf vals1 card c a).length ≤ 5564 := by
  have h500 := trs_length_le_500 hD
  have hof : (ofCardF card vals1).length ≤ vals1.length := List.length_filter_le _ _
  unfold modelHtmlOf
  simp only [List.length_append, length_modelHeadHtml, length_flatMap_modelTranHtml,
    length_modelTailHtml]
  omega

/-! ## 2. Array range indexing and terminal steps of `run_loop1` -/

theorem ite_true_of {c : Prop} [Decidable c] {α : Sort _} {a b : α} (h : c) :
    (if c then a else b) = a := by simp [h]

theorem array_index_range {n : Usize} (a : Array U8 n) (j k : Usize)
    (hjk : j.val ≤ k.val) (hk : k.val ≤ n.val) :
    core.array.Array.index (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeUsizeSlice U8))
      a { start := j, «end» := k } =
      .ok (Slice.from ((a.val.drop j.val).take (k.val - j.val)) (by simp; scalar_tac)) := by
  simp only [core.array.Array.index, core.ops.index.IndexSlice, core.slice.index.Slice.index,
    core.slice.index.SliceIndexRangeUsizeSlice, core.slice.index.SliceIndexRangeUsizeSlice.index]
  have hl : a.to_slice.length = n.val := by simp [Array.to_slice]
  rw [ite_true_of ⟨by simpa [UScalar.le_equiv] using hjk, by rw [hl]; exact hk⟩]
  congr 1
  rw [Slice.eq_iff]
  simp [List.slice, Array.to_slice]

theorem run_loop1_done_false (trnx_file : Slice cbstm03a.TrnxRecord)
    (xref_file : Slice cbstm03a.CardXrefRecord) (cust_file : Slice cbstm03a.CustomerRecord)
    (acct_file : Slice cbstm03a.AccountRecord) (tbl : Array U8 256#usize)
    (c : cbstm03a.Ctx) (mem : cbstm03a.Mem) (st : cbstm03a.St)
    (trnx_rec : Array U8 350#usize) (cr_cnt : Std.I64) (eof : U8)
    (xref_rec : Array U8 50#usize) (cust_rec : Array U8 500#usize)
    (acct_rec : Array U8 300#usize) :
    cbstm03a.run_loop1 trnx_file xref_file cust_file acct_file tbl c mem st trnx_rec cr_cnt
      false eof xref_rec cust_rec acct_rec = .ok (c, false) := by
  rw [cbstm03a.run_loop1, loop_unfold]
  simp [cbstm03a.run_loop1.body]

theorem run_loop1_done_eof (trnx_file : Slice cbstm03a.TrnxRecord)
    (xref_file : Slice cbstm03a.CardXrefRecord) (cust_file : Slice cbstm03a.CustomerRecord)
    (acct_file : Slice cbstm03a.AccountRecord) (tbl : Array U8 256#usize)
    (c : cbstm03a.Ctx) (mem : cbstm03a.Mem) (st : cbstm03a.St)
    (trnx_rec : Array U8 350#usize) (cr_cnt : Std.I64)
    (xref_rec : Array U8 50#usize) (cust_rec : Array U8 500#usize)
    (acct_rec : Array U8 300#usize) :
    cbstm03a.run_loop1 trnx_file xref_file cust_file acct_file tbl c mem st trnx_rec cr_cnt
      true 89#u8 xref_rec cust_rec acct_rec = .ok (c, true) := by
  rw [cbstm03a.run_loop1, loop_unfold]
  simp [cbstm03a.run_loop1.body]

theorem run_loop1_step {trnx_file : Slice cbstm03a.TrnxRecord}
    {xref_file : Slice cbstm03a.CardXrefRecord} {cust_file : Slice cbstm03a.CustomerRecord}
    {acct_file : Slice cbstm03a.AccountRecord} {tbl : Array U8 256#usize}
    {c c' : cbstm03a.Ctx} {mem : cbstm03a.Mem} {st st' : cbstm03a.St}
    {trnx_rec trnx_rec' : Array U8 350#usize} {cr_cnt : Std.I64} {ok1 ok1' : Bool} {eof eof' : U8}
    {xref_rec xref_rec' : Array U8 50#usize} {cust_rec cust_rec' : Array U8 500#usize}
    {acct_rec acct_rec' : Array U8 300#usize}
    (hb : cbstm03a.run_loop1.body trnx_file xref_file cust_file acct_file tbl mem cr_cnt
      c st trnx_rec ok1 eof xref_rec cust_rec acct_rec =
      .ok (.cont (c', st', trnx_rec', ok1', eof', xref_rec', cust_rec', acct_rec'))) :
    cbstm03a.run_loop1 trnx_file xref_file cust_file acct_file tbl c mem st trnx_rec cr_cnt
      ok1 eof xref_rec cust_rec acct_rec =
    cbstm03a.run_loop1 trnx_file xref_file cust_file acct_file tbl c' mem st' trnx_rec' cr_cnt
      ok1' eof' xref_rec' cust_rec' acct_rec' := by
  rw [cbstm03a.run_loop1, loop_unfold]
  dsimp only
  rw [hb, bind_ok]
  rfl

/-! ## 3. Helper constants and `linesOfVec` -/

def ddTrnxArr : Array U8 8#usize :=
  Array.make 8#usize [84#u8, 82#u8, 78#u8, 88#u8, 70#u8, 73#u8, 76#u8, 69#u8]
def ddXrefArr : Array U8 8#usize :=
  Array.make 8#usize [88#u8, 82#u8, 69#u8, 70#u8, 70#u8, 73#u8, 76#u8, 69#u8]
def ddCustArr : Array U8 8#usize :=
  Array.make 8#usize [67#u8, 85#u8, 83#u8, 84#u8, 70#u8, 73#u8, 76#u8, 69#u8]
def ddAcctArr : Array U8 8#usize :=
  Array.make 8#usize [65#u8, 67#u8, 67#u8, 84#u8, 70#u8, 73#u8, 76#u8, 69#u8]

def msgErrReadCustArr : Array U8 22#usize :=
  Array.make 22#usize
    [69#u8, 82#u8, 82#u8, 79#u8, 82#u8, 32#u8, 82#u8, 69#u8, 65#u8, 68#u8, 73#u8, 78#u8,
     71#u8, 32#u8, 67#u8, 85#u8, 83#u8, 84#u8, 70#u8, 73#u8, 76#u8, 69#u8]

def msgErrReadAcctArr : Array U8 22#usize :=
  Array.make 22#usize
    [69#u8, 82#u8, 82#u8, 79#u8, 82#u8, 32#u8, 82#u8, 69#u8, 65#u8, 68#u8, 73#u8, 78#u8,
     71#u8, 32#u8, 65#u8, 67#u8, 67#u8, 84#u8, 70#u8, 73#u8, 76#u8, 69#u8]

def linesOfVec (v : alloc.vec.Vec (alloc.vec.Vec U8)) : List (List Nat) :=
  v.val.map (fun l => l.val.map (·.val))

@[simp] theorem length_linesOfVec (v : alloc.vec.Vec (alloc.vec.Vec U8)) :
    (linesOfVec v).length = v.val.length := by
  simp [linesOfVec]

theorem finish_eq (c : cbstm03a.Ctx) :
    cbstm03a.finish c = .ok
      { displays := c.displays, stmt_file_writes := c.stmt, html_file_writes := c.html,
        abended := c.abended } := rfl

/-- Dependencies from `RustRun1`–`RustRun4` used by `run_loop1` and `run`. -/
structure MainlineDeps (trnx_file : Slice cbstm03a.TrnxRecord)
    (xref_file : Slice cbstm03a.CardXrefRecord) (cust_file : Slice cbstm03a.CustomerRecord)
    (acct_file : Slice cbstm03a.AccountRecord)
    (vals1 vals2 vals3 vals4 : List (List FVal))
    (tbl : Array U8 256#usize) (mem : cbstm03a.Mem) (cr_cnt : Std.I64) : Prop where
  put_eq : ∀ (dst : Slice U8) (off len : Usize) (src : Slice U8),
    off.val + len.val ≤ dst.val.length →
    ∃ s' : Slice U8, cbstm03a.put dst off len src = .ok s' ∧
      s'.val = putL dst.val off.val len.val src.val
  eq_bytes_eq : ∀ (a b : Slice U8),
    cbstm03a.eq_bytes a b = .ok (decide (a.val = b.val))
  set_dd_8 : ∀ (c : cbstm03a.Ctx) (dd : Array U8 8#usize),
    cbstm03a.set_dd c dd.to_slice = .ok { c with m_dd := dd }
  err_abend_cust : ∀ (c : cbstm03a.Ctx),
    c.displays.val = [] → c.m_rc = Array.make 2#usize [50#u8, 51#u8] →
    ∃ c' : cbstm03a.Ctx, cbstm03a.err_abend c msgErrReadCustArr.to_slice = .ok c' ∧
      linesOfVec c'.displays = modelCustAbortDisp ∧
      c'.stmt = c.stmt ∧ c'.html = c.html ∧ c'.abended = true
  err_abend_acct : ∀ (c : cbstm03a.Ctx),
    c.displays.val = [] → c.m_rc = Array.make 2#usize [50#u8, 51#u8] →
    ∃ c' : cbstm03a.Ctx, cbstm03a.err_abend c msgErrReadAcctArr.to_slice = .ok c' ∧
      linesOfVec c'.displays = modelAcctAbortDisp ∧
      c'.stmt = c.stmt ∧ c'.html = c.html ∧ c'.abended = true
  m03b_xref_some : ∀ (c : cbstm03a.Ctx) (idx : Nat),
    c.m_dd = ddXrefArr → c.m_oper = 82#u8 → c.xref_eof = false →
    c.xref_pos.val = idx → idx < vals2.length →
    ∃ c' : cbstm03a.Ctx,
      cbstm03a.call_m03b c trnx_file xref_file cust_file acct_file = .ok c' ∧
      c'.m_rc = Array.make 2#usize [48#u8, 48#u8] ∧
      c'.xref_pos.val = idx + 1 ∧ c'.xref_eof = false ∧
      c'.m_fldt.val = latL (CardXrefRecord.encode (vals2.getD idx [])) ++ List.replicate 950 32#u8 ∧
      c'.displays = c.displays ∧ c'.stmt = c.stmt ∧ c'.html = c.html ∧ c'.abended = c.abended
  m03b_xref_eof : ∀ (c : cbstm03a.Ctx),
    c.m_dd = ddXrefArr → c.m_oper = 82#u8 → c.xref_eof = false →
    c.xref_pos.val = vals2.length →
    ∃ c' : cbstm03a.Ctx,
      cbstm03a.call_m03b c trnx_file xref_file cust_file acct_file = .ok c' ∧
      c'.m_rc = Array.make 2#usize [49#u8, 48#u8] ∧
      c'.xref_eof = true ∧
      c'.displays = c.displays ∧ c'.stmt = c.stmt ∧ c'.html = c.html ∧ c'.abended = c.abended
  m03b_cust_key : ∀ (c : cbstm03a.Ctx) (cid : Int),
    c.m_dd = ddCustArr → c.m_oper = 75#u8 → c.m_key_ln = 9#i64 →
    0 ≤ cid → cid.natAbs < 10 ^ 9 →
    c.m_key.val.take 9 = latL (Sem.digitChars {} 9 cid.natAbs) →
    ∃ c' : cbstm03a.Ctx,
      cbstm03a.call_m03b c trnx_file xref_file cust_file acct_file = .ok c' ∧
      c'.displays = c.displays ∧ c'.stmt = c.stmt ∧ c'.html = c.html ∧ c'.abended = c.abended ∧
      c'.xref_pos = c.xref_pos ∧ c'.xref_eof = c.xref_eof ∧
      match vals3.find? (fun v => numOf (v.getD 0 default) == cid) with
      | none => c'.m_rc = Array.make 2#usize [50#u8, 51#u8]
      | some cval =>
        c'.m_rc = Array.make 2#usize [48#u8, 48#u8] ∧
        c'.m_fldt.val = latL (CustomerRecord.encode cval) ++ List.replicate 500 32#u8
  m03b_acct_key : ∀ (c : cbstm03a.Ctx) (aid : Int),
    c.m_dd = ddAcctArr → c.m_oper = 75#u8 → c.m_key_ln = 11#i64 →
    0 ≤ aid → aid.natAbs < 10 ^ 11 →
    c.m_key.val.take 11 = latL (Sem.digitChars {} 11 aid.natAbs) →
    ∃ c' : cbstm03a.Ctx,
      cbstm03a.call_m03b c trnx_file xref_file cust_file acct_file = .ok c' ∧
      c'.displays = c.displays ∧ c'.stmt = c.stmt ∧ c'.html = c.html ∧ c'.abended = c.abended ∧
      c'.xref_pos = c.xref_pos ∧ c'.xref_eof = c.xref_eof ∧
      match vals4.find? (fun v => numOf (v.getD 0 default) == aid) with
      | none => c'.m_rc = Array.make 2#usize [50#u8, 51#u8]
      | some aval =>
        c'.m_rc = Array.make 2#usize [48#u8, 48#u8] ∧
        c'.m_fldt.val = latL (AccountRecord.encode aval) ++ List.replicate 700 32#u8
  create_and_trnx_get : ∀ (c : cbstm03a.Ctx) (st : cbstm03a.St)
    (cust_rec : Array U8 500#usize) (acct_rec : Array U8 300#usize)
    (xref_rec : Array U8 50#usize) (trnx_rec : Array U8 350#usize)
    (xval cval aval : List FVal),
    CardXrefRecord.Valid xval → CustomerRecord.Valid cval → AccountRecord.Valid aval →
    xref_rec.val = latL (CardXrefRecord.encode xval) →
    cust_rec.val = latL (CustomerRecord.encode cval) →
    acct_rec.val = latL (AccountRecord.encode aval) →
    c.stmt.val.length + 519 ≤ Usize.max →
    c.html.val.length + 5564 ≤ Usize.max →
    ∃ c1 st1 c2 st2 trnx_rec',
      cbstm03a.create_statement c st cust_rec acct_rec = .ok (c1, st1) ∧
      cbstm03a.trnx_get c1 st1 mem cr_cnt xref_rec trnx_rec tbl = .ok (c2, st2, trnx_rec') ∧
      linesOfVec c2.stmt = linesOfVec c.stmt ++ modelStmtOf vals1 (strOf (xval.getD 0 default)) cval aval ∧
      linesOfVec c2.html = linesOfVec c.html ++ modelHtmlOf vals1 (strOf (xval.getD 0 default)) cval aval ∧
      c2.displays = c.displays ∧ c2.abended = c.abended ∧
      c2.xref_pos = c.xref_pos ∧ c2.xref_eof = c.xref_eof

/-! ## 4. Slice/array lemmas for `run_loop1.body` -/

theorem putL_full (dst src : List U8) (n : Nat) (hd : dst.length = n) (hs : src.length = n) :
    putL dst 0 n src = src := by
  simp [putL, hd, hs]

theorem take_putL_zero (dst src : List U8) (k : Nat) (hs : src.length = k) :
    (putL dst 0 k src).take k = src := by
  subst hs
  simp [putL]

theorem xref_key_bytes {x : List FVal} (hx : CardXrefRecord.Valid x) :
    (CardXrefRecord.encode x).length = 50 ∧
    0 ≤ numOf (x.getD 1 default) ∧ (numOf (x.getD 1 default)).natAbs < 10 ^ 9 ∧
    ((CardXrefRecord.encode x).drop 16).take 9 =
      Sem.digitChars {} 9 (numOf (x.getD 1 default)).natAbs ∧
    0 ≤ numOf (x.getD 2 default) ∧ (numOf (x.getD 2 default)).natAbs < 10 ^ 11 ∧
    ((CardXrefRecord.encode x).drop 25).take 11 =
      Sem.digitChars {} 11 (numOf (x.getD 2 default)).natAbs := by
  have h1 := (field_num_decode cardXrefRecord_contig hx 1 16 9 { digits := 9 } (by decide) rfl rfl rfl).1
  have h2 := (field_num_decode cardXrefRecord_contig hx 2 25 11 { digits := 11 } (by decide) rfl rfl rfl).1
  rw [encodeNum_unsigned_display (by decide)] at h1
  rw [encodeNum_unsigned_display (by decide)] at h2
  have hxf := xref_fields hx
  exact ⟨xref_length hx, hxf.2.2.2.2.1, hxf.2.2.2.2.2.1, h1,
    hxf.2.2.2.2.2.2.2.2.1, hxf.2.2.2.2.2.2.2.2.2, h2⟩

theorem to_slice_mut_back_val {n : Usize} (a : Array U8 n) (s : Slice U8) (hs : s.val.length = n.val) :
    ((Array.to_slice_mut a).2 s).val = s.val := by
  simp [Array.to_slice_mut, Array.from_slice, hs]

theorem eq_bytes_00_true
    (heq : ∀ (a b : Slice U8), cbstm03a.eq_bytes a b = .ok (decide (a.val = b.val)))
    {rc : Array U8 2#usize} (hrc : rc = Array.make 2#usize [48#u8, 48#u8]) :
    cbstm03a.eq_bytes rc.to_slice (Array.make 2#usize [48#u8, 48#u8]).to_slice = .ok true := by
  rw [heq, hrc]; rfl

theorem eq_bytes_00_of_10
    (heq : ∀ (a b : Slice U8), cbstm03a.eq_bytes a b = .ok (decide (a.val = b.val)))
    {rc : Array U8 2#usize} (hrc : rc = Array.make 2#usize [49#u8, 48#u8]) :
    cbstm03a.eq_bytes rc.to_slice (Array.make 2#usize [48#u8, 48#u8]).to_slice = .ok false := by
  rw [heq, hrc]
  simp [Array.to_slice, Array.make_val]

theorem eq_bytes_10_of_10
    (heq : ∀ (a b : Slice U8), cbstm03a.eq_bytes a b = .ok (decide (a.val = b.val)))
    {rc : Array U8 2#usize} (hrc : rc = Array.make 2#usize [49#u8, 48#u8]) :
    cbstm03a.eq_bytes rc.to_slice (Array.make 2#usize [49#u8, 48#u8]).to_slice = .ok true := by
  rw [heq, hrc]; rfl

theorem eq_bytes_00_of_23
    (heq : ∀ (a b : Slice U8), cbstm03a.eq_bytes a b = .ok (decide (a.val = b.val)))
    {rc : Array U8 2#usize} (hrc : rc = Array.make 2#usize [50#u8, 51#u8]) :
    cbstm03a.eq_bytes rc.to_slice (Array.make 2#usize [48#u8, 48#u8]).to_slice = .ok false := by
  rw [heq, hrc]
  simp [Array.to_slice, Array.make_val]

theorem copy_prefix_spec
    (hput : ∀ (dst : Slice U8) (off len : Usize) (src : Slice U8),
      off.val + len.val ≤ dst.val.length →
      ∃ s' : Slice U8, cbstm03a.put dst off len src = .ok s' ∧
        s'.val = putL dst.val off.val len.val src.val)
    {n : Usize} (dst : Array U8 n) (fldt : Array U8 1000#usize)
    (bs : List UInt8) (hbs : bs.length = n.val)
    (hfldt : fldt.val = latL bs ++ List.replicate (1000 - n.val) 32#u8)
    (hp : ((fldt.val.drop (0#usize).val).take (n.val - (0#usize).val)).length ≤ Usize.max) :
    ∃ s' : Slice U8,
      cbstm03a.put (Array.to_slice_mut dst).1 0#usize n
        (Slice.from ((fldt.val.drop (0#usize).val).take (n.val - (0#usize).val)) hp) = .ok s' ∧
      ((Array.to_slice_mut dst).2 s').val = latL bs := by
  obtain ⟨s', hput', hs'⟩ := hput (Array.to_slice_mut dst).1 0#usize n
    (Slice.from ((fldt.val.drop (0#usize).val).take (n.val - (0#usize).val)) hp)
    (by simp [Array.to_slice_mut, Array.to_slice, dst.property])
  refine ⟨s', hput', ?_⟩
  have hsrc : (fldt.val.drop (0#usize).val).take (n.val - (0#usize).val) = latL bs := by
    simp only [UScalar.ofNatCore_val_eq, Nat.sub_zero, List.drop_zero]
    rw [hfldt, List.take_left' (by simp [hbs])]
  have hs'_eq : s'.val = latL bs := by
    rw [hs', Slice.from_val, hsrc, UScalar.ofNatCore_val_eq]
    exact putL_full _ _ n.val (by simp [Array.to_slice_mut, Array.to_slice, dst.property]) (by simp [hbs])
  rw [to_slice_mut_back_val dst s' (by rw [hs'_eq]; simp [hbs]), hs'_eq]

theorem copy_key_spec
    (hput : ∀ (dst : Slice U8) (off len : Usize) (src : Slice U8),
      off.val + len.val ≤ dst.val.length →
      ∃ s' : Slice U8, cbstm03a.put dst off len src = .ok s' ∧
        s'.val = putL dst.val off.val len.val src.val)
    (xref_rec : Array U8 50#usize) (j k len : Usize)
    (hlen : k.val - j.val = len.val) (h25 : len.val ≤ 25)
    (bs : List UInt8) (hxref : xref_rec.val = latL bs)
    (kbs : List UInt8) (hkbs : ((bs.drop j.val).take len.val) = kbs)
    (hklen : kbs.length = len.val)
    (hp : ((xref_rec.val.drop j.val).take (k.val - j.val)).length ≤ Usize.max) :
    ∃ s' : Slice U8,
      cbstm03a.put (Array.to_slice_mut (Array.repeat 25#usize 32#u8)).1 0#usize len
        (Slice.from ((xref_rec.val.drop j.val).take (k.val - j.val)) hp) = .ok s' ∧
      ((Array.to_slice_mut (Array.repeat 25#usize 32#u8)).2 s').val.take len.val = latL kbs := by
  let a1 := Array.repeat 25#usize 32#u8
  obtain ⟨s', hput', hs'⟩ := hput (Array.to_slice_mut a1).1 0#usize len
    (Slice.from ((xref_rec.val.drop j.val).take (k.val - j.val)) hp)
    (by simp [a1, Array.to_slice_mut, Array.to_slice]; exact h25)
  refine ⟨s', hput', ?_⟩
  have hsrc : (xref_rec.val.drop j.val).take (k.val - j.val) = latL kbs := by
    rw [hxref, ← latL_drop, ← latL_take, hlen, hkbs]
  have hs'_len : s'.val.length = 25 := by
    rw [hs', Slice.from_val, UScalar.ofNatCore_val_eq]
    exact length_putL _ 0 len.val _ (by simp [a1, Array.to_slice_mut, Array.to_slice]; exact h25)
  rw [to_slice_mut_back_val a1 s' hs'_len, hs', Slice.from_val, hsrc, UScalar.ofNatCore_val_eq]
  exact take_putL_zero _ (latL kbs) len.val (by simp [hklen])

theorem ne_78_89 : (78#u8 != 89#u8) = true := by decide
theorem eq_89_78 : (89#u8 = 78#u8) = false := by decide

theorem prod_casesOn_mk {α β : Type} {γ : Sort _} (a : α) (b : β) (f : α → β → γ) :
    (@Prod.casesOn α β (fun _ => γ) (a, b) f) = f a b := rfl

/-! ## 5. Mainline loop `run_loop1_spec` -/

set_option maxRecDepth 20000 in
theorem run_loop1_spec
    {trnx_file : Slice cbstm03a.TrnxRecord}
    {xref_file : Slice cbstm03a.CardXrefRecord} {cust_file : Slice cbstm03a.CustomerRecord}
    {acct_file : Slice cbstm03a.AccountRecord}
    {vals1 vals2 vals3 vals4 : List (List FVal)}
    {tbl : Array U8 256#usize} {mem : cbstm03a.Mem} {cr_cnt : Std.I64}
    (D : MainlineDeps trnx_file xref_file cust_file acct_file vals1 vals2 vals3 vals4 tbl mem cr_cnt)
    (hv2 : ∀ v ∈ vals2, CardXrefRecord.Valid v)
    (hv3 : ∀ v ∈ vals3, CustomerRecord.Valid v)
    (hv4 : ∀ v ∈ vals4, AccountRecord.Valid v)
    (hD : EquivLean.Modernize.Cbstm03a.Domain vals1 vals2 vals3 vals4) :
    ∀ (xs : List (List FVal)) (idx : Nat),
      idx + xs.length = vals2.length →
      xs = vals2.drop idx →
      ∀ (c : cbstm03a.Ctx) (st : cbstm03a.St)
        (trnx_rec : Array U8 350#usize) (xref_rec : Array U8 50#usize)
        (cust_rec : Array U8 500#usize) (acct_rec : Array U8 300#usize),
        c.xref_pos.val = idx → c.xref_eof = false →
        c.displays.val = [] → c.abended = false →
        c.stmt.val.length ≤ 519 * idx →
        c.html.val.length ≤ 5564 * idx →
        let o := Model.loop vals1 vals3 vals4 xs (linesOfVec c.stmt) (linesOfVec c.html)
        ∃ c' ok2,
          cbstm03a.run_loop1 trnx_file xref_file cust_file acct_file tbl c mem st trnx_rec cr_cnt
            true 78#u8 xref_rec cust_rec acct_rec = .ok (c', ok2) ∧
          linesOfVec c'.displays = o.disp ∧
          linesOfVec c'.stmt = o.stmtWrites ∧
          linesOfVec c'.html = o.htmlWrites ∧
          c'.abended = o.abended ∧
          ok2 = !o.abended
  | [], idx, hlen, _, c, st, trnx_rec, xref_rec, cust_rec, acct_rec,
    hpos, heof, hdisp, hab, _, _ => by
    have hidx : idx = vals2.length := by simp at hlen; exact hlen
    have hset := D.set_dd_8 c ddXrefArr
    obtain ⟨c2, hm03b, hrc, _, hd2, hs2, hh2, ha2⟩ :=
      D.m03b_xref_eof
        { c with m_dd := ddXrefArr, m_oper := 82#u8,
                 m_rc := Array.make 2#usize [48#u8, 48#u8],
                 m_fldt := Array.repeat 1000#usize 32#u8 }
        rfl rfl heof (by simpa [hpos] using hidx)
    dsimp only at hd2 hs2 hh2 ha2
    have heq00 := eq_bytes_00_of_10 D.eq_bytes_eq hrc
    have heq10 := eq_bytes_10_of_10 D.eq_bytes_eq hrc
    have hrng := array_index_range c2.m_fldt 0#usize 50#usize (by decide) (by decide)
    obtain ⟨s5, hput, _⟩ := D.put_eq (Array.to_slice_mut xref_rec).1 0#usize 50#usize
      (Slice.from ((c2.m_fldt.val.drop (0#usize).val).take ((50#usize).val - (0#usize).val))
        (by simp; scalar_tac))
      (by simp [Array.to_slice_mut, Array.to_slice, xref_rec.property])
    have hbody : cbstm03a.run_loop1.body trnx_file xref_file cust_file acct_file tbl mem cr_cnt
        c st trnx_rec true 78#u8 xref_rec cust_rec acct_rec =
        .ok (.cont (c2, st, trnx_rec, true, 89#u8, (Array.to_slice_mut xref_rec).2 s5, cust_rec, acct_rec)) := by
      simp only [Array.to_slice_mut, UScalar.ofNatCore_val_eq] at hput ⊢
      refine eq_ok_of_wp ?_
      rw [cbstm03a.run_loop1.body]
      aeneas_wp [Array.to_slice_mut, Nat.reduceEqDiff, Bool.false_eq_true, not_false_eq_true, prod_casesOn_mk,
        show Array.make 8#usize [88#u8, 82#u8, 69#u8, 70#u8, 70#u8, 73#u8, 76#u8, 69#u8] = ddXrefArr from rfl,
        hset, hm03b, heq00, heq10, hrng, hput]
    rw [run_loop1_step hbody, run_loop1_done_eof]
    refine ⟨c2, true, rfl, ?_, ?_, ?_, ?_, rfl⟩
    · simp [Model.loop, linesOfVec, hd2, hdisp]
    · simp [Model.loop, hs2]
    · simp [Model.loop, hh2]
    · simp [Model.loop, ha2, hab]
  | x :: xs, idx, hlen, hxs, c, st, trnx_rec, xref_rec, cust_rec, acct_rec,
    hpos, heof, hdisp, hab, hstmt_le, hhtml_le => by
    have hidx : idx < vals2.length := by simp at hlen; omega
    have hget_idx : vals2.getD idx [] = x := by
      have hd : vals2.drop idx = x :: xs := hxs.symm
      have h0 : (vals2.drop idx).head? = some x := by rw [hd]; rfl
      rw [List.head?_drop, List.getElem?_eq_getElem hidx, Option.some.injEq] at h0
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hidx, Option.getD_some, h0]
    have hx : CardXrefRecord.Valid x := by
      apply hv2 x
      have hd : x ∈ vals2.drop idx := by rw [← hxs]; exact List.mem_cons_self ..
      exact List.mem_of_mem_drop hd
    obtain ⟨hxl, hcid0, hcid9, hcid_bs, haid0, haid11, haid_bs⟩ := xref_key_bytes hx
    have hsetX := D.set_dd_8 c ddXrefArr
    obtain ⟨c2, hm03bX, hrcX, hpos2, heof2, hfldtX, hd2, hs2, hh2, ha2⟩ :=
      D.m03b_xref_some
        { c with m_dd := ddXrefArr, m_oper := 82#u8,
                 m_rc := Array.make 2#usize [48#u8, 48#u8],
                 m_fldt := Array.repeat 1000#usize 32#u8 }
        idx rfl rfl heof hpos hidx
    dsimp only at hd2 hs2 hh2 ha2
    rw [hget_idx] at hfldtX
    have heqX := eq_bytes_00_true D.eq_bytes_eq hrcX
    have hrngX := array_index_range c2.m_fldt 0#usize 50#usize (by decide) (by decide)
    obtain ⟨sX, hputX, hxref1⟩ := copy_prefix_spec D.put_eq xref_rec c2.m_fldt
      (CardXrefRecord.encode x) hxl hfldtX (by simp; scalar_tac)
    let xref_rec1 := (Array.to_slice_mut xref_rec).2 sX
    have hsetC := D.set_dd_8 c2 ddCustArr
    have hrng16 := array_index_range xref_rec1 16#usize 25#usize (by decide) (by decide)
    obtain ⟨s6, hput16, ha3_take⟩ := copy_key_spec D.put_eq xref_rec1 16#usize 25#usize 9#usize
      rfl (by decide) (CardXrefRecord.encode x) hxref1
      (Sem.digitChars {} 9 (numOf (x.getD 1 default)).natAbs) hcid_bs
      (by simp [Sem.digitChars, Cobol.Digits.length_toDigits]) (by simp; scalar_tac)
    let a3 := (Array.to_slice_mut (Array.repeat 25#usize 32#u8)).2 s6
    obtain ⟨c6, hm03bC, hd6, hs6, hh6, ha6, hpos6, heof6, hfindC⟩ :=
      D.m03b_cust_key
        { c2 with m_dd := ddCustArr, m_oper := 75#u8,
                  m_rc := Array.make 2#usize [48#u8, 48#u8], m_key := a3, m_key_ln := 9#i64,
                  m_fldt := Array.repeat 1000#usize 32#u8 }
        (numOf (x.getD 1 default)) rfl rfl rfl hcid0 hcid9 ha3_take
    dsimp only at hd6 hs6 hh6 ha6 hpos6 heof6
    unfold Model.loop
    dsimp only
    cases hfc : vals3.find? (fun v => numOf (v.getD 0 default) == numOf (x.getD 1 default)) with
    | none =>
      rw [hfc] at hfindC
      have heqC := eq_bytes_00_of_23 D.eq_bytes_eq hfindC
      obtain ⟨c8, habendC, hd8, hs8, hh8, ha8⟩ :=
        D.err_abend_cust c6 (by rw [hd6, hd2, hdisp]) hfindC
      have hbody : cbstm03a.run_loop1.body trnx_file xref_file cust_file acct_file tbl mem cr_cnt
          c st trnx_rec true 78#u8 xref_rec cust_rec acct_rec =
          .ok (.cont (c8, st, trnx_rec, false, 78#u8, xref_rec1, cust_rec, acct_rec)) := by
        simp only [xref_rec1, a3, Array.to_slice_mut, UScalar.ofNatCore_val_eq] at hputX hrng16 hput16 hm03bC ⊢
        refine eq_ok_of_wp ?_
        rw [cbstm03a.run_loop1.body]
        aeneas_wp [Array.to_slice_mut, Nat.reduceEqDiff, Bool.false_eq_true, not_false_eq_true, prod_casesOn_mk,
          show Array.make 8#usize [88#u8, 82#u8, 69#u8, 70#u8, 70#u8, 73#u8, 76#u8, 69#u8] = ddXrefArr from rfl,
          show Array.make 8#usize [67#u8, 85#u8, 83#u8, 84#u8, 70#u8, 73#u8, 76#u8, 69#u8] = ddCustArr from rfl,
          show Array.make 22#usize [69#u8, 82#u8, 82#u8, 79#u8, 82#u8, 32#u8, 82#u8, 69#u8, 65#u8,
            68#u8, 73#u8, 78#u8, 71#u8, 32#u8, 67#u8, 85#u8, 83#u8, 84#u8, 70#u8, 73#u8, 76#u8, 69#u8] =
            msgErrReadCustArr from rfl,
          hsetX, hm03bX, heqX, hrngX, hputX, hsetC, hrng16, hput16,
          hm03bC, heqC, habendC]
      rw [run_loop1_step hbody, run_loop1_done_false]
      refine ⟨c8, false, rfl, hd8, ?_, ?_, ha8, rfl⟩
      · rw [hs8, hs6, hs2]
      · rw [hh8, hh6, hh2]
    | some cval =>
      rw [hfc] at hfindC
      obtain ⟨hrcC, hfldtC⟩ := hfindC
      have heqC := eq_bytes_00_true D.eq_bytes_eq hrcC
      have hcv : CustomerRecord.Valid cval := hv3 cval (List.mem_of_find?_eq_some hfc)
      have hrngC := array_index_range c6.m_fldt 0#usize 500#usize (by decide) (by decide)
      obtain ⟨sC, hputC, hcust2⟩ := copy_prefix_spec D.put_eq cust_rec c6.m_fldt
        (CustomerRecord.encode cval) (cust_length hcv) hfldtC (by simp; scalar_tac)
      let cust_rec2 := (Array.to_slice_mut cust_rec).2 sC
      have hsetA := D.set_dd_8 c6 ddAcctArr
      have hrng25 := array_index_range xref_rec1 25#usize 36#usize (by decide) (by decide)
      obtain ⟨s15, hput25, ha6_take⟩ := copy_key_spec D.put_eq xref_rec1 25#usize 36#usize 11#usize
        rfl (by decide) (CardXrefRecord.encode x) hxref1
        (Sem.digitChars {} 11 (numOf (x.getD 2 default)).natAbs) haid_bs
        (by simp [Sem.digitChars, Cobol.Digits.length_toDigits]) (by simp; scalar_tac)
      let a6 := (Array.to_slice_mut (Array.repeat 25#usize 32#u8)).2 s15
      obtain ⟨c10, hm03bA, hd10, hs10, hh10, ha10, hpos10, heof10, hfindA⟩ :=
        D.m03b_acct_key
          { c6 with m_dd := ddAcctArr, m_oper := 75#u8,
                    m_rc := Array.make 2#usize [48#u8, 48#u8], m_key := a6, m_key_ln := 11#i64,
                    m_fldt := Array.repeat 1000#usize 32#u8 }
          (numOf (x.getD 2 default)) rfl rfl rfl haid0 haid11 ha6_take
      dsimp only at hd10 hs10 hh10 ha10 hpos10 heof10
      cases hfa : vals4.find? (fun v => numOf (v.getD 0 default) == numOf (x.getD 2 default)) with
      | none =>
        rw [hfa] at hfindA
        have heqA := eq_bytes_00_of_23 D.eq_bytes_eq hfindA
        obtain ⟨c11, habendA, hd11, hs11, hh11, ha11⟩ :=
          D.err_abend_acct c10 (by rw [hd10, hd6, hd2, hdisp]) hfindA
        have hbody : cbstm03a.run_loop1.body trnx_file xref_file cust_file acct_file tbl mem cr_cnt
            c st trnx_rec true 78#u8 xref_rec cust_rec acct_rec =
            .ok (.cont (c11, st, trnx_rec, false, 78#u8, xref_rec1, cust_rec2, acct_rec)) := by
          simp only [xref_rec1, cust_rec2, a3, a6, Array.to_slice_mut, UScalar.ofNatCore_val_eq]
            at hputX hrng16 hput16 hm03bC hputC hrng25 hput25 hm03bA ⊢
          refine eq_ok_of_wp ?_
          rw [cbstm03a.run_loop1.body]
          aeneas_wp [Array.to_slice_mut, Nat.reduceEqDiff, Bool.false_eq_true, not_false_eq_true, prod_casesOn_mk,
            show Array.make 8#usize [88#u8, 82#u8, 69#u8, 70#u8, 70#u8, 73#u8, 76#u8, 69#u8] = ddXrefArr from rfl,
            show Array.make 8#usize [67#u8, 85#u8, 83#u8, 84#u8, 70#u8, 73#u8, 76#u8, 69#u8] = ddCustArr from rfl,
            show Array.make 8#usize [65#u8, 67#u8, 67#u8, 84#u8, 70#u8, 73#u8, 76#u8, 69#u8] = ddAcctArr from rfl,
            show Array.make 22#usize [69#u8, 82#u8, 82#u8, 79#u8, 82#u8, 32#u8, 82#u8, 69#u8, 65#u8,
              68#u8, 73#u8, 78#u8, 71#u8, 32#u8, 65#u8, 67#u8, 67#u8, 84#u8, 70#u8, 73#u8, 76#u8, 69#u8] =
              msgErrReadAcctArr from rfl,
            hsetX, hm03bX, heqX, hrngX, hputX,
            hsetC, hrng16, hput16, hm03bC, heqC, hrngC, hputC,
            hsetA, hrng25, hput25, hm03bA, heqA, habendA]
        rw [run_loop1_step hbody, run_loop1_done_false]
        refine ⟨c11, false, rfl, hd11, ?_, ?_, ha11, rfl⟩
        · rw [hs11, hs10, hs6, hs2]
        · rw [hh11, hh10, hh6, hh2]
      | some aval =>
        rw [hfa] at hfindA
        obtain ⟨hrcA, hfldtA⟩ := hfindA
        have heqA := eq_bytes_00_true D.eq_bytes_eq hrcA
        have hav : AccountRecord.Valid aval := hv4 aval (List.mem_of_find?_eq_some hfa)
        have hrngA := array_index_range c10.m_fldt 0#usize 300#usize (by decide) (by decide)
        obtain ⟨sA, hputA, hacct1⟩ := copy_prefix_spec D.put_eq acct_rec c10.m_fldt
          (AccountRecord.encode aval) (acct_length hav) hfldtA (by simp; scalar_tac)
        let acct_rec1 := (Array.to_slice_mut acct_rec).2 sA
        have hxlen : vals2.length < 10 ^ 5 := hD.2.2.2.2
        have hmax := usize_max_ge
        have hstmt_max : c10.stmt.val.length + 519 ≤ Usize.max := by
          rw [hs10, hs6, hs2]; omega
        have hhtml_max : c10.html.val.length + 5564 ≤ Usize.max := by
          rw [hh10, hh6, hh2]; omega
        obtain ⟨c9, st1, c10', st2, trnx_rec1, hcreate, htrnx, hstmt', hhtml', hd', hab', hpos', heof'⟩ :=
          D.create_and_trnx_get c10 st cust_rec2 acct_rec1 xref_rec1 trnx_rec x cval aval
            hx hcv hav hxref1 hcust2 hacct1 hstmt_max hhtml_max
        have hbody : cbstm03a.run_loop1.body trnx_file xref_file cust_file acct_file tbl mem cr_cnt
            c st trnx_rec true 78#u8 xref_rec cust_rec acct_rec =
            .ok (.cont (c10', st2, trnx_rec1, true, 78#u8, xref_rec1, cust_rec2, acct_rec1)) := by
          simp only [xref_rec1, cust_rec2, acct_rec1, a3, a6, Array.to_slice_mut, UScalar.ofNatCore_val_eq]
            at hputX hrng16 hput16 hm03bC hputC hrng25 hput25 hm03bA hputA hcreate htrnx ⊢
          refine eq_ok_of_wp ?_
          rw [cbstm03a.run_loop1.body]
          aeneas_wp [Array.to_slice_mut, Nat.reduceEqDiff, Bool.false_eq_true, not_false_eq_true, prod_casesOn_mk,
            show Array.make 8#usize [88#u8, 82#u8, 69#u8, 70#u8, 70#u8, 73#u8, 76#u8, 69#u8] = ddXrefArr from rfl,
            show Array.make 8#usize [67#u8, 85#u8, 83#u8, 84#u8, 70#u8, 73#u8, 76#u8, 69#u8] = ddCustArr from rfl,
            show Array.make 8#usize [65#u8, 67#u8, 67#u8, 84#u8, 70#u8, 73#u8, 76#u8, 69#u8] = ddAcctArr from rfl,
            hsetX, hm03bX, heqX, hrngX, hputX,
            hsetC, hrng16, hput16, hm03bC, heqC, hrngC, hputC,
            hsetA, hrng25, hput25, hm03bA, heqA, hrngA, hputA, hcreate, htrnx]
        rw [run_loop1_step hbody]
        have hxs' : xs = vals2.drop (idx + 1) := by
          have hd : vals2.drop idx = x :: xs := hxs.symm
          rw [← List.tail_drop, hd]; rfl
        have hstmt_len' : c10'.stmt.val.length ≤ 519 * (idx + 1) := by
          have hl := congrArg List.length hstmt'
          simp only [length_linesOfVec, List.length_append, hs10, hs6, hs2] at hl
          have hms := length_modelStmtOf_le hD (strOf (x.getD 0 default)) cval aval
          omega
        have hhtml_len' : c10'.html.val.length ≤ 5564 * (idx + 1) := by
          have hl := congrArg List.length hhtml'
          simp only [length_linesOfVec, List.length_append, hh10, hh6, hh2] at hl
          have hmh := length_modelHtmlOf_le hD (strOf (x.getD 0 default)) cval aval
          omega
        obtain ⟨c', ok2, hrec, hd_fin, hs_fin, hh_fin, ha_fin, hok_fin⟩ :=
          run_loop1_spec D hv2 hv3 hv4 hD xs (idx + 1) (by simp at hlen; omega) hxs'
            c10' st2 trnx_rec1 xref_rec1 cust_rec2 acct_rec1
            (by rw [hpos', hpos10, hpos6, hpos2])
            (by rw [heof', heof10, heof6, heof2])
            (by rw [hd', hd10, hd6, hd2, hdisp])
            (by rw [hab', ha10, ha6, ha2, hab])
            hstmt_len' hhtml_len'
        rw [hstmt', hs10, hs6, hs2, hhtml', hh10, hh6, hh2] at hd_fin hs_fin hh_fin ha_fin hok_fin
        exact ⟨c', ok2, hrec, hd_fin, hs_fin, hh_fin, ha_fin, hok_fin⟩

/-! ## 6. Entry point `cbstm03a.run` (`run_spec_of`) -/

def initCtx0 : cbstm03a.Ctx :=
  { displays := alloc.vec.Vec.new (alloc.vec.Vec U8)
    stmt := alloc.vec.Vec.new (alloc.vec.Vec U8)
    html := alloc.vec.Vec.new (alloc.vec.Vec U8)
    abended := false
    trnx_pos := 0#usize
    trnx_eof := false
    trnx_status := Array.repeat 2#usize 32#u8
    xref_pos := 0#usize
    xref_eof := false
    xref_status := Array.repeat 2#usize 32#u8
    cust_status := Array.repeat 2#usize 32#u8
    acct_status := Array.repeat 2#usize 32#u8
    m_dd := Array.repeat 8#usize 32#u8
    m_oper := 32#u8
    m_rc := Array.repeat 2#usize 32#u8
    m_key := Array.repeat 25#usize 32#u8
    m_key_ln := 0#i64
    m_fldt := Array.repeat 1000#usize 32#u8 }

def initMem0 : cbstm03a.Mem :=
  { offs := alloc.vec.Vec.new Std.I64
    starts := alloc.vec.Vec.new Usize
    lens := alloc.vec.Vec.new Usize
    bytes := alloc.vec.Vec.new U8 }

def initSt0 : cbstm03a.St :=
  { «name» := Array.repeat 75#usize 32#u8
    add1 := Array.repeat 50#usize 32#u8
    add2 := Array.repeat 50#usize 32#u8
    add3 := Array.repeat 80#usize 32#u8
    acct_id := Array.repeat 20#usize 32#u8
    curr_bal := Array.repeat 13#usize 32#u8
    fico := Array.repeat 20#usize 32#u8
    tranid := Array.repeat 16#usize 32#u8
    trandt := Array.repeat 49#usize 32#u8
    tranamt := Array.repeat 13#usize 32#u8
    total_tramt := Array.repeat 13#usize 32#u8 }

set_option maxRecDepth 20000 in
theorem run_eq_of_parts
    {trnx_file : Slice cbstm03a.TrnxRecord}
    {xref_file : Slice cbstm03a.CardXrefRecord} {cust_file : Slice cbstm03a.CustomerRecord}
    {acct_file : Slice cbstm03a.AccountRecord}
    {vals1 vals2 vals3 vals4 : List (List FVal)}
    {tbl : Array U8 256#usize}
    {c c1 c2 c3 c4 c5 : cbstm03a.Ctx}
    {mem mem1 : cbstm03a.Mem}
    {s4 s7 : Slice U8}
    {trnx_rec2 : Array U8 350#usize} {cr_cnt tr_cnt : Std.I64}
    (htbl : cbstm03a.lat2ebc_table = .ok tbl)
    (hop1 : ∀ msg : Slice U8,
      cbstm03a.open_file initCtx0 ddTrnxArr.to_slice msg trnx_file xref_file cust_file acct_file =
        .ok (true, c))
    (hm0 : cbstm03a.call_m03b { c with m_oper := 82#u8, m_fldt := Array.repeat 1000#usize 32#u8 }
      trnx_file xref_file cust_file acct_file = .ok c1)
    (hrc1 : cbstm03a.rc_ok c1 = .ok true)
    (hp350 : ∀ s : Slice U8, s.val = (c1.m_fldt.val.drop 0).take 350 →
      cbstm03a.put (Array.repeat 350#usize 32#u8).to_slice 0#usize 350#usize s = .ok s4)
    (hp16 : ∀ s : Slice U8, s.val = (((Array.repeat 350#usize 32#u8).from_slice s4).val.drop 0).take 16 →
      cbstm03a.put (Array.repeat 16#usize 32#u8).to_slice 0#usize 16#usize s = .ok s7)
    (hl0 : cbstm03a.run_loop0 trnx_file xref_file cust_file acct_file c1 initMem0
      ((Array.repeat 350#usize 32#u8).from_slice s4)
      ((Array.repeat 16#usize 32#u8).from_slice s7) 1#i64 0#i64 true true =
      .ok (c2, mem, trnx_rec2, cr_cnt, tr_cnt, true))
    (hwtrct : cbstm03a.write_trct mem cr_cnt tr_cnt = .ok mem1)
    (hop2 : ∀ msg : Slice U8,
      cbstm03a.open_file c2 ddXrefArr.to_slice msg trnx_file xref_file cust_file acct_file = .ok (true, c3))
    (hop3 : ∀ msg : Slice U8,
      cbstm03a.open_file c3 ddCustArr.to_slice msg trnx_file xref_file cust_file acct_file = .ok (true, c4))
    (hop4 : ∀ msg : Slice U8,
      cbstm03a.open_file c4 ddAcctArr.to_slice msg trnx_file xref_file cust_file acct_file = .ok (true, c5))
    (hc5_pos : c5.xref_pos.val = 0) (hc5_eof : c5.xref_eof = false)
    (hc5_disp : c5.displays.val = []) (hc5_ab : c5.abended = false)
    (hc5_stmt : c5.stmt.val = []) (hc5_html : c5.html.val = [])
    (hcl : ∀ (c0 : cbstm03a.Ctx) (dd msg : Slice U8),
      dd.val = ddTrnxArr.val ∨ dd.val = ddXrefArr.val ∨ dd.val = ddCustArr.val ∨ dd.val = ddAcctArr.val →
      ∃ c0', cbstm03a.close_file c0 dd msg trnx_file xref_file cust_file acct_file = .ok (true, c0') ∧
        c0'.displays = c0.displays ∧ c0'.stmt = c0.stmt ∧ c0'.html = c0.html ∧ c0'.abended = c0.abended)
    (D : MainlineDeps trnx_file xref_file cust_file acct_file vals1 vals2 vals3 vals4 tbl mem1 cr_cnt)
    (hv2 : ∀ v ∈ vals2, CardXrefRecord.Valid v)
    (hv3 : ∀ v ∈ vals3, CustomerRecord.Valid v)
    (hv4 : ∀ v ∈ vals4, AccountRecord.Valid v)
    (hD : EquivLean.Modernize.Cbstm03a.Domain vals1 vals2 vals3 vals4) :
    let o := EquivLean.Modernize.Cbstm03a.Model.run vals1 vals2 vals3 vals4
    ∃ out, cbstm03a.run trnx_file xref_file cust_file acct_file = .ok out ∧
      out.displays.val.map (fun l => l.val.map (·.val)) = o.disp ∧
      out.stmt_file_writes.val.map (fun l => l.val.map (·.val)) = o.stmtWrites ∧
      out.html_file_writes.val.map (fun l => l.val.map (·.val)) = o.htmlWrites ∧
      out.abended = o.abended := by
  have hrng350 := array_index_range c1.m_fldt 0#usize 350#usize (by decide) (by decide)
  let trnx_rec1 := (Array.repeat 350#usize 32#u8).from_slice s4
  have hrng16 := array_index_range trnx_rec1 0#usize 16#usize (by decide) (by decide)
  have hp350' := hp350 (Slice.from ((c1.m_fldt.val.drop 0).take 350) (by simp; scalar_tac)) (by simp)
  have hp16' := hp16 (Slice.from ((trnx_rec1.val.drop 0).take 16) (by simp; scalar_tac)) (by simp [trnx_rec1])
  simp only [trnx_rec1, UScalar.ofNatCore_val_eq, Nat.sub_zero] at hrng350 hrng16 hp16'
  obtain ⟨c6, ok2, hloop1, hd6, hs6, hh6, ha6, hok2⟩ :=
    run_loop1_spec D hv2 hv3 hv4 hD vals2 0 (by simp) (by simp)
      c5 initSt0 trnx_rec2 (Array.repeat 50#usize 32#u8)
      (Array.repeat 500#usize 32#u8) (Array.repeat 300#usize 32#u8)
      hc5_pos hc5_eof hc5_disp hc5_ab (by simp [hc5_stmt]) (by simp [hc5_html])
  have hst5 : linesOfVec c5.stmt = [] := by simp [linesOfVec, hc5_stmt]
  have hht5 : linesOfVec c5.html = [] := by simp [linesOfVec, hc5_html]
  rw [hst5, hht5] at hd6 hs6 hh6 ha6 hok2
  have hopen1 := hop1 (Array.make 22#usize [69#u8, 82#u8, 82#u8, 79#u8, 82#u8, 32#u8, 79#u8, 80#u8, 69#u8, 78#u8,
    73#u8, 78#u8, 71#u8, 32#u8, 84#u8, 82#u8, 78#u8, 88#u8, 70#u8, 73#u8, 76#u8, 69#u8]).to_slice
  have hopen2 := hop2 (Array.make 22#usize [69#u8, 82#u8, 82#u8, 79#u8, 82#u8, 32#u8, 79#u8, 80#u8, 69#u8, 78#u8,
    73#u8, 78#u8, 71#u8, 32#u8, 88#u8, 82#u8, 69#u8, 70#u8, 70#u8, 73#u8, 76#u8, 69#u8]).to_slice
  have hopen3 := hop3 (Array.make 22#usize [69#u8, 82#u8, 82#u8, 79#u8, 82#u8, 32#u8, 79#u8, 80#u8, 69#u8, 78#u8,
    73#u8, 78#u8, 71#u8, 32#u8, 67#u8, 85#u8, 83#u8, 84#u8, 70#u8, 73#u8, 76#u8, 69#u8]).to_slice
  have hopen4 := hop4 (Array.make 22#usize [69#u8, 82#u8, 82#u8, 79#u8, 82#u8, 32#u8, 79#u8, 80#u8, 69#u8, 78#u8,
    73#u8, 78#u8, 71#u8, 32#u8, 65#u8, 67#u8, 67#u8, 84#u8, 70#u8, 73#u8, 76#u8, 69#u8]).to_slice
  simp only [initCtx0, initMem0, initSt0] at hopen1 hl0 hloop1
  cases ok2 with
  | false =>
    refine ⟨{ displays := c6.displays, stmt_file_writes := c6.stmt, html_file_writes := c6.html, abended := c6.abended },
      ?_, hd6, hs6, hh6, ha6⟩
    refine eq_ok_of_wp ?_
    rw [cbstm03a.run]
    aeneas_wp [Array.to_slice_mut, Bool.false_eq_true, prod_casesOn_mk, initCtx0, initMem0, initSt0,
      show Array.make 8#usize [84#u8, 82#u8, 78#u8, 88#u8, 70#u8, 73#u8, 76#u8, 69#u8] = ddTrnxArr from rfl,
      show Array.make 8#usize [88#u8, 82#u8, 69#u8, 70#u8, 70#u8, 73#u8, 76#u8, 69#u8] = ddXrefArr from rfl,
      show Array.make 8#usize [67#u8, 85#u8, 83#u8, 84#u8, 70#u8, 73#u8, 76#u8, 69#u8] = ddCustArr from rfl,
      show Array.make 8#usize [65#u8, 67#u8, 67#u8, 84#u8, 70#u8, 73#u8, 76#u8, 69#u8] = ddAcctArr from rfl,
      htbl, hopen1, hm0, hrc1, hrng350, hp350', hrng16, hp16', hl0, hwtrct,
      hopen2, hopen3, hopen4, hloop1, finish_eq]
  | true =>
    obtain ⟨c7, hcl1, hd7, hs7, hh7, ha7⟩ := hcl c6 ddTrnxArr.to_slice
      (Array.make 22#usize [69#u8, 82#u8, 82#u8, 79#u8, 82#u8, 32#u8, 67#u8, 76#u8, 79#u8, 83#u8,
        73#u8, 78#u8, 71#u8, 32#u8, 84#u8, 82#u8, 78#u8, 88#u8, 70#u8, 73#u8, 76#u8, 69#u8]).to_slice
      (Or.inl rfl)
    obtain ⟨c8, hcl2, hd8, hs8, hh8, ha8⟩ := hcl c7 ddXrefArr.to_slice
      (Array.make 22#usize [69#u8, 82#u8, 82#u8, 79#u8, 82#u8, 32#u8, 67#u8, 76#u8, 79#u8, 83#u8,
        73#u8, 78#u8, 71#u8, 32#u8, 88#u8, 82#u8, 69#u8, 70#u8, 70#u8, 73#u8, 76#u8, 69#u8]).to_slice
      (Or.inr (Or.inl rfl))
    obtain ⟨c9, hcl3, hd9, hs9, hh9, ha9⟩ := hcl c8 ddCustArr.to_slice
      (Array.make 22#usize [69#u8, 82#u8, 82#u8, 79#u8, 82#u8, 32#u8, 67#u8, 76#u8, 79#u8, 83#u8,
        73#u8, 78#u8, 71#u8, 32#u8, 67#u8, 85#u8, 83#u8, 84#u8, 70#u8, 73#u8, 76#u8, 69#u8]).to_slice
      (Or.inr (Or.inr (Or.inl rfl)))
    obtain ⟨c10, hcl4, hd10, hs10, hh10, ha10⟩ := hcl c9 ddAcctArr.to_slice
      (Array.make 22#usize [69#u8, 82#u8, 82#u8, 79#u8, 82#u8, 32#u8, 67#u8, 76#u8, 79#u8, 83#u8,
        73#u8, 78#u8, 71#u8, 32#u8, 65#u8, 67#u8, 67#u8, 84#u8, 70#u8, 73#u8, 76#u8, 69#u8]).to_slice
      (Or.inr (Or.inr (Or.inr rfl)))
    refine ⟨{ displays := c10.displays, stmt_file_writes := c10.stmt, html_file_writes := c10.html, abended := c10.abended },
      ?_, ?_, ?_, ?_, ?_⟩
    · refine eq_ok_of_wp ?_
      rw [cbstm03a.run]
      aeneas_wp [Array.to_slice_mut, prod_casesOn_mk, initCtx0, initMem0, initSt0,
        show Array.make 8#usize [84#u8, 82#u8, 78#u8, 88#u8, 70#u8, 73#u8, 76#u8, 69#u8] = ddTrnxArr from rfl,
        show Array.make 8#usize [88#u8, 82#u8, 69#u8, 70#u8, 70#u8, 73#u8, 76#u8, 69#u8] = ddXrefArr from rfl,
        show Array.make 8#usize [67#u8, 85#u8, 83#u8, 84#u8, 70#u8, 73#u8, 76#u8, 69#u8] = ddCustArr from rfl,
        show Array.make 8#usize [65#u8, 67#u8, 67#u8, 84#u8, 70#u8, 73#u8, 76#u8, 69#u8] = ddAcctArr from rfl,
        htbl, hopen1, hm0, hrc1, hrng350, hp350', hrng16, hp16', hl0, hwtrct,
        hopen2, hopen3, hopen4, hloop1, hcl1, hcl2, hcl3, hcl4, finish_eq]
    · show linesOfVec c10.displays = _; rw [hd10, hd9, hd8, hd7, hd6]; rfl
    · show linesOfVec c10.stmt = _; rw [hs10, hs9, hs8, hs7, hs6]; rfl
    · show linesOfVec c10.html = _; rw [hh10, hh9, hh8, hh7, hh6]; rfl
    · rw [ha10, ha9, ha8, ha7, ha6]; rfl

end EquivLean.Modernize.Cbstm03a.Rust.ML
