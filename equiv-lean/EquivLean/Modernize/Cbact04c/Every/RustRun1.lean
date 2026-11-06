import EquivLean.Modernize.Cbact04c.RustRun
import EquivLean.Modernize.Cbact04c.ModelEvery

/-!
# CBACT04C → Rust on every input: the messages of the error paths, the model's state

* the error messages (`m_acct_not_found` …), `status_line` for status 23, `abend`;
* the every-input model's state `Model.StE` against the success model's `Model.St` (`toSt`,
  `ofSt`): the success paths are those of `Model.step`;
* the lookups on the field values (`findAcctO` …) from the Rust searches.
-/

open Aeneas Aeneas.Std EquivLean EquivLean.Aeneas
open Cobol EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbact04c.Rust

/-! ## The messages -/

theorem msg_le (l : List U8) (h : l.length ≤ 100) : l.length ≤ Usize.max := by
  have := usize_max_ge; omega

def notFoundBytes : List U8 := [65#u8, 67#u8, 67#u8, 79#u8, 85#u8, 78#u8, 84#u8, 32#u8, 78#u8,
  79#u8, 84#u8, 32#u8, 70#u8, 79#u8, 85#u8, 78#u8, 68#u8, 58#u8, 32#u8]
def errAcctBytes : List U8 := [69#u8, 82#u8, 82#u8, 79#u8, 82#u8, 32#u8, 82#u8, 69#u8, 65#u8,
  68#u8, 73#u8, 78#u8, 71#u8, 32#u8, 65#u8, 67#u8, 67#u8, 79#u8, 85#u8, 78#u8, 84#u8, 32#u8, 70#u8,
  73#u8, 76#u8, 69#u8]
def errXrefBytes : List U8 := [69#u8, 82#u8, 82#u8, 79#u8, 82#u8, 32#u8, 82#u8, 69#u8, 65#u8,
  68#u8, 73#u8, 78#u8, 71#u8, 32#u8, 88#u8, 82#u8, 69#u8, 70#u8, 32#u8, 70#u8, 73#u8, 76#u8, 69#u8]
def missingBytes : List U8 := [68#u8, 73#u8, 83#u8, 67#u8, 76#u8, 79#u8, 83#u8, 85#u8, 82#u8,
  69#u8, 32#u8, 71#u8, 82#u8, 79#u8, 85#u8, 80#u8, 32#u8, 82#u8, 69#u8, 67#u8, 79#u8, 82#u8, 68#u8,
  32#u8, 77#u8, 73#u8, 83#u8, 83#u8, 73#u8, 78#u8, 71#u8]
def tryDefaultBytes : List U8 := [84#u8, 82#u8, 89#u8, 32#u8, 87#u8, 73#u8, 84#u8, 72#u8, 32#u8,
  68#u8, 69#u8, 70#u8, 65#u8, 85#u8, 76#u8, 84#u8, 32#u8, 71#u8, 82#u8, 79#u8, 85#u8, 80#u8, 32#u8,
  67#u8, 79#u8, 68#u8, 69#u8]
def errDefaultBytes : List U8 := [69#u8, 82#u8, 82#u8, 79#u8, 82#u8, 32#u8, 82#u8, 69#u8, 65#u8,
  68#u8, 73#u8, 78#u8, 71#u8, 32#u8, 68#u8, 69#u8, 70#u8, 65#u8, 85#u8, 76#u8, 84#u8, 32#u8, 68#u8,
  73#u8, 83#u8, 67#u8, 76#u8, 79#u8, 83#u8, 85#u8, 82#u8, 69#u8, 32#u8, 71#u8, 82#u8, 79#u8, 85#u8,
  80#u8]
def abendingBytes : List U8 := [65#u8, 66#u8, 69#u8, 78#u8, 68#u8, 73#u8, 78#u8, 71#u8, 32#u8,
  80#u8, 82#u8, 79#u8, 71#u8, 82#u8, 65#u8, 77#u8]
def fileStatusBytes : List U8 := [70#u8, 73#u8, 76#u8, 69#u8, 32#u8, 83#u8, 84#u8, 65#u8, 84#u8,
  85#u8, 83#u8, 32#u8, 73#u8, 83#u8, 58#u8, 32#u8, 78#u8, 78#u8, 78#u8, 78#u8]
/-- `FILE STATUS IS: NNNN0023`. -/
def status23Bytes : List U8 := fileStatusBytes ++ [48#u8, 48#u8, 50#u8, 51#u8]

theorem m_acct_not_found_eq :
    cbact04c_t.m_acct_not_found = .ok (alloc.vec.Vec.from notFoundBytes (msg_le _ (by decide))) := by
  simp only [cbact04c_t.m_acct_not_found, lift, Std.Array.to_slice, bind_ok, to_vec_eq]; rfl
theorem m_err_read_acct_eq :
    cbact04c_t.m_err_read_acct = .ok (alloc.vec.Vec.from errAcctBytes (msg_le _ (by decide))) := by
  simp only [cbact04c_t.m_err_read_acct, lift, Std.Array.to_slice, bind_ok, to_vec_eq]; rfl
theorem m_err_read_xref_eq :
    cbact04c_t.m_err_read_xref = .ok (alloc.vec.Vec.from errXrefBytes (msg_le _ (by decide))) := by
  simp only [cbact04c_t.m_err_read_xref, lift, Std.Array.to_slice, bind_ok, to_vec_eq]; rfl
theorem m_disc_missing_eq :
    cbact04c_t.m_disc_missing = .ok (alloc.vec.Vec.from missingBytes (msg_le _ (by decide))) := by
  simp only [cbact04c_t.m_disc_missing, lift, Std.Array.to_slice, bind_ok, to_vec_eq]; rfl
theorem m_try_default_eq :
    cbact04c_t.m_try_default = .ok (alloc.vec.Vec.from tryDefaultBytes (msg_le _ (by decide))) := by
  simp only [cbact04c_t.m_try_default, lift, Std.Array.to_slice, bind_ok, to_vec_eq]; rfl
theorem m_err_default_disc_eq :
    cbact04c_t.m_err_default_disc = .ok (alloc.vec.Vec.from errDefaultBytes (msg_le _ (by decide))) := by
  simp only [cbact04c_t.m_err_default_disc, lift, Std.Array.to_slice, bind_ok, to_vec_eq]; rfl
theorem m_abending_eq :
    cbact04c_t.m_abending = .ok (alloc.vec.Vec.from abendingBytes (msg_le _ (by decide))) := by
  simp only [cbact04c_t.m_abending, lift, Std.Array.to_slice, bind_ok, to_vec_eq]; rfl
theorem m_file_status_eq :
    cbact04c_t.m_file_status = .ok (alloc.vec.Vec.from fileStatusBytes (msg_le _ (by decide))) := by
  simp only [cbact04c_t.m_file_status, lift, Std.Array.to_slice, bind_ok, to_vec_eq]; rfl

theorem notFound_text : notFoundBytes.map UScalar.val = Model.txt "ACCOUNT NOT FOUND: " := by
  decide +kernel
theorem errAcct_text : errAcctBytes.map UScalar.val = Model.txt "ERROR READING ACCOUNT FILE" := by
  decide +kernel
theorem errXref_text : errXrefBytes.map UScalar.val = Model.txt "ERROR READING XREF FILE" := by
  decide +kernel
theorem missing_text : missingBytes.map UScalar.val = Model.txt "DISCLOSURE GROUP RECORD MISSING" := by
  decide +kernel
theorem tryDefault_text : tryDefaultBytes.map UScalar.val = Model.txt "TRY WITH DEFAULT GROUP CODE" := by
  decide +kernel
theorem errDefault_text :
    errDefaultBytes.map UScalar.val = Model.txt "ERROR READING DEFAULT DISCLOSURE GROUP" := by
  decide +kernel
theorem abending_text : abendingBytes.map UScalar.val = Model.txt "ABENDING PROGRAM" := by
  decide +kernel
theorem status23_text : status23Bytes.map UScalar.val = Model.txt "FILE STATUS IS: NNNN0023" := by
  decide +kernel

set_option maxHeartbeats 1000000 in
theorem status_line_23 :
    cbact04c_t.status_line 50#u8 51#u8 = .ok (alloc.vec.Vec.from status23Bytes (msg_le _ (by decide))) := by
  have hm := usize_max_ge
  have hfl : fileStatusBytes.length = 20 := rfl
  refine eq_ok_of_wp' ?_
  simp only [cbact04c_t.status_line, cbact04c_t.is_digit, m_file_status_eq]
  aeneas_wp [usz_lit_val]
  simp (disch := omega) only [hfl, dite_eq_left, ite_eq_left, dite_eq_right, ite_eq_right,
    List.length_append, List.length_cons, List.length_nil, alloc.vec.Vec.from_val]
  rfl

/-- `9999-ABEND-PROGRAM` after a status-23 read: the message, the status line, `ABENDING PROGRAM`. -/
theorem abend_eq (out : cbact04c_t.Output) (msg : alloc.vec.Vec U8)
    (h : out.displays.val.length + 3 < Usize.max) :
    cbact04c_t.abend out msg 50#u8 51#u8 = .ok { out with
      displays := alloc.vec.Vec.from (out.displays.val ++ [msg,
        alloc.vec.Vec.from status23Bytes (msg_le _ (by decide)),
        alloc.vec.Vec.from abendingBytes (msg_le _ (by decide))]) (by simp; omega),
      abended := true } := by
  refine eq_ok_of_wp' ?_
  simp only [cbact04c_t.abend, status_line_23, m_abending_eq]
  aeneas_wp []
  simp (disch := omega) only [dite_eq_left, List.length_append, List.length_cons, List.length_nil,
    alloc.vec.Vec.from_val]
  simp only [Except.ok.injEq, List.append_assoc, List.cons_append, List.nil_append]

/-! ## The every-input model's state and the success model's -/

def toSt (s : Model.StE) : Model.St :=
  ⟨s.accts, s.lastId, s.acct, s.xref, s.total, s.k, s.disp, s.writes, s.rewrites⟩

def ofSt (s : Model.St) (b : Bool) : Model.StE :=
  ⟨s.accts, s.lastId, s.acct, s.xref, s.total, s.k, s.disp, s.writes, s.rewrites, b⟩

@[simp] theorem toSt_ofSt (s : Model.St) (b : Bool) : toSt (ofSt s b) = s := rfl
@[simp] theorem ofSt_stop (s : Model.St) (b : Bool) : (ofSt s b).stop = b := rfl

/-- The interest part at rate `r` (`Model.StE.interest` on the success model's state). -/
def mpostR (r : Int) (p c : List UInt8) (t : List FVal) (s2 : Model.St) : Model.St :=
  if r = 0 then s2
  else
    let amt := Int.tmod (Int.tdiv (Model.tBal t * r) 120000) (10 ^ 11)
    { s2 with total := Int.tmod (s2.total + amt) (10 ^ 11), k := (s2.k + 1) % 1000000,
              writes := s2.writes ++ [Model.tranVals p c ((s2.k + 1) % 1000000) (Model.aId s2.acct)
                (Model.xCard s2.xref) amt] }

theorem interest_ofSt (p c : List UInt8) (s2 : Model.St) (t : List FVal) (r : Int) :
    (ofSt s2 false).interest p c t r = ofSt (mpostR r p c t s2) false := by
  unfold Model.StE.interest mpostR
  split_ifs <;> rfl

theorem mpost_eq (dv : List (List FVal)) (p c : List UInt8) (t : List FVal) (s2 : Model.St) :
    mpost dv p c t s2 =
      mpostR (Model.findRate dv (Model.aGrp s2.acct) (Model.tType t) (Model.tCat t)) p c t s2 := rfl

/-! ## The lookups on the field values, from the Rust searches -/

theorem find_map_dite {α β : Type _} (f : α → β) (q : β → Bool) (p : α → Bool) (hp : q ∘ f = p)
    (l : List α) :
    (l.map f).find? q = if h : l.findIdx p < l.length then some (f l[l.findIdx p]) else none := by
  subst hp
  rw [List.find?_map, List.find?_eq_getElem?_findIdx]
  split_ifs with h
  · rw [List.getElem?_eq_getElem h]; rfl
  · rw [List.getElem?_eq_none (by omega)]; rfl

theorem findAcctO_eq (l : List cbact04c_t.AccountRecord) (id : Int) :
    Model.findAcctO (l.map AccountRecord.vals) id =
      if h : l.findIdx (fun r => r.acct_id.val == id) < l.length then
        some (AccountRecord.vals l[l.findIdx (fun r => r.acct_id.val == id)]) else none :=
  find_map_dite _ _ _ (acctKey_comp id) l

theorem findXrefO_eq (l : List cbact04c_t.CardXrefRecord) (id : Int) :
    Model.findXrefO (l.map CardXrefRecord.vals) id =
      if h : l.findIdx (fun r => r.xref_acct_id.val == id) < l.length then
        some (CardXrefRecord.vals l[l.findIdx (fun r => r.xref_acct_id.val == id)]) else none :=
  find_map_dite _ _ _ (xrefKey_comp id) l

theorem findRateO_eq (l : List cbact04c_t.DisGroupRecord) (group : Std.Array U8 10#usize)
    (typ : Std.Array U8 2#usize) (cat : I64) :
    Model.findRateO (l.map DisGroupRecord.vals) (group.val.map ebc) (typ.val.map ebc) cat.val =
      if h : l.findIdx (discKey group typ cat) < l.length then
        some (l[l.findIdx (discKey group typ cat)]).dis_int_rate.val else none := by
  unfold Model.findRateO
  rw [find_map_dite _ _ _ (discKey_comp group typ cat) l]
  split_ifs <;> rfl

/-- The default group (`DEFAULT   `, Latin-1) as the Rust code writes it. -/
def defR : Std.Array U8 10#usize :=
  Std.Array.make 10#usize [68#u8, 69#u8, 70#u8, 65#u8, 85#u8, 76#u8, 84#u8, 32#u8, 32#u8, 32#u8]

theorem defR_ebc : defR.val.map ebc = Model.defaultGrp := by decide +kernel

end EquivLean.Modernize.Cbact04c.Rust

/-!
# CBACT04C → Rust on every input: the every-input model's step, case by case
-/

open Aeneas Aeneas.Std EquivLean EquivLean.Aeneas
open Cobol EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbact04c.Rust

/-! ## The rate part -/

theorem rate_direct (dv : List (List FVal)) (p c : List UInt8) (s : Model.St) (t : List FVal)
    (r : Int) (h : Model.findRateO dv (Model.aGrp s.acct) (Model.tType t) (Model.tCat t) = some r) :
    (ofSt s false).rate dv p c t = ofSt (mpostR r p c t s) false := by
  have e : (ofSt s false).acct = s.acct := rfl
  unfold Model.StE.rate
  rw [e, h]
  exact interest_ofSt p c s t r

/-- The two lines of a missing disclosure group. -/
def dfltLines : List (List Nat) :=
  [Model.txt "DISCLOSURE GROUP RECORD MISSING", Model.txt "TRY WITH DEFAULT GROUP CODE"]

theorem rate_dflt (dv : List (List FVal)) (p c : List UInt8) (s : Model.St) (t : List FVal)
    (r : Int) (h1 : Model.findRateO dv (Model.aGrp s.acct) (Model.tType t) (Model.tCat t) = none)
    (h2 : Model.findRateO dv Model.defaultGrp (Model.tType t) (Model.tCat t) = some r) :
    (ofSt s false).rate dv p c t =
      ofSt (mpostR r p c t { s with disp := s.disp ++ dfltLines }) false := by
  have e : (ofSt s false).acct = s.acct := rfl
  unfold Model.StE.rate
  rw [e, h1]
  dsimp only
  rw [h2]
  exact interest_ofSt p c { s with disp := s.disp ++ dfltLines } t r

theorem rate_dmiss (dv : List (List FVal)) (p c : List UInt8) (s : Model.St) (t : List FVal)
    (h1 : Model.findRateO dv (Model.aGrp s.acct) (Model.tType t) (Model.tCat t) = none)
    (h2 : Model.findRateO dv Model.defaultGrp (Model.tType t) (Model.tCat t) = none) :
    (ofSt s false).rate dv p c t =
      (ofSt { s with disp := s.disp ++ dfltLines } false).abend
        [Model.txt "ERROR READING DEFAULT DISCLOSURE GROUP"] := by
  have e : (ofSt s false).acct = s.acct := rfl
  unfold Model.StE.rate
  rw [e, h1]
  dsimp only
  rw [h2]
  rfl

/-! ## The account part -/

theorem stepE_same (xr dv : List (List FVal)) (p c : List UInt8) (s : Model.St) (t : List FVal)
    (h : s.lastId = some (Model.tAcct t)) :
    Model.stepE xr dv p c (ofSt s false) t =
      (ofSt { s with disp := s.disp ++ [Model.TranCatBalRecord.textS t] } false).rate dv p c t := by
  have e : (ofSt s false).lastId = s.lastId := rfl
  unfold Model.stepE
  simp only [ofSt_stop, Bool.false_eq_true, _root_.ite_false]
  rw [ite_eq_left (by exact h)]
  rfl

/-- The line of a missing account or cross-reference. -/
def nfLine (id : Int) : List Nat := Model.txt "ACCOUNT NOT FOUND: " ++ zpad 11 id.natAbs

/-- The state after the account part of a new account's first record: the record's line and, when
there was a previous account, its rewrite. -/
def preAcct (s : Model.St) (t : List FVal) : Model.St :=
  if s.lastId.isSome then
    { s with disp := s.disp ++ [Model.TranCatBalRecord.textS t],
             accts := Model.replaceFirst (fun a => Model.aId a == Model.aId s.acct)
               (Model.posted s.acct s.total) s.accts,
             rewrites := s.rewrites ++ [Model.posted s.acct s.total] }
  else { s with disp := s.disp ++ [Model.TranCatBalRecord.textS t] }

/-- The state once the new account and its cross-reference are read. -/
def withAcct (s : Model.St) (t : List FVal) (a x : List FVal) : Model.St :=
  { s with lastId := some (Model.tAcct t), total := 0, acct := a, xref := x }

theorem stepE_new (xr dv : List (List FVal)) (p c : List UInt8) (s : Model.St) (t : List FVal)
    (h : s.lastId ≠ some (Model.tAcct t)) :
    Model.stepE xr dv p c (ofSt s false) t =
      match Model.findAcctO (preAcct s t).accts (Model.tAcct t) with
      | none => (ofSt (preAcct s t) false).abend [nfLine (Model.tAcct t),
          Model.txt "ERROR READING ACCOUNT FILE"]
      | some a =>
        match Model.findXrefO xr (Model.tAcct t) with
        | none => (ofSt (preAcct s t) false).abend [nfLine (Model.tAcct t),
            Model.txt "ERROR READING XREF FILE"]
        | some x => (ofSt (withAcct (preAcct s t) t a x) false).rate dv p c t := by
  unfold Model.stepE
  simp only [ofSt_stop, Bool.false_eq_true, _root_.ite_false]
  rw [ite_eq_right (by exact h)]
  unfold preAcct withAcct
  by_cases hs : s.lastId.isSome
  · simp only [ofSt, hs, _root_.ite_true, nfLine]
    rfl
  · simp only [ofSt, hs, Bool.false_eq_true, _root_.ite_false, nfLine]
    rfl

end EquivLean.Modernize.Cbact04c.Rust

/-!
# CBACT04C → Rust on every input: `process_record` on the same account, the `DEFAULT` group
-/

open Aeneas Aeneas.Std EquivLean EquivLean.Aeneas
open Cobol EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbact04c.Rust

/-- The outputs after an abend against the every-input model's state. -/
structure ORel (out : cbact04c_t.Output) (s : Model.StE) : Prop where
  disp : out.displays.val.map (fun l => l.val.map (·.val)) = s.disp
  writes : out.transact_file_writes.val.map TranRecord.vals = s.writes
  rewrites : out.account_file_rewrites.val.map AccountRecord.vals = s.rewrites
  abended : out.abended = s.stop

/-- Lines displayed: the relation with the lines appended. -/
theorem srel_lines (st : cbact04c_t.State) (out out' : cbact04c_t.Output) (s : Model.St)
    (hrel : SRel st out s) (lines : List (List Nat))
    (hd : out'.displays.val.map (fun l => l.val.map (·.val)) =
      out.displays.val.map (fun l => l.val.map (·.val)) ++ lines)
    (hw : out'.transact_file_writes = out.transact_file_writes)
    (hr : out'.account_file_rewrites = out.account_file_rewrites) (ha : out'.abended = out.abended) :
    SRel st out' { s with disp := s.disp ++ lines } := by
  refine ⟨?_, ?_, ?_, ?_, hrel.accts, hrel.set, hrel.first, hrel.last, hrel.acct, hrel.xref, hrel.total,
    hrel.k, hrel.desc, hrel.fill⟩
  · rw [hd, hrel.disp]
  · rw [hw, hrel.writes]
  · rw [hr, hrel.rewrites]
  · rw [ha, hrel.abended]

/-- After an abend: the outputs against the model's abended state. -/
theorem orel_abend (st : cbact04c_t.State) (out out' : cbact04c_t.Output) (s : Model.St)
    (hrel : SRel st out s) (lines : List (List Nat))
    (hd : out'.displays.val.map (fun l => l.val.map (·.val)) =
      out.displays.val.map (fun l => l.val.map (·.val)) ++ lines ++
        [Model.txt "FILE STATUS IS: NNNN0023", Model.txt "ABENDING PROGRAM"])
    (hw : out'.transact_file_writes = out.transact_file_writes)
    (hr : out'.account_file_rewrites = out.account_file_rewrites) (ha : out'.abended = true) :
    ORel out' ((ofSt s false).abend lines) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hd, hrel.disp]; rfl
  · rw [hw, hrel.writes]; rfl
  · rw [hr, hrel.rewrites]; rfl
  · rw [ha]; rfl

theorem vec_text (l : List U8) (h : l.length ≤ Usize.max) :
    (alloc.vec.Vec.from l h).val.map (·.val) = l.map UScalar.val := by
  rw [alloc.vec.Vec.from_val]

end EquivLean.Modernize.Cbact04c.Rust
