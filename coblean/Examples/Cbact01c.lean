/-
# CardDemo CBACT01C (account file extract), extracted by the front end

`examples/carddemo/cbact01c.ir.json` is the output of `tools/cobolfe` on `app/cbl/CBACT01C.cbl` of
AWS CardDemo, unchanged.  For each account record the program displays its fields, converts the
reissue date with the assembler routine COBDATFT (`Cobol/Ext/CardDemo.lean`), and writes three
extracts: a record of the account's fields (with a packed cycle debit), an array record (an
`OCCURS 5` group with packed fields) and two variable-length records (12 and 39 bytes).
-/
import Cobol
import Cobol.Ext.CardDemo
open Cobol

namespace CardDemo

cobol_program Cbact01c from "../examples/carddemo/cbact01c.ir.json"

namespace Cbact01c

/-- `START OF EXECUTION OF PROGRAM CBACT01C` in EBCDIC. -/
def startMsg : List UInt8 := [226, 227, 193, 217, 227, 64, 214, 198, 64, 197, 231, 197, 195, 228, 227, 201, 214, 213, 64, 214, 198, 64, 215, 217, 214, 199, 217, 193, 212, 64, 195, 194, 193, 195, 227, 240, 241, 195]

/-- `END OF EXECUTION OF PROGRAM CBACT01C` in EBCDIC. -/
def endMsg : List UInt8 := [197, 213, 196, 64, 214, 198, 64, 197, 231, 197, 195, 228, 227, 201, 214, 213, 64, 214, 198, 64, 215, 217, 214, 199, 217, 193, 212, 64, 195, 194, 193, 195, 227, 240, 241, 195]

/-- `ACCT-ID                 :` in EBCDIC. -/
def lblId : List UInt8 := [193, 195, 195, 227, 96, 201, 196, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 122]

/-- `ACCT-ACTIVE-STATUS      :` in EBCDIC. -/
def lblStatus : List UInt8 := [193, 195, 195, 227, 96, 193, 195, 227, 201, 229, 197, 96, 226, 227, 193, 227, 228, 226, 64, 64, 64, 64, 64, 64, 122]

/-- `ACCT-CURR-BAL           :` in EBCDIC. -/
def lblBal : List UInt8 := [193, 195, 195, 227, 96, 195, 228, 217, 217, 96, 194, 193, 211, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 122]

/-- `ACCT-CREDIT-LIMIT       :` in EBCDIC. -/
def lblLimit : List UInt8 := [193, 195, 195, 227, 96, 195, 217, 197, 196, 201, 227, 96, 211, 201, 212, 201, 227, 64, 64, 64, 64, 64, 64, 64, 122]

/-- `ACCT-CASH-CREDIT-LIMIT  :` in EBCDIC. -/
def lblCash : List UInt8 := [193, 195, 195, 227, 96, 195, 193, 226, 200, 96, 195, 217, 197, 196, 201, 227, 96, 211, 201, 212, 201, 227, 64, 64, 122]

/-- `ACCT-OPEN-DATE          :` in EBCDIC. -/
def lblOpen : List UInt8 := [193, 195, 195, 227, 96, 214, 215, 197, 213, 96, 196, 193, 227, 197, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 122]

/-- `ACCT-EXPIRAION-DATE     :` in EBCDIC. -/
def lblExp : List UInt8 := [193, 195, 195, 227, 96, 197, 231, 215, 201, 217, 193, 201, 214, 213, 96, 196, 193, 227, 197, 64, 64, 64, 64, 64, 122]

/-- `ACCT-REISSUE-DATE       :` in EBCDIC. -/
def lblReis : List UInt8 := [193, 195, 195, 227, 96, 217, 197, 201, 226, 226, 228, 197, 96, 196, 193, 227, 197, 64, 64, 64, 64, 64, 64, 64, 122]

/-- `ACCT-CURR-CYC-CREDIT    :` in EBCDIC. -/
def lblCc : List UInt8 := [193, 195, 195, 227, 96, 195, 228, 217, 217, 96, 195, 232, 195, 96, 195, 217, 197, 196, 201, 227, 64, 64, 64, 64, 122]

/-- `ACCT-CURR-CYC-DEBIT     :` in EBCDIC. -/
def lblCd : List UInt8 := [193, 195, 195, 227, 96, 195, 228, 217, 217, 96, 195, 232, 195, 96, 196, 197, 194, 201, 227, 64, 64, 64, 64, 64, 122]

/-- `ACCT-GROUP-ID           :` in EBCDIC. -/
def lblGrp : List UInt8 := [193, 195, 195, 227, 96, 199, 217, 214, 228, 215, 96, 201, 196, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 122]

/-- `-------------------------------------------------` in EBCDIC. -/
def dashes : List UInt8 := [96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96]

/-- `VBRC-REC1:` in EBCDIC. -/
def vb1Lbl : List UInt8 := [229, 194, 217, 195, 96, 217, 197, 195, 241, 122]

/-- `VBRC-REC2:` in EBCDIC. -/
def vb2Lbl : List UInt8 := [229, 194, 217, 195, 96, 217, 197, 195, 242, 122]

theorem startMsg_eq : Codepage.encode037 "START OF EXECUTION OF PROGRAM CBACT01C" = some startMsg := by decide +kernel
theorem endMsg_eq : Codepage.encode037 "END OF EXECUTION OF PROGRAM CBACT01C" = some endMsg := by decide +kernel
theorem lblId_eq : Codepage.encode037 "ACCT-ID                 :" = some lblId := by decide +kernel
theorem lblStatus_eq : Codepage.encode037 "ACCT-ACTIVE-STATUS      :" = some lblStatus := by decide +kernel
theorem lblBal_eq : Codepage.encode037 "ACCT-CURR-BAL           :" = some lblBal := by decide +kernel
theorem lblLimit_eq : Codepage.encode037 "ACCT-CREDIT-LIMIT       :" = some lblLimit := by decide +kernel
theorem lblCash_eq : Codepage.encode037 "ACCT-CASH-CREDIT-LIMIT  :" = some lblCash := by decide +kernel
theorem lblOpen_eq : Codepage.encode037 "ACCT-OPEN-DATE          :" = some lblOpen := by decide +kernel
theorem lblExp_eq : Codepage.encode037 "ACCT-EXPIRAION-DATE     :" = some lblExp := by decide +kernel
theorem lblReis_eq : Codepage.encode037 "ACCT-REISSUE-DATE       :" = some lblReis := by decide +kernel
theorem lblCc_eq : Codepage.encode037 "ACCT-CURR-CYC-CREDIT    :" = some lblCc := by decide +kernel
theorem lblCd_eq : Codepage.encode037 "ACCT-CURR-CYC-DEBIT     :" = some lblCd := by decide +kernel
theorem lblGrp_eq : Codepage.encode037 "ACCT-GROUP-ID           :" = some lblGrp := by decide +kernel
theorem dashes_eq : Codepage.encode037 "-------------------------------------------------" = some dashes := by decide +kernel
theorem vb1Lbl_eq : Codepage.encode037 "VBRC-REC1:" = some vb1Lbl := by decide +kernel
theorem vb2Lbl_eq : Codepage.encode037 "VBRC-REC2:" = some vb2Lbl := by decide +kernel

/-- An account record (`CVACT01Y`, 300 bytes); the program decodes the numeric fields. -/
structure Acct where
  id : Int
  st : List UInt8
  bal : Int
  limit : Int
  cash : Int
  openDt : List UInt8
  exp : List UInt8
  reis : List UInt8
  cc : Int
  cd : Int
  zip : List UInt8
  grp : List UInt8
  fill : List UInt8
  deriving Inhabited

def Acct.bytes (a : Acct) : List UInt8 :=
  encodeNum {} ACCT_ID.fmt a.id ++ a.st ++ encodeNum {} ACCT_CURR_BAL.fmt a.bal ++
    encodeNum {} ACCT_CREDIT_LIMIT.fmt a.limit ++ encodeNum {} ACCT_CASH_CREDIT_LIMIT.fmt a.cash ++
    a.openDt ++ a.exp ++ a.reis ++ encodeNum {} ACCT_CURR_CYC_CREDIT.fmt a.cc ++
    encodeNum {} ACCT_CURR_CYC_DEBIT.fmt a.cd ++ a.zip ++ a.grp ++ a.fill

def Acct.valid (a : Acct) : Prop :=
  a.id.natAbs < 100000000000 ∧ 0 ≤ a.id ∧ a.st.length = 1 ∧ a.bal.natAbs < 1000000000000 ∧
    a.limit.natAbs < 1000000000000 ∧ a.cash.natAbs < 1000000000000 ∧ a.openDt.length = 10 ∧
    a.exp.length = 10 ∧ a.reis.length = 10 ∧ a.cc.natAbs < 1000000000000 ∧
    a.cd.natAbs < 1000000000000 ∧ a.zip.length = 10 ∧ a.grp.length = 10 ∧ a.fill.length = 178

/-- COBDATFT on the reissue date: `YYYY-MM-DD` becomes `YYYYMMDD`. -/
def reisOut (r : List UInt8) : List UInt8 := r.take 4 ++ (r.drop 5).take 2 ++ (r.drop 8).take 2

/-- The OUTFILE record.  `rf`: the 2 bytes of COBDATFT's output date after the 8 it sets (initial
storage, never written); `cd`: `OUT-ACCT-CURR-CYC-DEBIT` (packed), which the program sets only
when the cycle debit is zero. -/
def outRec (rf cd : List UInt8) (a : Acct) : List UInt8 :=
  encodeNum {} OUT_ACCT_ID.fmt a.id ++ a.st ++ encodeNum {} OUT_ACCT_CURR_BAL.fmt a.bal ++
    encodeNum {} OUT_ACCT_CREDIT_LIMIT.fmt a.limit ++
    encodeNum {} OUT_ACCT_CASH_CREDIT_LIMIT.fmt a.cash ++ a.openDt ++ a.exp ++ reisOut a.reis ++ rf ++
    encodeNum {} OUT_ACCT_CURR_CYC_CREDIT.fmt a.cc ++ cd ++ a.grp

/-- The ARRYFILE record: the id, then 5 (balance, packed debit) pairs (the first three set, the
last two zero from `INITIALIZE`), then 4 spaces. -/
def arrRec (a : Acct) : List UInt8 :=
  encodeNum {} ARR_ACCT_ID.fmt a.id ++
    encodeNum {} ARR_ACCT_CURR_BAL.fmt a.bal ++ encodeNum {} ARR_ACCT_CURR_CYC_DEBIT.fmt 100500 ++
    encodeNum {} ARR_ACCT_CURR_BAL.fmt a.bal ++ encodeNum {} ARR_ACCT_CURR_CYC_DEBIT.fmt 152500 ++
    encodeNum {} ARR_ACCT_CURR_BAL.fmt (-102500) ++ encodeNum {} ARR_ACCT_CURR_CYC_DEBIT.fmt (-250000) ++
    encodeNum {} ARR_ACCT_CURR_BAL.fmt 0 ++ encodeNum {} ARR_ACCT_CURR_CYC_DEBIT.fmt 0 ++
    encodeNum {} ARR_ACCT_CURR_BAL.fmt 0 ++ encodeNum {} ARR_ACCT_CURR_CYC_DEBIT.fmt 0 ++
    [64, 64, 64, 64]

/-- The two VBRCFILE records (12 and 39 bytes). -/
def vb1 (a : Acct) : List UInt8 := encodeNum {} VB1_ACCT_ID.fmt a.id ++ a.st

def vb2 (a : Acct) : List UInt8 :=
  encodeNum {} VB2_ACCT_ID.fmt a.id ++ encodeNum {} VB2_ACCT_CURR_BAL.fmt a.bal ++
    encodeNum {} VB2_ACCT_CREDIT_LIMIT.fmt a.limit ++ a.reis.take 4

/-- What CBACT01C has done after some account records: the bytes of `OUT-ACCT-CURR-CYC-DEBIT`
and the events (newest first, as `State.out`). -/
structure Model where
  cd : List UInt8
  out : List Event

/-- One account record (`1000-ACCTFILE-GET-NEXT` and the main loop's `DISPLAY`). -/
def step (rf : List UInt8) (s : Model) (a : Acct) : Model :=
  let cd := if a.cd = 0 then encodeNum {} OUT_ACCT_CURR_CYC_DEBIT.fmt 252500 else s.cd
  { cd,
    out := [.display a.bytes, .write 4 (vb2 a), .write 4 (vb1 a), .display (vb2Lbl ++ vb2 a),
      .display (vb1Lbl ++ vb1 a), .write 3 (arrRec a), .write 2 (outRec rf cd a), .call "COBDATFT",
      .display dashes, .display (lblGrp ++ a.grp),
      .display (lblCd ++ encodeNum {} ACCT_CURR_CYC_DEBIT.fmt a.cd),
      .display (lblCc ++ encodeNum {} ACCT_CURR_CYC_CREDIT.fmt a.cc), .display (lblReis ++ a.reis),
      .display (lblExp ++ a.exp), .display (lblOpen ++ a.openDt),
      .display (lblCash ++ encodeNum {} ACCT_CASH_CREDIT_LIMIT.fmt a.cash),
      .display (lblLimit ++ encodeNum {} ACCT_CREDIT_LIMIT.fmt a.limit),
      .display (lblBal ++ encodeNum {} ACCT_CURR_BAL.fmt a.bal), .display (lblStatus ++ a.st),
      .display (lblId ++ encodeNum {} ACCT_ID.fmt a.id)] ++ s.out }

/-- The model after the account records `as`, from `OUT-ACCT-CURR-CYC-DEBIT`'s initial bytes `cd0`. -/
def model (rf cd0 : List UInt8) (as : List Acct) : Model := as.foldl (step rf) ⟨cd0, []⟩

/-! ## The account record's fields

Symbolic execution keeps `a.bytes` folded (it is read and displayed as a whole); a field read
from it is `(a.bytes.drop o).take n`, which these lemmas turn into the field. -/

theorem Acct.length_bytes (a : Acct) (h : a.valid) : a.bytes.length = 300 := by
  obtain ⟨-, -, h3, -, -, -, h7, h8, h9, -, -, h12, h13, h14⟩ := h
  simp [Acct.bytes, length_encodeNum, NumFmt.byteLen, h3, h7, h8, h9, h12, h13, h14]

theorem Acct.field_id (a : Acct) (h : a.valid) : a.bytes.take 11 = encodeNum {} ACCT_ID.fmt a.id := by
  obtain ⟨-, -, h3, -, -, -, h7, h8, h9, -, -, h12, h13, h14⟩ := h
  simp [Acct.bytes, length_encodeNum, NumFmt.byteLen, List.take_append, List.drop_append,
    List.drop_of_length_le, List.take_of_length_le, h3, h7, h8, h9, h12, h13, h14]

theorem Acct.field_st (a : Acct) (h : a.valid) : (a.bytes.drop 11).take 1 = a.st := by
  obtain ⟨-, -, h3, -, -, -, h7, h8, h9, -, -, h12, h13, h14⟩ := h
  simp [Acct.bytes, length_encodeNum, NumFmt.byteLen, List.take_append, List.drop_append,
    List.drop_of_length_le, List.take_of_length_le, h3, h7, h8, h9, h12, h13, h14]

theorem Acct.field_bal (a : Acct) (h : a.valid) : (a.bytes.drop 12).take 12 = encodeNum {} ACCT_CURR_BAL.fmt a.bal := by
  obtain ⟨-, -, h3, -, -, -, h7, h8, h9, -, -, h12, h13, h14⟩ := h
  simp [Acct.bytes, length_encodeNum, NumFmt.byteLen, List.take_append, List.drop_append,
    List.drop_of_length_le, List.take_of_length_le, h3, h7, h8, h9, h12, h13, h14]

theorem Acct.field_limit (a : Acct) (h : a.valid) : (a.bytes.drop 24).take 12 = encodeNum {} ACCT_CREDIT_LIMIT.fmt a.limit := by
  obtain ⟨-, -, h3, -, -, -, h7, h8, h9, -, -, h12, h13, h14⟩ := h
  simp [Acct.bytes, length_encodeNum, NumFmt.byteLen, List.take_append, List.drop_append,
    List.drop_of_length_le, List.take_of_length_le, h3, h7, h8, h9, h12, h13, h14]

theorem Acct.field_cash (a : Acct) (h : a.valid) : (a.bytes.drop 36).take 12 = encodeNum {} ACCT_CASH_CREDIT_LIMIT.fmt a.cash := by
  obtain ⟨-, -, h3, -, -, -, h7, h8, h9, -, -, h12, h13, h14⟩ := h
  simp [Acct.bytes, length_encodeNum, NumFmt.byteLen, List.take_append, List.drop_append,
    List.drop_of_length_le, List.take_of_length_le, h3, h7, h8, h9, h12, h13, h14]

theorem Acct.field_openDt (a : Acct) (h : a.valid) : (a.bytes.drop 48).take 10 = a.openDt := by
  obtain ⟨-, -, h3, -, -, -, h7, h8, h9, -, -, h12, h13, h14⟩ := h
  simp [Acct.bytes, length_encodeNum, NumFmt.byteLen, List.take_append, List.drop_append,
    List.drop_of_length_le, List.take_of_length_le, h3, h7, h8, h9, h12, h13, h14]

theorem Acct.field_exp (a : Acct) (h : a.valid) : (a.bytes.drop 58).take 10 = a.exp := by
  obtain ⟨-, -, h3, -, -, -, h7, h8, h9, -, -, h12, h13, h14⟩ := h
  simp [Acct.bytes, length_encodeNum, NumFmt.byteLen, List.take_append, List.drop_append,
    List.drop_of_length_le, List.take_of_length_le, h3, h7, h8, h9, h12, h13, h14]

theorem Acct.field_reis (a : Acct) (h : a.valid) : (a.bytes.drop 68).take 10 = a.reis := by
  obtain ⟨-, -, h3, -, -, -, h7, h8, h9, -, -, h12, h13, h14⟩ := h
  simp [Acct.bytes, length_encodeNum, NumFmt.byteLen, List.take_append, List.drop_append,
    List.drop_of_length_le, List.take_of_length_le, h3, h7, h8, h9, h12, h13, h14]

theorem Acct.field_cc (a : Acct) (h : a.valid) : (a.bytes.drop 78).take 12 = encodeNum {} ACCT_CURR_CYC_CREDIT.fmt a.cc := by
  obtain ⟨-, -, h3, -, -, -, h7, h8, h9, -, -, h12, h13, h14⟩ := h
  simp [Acct.bytes, length_encodeNum, NumFmt.byteLen, List.take_append, List.drop_append,
    List.drop_of_length_le, List.take_of_length_le, h3, h7, h8, h9, h12, h13, h14]

theorem Acct.field_cd (a : Acct) (h : a.valid) : (a.bytes.drop 90).take 12 = encodeNum {} ACCT_CURR_CYC_DEBIT.fmt a.cd := by
  obtain ⟨-, -, h3, -, -, -, h7, h8, h9, -, -, h12, h13, h14⟩ := h
  simp [Acct.bytes, length_encodeNum, NumFmt.byteLen, List.take_append, List.drop_append,
    List.drop_of_length_le, List.take_of_length_le, h3, h7, h8, h9, h12, h13, h14]

theorem Acct.field_zip (a : Acct) (h : a.valid) : (a.bytes.drop 102).take 10 = a.zip := by
  obtain ⟨-, -, h3, -, -, -, h7, h8, h9, -, -, h12, h13, h14⟩ := h
  simp [Acct.bytes, length_encodeNum, NumFmt.byteLen, List.take_append, List.drop_append,
    List.drop_of_length_le, List.take_of_length_le, h3, h7, h8, h9, h12, h13, h14]

theorem Acct.field_grp (a : Acct) (h : a.valid) : (a.bytes.drop 112).take 10 = a.grp := by
  obtain ⟨-, -, h3, -, -, -, h7, h8, h9, -, -, h12, h13, h14⟩ := h
  simp [Acct.bytes, length_encodeNum, NumFmt.byteLen, List.take_append, List.drop_append,
    List.drop_of_length_le, List.take_of_length_le, h3, h7, h8, h9, h12, h13, h14]

theorem Acct.field_fill (a : Acct) (h : a.valid) : (a.bytes.drop 122).take 178 = a.fill := by
  obtain ⟨-, -, h3, -, -, -, h7, h8, h9, -, -, h12, h13, h14⟩ := h
  simp [Acct.bytes, length_encodeNum, NumFmt.byteLen, List.take_append, List.drop_append,
    List.drop_of_length_le, List.take_of_length_le, h3, h7, h8, h9, h12, h13, h14]

/-! ## COBDATFT's character tests in this program's character set (EBCDIC) -/

@[simp] theorem chr_1 : Ext.chr ({} : Config) '1' = 241 := by decide +kernel
@[simp] theorem chr_2 : Ext.chr ({} : Config) '2' = 242 := by decide +kernel
@[simp] theorem chr_dash : Ext.chr ({} : Config) '-' = 96 := by decide +kernel

theorem cfg_eq' : Cbact01c.cfg = {} := rfl

theorem cardDemoCalls_cobdatft (cfg : Config) (area : List UInt8) :
    Ext.cardDemoCalls cfg "COBDATFT" [area] = (Ext.cobdatft cfg area).map ([·]) := rfl

/-- COBDATFT with input and output type `2` (`YYYY-MM-DD` to `YYYYMMDD`): its valid path. -/
theorem cobdatft_type2 (area : List UInt8) (hl : area.length = 80) (h0 : area.getD 0 0 = 242)
    (h21 : area.getD 21 0 = 242) :
    Ext.cobdatft {} area = some (area.take 22 ++
      ((((area.drop 1).take 20).take 4 ++ (((area.drop 1).take 20).drop 5).take 2 ++
        (((area.drop 1).take 20).drop 8).take 2 ++ ((area.drop 22).take 20).drop 8)) ++ area.drop 42) := by
  unfold Ext.cobdatft
  simp only [hl, h0, h21, chr_1, chr_2, chr_dash]
  simp

theorem getD_append_left' {l l' : List UInt8} {n : Nat} {d : UInt8} (h : n < l.length) :
    (l ++ l').getD n d = l.getD n d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_append_right' {l l' : List UInt8} {n : Nat} {d : UInt8} (h : l.length ≤ n) :
    (l ++ l').getD n d = l'.getD (n - l.length) d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right h]

/-- Slices of a memory read are memory reads. -/
theorem Mem.read_drop' (m : Mem) (o n k : Nat) : (m.read o n).drop k = m.read (o + k) (n - k) := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_drop, Mem.getElem_read]
    congr 1; omega

theorem Mem.read_take' (m : Mem) (o n k : Nat) (h : k ≤ n) : (m.read o n).take k = m.read o k := by
  apply List.ext_getElem
  · simp; omega
  · intro i h1 h2
    simp only [List.getElem_take, Mem.getElem_read]

/-! ## The loop invariant -/

/-- Loop invariant, indexed by the outcomes of the remaining `READ`s: after the records `done`,
the end-of-file flag, `OUT-ACCT-CURR-CYC-DEBIT`, the bytes of COBDATFT's output date it never
sets, the files and the events are the model's. -/
def Inv (m : Mem) (accts : List Acct) (inp0 : List (Nat × List (List UInt8)))
    (rest : List (Option Acct)) (st : State) : Prop :=
  ∃ done todo, accts = done ++ todo ∧
    ((rest = [] ∧ todo = []) ∨ rest = todo.map some ++ [none]) ∧
    st.idx = [] ∧ st.slots = [] ∧ st.active = [] ∧ st.inp = inp0 ∧ st.mem.size = 1071 ∧
    st.mem.read 997 1 = (if rest.isEmpty then [232] else [213]) ∧
    st.mem.read 390 7 = (model (m.read 927 2) (m.read 390 7) done).cd ∧
    st.mem.read 927 2 = m.read 927 2 ∧ st.mem.read 929 10 = m.read 929 10 ∧
    (∃ f1 f2 f3 f4 : FileSt, st.files = [(1, f1), (2, f2), (3, f3), (4, f4)] ∧
      f1.mode = some .input ∧ f1.recs = accts.map Acct.bytes ∧ f1.pos = done.length ∧
      f1.eof = rest.isEmpty ∧ f2.mode = some .output ∧ f3.mode = some .output ∧
      f4.mode = some .output) ∧
    st.out = (model (m.read 927 2) (m.read 390 7) done).out ++ [.display startMsg]

theorem model_append (rf cd0 : List UInt8) (as : List Acct) (a : Acct) :
    model rf cd0 (as ++ [a]) = step rf (model rf cd0 as) a := by
  simp [model, List.foldl_append]

/-- `OUT-ACCT-CURR-CYC-DEBIT` always has its 7 bytes. -/
theorem foldl_step_cd_length (rf : List UInt8) :
    ∀ (as : List Acct) (s : Model), s.cd.length = 7 → (as.foldl (step rf) s).cd.length = 7
  | [], _, h => h
  | a :: as, s, h => by
    rw [List.foldl_cons]
    apply foldl_step_cd_length rf as
    unfold step
    split
    · simp [length_encodeNum, NumFmt.byteLen]
    · exact h

theorem model_cd_length (rf cd0 : List UInt8) (h : cd0.length = 7) (as : List Acct) :
    (model rf cd0 as).cd.length = 7 :=
  foldl_step_cd_length rf as ⟨cd0, []⟩ h

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
/-- **CBACT01C on any account file.**  For every account file of valid records and every initial
storage, CBACT01C (with COBDATFT as its environment `CALL`) ends with `GOBACK`, and its events are
the start message, what `step` says for each account record in file order, and the end message. -/
theorem cbact01c_extracts (m : Mem) (hm : m.size = 1071) (accts : List Acct)
    (hval : ∀ a ∈ accts, a.valid) (n : Nat) (hn : accts.length < n) :
    let r := Cbact01c.run { call := Ext.cardDemoCalls Cbact01c.cfg } (n + 40)
      (Cbact01c.initState m [(1, accts.map Acct.bytes)])
    let s := model (m.read 927 2) (m.read 390 7) accts
    r.1 = .stop .goback ∧ r.2.out = [.display endMsg] ++ s.out ++ [.display startMsg] := by
  intro r s
  simp only [r, s]
  cobol_auto
  cobol_loop (Inv m accts [(1, accts.map Acct.bytes)]) (accts.map some ++ [none])
  · -- after the loop: CLOSE, DISPLAY, GOBACK
    obtain ⟨mem, idx, slots, saves, active, out, inp, files, clockN⟩ := loopState
    obtain ⟨done, todo, hd, hrest, rfl, rfl, rfl, rfl, hsz, heof, -, -, -,
      ⟨f1, f2, f3, f4, rfl, h1m, -, -, -, h2m, h3m, h4m⟩, hout⟩ := hloopInv
    rcases hrest with ⟨-, rfl⟩ | h
    · simp only [List.append_nil] at hd
      subst hd
      dsimp only at hsz heof hout
      simp only [List.isEmpty_nil, ↓reduceIte] at heof
      cobol_auto
      simp [hout, endMsg]
    · simp at h
  · -- before the loop: the start message, the files at their start
    cobol_inv [model, startMsg] with [], accts
  · simp; omega
  · -- the loop ends exactly after the end-of-file READ
    rintro ⟨mem, idx, slots, saves, active, out, inp, files, clockN⟩ ⟨-, -, -, -, -, -, -, -, -, heof, -⟩
    simp only [List.isEmpty_nil, ↓reduceIte] at heof
    cobol_auto
  · -- one iteration: READ the next account record and extract it, or reach the end of the file
    rintro y ys ⟨mem, idx, slots, saves, active, out, inp, files, clockN⟩
      ⟨done, todo, hd, hrest, rfl, rfl, rfl, rfl, hsz, heof, hcd, hrf, hrf2,
        ⟨f1, f2, f3, f4, rfl, h1m, h1r, h1p, h1e, h2m, h3m, h4m⟩, hout⟩
    dsimp only at hsz heof hcd hrf hrf2 hout
    rcases hrest with ⟨h, -⟩ | hrest
    · simp at h
    simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte] at heof h1e
    refine ⟨by cobol_auto, ?_⟩
    cases todo with
    | nil =>
      -- the end-of-file READ
      simp only [List.map_nil, List.nil_append, List.cons.injEq] at hrest
      obtain ⟨rfl, rfl⟩ := hrest
      simp only [List.append_nil] at hd
      subst hd
      have hnone : f1.recs[f1.pos]? = none := by rw [h1r, h1p]; simp
      cobol_auto
      cobol_inv [model] with accts, []
    | cons a todo' =>
      -- the next account record `a`
      simp only [List.map_cons, List.cons_append, List.cons.injEq] at hrest
      obtain ⟨rfl, rfl⟩ := hrest
      subst hd
      have hav := hval a (by simp)
      have hcdl := model_cd_length (m.read 927 2) (m.read 390 7) (by simp) done
      have hsome : f1.recs[f1.pos]? = some a.bytes := by rw [h1r, h1p]; simp
      -- the record stays folded; its fields
      have ab := Acct.length_bytes a hav
      have af1 := Acct.field_id a hav
      have af2 := Acct.field_st a hav
      have af3 := Acct.field_bal a hav
      have af4 := Acct.field_limit a hav
      have af5 := Acct.field_cash a hav
      have af6 := Acct.field_openDt a hav
      have af7 := Acct.field_exp a hav
      have af8 := Acct.field_reis a hav
      have af9 := Acct.field_cc a hav
      have af10 := Acct.field_cd a hav
      have af11 := Acct.field_zip a hav
      have af12 := Acct.field_grp a hav
      have af13 := Acct.field_fill a hav
      obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14⟩ := hav
      by_cases hcd0 : a.cd = 0
      · have hc : compare a.cd 0 = .eq := by simp [compare, compareOfLessAndEq, hcd0]
        cobol_auto [cardDemoCalls_cobdatft, cobdatft_type2, List.getD_cons_zero, List.getD_cons_succ, getD_append_left', getD_append_right', Mem.read_drop', Mem.read_take', List.zip_cons_cons, List.zip_nil_left, List.zip_nil_right, List.foldl_cons, List.foldl_nil, List.all_cons, List.all_nil]
        cobol_inv [model_append, step, outRec, arrRec, vb1, vb2, reisOut, hout, Mem.read_take', Mem.read_drop', lblId, lblStatus, lblBal, lblLimit, lblCash, lblOpen, lblExp, lblReis, lblCc, lblCd, lblGrp, dashes, vb1Lbl, vb2Lbl] with done ++ [a], todo'
      · have hc : compare a.cd 0 ≠ .eq := by
          simp only [compare, compareOfLessAndEq]
          by_cases h1 : a.cd < 0
          · simp [h1]
          · simp [h1, hcd0]
        cobol_auto [cardDemoCalls_cobdatft, cobdatft_type2, List.getD_cons_zero, List.getD_cons_succ, getD_append_left', getD_append_right', Mem.read_drop', Mem.read_take', List.zip_cons_cons, List.zip_nil_left, List.zip_nil_right, List.foldl_cons, List.foldl_nil, List.all_cons, List.all_nil]
        cobol_inv [model_append, step, outRec, arrRec, vb1, vb2, reisOut, hout, Mem.read_take', Mem.read_drop', lblId, lblStatus, lblBal, lblLimit, lblCash, lblOpen, lblExp, lblReis, lblCc, lblCd, lblGrp, dashes, vb1Lbl, vb2Lbl] with done ++ [a], todo'

end Cbact01c
end CardDemo

#print axioms CardDemo.Cbact01c.cbact01c_extracts
