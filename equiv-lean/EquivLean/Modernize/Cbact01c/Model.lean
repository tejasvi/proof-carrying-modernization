import EquivLean.Bridge.Cobol.Records

/-!
# CBACT01C: what the translations output, from the input field values

CBACT01C reads the account file (ACCTFILE, in key order) and, for each account record:
- DISPLAYs eleven of its fields after their labels, then a line of dashes
  (1100-DISPLAY-ACCT-RECORD);
- WRITEs a copy to OUT-FILE (1300-POPUL-ACCT-RECORD, 1350): the reissue date goes through
  `COBDATFT` with input and output type 2, which turns `YYYY-MM-DD` into `YYYYMMDD` (characters
  1-4, 6-7, 9-10 of the date) and leaves the rest of the output date as it was: the copy gets two
  spaces after the eight characters (never written; the storage starts with spaces there).  The
  cycle debit (COMP-3) is 2525.00 when the account's is zero, and otherwise keeps the value of the
  previous copy (initially 0);
- WRITEs an array record to ARRY-FILE (1400-POPUL-ARRAY-RECORD, 1450): the account id; the five
  `OCCURS` elements (balance, cycle debit) are (balance, 1005.00), (balance, 1525.00),
  (-1025.00, -2500.00), (0, 0), (0, 0) (`INITIALIZE ARR-ARRAY-REC`); spaces;
- DISPLAYs and WRITEs two variable-length records to VBRC-FILE (1500-POPUL-VBRC-RECORD, 1550,
  1575): VBRC-REC1 (12 bytes: id, status) and VBRC-REC2 (39 bytes: id, balance, credit limit,
  the first four characters of the reissue date);
- DISPLAYs the account record.

`run`: a fold over the account records that does what the translations do, on field values.

No generated schema covers two of the output records yet; they are represented as follows:
- the `OCCURS` record ARR-ARRAY-REC: its elementary items in storage order with the occurrences
  expanded, `ARR-ACCT-ID`, then `ARR-ACCT-CURR-BAL(k)`, `ARR-ACCT-CURR-CYC-DEBIT(k)` for
  k = 1 … 5, then `ARR-FILLER` (12 values; the translations hold one array per item of the
  group);
- a variable-length record of VBRC-FILE: its text, the code points of its bytes (as a DISPLAY
  line), whose length is the record's length (`WS-RECD-LEN`: 12 or 39).
The displayed lines are code points, as in `Cbact04c.Model`; the OUT-FILE copies are field
values (alphanumeric fields as EBCDIC bytes).
-/

open Cobol EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbact01c.Model

cobol_schema AccountRecord from "../../../examples/cobol/carddemo/cbact01c.ir.json" record "ACCOUNT-RECORD"
cobol_schema OutAcctRec from "../../../examples/cobol/carddemo/cbact01c.ir.json" record "OUT-ACCT-REC"
cobol_schema VbrcRec1 from "../../../examples/cobol/carddemo/cbact01c.ir.json" record "VBRC-REC1"
cobol_schema VbrcRec2 from "../../../examples/cobol/carddemo/cbact01c.ir.json" record "VBRC-REC2"

/-- The bytes of an alphanumeric value. -/
def strOf : FVal → List UInt8
  | .str bs => bs
  | .num _ => []

/-- The integer of a numeric value. -/
def numOf : FVal → Int
  | .num v => v
  | .str _ => 0

/-- The code points of a string literal. -/
def txt (s : String) : List Nat := s.toList.map Char.toNat

/-- `n` EBCDIC spaces. -/
def sp (n : Nat) : List UInt8 := List.replicate n 64

/-! ## Field access -/

/-- `ACCT-ID`, `ACCT-ACTIVE-STATUS`, `ACCT-CURR-BAL`, `ACCT-CREDIT-LIMIT`, `ACCT-REISSUE-DATE`,
`ACCT-CURR-CYC-DEBIT` of an account record. -/
def aId (a : List FVal) : Int := numOf (a.getD 0 default)
def aStatus (a : List FVal) : List UInt8 := strOf (a.getD 1 default)
def aBal (a : List FVal) : Int := numOf (a.getD 2 default)
def aLimit (a : List FVal) : Int := numOf (a.getD 3 default)
def aReissue (a : List FVal) : List UInt8 := strOf (a.getD 7 default)
def aCycDebit (a : List FVal) : Int := numOf (a.getD 9 default)

/-- The text of field `k` of an account record (as DISPLAY shows it). -/
def fld (a : List FVal) (k : Nat) : List Nat :=
  fieldTextS (AccountRecord.fields.getD k default) (a.getD k default)

/-! ## The records written -/

/-- The reissue date as `COBDATFT` leaves it in the output date (input and output type 2):
characters 1-4, 6-7 and 9-10, then two of the spaces the output date starts with. -/
def reissueOut (d : List UInt8) : List UInt8 :=
  d.take 4 ++ (d.drop 5).take 2 ++ (d.drop 8).take 2 ++ sp 2

/-- The copy of account `a` written to OUT-FILE, with cycle debit `cd`. -/
def outVals (a : List FVal) (cd : Int) : List FVal :=
  [a.getD 0 default, a.getD 1 default, a.getD 2 default, a.getD 3 default, a.getD 4 default,
    a.getD 5 default, a.getD 6 default, .str (reissueOut (aReissue a)), a.getD 8 default,
    .num cd, a.getD 11 default]

/-- The array record of account `a` written to ARRY-FILE (storage order, the occurrences
expanded). -/
def arrVals (a : List FVal) : List FVal :=
  [.num (aId a), .num (aBal a), .num 100500, .num (aBal a), .num 152500, .num (-102500),
    .num (-250000), .num 0, .num 0, .num 0, .num 0, .str (sp 4)]

/-- VBRC-REC1 and VBRC-REC2 of account `a`. -/
def vb1 (a : List FVal) : List FVal := [.num (aId a), .str (aStatus a)]
def vb2 (a : List FVal) : List FVal :=
  [.num (aId a), .num (aBal a), .num (aLimit a), .str ((aReissue a).take 4)]

/-- The lines DISPLAYed for account `a`: its fields (1100-DISPLAY-ACCT-RECORD), the two
variable-length records, the record. -/
def lines (a : List FVal) : List (List Nat) :=
  [txt "ACCT-ID                 :" ++ fld a 0,
    txt "ACCT-ACTIVE-STATUS      :" ++ fld a 1,
    txt "ACCT-CURR-BAL           :" ++ fld a 2,
    txt "ACCT-CREDIT-LIMIT       :" ++ fld a 3,
    txt "ACCT-CASH-CREDIT-LIMIT  :" ++ fld a 4,
    txt "ACCT-OPEN-DATE          :" ++ fld a 5,
    txt "ACCT-EXPIRAION-DATE     :" ++ fld a 6,
    txt "ACCT-REISSUE-DATE       :" ++ fld a 7,
    txt "ACCT-CURR-CYC-CREDIT    :" ++ fld a 8,
    txt "ACCT-CURR-CYC-DEBIT     :" ++ fld a 9,
    txt "ACCT-GROUP-ID           :" ++ fld a 11,
    txt "-------------------------------------------------",
    txt "VBRC-REC1:" ++ VbrcRec1.textS (vb1 a),
    txt "VBRC-REC2:" ++ VbrcRec2.textS (vb2 a),
    AccountRecord.textS a]

/-! ## The run -/

/-- The translations' state between two account records. -/
structure St where
  /-- `OUT-ACCT-CURR-CYC-DEBIT` of the last copy (the value of coblean's `Model.cd`). -/
  cd : Int
  /-- The outputs so far, oldest first. -/
  disp : List (List Nat)
  outWrites : List (List FVal)
  arryWrites : List (List FVal)
  vbrcWrites : List (List Nat)

/-- One account record `a`. -/
def step (s : St) (a : List FVal) : St :=
  let cd := if aCycDebit a = 0 then 252500 else s.cd
  { cd, disp := s.disp ++ lines a, outWrites := s.outWrites ++ [outVals a cd],
    arryWrites := s.arryWrites ++ [arrVals a],
    vbrcWrites := s.vbrcWrites ++ [VbrcRec1.textS (vb1 a), VbrcRec2.textS (vb2 a)] }

/-- The state before the first record. -/
def init : St :=
  { cd := 0, disp := [txt "START OF EXECUTION OF PROGRAM CBACT01C"], outWrites := [],
    arryWrites := [], vbrcWrites := [] }

/-- The outputs: the lines displayed (code points), the records written to OUT-FILE (field
values), ARRY-FILE (field values) and VBRC-FILE (code points). -/
structure Out where
  disp : List (List Nat)
  outWrites : List (List FVal)
  arryWrites : List (List FVal)
  vbrcWrites : List (List Nat)

/-- **What CBACT01C outputs**, for the account records `accts`. -/
def run (accts : List (List FVal)) : Out :=
  let s := accts.foldl step init
  { disp := s.disp ++ [txt "END OF EXECUTION OF PROGRAM CBACT01C"], outWrites := s.outWrites,
    arryWrites := s.arryWrites, vbrcWrites := s.vbrcWrites }

end EquivLean.Modernize.Cbact01c.Model
