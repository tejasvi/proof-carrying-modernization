-- Copied unchanged from coblean (frozen snapshot ~/coblean_snapshots/coblean-20261024T1628Z,
-- Examples/Cbtrn03c.lean); only the IR path differs. coblean and JimpleLean both have a library
-- named `Examples`, so equiv-lean cannot import the original module next to JimpleLean.
/-
# CardDemo CBTRN03C (daily transaction report), extracted by the front end

`examples/carddemo/cbtrn03c.ir.json` is the output of `tools/cobolfe` on `app/cbl/CBTRN03C.cbl`
of AWS CardDemo, unchanged.  The program reads the date range from the parameter file, then the
transaction file (sorted by card number by the job's SORT step), and writes a report: headers,
one detail line per transaction (with the account id, transaction type and category looked up
in three indexed files), an account total when the card number changes, a page total and new
headers every 20 lines, and at the end a page total and the grand total.
-/
import Cobol
open Cobol

namespace CardDemo

cobol_program Cbtrn03c from "../../../../examples/cobol/carddemo/cbtrn03c.ir.json"

namespace Cbtrn03c

/-- `START OF EXECUTION OF PROGRAM CBTRN03C` in EBCDIC. -/
def startMsg : List UInt8 := [226, 227, 193, 217, 227, 64, 214, 198, 64, 197, 231, 197, 195, 228, 227, 201, 214, 213, 64, 214, 198, 64, 215, 217, 214, 199, 217, 193, 212, 64, 195, 194, 227, 217, 213, 240, 243, 195]

/-- `END OF EXECUTION OF PROGRAM CBTRN03C` in EBCDIC. -/
def endMsg : List UInt8 := [197, 213, 196, 64, 214, 198, 64, 197, 231, 197, 195, 228, 227, 201, 214, 213, 64, 214, 198, 64, 215, 217, 214, 199, 217, 193, 212, 64, 195, 194, 227, 217, 213, 240, 243, 195]

/-- `Reporting from ` in EBCDIC. -/
def reportingMsg : List UInt8 := [217, 133, 151, 150, 153, 163, 137, 149, 135, 64, 134, 153, 150, 148, 64]

/-- ` to ` in EBCDIC. -/
def toMsg : List UInt8 := [64, 163, 150, 64]

/-- `TRAN-AMT ` in EBCDIC. -/
def amtMsg : List UInt8 := [227, 217, 193, 213, 96, 193, 212, 227, 64]

/-- `WS-PAGE-TOTAL` in EBCDIC. -/
def pageMsg : List UInt8 := [230, 226, 96, 215, 193, 199, 197, 96, 227, 214, 227, 193, 211]

/-- The report name header up to the date range: `DALYREPT`, `Daily Transaction Report`,
`Date Range: ` (91 bytes, EBCDIC). -/
def nameHead : List UInt8 := [196, 193, 211, 232, 217, 197, 215, 227, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 196, 129, 137, 147, 168, 64, 227, 153, 129, 149, 162, 129, 131, 163, 137, 150, 149, 64, 217, 133, 151, 150, 153, 163, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 196, 129, 163, 133, 64, 217, 129, 149, 135, 133, 122, 64]

/-- `TRANSACTION-HEADER-1` (114 bytes, EBCDIC). -/
def header1 : List UInt8 := [227, 153, 129, 149, 162, 129, 131, 163, 137, 150, 149, 64, 201, 196, 64, 64, 64, 193, 131, 131, 150, 164, 149, 163, 64, 201, 196, 64, 64, 227, 153, 129, 149, 162, 129, 131, 163, 137, 150, 149, 64, 227, 168, 151, 133, 64, 64, 64, 227, 153, 129, 149, 64, 195, 129, 163, 133, 135, 150, 153, 168, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 227, 153, 129, 149, 64, 226, 150, 164, 153, 131, 133, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 193, 148, 150, 164, 149, 163, 64, 64]

/-- `Page Total` and 86 dots (97 bytes, EBCDIC). -/
def pageHead : List UInt8 := [215, 129, 135, 133, 64, 227, 150, 163, 129, 147, 64, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75]

/-- `Account Total` and 84 dots (97 bytes, EBCDIC). -/
def acctHead : List UInt8 := [193, 131, 131, 150, 164, 149, 163, 64, 227, 150, 163, 129, 147, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75]

/-- `Grand Total` and 86 dots (97 bytes, EBCDIC). -/
def grandHead : List UInt8 := [199, 153, 129, 149, 132, 64, 227, 150, 163, 129, 147, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75, 75]

theorem startMsg_eq : Codepage.encode037 "START OF EXECUTION OF PROGRAM CBTRN03C" = some startMsg := by decide +kernel
theorem endMsg_eq : Codepage.encode037 "END OF EXECUTION OF PROGRAM CBTRN03C" = some endMsg := by decide +kernel
theorem reportingMsg_eq : Codepage.encode037 "Reporting from " = some reportingMsg := by decide +kernel
theorem toMsg_eq : Codepage.encode037 " to " = some toMsg := by decide +kernel
theorem amtMsg_eq : Codepage.encode037 "TRAN-AMT " = some amtMsg := by decide +kernel
theorem pageMsg_eq : Codepage.encode037 "WS-PAGE-TOTAL" = some pageMsg := by decide +kernel

theorem nameHead_length : nameHead.length = 91 := rfl
theorem header1_length : header1.length = 114 := rfl
theorem pageHead_length : pageHead.length = 97 := rfl
theorem acctHead_length : acctHead.length = 97 := rfl
theorem grandHead_length : grandHead.length = 97 := rfl
theorem toMsg_length : toMsg.length = 4 := rfl

/-- A transaction record (`CVTRA05Y`, 350 bytes); the merchant fields (id, name, city, zip:
119 bytes) are not read. -/
structure Tran where
  id : List UInt8
  ty : List UInt8
  cat : Int
  src : List UInt8
  desc : List UInt8
  amt : Int
  merch : List UInt8
  card : List UInt8
  orig : List UInt8
  proc : List UInt8
  fill : List UInt8
  deriving Inhabited

def Tran.bytes (t : Tran) : List UInt8 :=
  t.id ++ t.ty ++ encodeNum {} ({ digits := 4 } : NumFmt) t.cat ++ t.src ++ t.desc ++
    encodeNum {} TRAN_AMT.fmt t.amt ++ t.merch ++ t.card ++ t.orig ++ t.proc ++ t.fill

def Tran.valid (t : Tran) : Prop :=
  t.id.length = 16 ∧ t.ty.length = 2 ∧ t.cat.natAbs < 10000 ∧ 0 ≤ t.cat ∧ t.src.length = 10 ∧
    t.desc.length = 100 ∧ t.amt.natAbs < 100000000000 ∧ t.merch.length = 119 ∧
    t.card.length = 16 ∧ t.orig.length = 26 ∧ t.proc.length = 26 ∧ t.fill.length = 20

/-- A card cross-reference record (`CVACT03Y`): card number, customer id (not read), account
id, filler. -/
structure Xref where
  card : List UInt8
  cust : List UInt8
  acct : Int
  fill : List UInt8
  deriving Inhabited

def Xref.bytes (x : Xref) : List UInt8 :=
  x.card ++ x.cust ++ encodeNum {} XREF_ACCT_ID.fmt x.acct ++ x.fill

def Xref.valid (x : Xref) : Prop :=
  x.card.length = 16 ∧ x.cust.length = 9 ∧ x.acct.natAbs < 100000000000 ∧ 0 ≤ x.acct ∧
    x.fill.length = 14

/-! ## The report lines (133 bytes) -/

/-- `-ZZZ,ZZZ,ZZZ.ZZ` (the detail line's amount). -/
def minusPic : List ESym := [.minus, .z, .z, .z, .comma, .z, .z, .z, .comma, .z, .z, .z, .dot, .z, .z]

/-- `+ZZZ,ZZZ,ZZZ.ZZ` (the totals). -/
def plusPic : List ESym := [.plus, .z, .z, .z, .comma, .z, .z, .z, .comma, .z, .z, .z, .dot, .z, .z]

/-- An amount in cents edited by `-ZZZ,ZZZ,ZZZ.ZZ`. -/
def editMinus (v : Int) : List UInt8 := (Edit.edit {} minusPic false v 2).getD []

/-- An amount in cents edited by `+ZZZ,ZZZ,ZZZ.ZZ`. -/
def editPlus (v : Int) : List UInt8 := (Edit.edit {} plusPic false v 2).getD []

def hdr1Line : List UInt8 := header1 ++ List.replicate 19 64
def hdr2Line : List UInt8 := List.replicate 133 96
def blankLine : List UInt8 := List.replicate 133 64

theorem hdr2Line_length : hdr2Line.length = 133 := by simp [hdr2Line]
theorem blankLine_length : blankLine.length = 133 := by simp [blankLine]
def nameLine (start end_ : List UInt8) : List UInt8 :=
  nameHead ++ start ++ toMsg ++ end_ ++ List.replicate 18 64
def pageLine (v : Int) : List UInt8 := pageHead ++ editPlus v ++ List.replicate 21 64
def acctLine (v : Int) : List UInt8 := acctHead ++ editPlus v ++ List.replicate 21 64
def grandLine (v : Int) : List UInt8 := grandHead ++ editPlus v ++ List.replicate 21 64

/-- A detail line: transaction id, account id, type and its description (15 characters),
category and its description (29 characters), source, amount. -/
def detailLine (t : Tran) (acct : Int) (tdesc cdesc : List UInt8) : List UInt8 :=
  t.id ++ [64] ++ Sem.digitChars {} 11 acct.natAbs ++ [64] ++ t.ty ++ [96] ++ tdesc ++ [64] ++
    encodeNum {} TRAN_REPORT_CAT_CD.fmt t.cat ++ [96] ++ cdesc ++ [64] ++ t.src ++
    List.replicate 4 64 ++ editMinus t.amt ++ List.replicate 21 64

/-! ## The model -/

/-- The cross-reference record of a card (first match). -/
def xrefOf (xrefs : List Xref) (card : List UInt8) : Xref :=
  xrefs.getD ((Sem.findKey { off := 0, len := 16 } card (xrefs.map Xref.bytes)).getD 0) default

/-- The description of a transaction type (its first 15 characters). -/
def typeDesc (types : List (List UInt8)) (ty : List UInt8) : List UInt8 :=
  ((types.getD ((Sem.findKey { off := 0, len := 2 } ty types).getD 0) []).drop 2).take 15

/-- The description of a transaction category (its first 29 characters). -/
def catDesc (catgs : List (List UInt8)) (ty : List UInt8) (cat : Int) : List UInt8 :=
  ((catgs.getD ((Sem.findKey { off := 0, len := 6 } (ty ++ encodeNum {} FD_TRAN_CAT_CD.fmt cat) catgs).getD 0)
    []).drop 6).take 29

/-- A running total after an `ADD` (`S9(09)V99`, high-order truncation). -/
def fitTot (v : Int) : Int := (Sem.fitNum {} WS_PAGE_TOTAL.fmt v).2

/-- The report so far: the current card, the first-detail flag, the line counter, the page,
account and grand totals, the account id of the current card, the events (newest first). -/
structure M3 where
  card : List UInt8
  first : Bool
  lines : Nat
  page : Int
  acct : Int
  grand : Int
  xacct : Int
  out : List Event

/-- The four header lines (newest first). -/
def headers (start end_ : List UInt8) : List Event :=
  [.write 5 hdr2Line, .write 5 hdr1Line, .write 5 blankLine, .write 5 (nameLine start end_)]

/-- One transaction: `DISPLAY` it; on a new card the account total of the previous one (not
before the first detail) and the new card's account id; headers before the first detail; a page
total and headers when the line counter is a multiple of 20; the amount added to the page and
account totals; the detail line. -/
def step3 (xrefs : List Xref) (types catgs : List (List UInt8)) (start end_ : List UInt8)
    (s : M3) (t : Tran) : M3 :=
  let out1 := Event.display t.bytes :: s.out
  let same := decide (s.card = t.card)
  let out2 := if same || s.first then out1 else .write 5 hdr2Line :: .write 5 (acctLine s.acct) :: out1
  let lines2 := if same || s.first then s.lines else s.lines + 2
  let acct2 := if same || s.first then s.acct else 0
  let xacct := if same then s.xacct else (xrefOf xrefs t.card).acct
  let out3 := if s.first then headers start end_ ++ out2 else out2
  let lines3 := if s.first then lines2 + 4 else lines2
  let brk := decide (lines3 % 20 = 0)
  let out4 := if brk then headers start end_ ++ [.write 5 hdr2Line, .write 5 (pageLine s.page)] ++ out3
    else out3
  let lines4 := if brk then lines3 + 6 else lines3
  let grand := if brk then fitTot (s.grand + s.page) else s.grand
  let page := if brk then 0 else s.page
  { card := t.card, first := false, lines := lines4 + 1, page := fitTot (page + t.amt),
    acct := fitTot (acct2 + t.amt), grand, xacct,
    out := .write 5 (detailLine t xacct (typeDesc types t.ty) (catDesc catgs t.ty t.cat)) :: out4 }

/-- The model after the transactions `ts`. -/
def report3 (xrefs : List Xref) (types catgs : List (List UInt8)) (start end_ : List UInt8)
    (ts : List Tran) : M3 :=
  ts.foldl (step3 xrefs types catgs start end_) ⟨List.replicate 16 64, true, 0, 0, 0, 0, 0, []⟩

/-- At the end of the file (the record area still holds the last transaction `t`): its amount
and the page total are displayed, the amount is added again, the page total and the grand
total are written (newest first). -/
def eofEvents (s : M3) (t : Tran) : List Event :=
  [.write 5 (grandLine (fitTot (s.grand + fitTot (s.page + t.amt)))), .write 5 hdr2Line,
    .write 5 (pageLine (fitTot (s.page + t.amt))),
    .display (pageMsg ++ encodeNum {} WS_PAGE_TOTAL.fmt s.page),
    .display (amtMsg ++ encodeNum {} TRAN_AMT.fmt t.amt)]


/-! ## Lemmas: editing -/

/-- `-ZZZ,ZZZ,ZZZ.ZZ` edits every value (the picture is well formed). -/
theorem edit_minus (v : Int) : Edit.edit {} [.minus, .z, .z, .z, .comma, .z, .z, .z, .comma, .z, .z, .z, .dot, .z, .z] false v 2 = some (editMinus v) := by
  have h : (Edit.edit {} [.minus, .z, .z, .z, .comma, .z, .z, .z, .comma, .z, .z, .z, .dot, .z, .z] false v 2).isSome = true := by
    have hc : Edit.classify [.minus, .z, .z, .z, .comma, .z, .z, .z, .comma, .z, .z, .z, .dot, .z, .z] =
        some [.fixed .minus, .digit (some .z), .digit (some .z), .digit (some .z), .insert .comma,
        .digit (some .z), .digit (some .z), .digit (some .z), .insert .comma, .digit (some .z),
        .digit (some .z), .digit (some .z), .point, .digit (some .z), .digit (some .z)] := by decide
    have hf : Edit.floatBeforePoint [.fixed .minus, .digit (some .z), .digit (some .z), .digit (some .z), .insert .comma,
        .digit (some .z), .digit (some .z), .digit (some .z), .insert .comma, .digit (some .z),
        .digit (some .z), .digit (some .z), .point, .digit (some .z), .digit (some .z)] = true := by decide
    have hfs : Edit.floatSym [.minus, .z, .z, .z, .comma, .z, .z, .z, .comma, .z, .z, .z, .dot, .z, .z] = none := by decide
    unfold Edit.edit Edit.editOpt
    simp only [hc, Option.bind_eq_bind, Option.bind_some, hf, hfs, Bool.not_true, Bool.false_eq_true,
      ↓reduceIte]
    repeat' split
    all_goals simp
  obtain ⟨bs, hbs⟩ := Option.isSome_iff_exists.mp h
  simp [editMinus, minusPic, hbs]

/-- `+ZZZ,ZZZ,ZZZ.ZZ` edits every value. -/
theorem edit_plus (v : Int) : Edit.edit {} [.plus, .z, .z, .z, .comma, .z, .z, .z, .comma, .z, .z, .z, .dot, .z, .z] false v 2 = some (editPlus v) := by
  have h : (Edit.edit {} [.plus, .z, .z, .z, .comma, .z, .z, .z, .comma, .z, .z, .z, .dot, .z, .z] false v 2).isSome = true := by
    have hc : Edit.classify [.plus, .z, .z, .z, .comma, .z, .z, .z, .comma, .z, .z, .z, .dot, .z, .z] =
        some [.fixed .plus, .digit (some .z), .digit (some .z), .digit (some .z), .insert .comma,
        .digit (some .z), .digit (some .z), .digit (some .z), .insert .comma, .digit (some .z),
        .digit (some .z), .digit (some .z), .point, .digit (some .z), .digit (some .z)] := by decide
    have hf : Edit.floatBeforePoint [.fixed .plus, .digit (some .z), .digit (some .z), .digit (some .z), .insert .comma,
        .digit (some .z), .digit (some .z), .digit (some .z), .insert .comma, .digit (some .z),
        .digit (some .z), .digit (some .z), .point, .digit (some .z), .digit (some .z)] = true := by decide
    have hfs : Edit.floatSym [.plus, .z, .z, .z, .comma, .z, .z, .z, .comma, .z, .z, .z, .dot, .z, .z] = none := by decide
    unfold Edit.edit Edit.editOpt
    simp only [hc, Option.bind_eq_bind, Option.bind_some, hf, hfs, Bool.not_true, Bool.false_eq_true,
      ↓reduceIte]
    repeat' split
    all_goals simp
  obtain ⟨bs, hbs⟩ := Option.isSome_iff_exists.mp h
  simp [editPlus, plusPic, hbs]

/-- `INITIALIZE` moves zero to the amount: all spaces. -/
theorem edit_minus_zero : Edit.edit {} [.minus, .z, .z, .z, .comma, .z, .z, .z, .comma, .z, .z, .z, .dot, .z, .z] false 0 0 = some (List.replicate 15 64) := by
  decide +kernel

theorem editMinus_length (v : Int) : (editMinus v).length = 15 := by
  have hc : Edit.classify [.minus, .z, .z, .z, .comma, .z, .z, .z, .comma, .z, .z, .z, .dot, .z, .z] =
      some [.fixed .minus, .digit (some .z), .digit (some .z), .digit (some .z), .insert .comma,
        .digit (some .z), .digit (some .z), .digit (some .z), .insert .comma, .digit (some .z),
        .digit (some .z), .digit (some .z), .point, .digit (some .z), .digit (some .z)] := by decide
  have hf : Edit.floatBeforePoint [.fixed .minus, .digit (some .z), .digit (some .z), .digit (some .z), .insert .comma,
        .digit (some .z), .digit (some .z), .digit (some .z), .insert .comma, .digit (some .z),
        .digit (some .z), .digit (some .z), .point, .digit (some .z), .digit (some .z)] = true := by decide
  have hfs : Edit.floatSym [.minus, .z, .z, .z, .comma, .z, .z, .z, .comma, .z, .z, .z, .dot, .z, .z] = none := by decide
  unfold editMinus minusPic Edit.edit Edit.editOpt
  simp only [hc, Option.bind_eq_bind, Option.bind_some, hf, hfs, Bool.not_true, Bool.false_eq_true,
    ↓reduceIte]
  repeat' split
  all_goals simp [Edit.editOpt.gen, Edit.picWidth, Edit.width, Edit.fixedBytes]

theorem editPlus_length (v : Int) : (editPlus v).length = 15 := by
  have hc : Edit.classify [.plus, .z, .z, .z, .comma, .z, .z, .z, .comma, .z, .z, .z, .dot, .z, .z] =
      some [.fixed .plus, .digit (some .z), .digit (some .z), .digit (some .z), .insert .comma,
        .digit (some .z), .digit (some .z), .digit (some .z), .insert .comma, .digit (some .z),
        .digit (some .z), .digit (some .z), .point, .digit (some .z), .digit (some .z)] := by decide
  have hf : Edit.floatBeforePoint [.fixed .plus, .digit (some .z), .digit (some .z), .digit (some .z), .insert .comma,
        .digit (some .z), .digit (some .z), .digit (some .z), .insert .comma, .digit (some .z),
        .digit (some .z), .digit (some .z), .point, .digit (some .z), .digit (some .z)] = true := by decide
  have hfs : Edit.floatSym [.plus, .z, .z, .z, .comma, .z, .z, .z, .comma, .z, .z, .z, .dot, .z, .z] = none := by decide
  unfold editPlus plusPic Edit.edit Edit.editOpt
  simp only [hc, Option.bind_eq_bind, Option.bind_some, hf, hfs, Bool.not_true, Bool.false_eq_true,
    ↓reduceIte]
  repeat' split
  all_goals simp [Edit.editOpt.gen, Edit.picWidth, Edit.width, Edit.fixedBytes]

/-! ## Lemmas: key lookups -/

theorem findKey_lt {k : KeyDecl} {v : List UInt8} :
    ∀ {l : List (List UInt8)} {i : Nat}, Sem.findKey k v l = some i → i < l.length
  | [], _, h => by simp [Sem.findKey] at h
  | r :: rs, i, h => by
    simp only [Sem.findKey] at h
    split at h
    · simp at h; subst h; simp
    · obtain ⟨j, hj, rfl⟩ := Option.map_eq_some_iff.mp h
      have := findKey_lt hj
      simp; omega

theorem getD_mem {α : Type} [Inhabited α] {l : List α} {i : Nat} (h : i < l.length) :
    l.getD i default ∈ l := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

theorem getD_map {α : Type} [Inhabited α] (f : α → List UInt8) (l : List α) {i : Nat}
    (h : i < l.length) : (l.map f).getD i [] = f (l.getD i default) := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

theorem getD_mem' {l : List (List UInt8)} {i : Nat} (h : i < l.length) : l.getD i [] ∈ l := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

/-! ## Lemmas: the page break test `FUNCTION MOD (WS-LINE-COUNTER, WS-PAGE-SIZE) = 0` -/

theorem mod20 (x : Int) : x - 20 * divRound .towardLesser x 20 = x % 20 := by
  simp only [divRound]; exact (Int.emod_def x 20).symm

theorem compare_mod20_eq {x : Int} (h : x % 20 = 0) : compare (x % 20) 0 = .eq := by
  rw [h]; decide

theorem compare_mod20_gt {x : Int} (h : x % 20 ≠ 0) : compare (x % 20) 0 = .gt := by
  have h1 : ¬ x % 20 < 0 := by omega
  simp only [compare, compareOfLessAndEq, h1, h, ↓reduceIte]

/-! ## Lemmas: the transaction record's fields

Symbolic execution keeps `t.bytes` folded; a field read from it is `(t.bytes.drop o).take n`. -/

theorem Tran.length_bytes (t : Tran) (h : t.valid) : t.bytes.length = 350 := by
  obtain ⟨h1, h2, -, -, h5, h6, -, h8, h9, h10, h11, h12⟩ := h
  simp [Tran.bytes, length_encodeNum, NumFmt.byteLen, h1, h2, h5, h6, h8, h9, h10, h11, h12]

theorem Tran.field_id (t : Tran) (h : t.valid) : t.bytes.take 16 = t.id := by
  obtain ⟨h1, -, -, -, -, -, -, -, -, -, -, -⟩ := h
  simp [Tran.bytes, h1]

theorem Tran.field_ty (t : Tran) (h : t.valid) : (t.bytes.drop 16).take 2 = t.ty := by
  obtain ⟨h1, h2, -, -, -, -, -, -, -, -, -, -⟩ := h
  simp [Tran.bytes, h1, h2]

theorem Tran.field_cat (t : Tran) (h : t.valid) : (t.bytes.drop 18).take 4 = encodeNum {} ({ digits := 4 } : NumFmt) t.cat := by
  obtain ⟨h1, h2, -, -, -, -, -, -, -, -, -, -⟩ := h
  simp [Tran.bytes, length_encodeNum, NumFmt.byteLen, List.drop_append, List.drop_of_length_le,
    h1, h2]

theorem Tran.field_src (t : Tran) (h : t.valid) : (t.bytes.drop 22).take 10 = t.src := by
  obtain ⟨h1, h2, -, -, h5, -, -, -, -, -, -, -⟩ := h
  simp [Tran.bytes, length_encodeNum, NumFmt.byteLen, List.drop_append, List.drop_of_length_le,
    h1, h2, h5]

theorem Tran.field_amt (t : Tran) (h : t.valid) : (t.bytes.drop 132).take 11 = encodeNum {} TRAN_AMT.fmt t.amt := by
  obtain ⟨h1, h2, -, -, h5, h6, -, -, -, -, -, -⟩ := h
  simp [Tran.bytes, length_encodeNum, NumFmt.byteLen, List.drop_append, List.drop_of_length_le,
    h1, h2, h5, h6]

theorem Tran.field_card (t : Tran) (h : t.valid) : (t.bytes.drop 262).take 16 = t.card := by
  obtain ⟨h1, h2, -, -, h5, h6, -, h8, h9, -, -, -⟩ := h
  simp [Tran.bytes, length_encodeNum, NumFmt.byteLen, List.drop_append, List.drop_of_length_le,
    h1, h2, h5, h6, h8, h9]

theorem Tran.field_proc (t : Tran) (h : t.valid) : (t.bytes.drop 304).take 26 = t.proc := by
  obtain ⟨h1, h2, -, -, h5, h6, -, h8, h9, h10, h11, -⟩ := h
  simp [Tran.bytes, length_encodeNum, NumFmt.byteLen, List.drop_append, List.drop_of_length_le,
    h1, h2, h5, h6, h8, h9, h10, h11]

/-- `TRAN-PROC-TS (1:10)`, the date the range check compares. -/
theorem Tran.field_proc10 (t : Tran) (h : t.valid) : (t.bytes.drop 304).take 10 = t.proc.take 10 := by
  rw [← Tran.field_proc t h, List.take_take]
  simp

/-! ## Lemmas: the model -/

section ModelLemmas
variable (xrefs : List Xref) (types catgs : List (List UInt8)) (start end_ : List UInt8)

theorem report3_append (ts : List Tran) (t : Tran) :
    report3 xrefs types catgs start end_ (ts ++ [t]) =
      step3 xrefs types catgs start end_ (report3 xrefs types catgs start end_ ts) t := by
  simp [report3, List.foldl_append]

theorem report3_nil : report3 xrefs types catgs start end_ [] =
    ⟨List.replicate 16 64, true, 0, 0, 0, 0, 0, []⟩ := rfl

theorem foldl_step3_first : ∀ (ts : List Tran) (s : M3), ts ≠ [] →
    (ts.foldl (step3 xrefs types catgs start end_) s).first = false
  | [], _, h => absurd rfl h
  | [t], s, _ => by simp [step3]
  | t :: u :: us, s, _ => by
    rw [List.foldl_cons]
    exact foldl_step3_first (u :: us) _ (by simp)

theorem report3_first (ts : List Tran) (h : ts ≠ []) :
    (report3 xrefs types catgs start end_ ts).first = false :=
  foldl_step3_first xrefs types catgs start end_ ts _ h

theorem foldl_step3_lines : ∀ (ts : List Tran) (s : M3),
    (ts.foldl (step3 xrefs types catgs start end_) s).lines ≤ s.lines + 13 * ts.length
  | [], s => by simp
  | t :: ts, s => by
    rw [List.foldl_cons]
    have := foldl_step3_lines ts (step3 xrefs types catgs start end_ s t)
    have hs : (step3 xrefs types catgs start end_ s t).lines ≤ s.lines + 13 := by
      unfold step3
      simp only
      split <;> split <;> split <;> omega
    simp only [List.length_cons]
    omega

theorem report3_lines (ts : List Tran) :
    (report3 xrefs types catgs start end_ ts).lines ≤ 13 * ts.length := by
  have := foldl_step3_lines xrefs types catgs start end_ ts ⟨List.replicate 16 64, true, 0, 0, 0, 0, 0, []⟩
  simpa [report3] using this

theorem fitTot_bound (v : Int) : (fitTot v).natAbs < 100000000000 := by
  have h := fitNum_holds {} WS_PAGE_TOTAL.fmt v
  unfold NumFmt.Holds at h
  simp [NumFmt.fullBinary, WS_PAGE_TOTAL.fmt] at h
  unfold fitTot
  simp [WS_PAGE_TOTAL.fmt]
  omega

theorem ite_natAbs_lt {c : Prop} [Decidable c] {a b : Int} {B : Nat} (ha : a.natAbs < B)
    (hb : b.natAbs < B) : (if c then a else b).natAbs < B := by
  split <;> assumption

/-- The running totals are values of their `S9(09)V99` fields. -/
theorem foldl_step3_bounds : ∀ (ts : List Tran) (s : M3), s.page.natAbs < 100000000000 →
    s.acct.natAbs < 100000000000 → s.grand.natAbs < 100000000000 →
    (ts.foldl (step3 xrefs types catgs start end_) s).page.natAbs < 100000000000 ∧
    (ts.foldl (step3 xrefs types catgs start end_) s).acct.natAbs < 100000000000 ∧
    (ts.foldl (step3 xrefs types catgs start end_) s).grand.natAbs < 100000000000
  | [], s, h1, h2, h3 => ⟨h1, h2, h3⟩
  | t :: ts, s, h1, h2, h3 => by
    rw [List.foldl_cons]
    apply foldl_step3_bounds ts
    · simp only [step3]; apply fitTot_bound
    · simp only [step3]; apply fitTot_bound
    · simp only [step3]
      exact ite_natAbs_lt (fitTot_bound _) h3

theorem report3_bounds (ts : List Tran) :
    (report3 xrefs types catgs start end_ ts).page.natAbs < 100000000000 ∧
    (report3 xrefs types catgs start end_ ts).acct.natAbs < 100000000000 ∧
    (report3 xrefs types catgs start end_ ts).grand.natAbs < 100000000000 :=
  foldl_step3_bounds xrefs types catgs start end_ ts _ (by decide) (by decide) (by decide)

/-- The current card is a transaction's card (or the initial spaces). -/
theorem foldl_step3_card_length : ∀ (ts : List Tran) (s : M3), s.card.length = 16 →
    (∀ t ∈ ts, t.card.length = 16) → (ts.foldl (step3 xrefs types catgs start end_) s).card.length = 16
  | [], s, h, _ => h
  | t :: ts, s, _, ht => by
    rw [List.foldl_cons]
    exact foldl_step3_card_length ts _ (by simp [step3, ht t (by simp)]) (fun u hu => ht u (by simp [hu]))

theorem report3_card_length (ts : List Tran) (h : ∀ t ∈ ts, t.card.length = 16) :
    (report3 xrefs types catgs start end_ ts).card.length = 16 :=
  foldl_step3_card_length xrefs types catgs start end_ ts _ (by simp) h

end ModelLemmas

/-- The initial values of the totals and the line counter (`VALUE 0`). -/
theorem enc_total_zero : encodeNum {} WS_PAGE_TOTAL.fmt 0 =
    [240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 192] := by decide +kernel

theorem enc_lines_zero : encodeNum {} WS_LINE_COUNTER.fmt 0 = [0, 0, 0, 0, 15] := by decide +kernel

/-- The report name header in storage after the first detail: the name, the two dates. -/
theorem name_read (mem : Mem) (parm : List UInt8) (h1 : mem.read 1261 91 = nameHead)
    (h2 : mem.read 1352 10 = parm.take 10) (h3 : mem.read 1362 4 = toMsg)
    (h4 : mem.read 1366 10 = (parm.drop 11).take 10) :
    mem.read 1261 115 = nameHead ++ (parm.take 10 ++ (toMsg ++ (parm.drop 11).take 10)) := by
  have e1 := Mem.read_append mem 1261 91 24
  have e2 := Mem.read_append mem 1352 10 14
  have e3 := Mem.read_append mem 1362 4 10
  simp only [Nat.reduceAdd] at e1 e2 e3
  rw [e1, e2, e3, h1, h2, h3, h4]

/-! ## The loop invariant -/

/-- Loop invariant, indexed by the outcomes of the remaining `READ`s: after the transactions
`done`, the report state in storage is the model's (current card, first-detail flag, line
counter, totals); the constants (headers, fillers, page size, date range) are unchanged; after the
first detail the report dates, the current card's account id and the last transaction are in
storage; the events are the model's, and after the end of file also `eofEvents`. -/
def Inv (xrefs : List Xref) (types catgs : List (List UInt8)) (parm : List UInt8)
    (trans : List Tran) (inp0 : List (Nat × List (List UInt8))) (rest : List (Option Tran))
    (st : State) : Prop :=
  ∃ done todo, trans = done ++ todo ∧
    ((rest = [] ∧ todo = []) ∨ rest = todo.map some ++ [none]) ∧
    st.idx = [] ∧ st.slots = [] ∧ st.active = [] ∧ st.inp = inp0 ∧ st.mem.size = 2309 ∧
    st.mem.read 2300 1 = (if rest.isEmpty then [232] else [213]) ∧
    st.mem.read 2272 16 = (report3 xrefs types catgs (parm.take 10) ((parm.drop 11).take 10) done).card ∧
    st.mem.read 2098 1 = (if done = [] then [232] else [213]) ∧
    (rest ≠ [] → st.mem.read 2099 5 = encodeNum {} WS_LINE_COUNTER.fmt (report3 xrefs types catgs (parm.take 10) ((parm.drop 11).take 10) done).lines ∧
      st.mem.read 2239 11 = encodeNum {} WS_PAGE_TOTAL.fmt (report3 xrefs types catgs (parm.take 10) ((parm.drop 11).take 10) done).page ∧
      st.mem.read 2250 11 = encodeNum {} WS_ACCOUNT_TOTAL.fmt (report3 xrefs types catgs (parm.take 10) ((parm.drop 11).take 10) done).acct ∧
      st.mem.read 2261 11 = encodeNum {} WS_GRAND_TOTAL.fmt (report3 xrefs types catgs (parm.take 10) ((parm.drop 11).take 10) done).grand) ∧
    st.mem.read 2077 21 = parm.take 21 ∧
    st.mem.read 2104 2 = encodeNum {} WS_PAGE_SIZE.fmt 20 ∧
    st.mem.read 2106 133 = blankLine ∧ st.mem.read 1490 114 = header1 ∧
    st.mem.read 1604 133 = hdr2Line ∧ st.mem.read 1261 91 = nameHead ∧ st.mem.read 1362 4 = toMsg ∧
    st.mem.read 1737 97 = pageHead ∧ st.mem.read 1849 97 = acctHead ∧
    st.mem.read 1961 97 = grandHead ∧
    st.mem.read 1392 1 = [64] ∧ st.mem.read 1404 1 = [64] ∧ st.mem.read 1407 1 = [96] ∧
    st.mem.read 1423 1 = [64] ∧ st.mem.read 1428 1 = [96] ∧ st.mem.read 1458 1 = [64] ∧
    st.mem.read 1469 4 = [64, 64, 64, 64] ∧ st.mem.read 1488 2 = [64, 64] ∧
    (done = [] ∨
      (st.mem.read 1352 10 = parm.take 10 ∧ st.mem.read 1366 10 = (parm.drop 11).take 10 ∧
        st.mem.read 1110 11 = encodeNum {} XREF_ACCT_ID.fmt (report3 xrefs types catgs (parm.take 10) ((parm.drop 11).take 10) done).xacct ∧
        (report3 xrefs types catgs (parm.take 10) ((parm.drop 11).take 10) done).xacct.natAbs < 100000000000 ∧ 0 ≤ (report3 xrefs types catgs (parm.take 10) ((parm.drop 11).take 10) done).xacct ∧
        st.mem.read 733 350 = (done.getLast?.getD default).bytes)) ∧
    (∃ f1 f2 f3 f4 f5 f6 : FileSt,
      st.files = [(1, f1), (5, f5), (2, f2), (3, f3), (4, f4), (6, f6)] ∧
      f1.mode = some .input ∧ f1.recs = trans.map Tran.bytes ∧ f1.pos = done.length ∧
      f1.eof = rest.isEmpty ∧
      f2.mode = some .input ∧ f2.recs = xrefs.map Xref.bytes ∧ f3.mode = some .input ∧
      f3.recs = types ∧ f4.mode = some .input ∧ f4.recs = catgs ∧ f5.mode = some .output ∧
      f6.mode = some .input) ∧
    st.out = (if rest.isEmpty then eofEvents (report3 xrefs types catgs (parm.take 10) ((parm.drop 11).take 10) done) (done.getLast?.getD default) else []) ++
      (report3 xrefs types catgs (parm.take 10) ((parm.drop 11).take 10) done).out ++
      [.display (reportingMsg ++ parm.take 10 ++ toMsg ++ (parm.drop 11).take 10), .display startMsg]

set_option maxHeartbeats 60000000 in
set_option maxRecDepth 20000 in
/-- **CBTRN03C on any input (in its domain).**  For every non-empty transaction file, every
cross-reference, transaction type and category file, every date-parameter record and every
initial storage, CBTRN03C ends with `GOBACK` and its events are: the start message, the date
range, then for each transaction what `step3` says, then what `eofEvents` says (the last
transaction's amount is counted again, the last card's account total is never written), then
the end message.  The domain: every transaction's processing date is in the range (the job's
SORT step selects them; a date outside it ends the report early by `NEXT SENTENCE`), every
lookup finds its record (otherwise the program abends), and no card number is blank (the
initial value of the current card). -/
theorem cbtrn03c_report (m : Mem) (hm : m.size = 2309)
    (trans : List Tran) (htv : ∀ t ∈ trans, t.valid) (hne : trans ≠ [])
    (hlen : trans.length < 10000000)
    (xrefs : List Xref) (hxv : ∀ x ∈ xrefs, x.valid)
    (types catgs : List (List UInt8)) (htyl : ∀ r ∈ types, r.length = 60)
    (hcgl : ∀ r ∈ catgs, r.length = 60)
    (parm : List UInt8) (hpl : parm.length = 80) (prest : List (List UInt8))
    (hdate : ∀ t ∈ trans, Sem.cmpBytes (t.proc.take 10) (parm.take 10) ≠ .lt ∧
      Sem.cmpBytes (t.proc.take 10) ((parm.drop 11).take 10) ≠ .gt)
    (hxf : ∀ t ∈ trans,
      (Sem.findKey { off := 0, len := 16 } t.card (xrefs.map Xref.bytes)).isSome)
    (htf : ∀ t ∈ trans, (Sem.findKey { off := 0, len := 2 } t.ty types).isSome)
    (hcf : ∀ t ∈ trans, (Sem.findKey { off := 0, len := 6 }
      (t.ty ++ encodeNum {} FD_TRAN_CAT_CD.fmt t.cat) catgs).isSome)
    (hcard : ∀ t ∈ trans, t.card ≠ List.replicate 16 64)
    (n : Nat) (hn : trans.length < n) :
    let r := Cbtrn03c.run {} (n + 60) (Cbtrn03c.initState m
      [(1, trans.map Tran.bytes), (2, xrefs.map Xref.bytes), (3, types), (4, catgs),
        (6, parm :: prest)])
    let s := report3 xrefs types catgs (parm.take 10) ((parm.drop 11).take 10) trans
    r.1 = .stop .goback ∧
      r.2.out = [.display endMsg] ++ eofEvents s (trans.getLast hne) ++ s.out ++
        [.display (reportingMsg ++ parm.take 10 ++ toMsg ++ (parm.drop 11).take 10),
          .display startMsg] := by
  intro r s
  simp only [r]
  cobol_auto
  cobol_loop (Inv xrefs types catgs parm trans
      [(1, trans.map Tran.bytes), (2, xrefs.map Xref.bytes), (3, types), (4, catgs),
        (6, parm :: prest)]) (trans.map some ++ [none])
  · -- after the loop: six CLOSEs, DISPLAY, GOBACK
    obtain ⟨mem, idx, slots, saves, active, out, inp, files, clockN⟩ := loopState
    obtain ⟨done, todo, hd, hrest, rfl, rfl, rfl, rfl, hsz, heof, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
      ⟨f1, f2, f3, f4, f5, f6, rfl, h1m, -, -, -, h2m, -, h3m, -, h4m, -, h5m, h6m⟩, hout⟩ := hloopInv
    rcases hrest with ⟨-, rfl⟩ | h
    · simp only [List.append_nil] at hd
      subst hd
      dsimp only at hsz heof hout
      simp only [List.isEmpty_nil, ↓reduceIte] at heof hout
      cobol_auto
      simp only [s, List.getLast?_eq_some_getLast hne, Option.getD_some] at hout ⊢
      simp [hout, endMsg]
    · simp at h
  · -- before the loop: the date range read, nothing else
    cobol_inv [report3_nil, blankLine, hdr2Line, header1, nameHead, toMsg, pageHead, acctHead, grandHead,
      reportingMsg, startMsg, List.drop_take, List.take_take, enc_total_zero, enc_lines_zero] with [], trans
  · simp; omega
  · -- the loop ends exactly after the end-of-file READ
    rintro ⟨mem, idx, slots, saves, active, out, inp, files, clockN⟩
      ⟨-, -, -, -, -, -, -, -, -, heof, -⟩
    simp only [List.isEmpty_nil, ↓reduceIte] at heof
    cobol_auto
  · -- one iteration: READ the next transaction and report it, or reach the end of the file
    rintro y ys ⟨mem, idx, slots, saves, active, out, inp, files, clockN⟩
      ⟨done, todo, hd, hrest, rfl, rfl, rfl, rfl, hsz, heof, hcard, hfirst, hnum, hdp, hps, hbl, hh1,
        hh2, hnh, hto, hph, hah, hgh, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hphase,
        ⟨f1, f2, f3, f4, f5, f6, rfl, h1m, h1r, h1p, h1e, h2m, h2r, h3m, h3r, h4m, h4r, h5m, h6m⟩,
        hout⟩
    dsimp only at hsz heof hcard hfirst hnum hdp hps hbl hh1 hh2 hnh hto hph hah hgh
    dsimp only at hf1 hf2 hf3 hf4 hf5 hf6 hf7 hf8 hphase hout
    rcases hrest with ⟨h, -⟩ | hrest
    · simp at h
    obtain ⟨hlines, hpage, hacct, hgrand⟩ := hnum (by simp)
    clear hnum
    simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte] at heof h1e hout
    refine ⟨by cobol_auto, ?_⟩
    -- the model after `done`
    have hb := report3_bounds xrefs types catgs (parm.take 10) ((parm.drop 11).take 10) done
    have hlb := report3_lines xrefs types catgs (parm.take 10) ((parm.drop 11).take 10) done
    have hcl := report3_card_length xrefs types catgs (parm.take 10) ((parm.drop 11).take 10) done
      (fun t ht => (htv t (by simp [hd, ht])).2.2.2.2.2.2.2.2.1)
    generalize hS : report3 xrefs types catgs (parm.take 10) ((parm.drop 11).take 10) done = S
      at hcard hlines hpage hacct hgrand hphase hout hb hlb hcl
    obtain ⟨hpb, hab, hgb⟩ := hb
    have hdl : done.length < 10000000 := by
      have := hlen; rw [hd] at this; simp only [List.length_append] at this; omega
    have hl0 : S.lines < 130000000 := by omega
    cases todo with
    | nil =>
      -- the end-of-file READ: the last transaction's amount is added again, page and grand totals
      simp only [List.map_nil, List.nil_append, List.cons.injEq] at hrest
      obtain ⟨rfl, rfl⟩ := hrest
      simp only [List.append_nil] at hd
      subst hd
      have hnone : f1.recs[f1.pos]? = none := by rw [h1r, h1p]; simp
      rcases hphase with h0 | ⟨hsd, hed, hxa, hxa1, hxa2, htr⟩
      · exact absurd h0 hne
      have hlm : trans.getLast?.getD default ∈ trans := by
        cases h : trans.getLast? with
        | none => simp at h; exact absurd h hne
        | some t => simpa using List.mem_of_getLast? h
      generalize hL : trans.getLast?.getD default = tl at htr hout hlm
      have htl := htv tl hlm
      obtain ⟨hd1, hd2⟩ := hdate tl hlm
      have tb := Tran.length_bytes tl htl
      have tfa := Tran.field_amt tl htl
      have tfp := Tran.field_proc10 tl htl
      obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12⟩ := htl
      cobol_auto [edit_plus, editPlus_length, List.take_take, List.drop_take, pageHead_length,
        grandHead_length, hdr2Line_length]
      cobol_inv [eofEvents, pageLine, grandLine, pageMsg, amtMsg, hout, editPlus_length,
        pageHead_length, grandHead_length, hdr2Line_length, hS, hL, fitTot] with trans, []
    | cons t todo' =>
      -- a transaction: READ, the date check, DISPLAY, the lookups, the report lines
      simp only [List.map_cons, List.cons_append, List.cons.injEq] at hrest
      obtain ⟨rfl, rfl⟩ := hrest
      subst hd
      have htm : t ∈ done ++ t :: todo' := by simp
      obtain ⟨hd1, hd2⟩ := hdate t htm
      have hc0 := hcard t htm
      obtain ⟨ix, hix⟩ := Option.isSome_iff_exists.mp (hxf t htm)
      obtain ⟨it, hit⟩ := Option.isSome_iff_exists.mp (htf t htm)
      obtain ⟨ic, hic⟩ := Option.isSome_iff_exists.mp (hcf t htm)
      have htv' := htv t htm
      have hsome : f1.recs[f1.pos]? = some t.bytes := by rw [h1r, h1p]; simp
      have tb := Tran.length_bytes t htv'
      have tf1 := Tran.field_id t htv'
      have tf2 := Tran.field_ty t htv'
      have tf3 := Tran.field_cat t htv'
      have tf4 := Tran.field_src t htv'
      have tf6 := Tran.field_amt t htv'
      have tf11 := Tran.field_card t htv'
      have tfp := Tran.field_proc10 t htv'
      obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12⟩ := htv'
      -- the type and category records
      have hitl := findKey_lt hit
      have hicl := findKey_lt hic
      have htyr := htyl _ (getD_mem' hitl)
      have hcgr := hcgl _ (getD_mem' hicl)
      -- the cross-reference record (read on a new card)
      have hixl := findKey_lt hix
      simp only [List.length_map] at hixl
      obtain ⟨x1, x2, x3, x4, x5⟩ := hxv _ (getD_mem hixl)
      have hxg := getD_map Xref.bytes xrefs hixl
      by_cases hc : S.card = t.card
      · -- the card of the previous transaction (so not the first one)
        have hdn : done ≠ [] := by
          rintro rfl
          rw [report3_nil] at hS
          exact hc0 (by rw [← hc, ← hS])
        have hSf : S.first = false := by rw [← hS]; exact report3_first _ _ _ _ _ done hdn
        simp only [hdn, ↓reduceIte] at hfirst
        rcases hphase with h0 | ⟨hsd, hed, hxa, hxa1, hxa2, htr⟩
        · exact absurd h0 hdn
        have hnl := name_read mem parm hnh hsd hto hed
        by_cases hb : S.lines % 20 = 0
        · -- a page break before the detail line
          have hm := compare_mod20_eq (x := (S.lines : Int)) (by omega)
          cobol_auto [edit_minus, edit_minus_zero, edit_plus, editMinus_length, editPlus_length, List.take_take,
            List.drop_take, pageHead_length, nameHead_length, header1_length, toMsg_length,
            hdr2Line_length, blankLine_length, mod20, hm, hc, hit, hic, htyr, hcgr, hnl]
          cobol_inv [report3_append, step3, hS, hout, hSf, hc, hb, headers, hdr1Line, nameLine,
            pageLine, detailLine, typeDesc, catDesc, hit, hic, fitTot, editPlus_length,
            editMinus_length, pageHead_length, nameHead_length, header1_length, toMsg_length,
            hdr2Line_length, blankLine_length, Int.natCast_add,
            Int.add_assoc] with done ++ [t], todo'
        · -- no page break
          have hm := compare_mod20_gt (x := (S.lines : Int)) (by omega)
          cobol_auto [edit_minus, edit_minus_zero, edit_plus, editMinus_length, editPlus_length, List.take_take,
            List.drop_take, mod20, hm, hc, hit, hic, htyr, hcgr]
          cobol_inv [report3_append, step3, hS, hout, hSf, hc, hb, detailLine, typeDesc, catDesc,
            hit, hic, fitTot, editMinus_length, Int.natCast_add,
            Int.add_assoc] with done ++ [t], todo'
      · by_cases hdn : done = []
        · -- the first transaction: the headers, the cross-reference lookup
          have hS0 : report3 xrefs types catgs (parm.take 10) ((parm.drop 11).take 10) done =
              ⟨List.replicate 16 64, true, 0, 0, 0, 0, 0, []⟩ := by rw [hdn]; rfl
          have hSl : S.lines = 0 := by rw [← hS, hS0]
          have hSp : S.page = 0 := by rw [← hS, hS0]
          have hSa : S.acct = 0 := by rw [← hS, hS0]
          have hSg : S.grand = 0 := by rw [← hS, hS0]
          have hSf : S.first = true := by rw [← hS, hS0]
          have hSo : S.out = [] := by rw [← hS, hS0]
          simp [hdn] at hfirst
          have hm : compare ((4 : Int) % 20) 0 = .gt := by decide
          have hm' : compare (4 : Int) 0 = .gt := by decide
          cobol_auto [edit_minus, edit_minus_zero, edit_plus, editMinus_length, editPlus_length, List.take_take,
            List.drop_take, nameHead_length, header1_length, toMsg_length, hdr2Line_length,
            blankLine_length, mod20, hm, hm', hc, hSl, hSp, hSa, hSg, Xref.bytes, hxg, hix, hit,
            hic, htyr, hcgr]
          cobol_inv [report3_append, step3, hS, hout, hSl, hSp, hSa, hSg, hSf, hSo, hc, headers,
            hdr1Line, nameLine, detailLine, typeDesc, catDesc, xrefOf, hix, hit, hic, fitTot,
            editMinus_length, nameHead_length, header1_length, toMsg_length, hdr2Line_length,
            blankLine_length, Int.natCast_add, Int.add_assoc] with done ++ [t], todo'
        · -- a new card: the account total of the previous card, the cross-reference lookup
          have hSf : S.first = false := by rw [← hS]; exact report3_first _ _ _ _ _ done hdn
          simp only [hdn, ↓reduceIte] at hfirst
          rcases hphase with h0 | ⟨hsd, hed, hxa, hxa1, hxa2, htr⟩
          · exact absurd h0 hdn
          have hnl := name_read mem parm hnh hsd hto hed
          by_cases hb : (S.lines + 2) % 20 = 0
          · have hm := compare_mod20_eq (x := (S.lines : Int) + 1 + 1) (by omega)
            cobol_auto [edit_minus, edit_minus_zero, edit_plus, editMinus_length, editPlus_length, List.take_take,
              List.drop_take, pageHead_length, acctHead_length, nameHead_length, header1_length,
              toMsg_length, hdr2Line_length, blankLine_length, mod20, hm, hc, Xref.bytes, hxg,
              hix, hit, hic, htyr, hcgr, hnl]
            cobol_inv [report3_append, step3, hS, hout, hSf, hc, hb, headers, hdr1Line, nameLine,
              pageLine, acctLine, detailLine, typeDesc, catDesc, xrefOf, hix, hit, hic, fitTot,
              editPlus_length, editMinus_length, pageHead_length, acctHead_length,
              nameHead_length, header1_length, toMsg_length, hdr2Line_length, blankLine_length,
              Int.natCast_add, Int.add_assoc] with done ++ [t], todo'
          · have hm := compare_mod20_gt (x := (S.lines : Int) + 1 + 1) (by omega)
            cobol_auto [edit_minus, edit_minus_zero, edit_plus, editMinus_length, editPlus_length, List.take_take,
              List.drop_take, acctHead_length, hdr2Line_length, mod20, hm, hc, Xref.bytes, hxg,
              hix, hit, hic, htyr, hcgr]
            cobol_inv [report3_append, step3, hS, hout, hSf, hc, hb, acctLine, detailLine,
              typeDesc, catDesc, xrefOf, hix, hit, hic, fitTot, editPlus_length,
              editMinus_length, acctHead_length, hdr2Line_length, Int.natCast_add, Int.add_assoc] with done ++ [t], todo'

end Cbtrn03c
end CardDemo

#print axioms CardDemo.Cbtrn03c.cbtrn03c_report
