import EquivLean.Bridge.Cobol.Records

/-!
# CBTRN03C: what the translations output, from the input field values

CBTRN03C reads the reporting date range (the first record of the date parameter file; with none
it stops at once), then the transactions in order:
- a transaction whose processing date (`TRAN-PROC-TS (1:10)`) is outside the range ends the loop
  (`NEXT SENTENCE` leaves the inline `PERFORM`; nothing more is written);
- otherwise it DISPLAYs the record; on a change of card it writes the previous account's totals
  (not before the first transaction) and looks up the card's cross-reference; it looks up the
  transaction type and the category (a failed keyed READ displays the key and abends); it writes
  the report lines: the headers at the first transaction, the page totals and headers when the
  line counter is a multiple of the page size 20, and the detail line;
- at the end of file the date test applies to the last record read (the record area's initial
  contents when there is none); when it passes, the last amount is added to the totals once more,
  the totals are DISPLAYed, and the page and grand totals are written.  The last account's totals
  are not written.

`run`: these steps on field values, as the translations perform them.  `loop` walks the
transaction file; a failed lookup ends it with `.error` (the abend).  The displayed lines and the
report lines are code points, as in `Cbtrn01c.Model`; the outputs give the report lines as field
values of `FD-REPTFILE-REC` (EBCDIC bytes, `ebc`).
-/

open Cobol EquivLean.Cobol.Rec
open Cobol.Digits (toDigits)

namespace EquivLean.Modernize.Cbtrn03c.Model

cobol_schema TranRecord from "../../../examples/cobol/carddemo/cbtrn03c.ir.json" record "TRAN-RECORD"
cobol_schema CardXrefRecord from "../../../examples/cobol/carddemo/cbtrn03c.ir.json" record "CARD-XREF-RECORD"
cobol_schema TranTypeRecord from "../../../examples/cobol/carddemo/cbtrn03c.ir.json" record "TRAN-TYPE-RECORD"
cobol_schema TranCatRecord from "../../../examples/cobol/carddemo/cbtrn03c.ir.json" record "TRAN-CAT-RECORD"
cobol_schema WsDateparmRecord from "../../../examples/cobol/carddemo/cbtrn03c.ir.json" record "WS-DATEPARM-RECORD"
cobol_schema FdReptfileRec from "../../../examples/cobol/carddemo/cbtrn03c.ir.json" record "FD-REPTFILE-REC"

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

/-- The code points of EBCDIC bytes (CP037). -/
def cps (bs : List UInt8) : List Nat := bs.map cp037Code

/-- The EBCDIC byte of a code point (CP037 maps `0 ..= 255` onto the bytes). -/
def ebc (u : Nat) : UInt8 := (_root_.Cobol.Codepage.cp037Byte (Char.ofNat u)).getD 0

/-- `n` EBCDIC spaces. -/
def sp (n : Nat) : List UInt8 := List.replicate n 64

/-! ## Field access -/

/-- `TRAN-ID`, `TRAN-TYPE-CD`, `TRAN-CAT-CD`, `TRAN-SOURCE`, `TRAN-AMT`, `TRAN-CARD-NUM` of a
transaction, and the date part of `TRAN-PROC-TS`. -/
def tId (t : List FVal) : List UInt8 := strOf (t.getD 0 default)
def tType (t : List FVal) : List UInt8 := strOf (t.getD 1 default)
def tCat (t : List FVal) : Int := numOf (t.getD 2 default)
def tSource (t : List FVal) : List UInt8 := strOf (t.getD 3 default)
def tAmt (t : List FVal) : Int := numOf (t.getD 5 default)
def tCard (t : List FVal) : List UInt8 := strOf (t.getD 10 default)
def tDate (t : List FVal) : List UInt8 := (strOf (t.getD 12 default)).take 10

/-- `XREF-CARD-NUM`, `XREF-ACCT-ID` of a cross-reference record. -/
def xCard (x : List FVal) : List UInt8 := strOf (x.getD 0 default)
def xAcct (x : List FVal) : Int := numOf (x.getD 2 default)

/-- `TRAN-TYPE`, `TRAN-TYPE-DESC` of a transaction type record. -/
def yType (y : List FVal) : List UInt8 := strOf (y.getD 0 default)
def yDesc (y : List FVal) : List UInt8 := strOf (y.getD 1 default)

/-- `TRAN-TYPE-CD`, `TRAN-CAT-CD`, `TRAN-CAT-TYPE-DESC` of a category record. -/
def cType (c : List FVal) : List UInt8 := strOf (c.getD 0 default)
def cCat (c : List FVal) : Int := numOf (c.getD 1 default)
def cDesc (c : List FVal) : List UInt8 := strOf (c.getD 2 default)

/-- `WS-START-DATE`, `WS-END-DATE` of the date parameters. -/
def dStart (d : List FVal) : List UInt8 := strOf (d.getD 0 default)
def dEnd (d : List FVal) : List UInt8 := strOf (d.getD 2 default)

/-! ## The date test -/

/-- Byte strings in the EBCDIC collating sequence, at their first difference (the strings
compared have equal lengths). -/
def cmpB : List UInt8 → List UInt8 → Ordering
  | a :: as, b :: bs => if a < b then .lt else if b < a then .gt else cmpB as bs
  | _, _ => .eq

/-- `TRAN-PROC-TS (1:10) >= WS-START-DATE AND TRAN-PROC-TS (1:10) <= WS-END-DATE`. -/
def inRange (d t : List FVal) : Bool :=
  cmpB (tDate t) (dStart d) != .lt && cmpB (tDate t) (dEnd d) != .gt

/-! ## The report lines (code points) -/

/-- `s` in a field of width `w`: truncated, or padded with spaces. -/
def pad (s : List Nat) (w : Nat) : List Nat := s.take w ++ List.replicate (w - s.length) 32

/-- The `w` low digits of `|v|` (an unsigned DISPLAY field). -/
def digs (w : Nat) (v : Int) : List Nat := zpad w v.natAbs

/-- A signed DISPLAY field of `w` digits: the leading digits, then the last digit overpunched
with the sign. -/
def zoned (w : Nat) (v : Int) : List Nat :=
  zpad (w - 1) (v.natAbs / 10) ++ [overpunch (decide (v < 0)) (v.natAbs % 10)]

/-- `ZZZ,ZZZ,ZZZ` over the digits `ds`: while `sup` (zero suppression), leading zeros and the
commas between them become spaces. -/
def zzz : List Char → List Nat → Bool → List Nat
  | [], _, _ => []
  | c :: p, ds, sup =>
    if c = ',' then (if sup then 32 else 44) :: zzz p ds sup
    else match ds with
      | [] => []
      | d :: ds => if sup && d == 0 then 32 :: zzz p ds true else (48 + d) :: zzz p ds false

/-- The numeric-edited amount `[+|-]ZZZ,ZZZ,ZZZ.ZZ` (`-ZZZ…` when `plus` is false): all spaces
for zero; else the sign (`-` for a negative amount, `+` or a space otherwise), the integer part
with zero suppression and commas, the point and two decimals. -/
def editAmt (v : Int) (plus : Bool) : List Nat :=
  let mag := v.natAbs % 100000000000
  if mag = 0 then List.replicate 15 32
  else (if v < 0 then 45 else if plus then 43 else 32) ::
    (zzz "ZZZ,ZZZ,ZZZ".toList (toDigits 10 9 (mag / 100)) true ++
      [46, 48 + mag % 100 / 10, 48 + mag % 10])

/-- A report line: 133 characters. -/
def to133 (l : List Nat) : List Nat := pad l 133

/-- `REPORT-NAME-HEADER` with the date range `rs` … `re`. -/
def nameHeader (rs re : List Nat) : List Nat :=
  to133 (pad (txt "DALYREPT") 38 ++ pad (txt "Daily Transaction Report") 41 ++
    pad (txt "Date Range: ") 12 ++ rs ++ txt " to " ++ re)

/-- `WS-BLANK-LINE`. -/
def blankLine : List Nat := List.replicate 133 32

/-- `TRANSACTION-HEADER-1`. -/
def header1 : List Nat :=
  to133 (pad (txt "Transaction ID") 17 ++ pad (txt "Account ID") 12 ++
    pad (txt "Transaction Type") 19 ++ pad (txt "Tran Category") 35 ++ pad (txt "Tran Source") 14 ++
    pad (txt " ") 1 ++ pad (txt "        Amount") 16)

/-- `TRANSACTION-HEADER-2`: dashes. -/
def header2 : List Nat := List.replicate 133 45

/-- `REPORT-PAGE-TOTALS`, `REPORT-ACCOUNT-TOTALS`, `REPORT-GRAND-TOTALS`. -/
def pageTotalLine (p : Int) : List Nat :=
  to133 (pad (txt "Page Total") 11 ++ List.replicate 86 46 ++ editAmt p true)
def acctTotalLine (a : Int) : List Nat :=
  to133 (pad (txt "Account Total") 13 ++ List.replicate 84 46 ++ editAmt a true)
def grandTotalLine (g : Int) : List Nat :=
  to133 (pad (txt "Grand Total") 11 ++ List.replicate 86 46 ++ editAmt g true)

/-- `TRANSACTION-DETAIL-REPORT` for transaction `t`, cross-reference `x`, type `y`, category `c`. -/
def detailLine (t x y c : List FVal) : List Nat :=
  to133 (cps (tId t) ++ [32] ++ digs 11 (xAcct x) ++ [32] ++ cps (tType t) ++ [45] ++
    pad (cps ((yDesc y).take 15)) 15 ++ [32] ++ digs 4 (tCat t) ++ [45] ++
    pad (cps ((cDesc c).take 29)) 29 ++ [32] ++ cps (tSource t) ++ List.replicate 4 32 ++
    editAmt (tAmt t) false ++ List.replicate 2 32)

/-! ## The run -/

/-- `ADD` to an `S9(09)V99` total without `ON SIZE ERROR`: the 11 low digits, with the sign. -/
def trunc11 (x : Int) : Int := x.tmod 100000000000

/-- The translations' state between two transactions. -/
structure St where
  /-- The outputs so far, oldest first. -/
  disp : List (List Nat)
  writes : List (List Nat)
  /-- `WS-LINE-COUNTER`, `WS-PAGE-TOTAL`, `WS-ACCOUNT-TOTAL`, `WS-GRAND-TOTAL`. -/
  lc : Nat
  page : Int
  acct : Int
  grand : Int
  /-- `REPT-START-DATE`, `REPT-END-DATE` (code points). -/
  rs : List Nat
  re : List Nat
  /-- `WS-FIRST-TIME = 'Y'`, `WS-CURR-CARD-NUM`, and the cross-reference record area. -/
  first : Bool
  card : List UInt8
  xref : List FVal

/-- DISPLAY a line; WRITE a report line; add 1 to the line counter (`PIC 9(09)`). -/
def dsp (s : St) (l : List Nat) : St := { s with disp := s.disp ++ [l] }
def wr (s : St) (l : List Nat) : St := { s with writes := s.writes ++ [l] }
def inc (s : St) : St := { s with lc := (s.lc + 1) % 1000000000 }

/-- 1110-WRITE-PAGE-TOTALS: the page total line, the page total added to the grand total and
reset, the dashes. -/
def pageTotals (s : St) : St :=
  inc (wr (inc { wr s (pageTotalLine s.page) with grand := trunc11 (s.grand + s.page), page := 0 })
    header2)

/-- 1120-WRITE-ACCOUNT-TOTALS. -/
def acctTotals (s : St) : St :=
  inc (wr (inc { wr s (acctTotalLine s.acct) with acct := 0 }) header2)

/-- 1110-WRITE-GRAND-TOTALS. -/
def grandTotals (s : St) : St := wr s (grandTotalLine s.grand)

/-- 1120-WRITE-HEADERS. -/
def headers (s : St) : St :=
  inc (wr (inc (wr (inc (wr (inc (wr s (nameHeader s.rs s.re))) blankLine)) header1)) header2)

/-- 1100-WRITE-TRANSACTION-REPORT for transaction `t` with type `y` and category `c` (date
parameters `d`). -/
def report (d : List FVal) (s : St) (t y c : List FVal) : St :=
  let s := if s.first then headers { s with first := false, rs := cps (dStart d), re := cps (dEnd d) }
    else s
  let s := if s.lc % 20 = 0 then headers (pageTotals s) else s
  let s := { s with page := trunc11 (s.page + tAmt t), acct := trunc11 (s.acct + tAmt t) }
  inc (wr s (detailLine t s.xref y c))

/-- A failed keyed READ: the message `msg`, the file status `23`, the abend message. -/
def abend23 (s : St) (msg : List Nat) : St :=
  dsp (dsp (dsp s msg) (txt "FILE STATUS IS: NNNN0023")) (txt "ABENDING PROGRAM")

/-- The card lookup (on a change of card): the state with the cross-reference record read, or the
abend. -/
def cardStep (xs : List (List FVal)) (s : St) (t : List FVal) : Except St St :=
  if s.card = tCard t then .ok s
  else
    let s := { (if s.first then s else acctTotals s) with card := tCard t }
    match xs.find? (fun x => xCard x == tCard t) with
    | none => .error (abend23 s (txt "INVALID CARD NUMBER : " ++ cps (tCard t)))
    | some x => .ok { s with xref := x }

/-- One transaction `t` in the date range (cross-references `xs`, types `ys`, categories `cs`,
date parameters `d`): DISPLAY it, the lookups, the report lines; or the abend. -/
def tranStep (xs ys cs : List (List FVal)) (d : List FVal) (s : St) (t : List FVal) : Except St St :=
  match cardStep xs (dsp s (TranRecord.textS t)) t with
  | .error s => .error s
  | .ok s =>
    match ys.find? (fun y => yType y == tType t) with
    | none => .error (abend23 s (txt "INVALID TRANSACTION TYPE : " ++ cps (tType t)))
    | some y =>
      match cs.find? (fun c => cType c == tType t && cCat c == tCat t) with
      | none => .error (abend23 s (txt "INVALID TRAN CATG KEY : " ++ cps (tType t) ++ digs 4 (tCat t)))
      | some c => .ok (report d s t y c)

/-- After the end of file (`tran` is the record area: the last record read): the amount DISPLAYed
and added once more, the page and grand totals. -/
def eofTail (s : St) (tran : List FVal) : St :=
  let s := dsp (dsp s (txt "TRAN-AMT " ++ zoned 11 (tAmt tran))) (txt "WS-PAGE-TOTAL" ++ zoned 11 s.page)
  grandTotals (pageTotals
    { s with page := trunc11 (s.page + tAmt tran), acct := trunc11 (s.acct + tAmt tran) })

/-- The main loop over the transactions `ts` still to read; `tran` is the record area. -/
def loop (xs ys cs : List (List FVal)) (d : List FVal) :
    List (List FVal) → List FVal → St → Except St St
  | [], tran, s => if inRange d tran then .ok (eofTail s tran) else .ok s
  | t :: ts, _, s =>
    if inRange d t then
      match tranStep xs ys cs d s t with
      | .ok s => loop xs ys cs d ts t s
      | .error s => .error s
    else .ok s

/-- The initial contents of `TRAN-RECORD` and `CARD-XREF-RECORD` (spaces and zeros). -/
def tran0 : List FVal :=
  [.str (sp 16), .str (sp 2), .num 0, .str (sp 10), .str (sp 100), .num 0, .num 0, .str (sp 50),
    .str (sp 50), .str (sp 10), .str (sp 16), .str (sp 26), .str (sp 26), .str (sp 20)]
def xref0 : List FVal := [.str (sp 16), .num 0, .num 0, .str (sp 14)]

/-- The state at the start. -/
def init : St :=
  { disp := [txt "START OF EXECUTION OF PROGRAM CBTRN03C"], writes := [], lc := 0, page := 0,
    acct := 0, grand := 0, rs := List.replicate 10 32, re := List.replicate 10 32, first := true,
    card := sp 16, xref := xref0 }

/-- The outputs: the lines displayed (code points), the report records written (field values of
`FD-REPTFILE-REC`), whether the run abended. -/
structure Out where
  disp : List (List Nat)
  writes : List (List FVal)
  abended : Bool

/-- The outputs of a final state (`END OF EXECUTION …` when the run did not abend). -/
def out (s : St) (ab : Bool) : Out :=
  { disp := if ab then s.disp else s.disp ++ [txt "END OF EXECUTION OF PROGRAM CBTRN03C"],
    writes := s.writes.map fun l => [.str (l.map ebc)], abended := ab }

/-- **What CBTRN03C outputs**, for the transactions `trans`, cross-references `xs`, transaction
types `ys`, categories `cs` and date parameter records `ds`. -/
def run (trans xs ys cs ds : List (List FVal)) : Out :=
  match ds with
  | [] => out init false
  | d :: _ =>
    let s := dsp init (txt "Reporting from " ++ cps (dStart d) ++ txt " to " ++ cps (dEnd d))
    match loop xs ys cs d trans tran0 s with
    | .ok s => out s false
    | .error s => out s true

end EquivLean.Modernize.Cbtrn03c.Model
