import EquivLean.Bridge.Cobol.Records
import EquivLean.Bridge.Aeneas.CobolRec
import EquivLean.Demo.Cobol.Cbstm03b.Prog

/-!
# CBSTM03B: one call, on the translations' values

CBSTM03B (CardDemo's file access subroutine) is called with the 1040-byte area `LK-M03B-AREA`: a DD name, an
operation, a return code, a key, a key length and a 1000-byte record buffer. It opens, reads or closes one of four
indexed files, chosen by the DD name, and returns the file status in the return code; its files, record areas and
status items persist between calls.

`call oe st area` does what the translations do in one call, on field values: the four files (open or not, their
records as field values, the position of the next sequential read, the end-of-file flag), the four FD record areas
(field values), the four `FILE STATUS` items (two Latin-1 code points each, the translations' `[u8; 2]`) and the
area (field values; alphanumeric fields as EBCDIC bytes, as in the other CardDemo models, so a status moved into
the return code is mapped by `ebcdicOfLatin1`). `oe id` is the status an `OPEN INPUT` of file `id` fails with, if
it does. A keyed `READ` is a first-match search on the key field: CUSTFILE's `FD-CUST-ID` as bytes, ACCTFILE's
`FD-ACCT-ID` as a number. The schemas have the names of the generated statement. `Glue.lean` relates `call` to
coblean's `call3b` (`Demo/Cobol/Cbstm03b/Prog.lean`).
-/

open Cobol EquivLean.Cobol.Rec
open CardDemo.Cbstm03b (ddTrnx ddXref ddCust ddAcct opOpen opRead opReadK opClose stBytes intoBuf)

namespace EquivLean.Modernize.Cbstm03b.Model

cobol_schema FdTrnxfileRec from "../../../examples/cobol/carddemo/cbstm03b.ir.json" record "FD-TRNXFILE-REC"
cobol_schema FdXreffileRec from "../../../examples/cobol/carddemo/cbstm03b.ir.json" record "FD-XREFFILE-REC"
cobol_schema FdCustfileRec from "../../../examples/cobol/carddemo/cbstm03b.ir.json" record "FD-CUSTFILE-REC"
cobol_schema FdAcctfileRec from "../../../examples/cobol/carddemo/cbstm03b.ir.json" record "FD-ACCTFILE-REC"
cobol_schema LkM03bArea from "../../../examples/cobol/carddemo/cbstm03b.ir.json" record "LK-M03B-AREA"

/-- The bytes of an alphanumeric value. -/
def strOf : FVal → List UInt8
  | .str bs => bs
  | .num _ => []

/-- The integer of a numeric value. -/
def numOf : FVal → Int
  | .num v => v
  | .str _ => 0

/-- The two characters of file status `c`, as code points. -/
def stCp (c : Nat) : List Nat := [48 + c / 10 % 10, 48 + c % 10]

/-! ## The state -/

/-- A file: open or not, its records (field values), the position of the next sequential read, end of file. -/
structure FileM where
  isOpen : Bool
  recs : List (List FVal)
  pos : Nat
  eof : Bool
  deriving DecidableEq, Repr

/-- The state CBSTM03B keeps between calls: its four files, the four FD record areas, the four `FILE STATUS`
items (two code points each). -/
structure StM where
  trnx : FileM
  xref : FileM
  cust : FileM
  acct : FileM
  trnxRec : List FVal
  xrefRec : List FVal
  custRec : List FVal
  acctRec : List FVal
  trnxSt : List Nat
  xrefSt : List Nat
  custSt : List Nat
  acctSt : List Nat
  deriving DecidableEq, Repr

/-- The status an `OPEN INPUT` of file `id` (1 TRNXFILE, 2 XREFFILE, 3 CUSTFILE, 4 ACCTFILE) fails with, if it
does. -/
abbrev OpenErrs := Nat → Option Nat

/-! ## The file operations -/

/-- `OPEN INPUT`: status 41 if the file is open; the open error if there is one (the file stays closed); else 00
and the file is open at its first record. -/
def openM (oe : Option Nat) (f : FileM) : Nat × FileM :=
  if f.isOpen then (41, f)
  else match oe with
    | some c => (c, f)
    | none => (0, { f with isOpen := true, pos := 0, eof := false })

/-- `CLOSE`: status 42 if the file is closed, else 00 and the file is closed. -/
def closeM (f : FileM) : Nat × FileM :=
  if f.isOpen then (0, { f with isOpen := false }) else (42, f)

/-- Sequential `READ`: status 47 if the file is not open, 46 after the end, 10 at the end, else 00 and the next
record. -/
def seqReadM (f : FileM) : Nat × FileM × Option (List FVal) :=
  if !f.isOpen then (47, f, none)
  else if f.eof then (46, f, none)
  else match f.recs[f.pos]? with
    | none => (10, { f with eof := true }, none)
    | some r => (0, { f with pos := f.pos + 1 }, some r)

/-- Keyed `READ`: status 47 if the file is not open, 23 if no record matches, else 00 and the first matching
record. -/
def keyReadM (p : List FVal → Bool) (f : FileM) : Nat × FileM × Option (List FVal) :=
  if !f.isOpen then (47, f, none)
  else match f.recs.findIdx? p with
    | none => (23, f, none)
    | some i => (0, { f with pos := i + 1, eof := false }, some (f.recs.getD i []))

/-! ## The area -/

/-- `LK-M03B-DD`, `LK-M03B-OPER`, `LK-M03B-KEY`, `LK-M03B-KEY-LN`. -/
def aDd (a : List FVal) : List UInt8 := strOf (a.getD 0 default)
def aOp (a : List FVal) : UInt8 := (strOf (a.getD 1 default)).headD 0
def aKey (a : List FVal) : List UInt8 := strOf (a.getD 3 default)
def aKeyLn (a : List FVal) : Int := numOf (a.getD 4 default)

/-- `LK-M03B-RC` set to `bs`. -/
def setRc (a : List FVal) (bs : List UInt8) : List FVal := a.set 2 (.str bs)

/-- `READ … INTO LK-M03B-FLDT`: the record's bytes, space-padded to 1000. -/
def setFldt (a : List FVal) (bs : List UInt8) : List FVal := a.set 5 (.str (intoBuf bs))

/-- The bytes `MOVE LK-M03B-KEY (1:k) TO FD-CUST-ID` stores (9 bytes, space-padded). -/
def custKey (key : List UInt8) (k : Nat) : List UInt8 := (key.take k ++ List.replicate (9 - k) 64).take 9

/-- The number `MOVE LK-M03B-KEY (1:k) TO FD-ACCT-ID` stores (`PIC 9(11)`): the value of the key's first `k`
digits, high-order truncated to 11 digits. -/
def acctVal (key : List UInt8) (k : Nat) : Int :=
  (Sem.fitNum {} { digits := 11 } ((decodeNum {} { digits := k } (key.take k)).getD 0)).2

/-! ## One call -/

/-- One call for a sequentially read file: the file, its record area, its status item, the area after. -/
def seqStep (oe : Option Nat) (S : Schema) (op : UInt8) (f : FileM) (rec : List FVal) (st : List Nat)
    (a : List FVal) : FileM × List FVal × List Nat × List FVal :=
  if op = opOpen then let (c, f') := openM oe f; (f', rec, stCp c, setRc a (stBytes c))
  else if op = opRead then
    match seqReadM f with
    | (c, f', some r) => (f', r, stCp c, setFldt (setRc a (stBytes c)) (S.encode r))
    | (c, f', none) => (f', rec, stCp c, setRc a (stBytes c))
  else if op = opClose then let (c, f') := closeM f; (f', rec, stCp c, setRc a (stBytes c))
  else (f, rec, st, setRc a (st.map ebcdicOfLatin1))

/-- One call for a keyed file: `setKey` stores the key in the record area's key field, `p` matches a record's
key. -/
def keyStep (oe : Option Nat) (S : Schema) (setKey : List FVal → List FVal) (p : List FVal → Bool) (op : UInt8)
    (f : FileM) (rec : List FVal) (st : List Nat) (a : List FVal) : FileM × List FVal × List Nat × List FVal :=
  if op = opOpen then let (c, f') := openM oe f; (f', rec, stCp c, setRc a (stBytes c))
  else if op = opReadK then
    match keyReadM p f with
    | (c, f', some r) => (f', r, stCp c, setFldt (setRc a (stBytes c)) (S.encode r))
    | (c, f', none) => (f', setKey rec, stCp c, setRc a (stBytes c))
  else if op = opClose then let (c, f') := closeM f; (f', rec, stCp c, setRc a (stBytes c))
  else (f, rec, st, setRc a (st.map ebcdicOfLatin1))

/-- **One call of CBSTM03B** on the translations' values: dispatch on the DD name and the operation. -/
def call (oe : OpenErrs) (st : StM) (a : List FVal) : StM × List FVal :=
  let dd := aDd a
  let op := aOp a
  if dd = ddTrnx then
    let r := seqStep (oe 1) FdTrnxfileRec op st.trnx st.trnxRec st.trnxSt a
    ({ st with trnx := r.1, trnxRec := r.2.1, trnxSt := r.2.2.1 }, r.2.2.2)
  else if dd = ddXref then
    let r := seqStep (oe 2) FdXreffileRec op st.xref st.xrefRec st.xrefSt a
    ({ st with xref := r.1, xrefRec := r.2.1, xrefSt := r.2.2.1 }, r.2.2.2)
  else if dd = ddCust then
    let key := custKey (aKey a) (aKeyLn a).toNat
    let r := keyStep (oe 3) FdCustfileRec (fun rec => rec.set 0 (.str key))
      (fun x => strOf (x.getD 0 default) == key) op st.cust st.custRec st.custSt a
    ({ st with cust := r.1, custRec := r.2.1, custSt := r.2.2.1 }, r.2.2.2)
  else if dd = ddAcct then
    let v := acctVal (aKey a) (aKeyLn a).toNat
    let r := keyStep (oe 4) FdAcctfileRec (fun rec => rec.set 0 (.num v))
      (fun x => numOf (x.getD 0 default) == v) op st.acct st.acctRec st.acctSt a
    ({ st with acct := r.1, acctRec := r.2.1, acctSt := r.2.2.1 }, r.2.2.2)
  else (st, a)

end EquivLean.Modernize.Cbstm03b.Model
