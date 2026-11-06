import EquivLean.Bridge.Cobol.Records
import EquivLean.Demo.Cobol.Cbtrn02c.Prog

/-!
# CBTRN02C: what the translations output, from the input field values

CBTRN02C posts the daily transactions (DALYTRAN, in file order).  For each transaction:
* `1500-A-LOOKUP-XREF`: the card's cross-reference record (keyed READ), else reject 100;
* `1500-B-LOOKUP-ACCT`: the account of the cross-reference (keyed READ), else reject 101; then
  reject 102 if the credit limit is below the cycle credit minus the cycle debit plus the amount
  (truncated to `S9(09)V99`), and reject 103 (it wins over 102) if the account's expiration date
  is below the first 10 characters of the transaction's origination timestamp (EBCDIC order);
* a rejected transaction is written to DALYREJS (the 350-byte record and the trailer: the reason
  in 4 digits and its description in 76 characters);
* a valid one: `2700-UPDATE-TCATBAL` adds the amount to the category balance record of (account,
  type, category), or creates it (a display, then a WRITE; the new record's `FILLER` is the one of
  the last category record read, as `INITIALIZE` leaves `FILLER` alone); `2800-UPDATE-ACCOUNT-REC`
  adds the amount to the balance and to the cycle credit (amount ≥ 0) or debit (REWRITE);
  `2900-WRITE-TRANSACTION-FILE` writes the transaction record (the processing timestamp from the
  clock, the WORKING-STORAGE `FILLER`: spaces).

At the end: the counts of transactions read and rejected, RETURN-CODE 4 when some transaction was
rejected, the end message.

`run`: a fold over the transactions that does what the translations do, on field values; it
follows coblean's functional model `CardDemo.Cbtrn02c.model` (`step`, `Model.reject`,
`Model.post`), with its arithmetic (`Sem.fitNum`), timestamp (`db2ts`) and trailer (`trailer`).
The transaction ids are distinct (the domain `Domain`, coblean's hypothesis): with a repeated id
the WRITE to TRANSACT would fail and the program abend.  The tables are updated as the
translations update their copies: a rewrite replaces the first record with the key, a new
category balance record is appended (coblean inserts it in key order; the keyed lookups give the
same records, as a key is created only when it is absent).  The displayed lines are code points;
the records are field values (alphanumeric fields as EBCDIC bytes).
-/

open Cobol EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbtrn02c.Model

cobol_schema DalytranRecord from "../../../examples/cobol/carddemo/cbtrn02c.ir.json" record "DALYTRAN-RECORD"
cobol_schema CardXrefRecord from "../../../examples/cobol/carddemo/cbtrn02c.ir.json" record "CARD-XREF-RECORD"
cobol_schema AccountRecord from "../../../examples/cobol/carddemo/cbtrn02c.ir.json" record "ACCOUNT-RECORD"
cobol_schema TranCatBalRecord from "../../../examples/cobol/carddemo/cbtrn02c.ir.json" record "TRAN-CAT-BAL-RECORD"
cobol_schema TranRecord from "../../../examples/cobol/carddemo/cbtrn02c.ir.json" record "TRAN-RECORD"
cobol_schema RejectRecord from "../../../examples/cobol/carddemo/cbtrn02c.ir.json" record "REJECT-RECORD"

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

/-- `DALYTRAN-ID`, `-TYPE-CD`, `-CAT-CD`, `-AMT`, `-CARD-NUM`, `-ORIG-TS` of a daily
transaction. -/
def tId (t : List FVal) : List UInt8 := strOf (t.getD 0 default)
def tType (t : List FVal) : List UInt8 := strOf (t.getD 1 default)
def tCat (t : List FVal) : Int := numOf (t.getD 2 default)
def tAmt (t : List FVal) : Int := numOf (t.getD 5 default)
def tCard (t : List FVal) : List UInt8 := strOf (t.getD 10 default)
def tOrig (t : List FVal) : List UInt8 := strOf (t.getD 11 default)

/-- `XREF-CARD-NUM`, `XREF-ACCT-ID` of a cross-reference record. -/
def xCard (x : List FVal) : List UInt8 := strOf (x.getD 0 default)
def xAcct (x : List FVal) : Int := numOf (x.getD 2 default)

/-- `ACCT-ID`, `-CURR-BAL`, `-CREDIT-LIMIT`, `-EXPIRAION-DATE`, `-CURR-CYC-CREDIT`,
`-CURR-CYC-DEBIT` of an account record. -/
def aId (a : List FVal) : Int := numOf (a.getD 0 default)
def aBal (a : List FVal) : Int := numOf (a.getD 2 default)
def aLimit (a : List FVal) : Int := numOf (a.getD 3 default)
def aExp (a : List FVal) : List UInt8 := strOf (a.getD 6 default)
def aCC (a : List FVal) : Int := numOf (a.getD 8 default)
def aCD (a : List FVal) : Int := numOf (a.getD 9 default)

/-- `TRANCAT-ACCT-ID`, `-TYPE-CD`, `TRANCAT-CD`, `TRAN-CAT-BAL`, `FILLER` of a category balance
record. -/
def cAcct (c : List FVal) : Int := numOf (c.getD 0 default)
def cType (c : List FVal) : List UInt8 := strOf (c.getD 1 default)
def cCd (c : List FVal) : Int := numOf (c.getD 2 default)
def cBal (c : List FVal) : Int := numOf (c.getD 3 default)
def cFill (c : List FVal) : List UInt8 := strOf (c.getD 4 default)

/-! ## The lookups (first match) -/

/-- The cross-reference record of card `card` (`1500-A-LOOKUP-XREF`). -/
def findXref (xrefs : List (List FVal)) (card : List UInt8) : Option (List FVal) :=
  xrefs.find? (fun x => xCard x == card)

/-- The account with id `id` (`1500-B-LOOKUP-ACCT`). -/
def findAcct (accts : List (List FVal)) (id : Int) : Option (List FVal) :=
  accts.find? (fun a => aId a == id)

/-- The key test of a category balance record: account, type, category. -/
def catKey (acct : Int) (ty : List UInt8) (cd : Int) (c : List FVal) : Bool :=
  cAcct c == acct && cType c == ty && cCd c == cd

/-- The category balance record of (account, type, category) (`2700-UPDATE-TCATBAL`). -/
def findCat (cats : List (List FVal)) (acct : Int) (ty : List UInt8) (cd : Int) :
    Option (List FVal) :=
  cats.find? (catKey acct ty cd)

/-- Replace the first element satisfying `p` by `x` (the keyed REWRITE). -/
def replaceFirst {α : Type} (p : α → Bool) (x : α) : List α → List α
  | [] => []
  | y :: ys => if p y then x :: ys else y :: replaceFirst p x ys

/-! ## The records written -/

/-- The rejected transaction `t` with reason `code` and description `desc` (`2500-WRITE-REJECT-
REC`): the daily record's 350 bytes, and the trailer (coblean's `trailer`). -/
def rejectVals (t : List FVal) (code : Int) (desc : List UInt8) : List FVal :=
  [.str (DalytranRecord.encode t), .str (CardDemo.Cbtrn02c.trailer code desc)]

/-- The transaction record of a posted transaction `t` (`2000-POST-TRANSACTION`): the daily
record's fields up to the origination timestamp, the processing timestamp of the clock reading
`clk`, the WORKING-STORAGE `FILLER` (spaces). -/
def tranVals (t : List FVal) (clk : List UInt8) : List FVal :=
  t.take 12 ++ [.str (CardDemo.Cbtrn02c.db2ts clk), .str (sp 20)]

/-- The account record `a` with amount `amt` posted (`2800-UPDATE-ACCOUNT-REC`): the balance,
and the cycle credit (`amt ≥ 0`) or debit, truncated like `ADD` without `ON SIZE ERROR`
(coblean's `a'`). -/
def postAcct (a : List FVal) (amt : Int) : List FVal :=
  ((a.set 2 (.num (Sem.fitNum {} CardDemo.Cbtrn02c.ACCT_CURR_BAL.fmt (aBal a + amt)).2)).set 8
    (.num (if 0 ≤ amt then (Sem.fitNum {} CardDemo.Cbtrn02c.ACCT_CURR_CYC_CREDIT.fmt (aCC a + amt)).2
      else aCC a))).set 9
    (.num (if 0 ≤ amt then aCD a
      else (Sem.fitNum {} CardDemo.Cbtrn02c.ACCT_CURR_CYC_DEBIT.fmt (aCD a + amt)).2))

/-- The display line of `2700-UPDATE-TCATBAL` for a missing key. -/
def noCatLine (acct : Int) (ty : List UInt8) (cd : Int) : List Nat :=
  txt "TCATBAL record not found for key : " ++ zpad 11 acct.natAbs ++ ty.map cp037Code ++
    zpad 4 cd.natAbs ++ txt ".. Creating."

/-! ## The run -/

/-- The translations' state between two transactions (coblean's `Model`, with the outputs per
file). -/
structure St where
  /-- The account and category balance files. -/
  accts : List (List FVal)
  cats : List (List FVal)
  /-- The `FILLER` of `TRAN-CAT-BAL-RECORD`: that of the last category record read. -/
  catFill : List UInt8
  /-- Transactions posted and rejected. -/
  posted : Nat
  rejects : Nat
  /-- The outputs so far, oldest first: the displayed lines, the records written to TRANSACT,
  DALYREJS and TCATBAL, the records rewritten in ACCOUNT and TCATBAL. -/
  disp : List (List Nat)
  tranW : List (List FVal)
  rejW : List (List FVal)
  catW : List (List FVal)
  acctRW : List (List FVal)
  catRW : List (List FVal)

/-- A rejected transaction (coblean's `Model.reject`). -/
def St.reject (s : St) (t : List FVal) (code : Int) (desc : List UInt8) : St :=
  { s with rejects := s.rejects + 1, rejW := s.rejW ++ [rejectVals t code desc] }

/-- A valid transaction `t` of cross-reference `x` and account `a` (coblean's `Model.post`):
`2700-UPDATE-TCATBAL`, `2800-UPDATE-ACCOUNT-REC`, `2900-WRITE-TRANSACTION-FILE`. -/
def St.post (clk : List UInt8) (s : St) (t x a : List FVal) : St :=
  let a' := postAcct a (tAmt t)
  let s1 : St :=
    match findCat s.cats (xAcct x) (tType t) (tCat t) with
    | none =>
      let c : List FVal := [.num (xAcct x), .str (tType t), .num (tCat t), .num (tAmt t),
        .str s.catFill]
      { s with cats := s.cats ++ [c], disp := s.disp ++ [noCatLine (xAcct x) (tType t) (tCat t)],
               catW := s.catW ++ [c] }
    | some c =>
      let c' := c.set 3 (.num (Sem.fitNum {} CardDemo.Cbtrn02c.TRAN_CAT_BAL.fmt (cBal c + tAmt t)).2)
      { s with cats := replaceFirst (catKey (xAcct x) (tType t) (tCat t)) c' s.cats,
               catFill := cFill c, catRW := s.catRW ++ [c'] }
  { s1 with accts := replaceFirst (fun b => aId b == aId a) a' s1.accts,
            acctRW := s1.acctRW ++ [a'], tranW := s1.tranW ++ [tranVals t clk],
            posted := s1.posted + 1 }

/-- One daily transaction (coblean's `step`): validate, then post or reject. -/
def step (xrefs : List (List FVal)) (clk : List UInt8) (s : St) (t : List FVal) : St :=
  match findXref xrefs (tCard t) with
  | none => s.reject t 100 CardDemo.Cbtrn02c.badCardDesc
  | some x =>
    match findAcct s.accts (xAcct x) with
    | none => s.reject t 101 CardDemo.Cbtrn02c.noAcctDesc
    | some a =>
      if Sem.cmpBytes (aExp a) ((tOrig t).take 10) = .lt then
        s.reject t 103 CardDemo.Cbtrn02c.expiredDesc
      else if aLimit a < (Sem.fitNum {} CardDemo.Cbtrn02c.WS_TEMP_BAL.fmt
          (aCC a - aCD a + tAmt t)).2 then
        s.reject t 102 CardDemo.Cbtrn02c.overLimitDesc
      else s.post clk t x a

/-- The state before the first transaction. -/
def init (accts cats : List (List FVal)) : St :=
  { accts, cats, catFill := sp 22, posted := 0, rejects := 0,
    disp := [txt "START OF EXECUTION OF PROGRAM CBTRN02C"], tranW := [], rejW := [], catW := [],
    acctRW := [], catRW := [] }

/-- The outputs: the lines displayed (code points), the records written and rewritten per file,
RETURN-CODE (the program never abends on the domain). -/
structure Out where
  disp : List (List Nat)
  tranW : List (List FVal)
  rejW : List (List FVal)
  catW : List (List FVal)
  acctRW : List (List FVal)
  catRW : List (List FVal)
  rc : Int

/-- **What CBTRN02C outputs**, for the daily transactions `trans`, cross-references `xrefs`,
accounts `accts`, category balances `cats` and the clock reading `clk`. -/
def run (trans xrefs accts cats : List (List FVal)) (clk : List UInt8) : Out :=
  let s := trans.foldl (step xrefs clk) (init accts cats)
  { disp := s.disp ++ [txt "TRANSACTIONS PROCESSED :" ++ zpad 9 trans.length,
      txt "TRANSACTIONS REJECTED  :" ++ zpad 9 s.rejects, txt "END OF EXECUTION OF PROGRAM CBTRN02C"],
    tranW := s.tranW, rejW := s.rejW, catW := s.catW, acctRW := s.acctRW, catRW := s.catRW,
    rc := if 0 < s.rejects then 4 else 0 }

end EquivLean.Modernize.Cbtrn02c.Model
