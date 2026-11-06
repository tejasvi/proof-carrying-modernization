import EquivLean.Bridge.Cobol.Records
import EquivLean.Demo.Cobol.Cbact04c.Events

/-!
# CBACT04C: what the translations output, from the input field values

CBACT04C reads the category balances (TCATBAL, in key order) and for each record:
- DISPLAYs it;
- on a change of account, REWRITEs the previous account with its interest posted, then reads the
  new account and its card cross-reference (keyed READs);
- reads the interest rate of the account's disclosure group for the record's type and category;
- for a nonzero rate, adds the monthly interest to the account's total and WRITEs an interest
  transaction.

The last account is not rewritten (CardDemo issue #64; `Demo/Jimple/Cbact04c/Fixed` treats the
fix).

`run`: a fold over the category records that does what the translations do, on field values. The
account table is updated by each rewrite, as the translations update their copy. The lookups are
first-match searches whose success is assumed (the domain `Domain`). The displayed lines are code
points, as `Cbtrn01c.Model`; the written transactions and rewritten accounts are field values
(alphanumeric fields as EBCDIC bytes). The Java contract and the Rust equation state the outputs of
`run`; `Glue.lean` relates them to coblean's `cbact04c_events`.
-/

open Cobol EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbact04c.Model

cobol_schema TranCatBalRecord from "../../../examples/cobol/carddemo/cbact04c.ir.json" record "TRAN-CAT-BAL-RECORD"
cobol_schema CardXrefRecord from "../../../examples/cobol/carddemo/cbact04c.ir.json" record "CARD-XREF-RECORD"
cobol_schema AccountRecord from "../../../examples/cobol/carddemo/cbact04c.ir.json" record "ACCOUNT-RECORD"
cobol_schema DisGroupRecord from "../../../examples/cobol/carddemo/cbact04c.ir.json" record "DIS-GROUP-RECORD"
cobol_schema TranRecord from "../../../examples/cobol/carddemo/cbact04c.ir.json" record "TRAN-RECORD"
cobol_schema ExternalParms from "../../../examples/cobol/carddemo/cbact04c.ir.json" record "EXTERNAL-PARMS"

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

/-- `TRANCAT-ACCT-ID`, `TRANCAT-TYPE-CD`, `TRANCAT-CD`, `TRAN-CAT-BAL` of a category record. -/
def tAcct (t : List FVal) : Int := numOf (t.getD 0 default)
def tType (t : List FVal) : List UInt8 := strOf (t.getD 1 default)
def tCat (t : List FVal) : Int := numOf (t.getD 2 default)
def tBal (t : List FVal) : Int := numOf (t.getD 3 default)

/-- `ACCT-ID`, `ACCT-CURR-BAL`, `ACCT-GROUP-ID` of an account record. -/
def aId (a : List FVal) : Int := numOf (a.getD 0 default)
def aBal (a : List FVal) : Int := numOf (a.getD 2 default)
def aGrp (a : List FVal) : List UInt8 := strOf (a.getD 11 default)

/-- `XREF-CARD-NUM`, `XREF-ACCT-ID` of a cross-reference record. -/
def xCard (x : List FVal) : List UInt8 := strOf (x.getD 0 default)
def xAcct (x : List FVal) : Int := numOf (x.getD 2 default)

/-- `DIS-ACCT-GROUP-ID`, `DIS-TRAN-TYPE-CD`, `DIS-TRAN-CAT-CD`, `DIS-INT-RATE` of a disclosure
group record. -/
def dGrp (d : List FVal) : List UInt8 := strOf (d.getD 0 default)
def dType (d : List FVal) : List UInt8 := strOf (d.getD 1 default)
def dCat (d : List FVal) : Int := numOf (d.getD 2 default)
def dRate (d : List FVal) : Int := numOf (d.getD 3 default)

/-! ## The lookups (first match; success assumed) -/

/-- The account with id `id` (1100-GET-ACCT-DATA). -/
def findAcct (accts : List (List FVal)) (id : Int) : List FVal :=
  (accts.find? (fun a => aId a == id)).getD []

/-- The cross-reference of account `id` (1110-GET-XREF-DATA, by the alternate key). -/
def findXref (xrefs : List (List FVal)) (id : Int) : List FVal :=
  (xrefs.find? (fun x => xAcct x == id)).getD []

/-- The interest rate of group `grp`, type `ty`, category `cat` (1200-GET-INTEREST-RATE). -/
def findRate (discs : List (List FVal)) (grp ty : List UInt8) (cat : Int) : Int :=
  dRate ((discs.find? (fun d => dGrp d == grp && dType d == ty && dCat d == cat)).getD [])

/-- Replace the first element satisfying `p` by `x` (the keyed REWRITE). -/
def replaceFirst {α : Type} (p : α → Bool) (x : α) : List α → List α
  | [] => []
  | y :: ys => if p y then x :: ys else y :: replaceFirst p x ys

/-! ## The records written -/

/-- The account record with interest `total` posted (1050-UPDATE-ACCOUNT): balance plus the
interest, truncated to 12 digits like `ADD` without `ON SIZE ERROR`; cycle credit and debit 0. -/
def posted (a : List FVal) (total : Int) : List FVal :=
  ((a.set 2 (.num (Int.tmod (aBal a + total) (10 ^ 12)))).set 8 (.num 0)).set 9 (.num 0)

/-- The interest transaction with suffix `k` for account `id`, card `card`, amount `amt`
(1300-B-WRITE-TX): id `PARM-DATE` and the 6-digit suffix, type `01`, category 5, source `System`,
description `Int. for a/c ` and the account id, the amount, merchant 0, spaces, the card number,
the clock reading as a DB2 timestamp twice, spaces. -/
def tranVals (parm clk : List UInt8) (k : Nat) (id : Int) (card : List UInt8) (amt : Int) :
    List FVal :=
  [.str (parm ++ encodeNum {} CardDemo.Cbact04c.WS_TRANID_SUFFIX.fmt (k : Int)), .str [240, 241],
    .num 5, .str CardDemo.Cbact04c.systemSrc,
    .str (CardDemo.Cbact04c.descHead ++ encodeNum {} CardDemo.Cbact04c.ACCT_ID.fmt id ++ sp 76),
    .num amt, .num 0, .str (sp 50), .str (sp 50), .str (sp 10), .str card,
    .str (CardDemo.Cbact04c.db2ts clk), .str (CardDemo.Cbact04c.db2ts clk), .str (sp 20)]

/-! ## The run -/

/-- The translations' state between two category records. -/
structure St where
  /-- The account file (each rewrite replaces its account). -/
  accts : List (List FVal)
  /-- The account of the previous record (`WS-LAST-ACCT-NUM`; none before the first). -/
  lastId : Option Int
  /-- The current account and cross-reference records. -/
  acct : List FVal
  xref : List FVal
  /-- `WS-TOTAL-INT`, and the transactions written (`WS-TRANID-SUFFIX`). -/
  total : Int
  k : Nat
  /-- The outputs so far, oldest first. -/
  disp : List (List Nat)
  writes : List (List FVal)
  rewrites : List (List FVal)

/-- One category record `t`. -/
def step (xrefs discs : List (List FVal)) (parm clk : List UInt8) (s : St) (t : List FVal) : St :=
  let s1 : St := { s with disp := s.disp ++ [TranCatBalRecord.textS t] }
  let s2 : St :=
    if s1.lastId = some (tAcct t) then s1
    else
      let p := posted s1.acct s1.total
      let accts := if s1.lastId.isSome then replaceFirst (fun a => aId a == aId s1.acct) p s1.accts
        else s1.accts
      { s1 with accts, rewrites := if s1.lastId.isSome then s1.rewrites ++ [p] else s1.rewrites,
                lastId := some (tAcct t), total := 0, acct := findAcct accts (tAcct t),
                xref := findXref xrefs (tAcct t) }
  let rate := findRate discs (aGrp s2.acct) (tType t) (tCat t)
  if rate = 0 then s2
  else
    let amt := Int.tmod (Int.tdiv (tBal t * rate) 120000) (10 ^ 11)
    let k := (s2.k + 1) % 1000000
    { s2 with total := Int.tmod (s2.total + amt) (10 ^ 11), k,
              writes := s2.writes ++ [tranVals parm clk k (aId s2.acct) (xCard s2.xref) amt] }

/-- The state before the first record. -/
def init (accts : List (List FVal)) : St :=
  { accts, lastId := none, acct := [], xref := [], total := 0, k := 0,
    disp := [txt "START OF EXECUTION OF PROGRAM CBACT04C"], writes := [], rewrites := [] }

/-- The outputs: the lines displayed (code points), the transactions written, the accounts
rewritten. -/
structure Out where
  disp : List (List Nat)
  writes : List (List FVal)
  rewrites : List (List FVal)

/-- **What CBACT04C outputs**, for the category records `tcat`, cross-references `xrefs`, accounts
`accts`, disclosure groups `discs`, `PARM-DATE` `parm` and the clock reading `clk`. -/
def run (tcat xrefs accts discs : List (List FVal)) (parm clk : List UInt8) : Out :=
  let s := tcat.foldl (step xrefs discs parm clk) (init accts)
  { disp := s.disp ++ [txt "END OF EXECUTION OF PROGRAM CBACT04C"], writes := s.writes,
    rewrites := s.rewrites }

/-- `PARM-DATE` of the linkage record. -/
def parmOf (link : List FVal) : List UInt8 := strOf (link.getD 1 default)

end EquivLean.Modernize.Cbact04c.Model
