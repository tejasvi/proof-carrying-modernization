import EquivLean.Modernize.Cbstm03a.Java.JRun

/-!
# CBSTM03A → Java: `run` at the level of records (`jRunHL`)

`jRunT` follows the Java statement by statement: the transactions are loaded into the emulated table (one block
per card, `memWr` on the table memory) and read back card by card. `jRunHL` says what that computes when the table
is used as intended: for each cross-reference record, the statement's head, then the transactions of its card in
file order (`ofCardT`), each giving its lines and adding its amount to the total (`tranStep`), then the tail.

`DomainT`: the load records' cards come in groups of equal consecutive cards (`groupsOf`), at most 50 groups of at
most 10 records (the table's 51 card blocks of 10 transaction slots, with one block to spare), the groups'
cards strictly increasing in EBCDIC order (`ebcCmp`). Under `DomainT`, `jRunT = jRunHL` (`CbAHL.jRunT_eq_HL`).
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows fixStr zpadStr argText StrOk space)

namespace EquivLean.Modernize.Cbstm03a.Java

/-- The records of card `card` among `rs`, in order. -/
def ofCardT (card : JStr) (rs : List JStr) : List JStr := rs.filter (fun r => decide (sub r 0 16 = card))

/-- One transaction record `r`: its statement and HTML lines appended, its amount added to the total (kept to 11
digits). -/
def tranStep (acc : JOut × I64) (r : JStr) : JOut × I64 :=
  let tid := sub r 16 32
  let trest := sub r 32 350
  let amt : I64 := BitVec.ofInt 64 (zonedVal (sub trest 116 127))
  (acc.1.add (jWriteTrans tid trest amt.toInt), BitVec.ofInt 64 (trunc11Z (acc.2 + amt).toInt))

/-- One cross-reference record at the level of records; `.error` when it abends (with the outputs). -/
def xrefStepHL (custKeys custTexts acctTexts recs : List JStr) (o : JOut) (x : JStr) : Except JOut JOut :=
  let fldt := fixStr x 1000
  let card := sub fldt 0 16
  match custFind custKeys custTexts (sub fldt 16 25) with
  | none => .error (o.abend (jl "ERROR READING CUSTFILE") (jl "23"))
  | some custRec =>
    match acctFind acctTexts (sub fldt 25 36) with
    | none => .error (o.abend (jl "ERROR READING ACCTFILE") (jl "23"))
    | some acctRec =>
      let p := (ofCardT card recs).foldl tranStep (o.add (jCreateStatement custRec acctRec), 0)
      .ok (tailOf p.1 p.2)

def xrefAllHL (custKeys custTexts acctTexts recs : List JStr) : JOut → List JStr → JOut
  | o, [] => o
  | o, x :: xs =>
    match xrefStepHL custKeys custTexts acctTexts recs o x with
    | .error o' => o'
    | .ok o' => xrefAllHL custKeys custTexts acctTexts recs o' xs

/-- **`run` at the level of records.** -/
def jRunHL (trnxTexts xrefTexts custTexts acctTexts : List JStr) : JOut :=
  match trnxTexts with
  | [] => JOut.init.abend (jl "ERROR READING TRNXFILE") (jl "10")
  | _ :: _ =>
    xrefAllHL (custTexts.map (sub · 0 9)) custTexts acctTexts (trnxTexts.map (recOf · 350)) JOut.init xrefTexts

/-- The groups of equal consecutive cards of the records: each card with the number of its records. -/
def groupsOf : List JStr → List (JStr × Nat)
  | [] => []
  | r :: rs =>
    match groupsOf rs with
    | (c, n) :: gs => if sub r 0 16 = c then (c, n + 1) :: gs else (sub r 0 16, 1) :: (c, n) :: gs
    | [] => [(sub r 0 16, 1)]

/-- Consecutive elements in strictly increasing EBCDIC order. -/
def EbcAsc : List JStr → Prop
  | a :: b :: rest => ebcCmp a b < 0 ∧ EbcAsc (b :: rest)
  | _ => True

/-- The load records fit the table as intended: at most 50 groups of at most 10 records, cards strictly increasing
from group to group. -/
def DomainT (recs : List JStr) : Prop :=
  (groupsOf recs).length ≤ 50 ∧ (∀ g ∈ groupsOf recs, g.2 ≤ 10) ∧ EbcAsc ((groupsOf recs).map (·.1))

/-- The statement proved in `CbAHL`. -/
def JRunHLStmt : Prop :=
  ∀ T1 T2 T3 T4 : List JStr, DomainT (T1.map (recOf · 350)) → jRunT T1 T2 T3 T4 = jRunHL T1 T2 T3 T4

end EquivLean.Modernize.Cbstm03a.Java
