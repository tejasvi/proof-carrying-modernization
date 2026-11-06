import EquivLean.Modernize.Cbstm03a.Java.Iface1
import EquivLean.Modernize.Cbstm03a.Java.Iface2
import EquivLean.Modernize.Cbstm03a.Java.Iface3

/-!
# CBSTM03A → Java: what `run` computes, as a Lean function

`jRunT`: the outputs of `Cbstm03a.run` from the record texts it builds (`trnxText`, … of the four files),
statement by statement as the Java does it: the first sequential read of TRNXFILE (an empty file abends with
return code 10); the load of every transaction into the emulated table (`memWr` on the table memory, the counts in
`trctSet`, card and transaction counters modulo 10000); then, per cross-reference record, the keyed reads (first
match; none abends with 23), the statement's head (the lines of `jCreateStatement`), the transactions of the card
(cards `1 … crCnt` in table order, stopping at the first card number above the record's in EBCDIC order; the lines
of `jWriteTrans`) and the statement's tail. `jRunR`: the same from the records' field values.
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows fixStr zpadStr argText StrOk space)

namespace EquivLean.Modernize.Cbstm03a.Java

/-- What `run` returns: the three lists of the `Result` and `abended`. -/
structure JOut where
  disp : List JStr
  stmt : List JStr
  html : List JStr
  ab : Bool

def JOut.init : JOut := ⟨[], [], [], false⟩

/-- `abend(res, msg, rc)`. -/
def JOut.abend (o : JOut) (msg rc : JStr) : JOut :=
  ⟨o.disp ++ [msg, jl "RETURN CODE: " ++ rc, jl "ABENDING PROGRAM"], o.stmt, o.html, true⟩

/-- Lines appended to the statement and HTML lists. -/
def JOut.add (o : JOut) (p : List JStr × List JStr) : JOut := ⟨o.disp, o.stmt ++ p.1, o.html ++ p.2, o.ab⟩

/-- `stmt(res, s)`, `html(res, s)`. -/
def JOut.stmt1 (o : JOut) (s : JStr) : JOut := ⟨o.disp, o.stmt ++ [sl s], o.html, o.ab⟩
def JOut.html1 (o : JOut) (s : JStr) : JOut := ⟨o.disp, o.stmt, o.html ++ [hl s], o.ab⟩

/-- The table load's state: the table memory, the counts array (51 `long`s), `crCnt`, `trCnt`, `saveCard`. -/
structure LdSt where
  m : Nat → JChar
  trct : List Value
  cr : I64
  tr : I64
  save : JStr

def cardOffJ (cr : I64) : I64 := (cr - 1) * 3356
def tranOffJ (cr tr : I64) : I64 := (cr - 1) * 3356 + 16 + (tr - 1) * 334

/-- One record `rec` (350 characters) into the table (one iteration of 8500-READTRNX-READ's loop body). -/
def ldStep (s : LdSt) (rec : JStr) : LdSt :=
  let tCard := sub rec 0 16
  let tId := sub rec 16 32
  let tRest := sub rec 32 350
  let (trct, cr, tr) :=
    if s.save = tCard then (s.trct, s.cr, (s.tr + 1).srem 10000)
    else (trctSet s.trct s.cr s.tr, (s.cr + 1).srem 10000, (1 : I64))
  let m1 := memWr s.m (cardOffJ cr).toInt tCard
  let m2 := memWr m1 (tranOffJ cr tr).toInt tId
  let m3 := memWr m2 (tranOffJ cr tr + 16).toInt tRest
  ⟨m3, trct, cr, tr, tCard⟩

def ldAll (s : LdSt) : List JStr → LdSt
  | [] => s
  | r :: rs => ldAll (ldStep s r) rs

/-- The record of a text as `run` reads it: `fix(text, 1000).substring(0, len)`. -/
def recOf (t : JStr) (len : Nat) : JStr := sub (fixStr t 1000) 0 len

/-- The empty table: every slot `null` (spaces), every count 0. -/
def mem0 : Nat → JChar := fun _ => space
def trct0 : List Value := List.replicate 51 (.long 0)

/-- 2000-CUSTFILE-GET: the first customer text whose key (its first 9 characters) is `k`. -/
def custFind (keys texts : List JStr) (k : JStr) : Option JStr :=
  ((keys.zip texts).find? (fun p => decide (p.1 = k))).map (·.2)

/-- 3000-ACCTFILE-GET: the first account text whose first 11 characters are `k`. -/
def acctFind (texts : List JStr) (k : JStr) : Option JStr :=
  texts.find? (fun t => decide (sub t 0 11 = k))

/-- The transactions `1 … k` of card number `crJmp` in the table (4000-TRNXFILE-GET's inner loop): the lines
`writeTrans` writes and the running total. -/
def transOf (m : Nat → JChar) (crJmp : I64) : Nat → JOut × I64 → JOut × I64
  | 0, acc => acc
  | k + 1, acc =>
    let (o, total) := transOf m crJmp k acc
    let trJmp : I64 := BitVec.ofNat 64 (k + 1)
    let tid := memRd m (tranOffJ crJmp trJmp).toInt 16
    let trest := memRd m (tranOffJ crJmp trJmp + 16).toInt 318
    let amt : I64 := BitVec.ofInt 64 (zonedVal (sub trest 116 127))
    (o.add (jWriteTrans tid trest amt.toInt), BitVec.ofInt 64 (trunc11Z (total + amt).toInt))

/-- The cards loop of 4000-TRNXFILE-GET from card number `crJmp` (fuel `n`: the cards left). -/
def cardsFrom (m : Nat → JChar) (trct : List Value) (crCnt : I64) (card : JStr) :
    Nat → I64 → JOut × I64 → JOut × I64
  | 0, _, acc => acc
  | n + 1, crJmp, acc =>
    if crCnt.toInt < crJmp.toInt then acc
    else
      let cn := memRd m (cardOffJ crJmp).toInt 16
      if 0 < ebcCmp cn card then acc
      else
        let acc' :=
          if card = cn then
            match trctGet trct crJmp with
            | .long cnt => transOf m crJmp cnt.toInt.toNat acc
            | _ => acc
          else acc
        cardsFrom m trct crCnt card n (crJmp + 1) acc'

/-- The statement's tail (after the transactions). -/
def tailOf (o : JOut) (total : I64) : JOut :=
  let o := o.stmt1 (List.replicate 80 chDash)
  let o := o.stmt1 (jl "Total EXP:" ++ List.replicate 56 space ++ jl "$" ++ fmtZStr total.toInt)
  let o := o.stmt1 (List.replicate 32 chStar ++ jl "END OF STATEMENT" ++ List.replicate 32 chStar)
  [LTRS, L10, L75, LTDE, LTRE, L78, L79, L80].foldl JOut.html1 o

/-- One cross-reference record (one iteration of 1000-MAINLINE); `.error` when it abends (with the outputs). -/
def xrefStep (custKeys custTexts acctTexts : List JStr) (ld : LdSt) (o : JOut) (x : JStr) : Except JOut JOut :=
  let fldt := fixStr x 1000
  let card := sub fldt 0 16
  let custId := sub fldt 16 25
  let acctId := sub fldt 25 36
  match custFind custKeys custTexts custId with
  | none => .error (o.abend (jl "ERROR READING CUSTFILE") (jl "23"))
  | some custRec =>
    match acctFind acctTexts acctId with
    | none => .error (o.abend (jl "ERROR READING ACCTFILE") (jl "23"))
    | some acctRec =>
      let o := o.add (jCreateStatement custRec acctRec)
      let (o, total) := cardsFrom ld.m ld.trct ld.cr card ld.cr.toInt.toNat 1 (o, 0)
      .ok (tailOf o total)

def xrefAll (custKeys custTexts acctTexts : List JStr) (ld : LdSt) : JOut → List JStr → JOut
  | o, [] => o
  | o, x :: xs =>
    match xrefStep custKeys custTexts acctTexts ld o x with
    | .error o' => o'
    | .ok o' => xrefAll custKeys custTexts acctTexts ld o' xs

/-- The table after the load: the counts of the last card stored. -/
def ldFin (s : LdSt) : LdSt := { s with trct := trctSet s.trct s.cr s.tr }

/-- The load's start for the first record `r0`. -/
def ld0 (r0 : JStr) : LdSt := ⟨mem0, trct0, 1, 0, sub r0 0 16⟩

/-- **`run` on the record texts.** -/
def jRunT (trnxTexts xrefTexts custTexts acctTexts : List JStr) : JOut :=
  match trnxTexts with
  | [] => JOut.init.abend (jl "ERROR READING TRNXFILE") (jl "10")
  | t0 :: ts =>
    let ld := ldFin (ldAll (ld0 (recOf t0 350)) ((t0 :: ts).map (recOf · 350)))
    xrefAll (custTexts.map (sub · 0 9)) custTexts acctTexts ld JOut.init xrefTexts

/-- **`run` on the records' field values.** -/
def jRunR (trs : List TrnxR) (xrs : List XrefR) (crs : List CustR) (ars : List AcctR) : JOut :=
  jRunT (trs.map trnxTextR) (xrs.map xrefTextR) (crs.map custTextR) (ars.map acctTextR)

end EquivLean.Modernize.Cbstm03a.Java
