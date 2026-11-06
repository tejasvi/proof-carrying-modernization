import EquivLean.Modernize.Cbact01c.JavaRunDisp

/-!
# CBACT01C → Java: `writeOutRecord`

`writeOutRecord(res, c, d, cd)` adds to the `outFileWrites` list `L` of the `Result` a new
`OutAcctRec` holding the record's fields (strings padded by `pad`), the date `d` padded to ten
characters and the cycle debit `cd` (`OutRecJ`); every other object is unchanged. Against the
contract of `pad`; the constructor is inlined. No loop: cut points after every two `pad` calls
(statements 13, 16, 19), so that the new object is never read across more than two calls.

Locals: `r0` 0, `l0` 1 (`cd`), `$l1` 2, `$l2` 3, `$l3` 4, `$l4` 5, `$l5` 6, `$r3` 7 (the new
record), `$r13` 8, `r2` 9 (`d`, then its padded copy), `$r4` 10, `$r6` 11, `$r8` 12, `$r11` 13,
`r1` 14 (the account record).
-/

-- JimpleLean 2006Z took `ite_nat_ne` out of `jsimp`: these proofs decide address
-- (dis)equalities with it.
attribute [local jsimp high] Jimple.ite_nat_ne

open Jimple EquivLean EquivLean.Jimple EquivLean.Jimple.Spec EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbact01c.Java

def outCallees : Contracts := [(padSig, padSpecF)]

abbrev writeOutRecordRef : MethodRef :=
  Gen.Cbact01c.«writeOutRecord(Cbact01c$Result,Cbact01c$AccountRecord,java.lang.String,long)».ref

/-- `writeOutRecord(res, c, d, cd)` with `L` the `outFileWrites` list of `res`. -/
def writeOutRecordSpec (L : Addr) : Spec := Spec.of
  (fun args σ => ∃ res c d cd fs ys m sd, args = [.ref res, .ref c, .ref d, .long cd] ∧
     σ.heap res = some (.plain resCls fs) ∧ Fields.get fs (resCls, "outFileWrites") = some (.ref L) ∧
     σ.heap L = some (.list .arrayList ys m) ∧ res < L ∧ L < σ.next ∧ AcctOkB σ c L ∧
     σ.heap d = some (.str sd) ∧ sd.length < 2147483648 ∧ d ≠ L ∧
     σ.initOf "Cbact01c" = .done ∧ σ.initOf "Cbact01c$OutAcctRec" = .done)
  (fun args σ r σ' => ∀ res c d cd, args = [.ref res, .ref c, .ref d, .long cd] →
     r = none ∧
     (∃ o, σ'.heap L = some (.list .arrayList (lElems σ L ++ [.ref o]) (lMods σ L + 1)) ∧
       σ.next ≤ o ∧ OutRecJ σ' o σ c (argText σ (.ref d)) cd σ.next) ∧
     σ.next ≤ σ'.next ∧ (∀ x, x < σ.next → x ≠ L → σ'.heap x = σ.heap x) ∧
     σ'.inits = σ.inits ∧ σ'.statics = σ.statics)

/-- The common facts at the cut points: the arguments in their locals, the new record `o`, the
heap grown from the entry state. -/
def WOutBase (σ0 : Jimple.State) (fr : Frame) (σ : Jimple.State) (res c : Addr)
    (cd : I64) (o : Addr) (v0 v2 v3 v4 : I64) (x1 x5 : Addr) : Prop :=
  fr.get 0 = some (.ref res) ∧ fr.get 14 = some (.ref c) ∧ fr.get 1 = some (.long cd) ∧
  fr.get 7 = some (.ref o) ∧ σ.heap o = some (.plain outCls outFields0) ∧ σ0.next ≤ o ∧ o < σ.next ∧
  fr.get 2 = some (.long v0) ∧ v0 = fieldLong σ0 c "acctId" ∧
  fr.get 10 = some (.ref x1) ∧ σ0.next ≤ x1 ∧ x1 < σ.next ∧
  σ.heap x1 = some (.str (fixStr (sfJ σ0 c "acctActiveStatus") 1)) ∧
  fr.get 3 = some (.long v2) ∧ v2 = fieldLong σ0 c "acctCurrBal" ∧
  fr.get 4 = some (.long v3) ∧ v3 = fieldLong σ0 c "acctCreditLimit" ∧
  fr.get 5 = some (.long v4) ∧ v4 = fieldLong σ0 c "acctCashCreditLimit" ∧
  fr.get 11 = some (.ref x5) ∧ σ0.next ≤ x5 ∧ x5 < σ.next ∧
  σ.heap x5 = some (.str (fixStr (sfJ σ0 c "acctOpenDate") 10)) ∧
  σ0.next ≤ σ.next ∧ (∀ x, x < σ0.next → σ.heap x = σ0.heap x) ∧
  σ.inits = σ0.inits ∧ σ.statics = σ0.statics

/-- Statement 13: `pad` of the status and of the open date done. -/
def woutCut13 (args : List Value) (σ0 : Jimple.State) (fr : Frame) (σ : Jimple.State) : Prop :=
  ∀ res c d cd, args = [.ref res, .ref c, .ref d, .long cd] → ∃ o v0 v2 v3 v4 x1 x5,
    WOutBase σ0 fr σ res c cd o v0 v2 v3 v4 x1 x5 ∧ fr.get 9 = some (.ref d)

/-- Statement 16: also the expiry date and the date `d` (`r2` now its padded copy). -/
def woutCut16 (args : List Value) (σ0 : Jimple.State) (fr : Frame) (σ : Jimple.State) : Prop :=
  ∀ res c d cd, args = [.ref res, .ref c, .ref d, .long cd] → ∃ o v0 v2 v3 v4 x1 x5 x6 x7,
    WOutBase σ0 fr σ res c cd o v0 v2 v3 v4 x1 x5 ∧
    fr.get 12 = some (.ref x6) ∧ σ0.next ≤ x6 ∧ x6 < σ.next ∧
    σ.heap x6 = some (.str (fixStr (sfJ σ0 c "acctExpiraionDate") 10)) ∧
    fr.get 9 = some (.ref x7) ∧ σ0.next ≤ x7 ∧ x7 < σ.next ∧
    σ.heap x7 = some (.str (fixStr (argText σ0 (.ref d)) 10))

/-- Statement 19 (the constructor): also the cycle credit and the group id. -/
def woutCut19 (args : List Value) (σ0 : Jimple.State) (fr : Frame) (σ : Jimple.State) : Prop :=
  ∀ res c d cd, args = [.ref res, .ref c, .ref d, .long cd] → ∃ o v0 v2 v3 v4 x1 x5 x6 x7 v8 x10,
    WOutBase σ0 fr σ res c cd o v0 v2 v3 v4 x1 x5 ∧
    fr.get 12 = some (.ref x6) ∧ σ0.next ≤ x6 ∧ x6 < σ.next ∧
    σ.heap x6 = some (.str (fixStr (sfJ σ0 c "acctExpiraionDate") 10)) ∧
    fr.get 9 = some (.ref x7) ∧ σ0.next ≤ x7 ∧ x7 < σ.next ∧
    σ.heap x7 = some (.str (fixStr (argText σ0 (.ref d)) 10)) ∧
    fr.get 6 = some (.long v8) ∧ v8 = fieldLong σ0 c "acctCurrCycCredit" ∧
    fr.get 13 = some (.ref x10) ∧ σ0.next ≤ x10 ∧ x10 < σ.next ∧
    σ.heap x10 = some (.str (fixStr (sfJ σ0 c "acctGroupId") 10))

def woutInv : Invariants := [(13, woutCut13), (16, woutCut16), (19, woutCut19)]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem writeOutRecord_vc (L : Addr) :
    MethodVC Gen.prog outCallees.env 1 writeOutRecordRef (writeOutRecordSpec L) woutInv 120 := by
  jverify [writeOutRecordSpec, woutInv, woutCut13, woutCut16, woutCut19, WOutBase, outCallees,
    padSig, padSpecF, AcctOkB, StrFieldB, LongField, StrOk, OutRecJ, outFields0, lElems, lMods, sfJ, fieldOf,
    fieldLong, argText, acctCls, resCls, outCls, inlineFuel, Grows]

end EquivLean.Modernize.Cbact01c.Java
