import EquivLean.Modernize.Cbact01c.JavaRunGlueOut

/-!
# CBACT01C → Java: `displayAcctRecord`

The twelve lines it adds to the `displays` list `L` of the `Result` (`dispLine σ c 0` … `11`),
new strings; every other object is unchanged. Against the contract of `zoned`. No loop: three
cut points split the twelve lines into four segments (statements 16, 30, 43).
-/

-- JimpleLean 2006Z took `ite_nat_ne` out of `jsimp`: these proofs decide address
-- (dis)equalities with it.
attribute [local jsimp high] Jimple.ite_nat_ne

open Jimple EquivLean EquivLean.Jimple EquivLean.Jimple.Spec EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbact01c.Java

def dispCallees : Contracts := [(zonedSig, zonedSpec)]

abbrev displayAcctRecordRef : MethodRef :=
  Gen.Cbact01c.«displayAcctRecord(Cbact01c$Result,Cbact01c$AccountRecord)».ref

/-- `displayAcctRecord(res, c)` with `L` the `displays` list of `res`. -/
def displayAcctRecordSpec (L : Addr) : Spec := Spec.of
  (fun args σ => ∃ res c fs ys m, args = [.ref res, .ref c] ∧
     σ.heap res = some (.plain resCls fs) ∧ Fields.get fs (resCls, "displays") = some (.ref L) ∧
     σ.heap L = some (.list .arrayList ys m) ∧ res < L ∧ L < σ.next ∧ AcctOkB σ c L ∧
     σ.initOf "Cbact01c" = .done)
  (fun args σ r σ' => ∀ res c, args = [.ref res, .ref c] →
     r = none ∧
     (∃ w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 : Addr,
       σ'.heap L = some (.list .arrayList (lElems σ L ++
         [.ref w1, .ref w2, .ref w3, .ref w4, .ref w5, .ref w6, .ref w7, .ref w8, .ref w9, .ref w10,
          .ref w11, .ref w12]) (lMods σ L + 12)) ∧
       σ.next ≤ w1 ∧ σ.next ≤ w2 ∧ σ.next ≤ w3 ∧ σ.next ≤ w4 ∧ σ.next ≤ w5 ∧ σ.next ≤ w6 ∧
       σ.next ≤ w7 ∧ σ.next ≤ w8 ∧ σ.next ≤ w9 ∧ σ.next ≤ w10 ∧ σ.next ≤ w11 ∧ σ.next ≤ w12 ∧
       σ'.heap w1 = some (.str (dispLine σ c 0)) ∧ σ'.heap w2 = some (.str (dispLine σ c 1)) ∧
       σ'.heap w3 = some (.str (dispLine σ c 2)) ∧ σ'.heap w4 = some (.str (dispLine σ c 3)) ∧
       σ'.heap w5 = some (.str (dispLine σ c 4)) ∧ σ'.heap w6 = some (.str (dispLine σ c 5)) ∧
       σ'.heap w7 = some (.str (dispLine σ c 6)) ∧ σ'.heap w8 = some (.str (dispLine σ c 7)) ∧
       σ'.heap w9 = some (.str (dispLine σ c 8)) ∧ σ'.heap w10 = some (.str (dispLine σ c 9)) ∧
       σ'.heap w11 = some (.str (dispLine σ c 10)) ∧ σ'.heap w12 = some (.str (dispLine σ c 11))) ∧
     σ.next ≤ σ'.next ∧ (∀ x, x < σ.next → x ≠ L → σ'.heap x = σ.heap x) ∧
     σ'.inits = σ.inits ∧ σ'.statics = σ.statics)

/-- After three lines (statement 16). Locals: `r0` 0 (the `Result`), `r1` 4 (the record). -/
def dispCut3 (L : Addr) (args : List Value) (σ0 : Jimple.State) (fr : Frame) (σ : Jimple.State) :
    Prop :=
  ∀ res c, args = [.ref res, .ref c] → ∃ w1 w2 w3 : Addr,
    fr.get 0 = some (.ref res) ∧ fr.get 4 = some (.ref c) ∧
    σ.heap L = some (.list .arrayList (lElems σ0 L ++ [.ref w1, .ref w2, .ref w3]) (lMods σ0 L + 3)) ∧
    σ0.next ≤ w1 ∧ σ0.next ≤ w2 ∧ σ0.next ≤ w3 ∧
    σ.heap w1 = some (.str (dispLine σ0 c 0)) ∧ σ.heap w2 = some (.str (dispLine σ0 c 1)) ∧
    σ.heap w3 = some (.str (dispLine σ0 c 2)) ∧
    σ0.next ≤ σ.next ∧ (∀ x, x < σ0.next → x ≠ L → σ.heap x = σ0.heap x) ∧
    σ.inits = σ0.inits ∧ σ.statics = σ0.statics

/-- After six lines (statement 30). -/
def dispCut6 (L : Addr) (args : List Value) (σ0 : Jimple.State) (fr : Frame) (σ : Jimple.State) :
    Prop :=
  ∀ res c, args = [.ref res, .ref c] → ∃ w1 w2 w3 w4 w5 w6 : Addr,
    fr.get 0 = some (.ref res) ∧ fr.get 4 = some (.ref c) ∧
    σ.heap L = some (.list .arrayList
      (lElems σ0 L ++ [.ref w1, .ref w2, .ref w3, .ref w4, .ref w5, .ref w6]) (lMods σ0 L + 6)) ∧
    σ0.next ≤ w1 ∧ σ0.next ≤ w2 ∧ σ0.next ≤ w3 ∧ σ0.next ≤ w4 ∧ σ0.next ≤ w5 ∧ σ0.next ≤ w6 ∧
    σ.heap w1 = some (.str (dispLine σ0 c 0)) ∧ σ.heap w2 = some (.str (dispLine σ0 c 1)) ∧
    σ.heap w3 = some (.str (dispLine σ0 c 2)) ∧ σ.heap w4 = some (.str (dispLine σ0 c 3)) ∧
    σ.heap w5 = some (.str (dispLine σ0 c 4)) ∧ σ.heap w6 = some (.str (dispLine σ0 c 5)) ∧
    σ0.next ≤ σ.next ∧ (∀ x, x < σ0.next → x ≠ L → σ.heap x = σ0.heap x) ∧
    σ.inits = σ0.inits ∧ σ.statics = σ0.statics

/-- After nine lines (statement 43). -/
def dispCut9 (L : Addr) (args : List Value) (σ0 : Jimple.State) (fr : Frame) (σ : Jimple.State) :
    Prop :=
  ∀ res c, args = [.ref res, .ref c] → ∃ w1 w2 w3 w4 w5 w6 w7 w8 w9 : Addr,
    fr.get 0 = some (.ref res) ∧ fr.get 4 = some (.ref c) ∧
    σ.heap L = some (.list .arrayList (lElems σ0 L ++
      [.ref w1, .ref w2, .ref w3, .ref w4, .ref w5, .ref w6, .ref w7, .ref w8, .ref w9])
      (lMods σ0 L + 9)) ∧
    σ0.next ≤ w1 ∧ σ0.next ≤ w2 ∧ σ0.next ≤ w3 ∧ σ0.next ≤ w4 ∧ σ0.next ≤ w5 ∧ σ0.next ≤ w6 ∧
    σ0.next ≤ w7 ∧ σ0.next ≤ w8 ∧ σ0.next ≤ w9 ∧
    σ.heap w1 = some (.str (dispLine σ0 c 0)) ∧ σ.heap w2 = some (.str (dispLine σ0 c 1)) ∧
    σ.heap w3 = some (.str (dispLine σ0 c 2)) ∧ σ.heap w4 = some (.str (dispLine σ0 c 3)) ∧
    σ.heap w5 = some (.str (dispLine σ0 c 4)) ∧ σ.heap w6 = some (.str (dispLine σ0 c 5)) ∧
    σ.heap w7 = some (.str (dispLine σ0 c 6)) ∧ σ.heap w8 = some (.str (dispLine σ0 c 7)) ∧
    σ.heap w9 = some (.str (dispLine σ0 c 8)) ∧
    σ0.next ≤ σ.next ∧ (∀ x, x < σ0.next → x ≠ L → σ.heap x = σ0.heap x) ∧
    σ.inits = σ0.inits ∧ σ.statics = σ0.statics

def dispInv (L : Addr) : Invariants :=
  [(16, dispCut3 L), (30, dispCut6 L), (43, dispCut9 L)]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem displayAcctRecord_vc (L : Addr) :
    MethodVC Gen.prog dispCallees.env 0 displayAcctRecordRef (displayAcctRecordSpec L) (dispInv L)
      120 := by
  jverify [displayAcctRecordSpec, dispInv, dispCut3, dispCut6, dispCut9, dispLine, dispCallees,
    zonedSig, zonedSpec, AcctOkB, StrFieldB, LongField,
    dispLinesJ, lElems, lMods, sfJ, zfJ, fieldOf, fieldLong, argText, acctCls, resCls,
    evalDynamic, concatRecipe_nil', concatRecipe_const, concatRecipe_arg, Native.valueOfArg, JType.isRef, jstrLit, Grows,
    exists_and_left, exists_and_right, and_assoc, exists_eq_left, exists_eq_left', exists_eq_right,
    exists_eq_right']

end EquivLean.Modernize.Cbact01c.Java
