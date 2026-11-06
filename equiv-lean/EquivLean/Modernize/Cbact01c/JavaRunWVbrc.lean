import EquivLean.Modernize.Cbact01c.JavaRunWArr

/-!
# CBACT01C → Java: `writeVbrcRecords`

`writeVbrcRecords(res, c)` builds the two variable-length records of the record at `c` (`vb1J`,
`vb2J`), adds their lines to the `displays` list `L1` and the records to the `vbrcFileWrites`
list `L4` of the `Result`; every other object is unchanged. Against the contracts of `zoned` and
`pad`. No loop.
-/

-- JimpleLean 2006Z took `ite_nat_ne` out of `jsimp`: these proofs decide address
-- (dis)equalities with it.
attribute [local jsimp high] Jimple.ite_nat_ne

open Jimple EquivLean EquivLean.Jimple EquivLean.Jimple.Spec EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbact01c.Java

abbrev writeVbrcRecordsRef : MethodRef :=
  Gen.Cbact01c.«writeVbrcRecords(Cbact01c$Result,Cbact01c$AccountRecord)».ref

/-- `writeVbrcRecords(res, c)` with `L1`, `L4` the `displays` and `vbrcFileWrites` lists of
`res`. -/
def writeVbrcRecordsSpec (L1 L4 : Addr) : Spec := Spec.of
  (fun args σ => ∃ res c fs ys1 m1 ys4 m4, args = [.ref res, .ref c] ∧
     σ.heap res = some (.plain resCls fs) ∧ Fields.get fs (resCls, "displays") = some (.ref L1) ∧
     Fields.get fs (resCls, "vbrcFileWrites") = some (.ref L4) ∧ L1 < L4 ∧ res < L1 ∧
     L4 < σ.next ∧
     σ.heap L1 = some (.list .arrayList ys1 m1) ∧ σ.heap L4 = some (.list .arrayList ys4 m4) ∧
     AcctOkB σ c L1 ∧ σ.initOf "Cbact01c" = .done)
  (fun args σ r σ' => ∀ res c, args = [.ref res, .ref c] →
     r = none ∧
     (∃ y1 y2 : Addr,
       σ'.heap L1 = some (.list .arrayList (lElems σ L1 ++ [.ref y1, .ref y2]) (lMods σ L1 + 2)) ∧
       σ.next ≤ y1 ∧ σ.next ≤ y2 ∧
       σ'.heap y1 = some (.str (JStr.ofString "VBRC-REC1:" ++ vb1J σ c)) ∧
       σ'.heap y2 = some (.str (JStr.ofString "VBRC-REC2:" ++ vb2J σ c))) ∧
     (∃ w1 w2 : Addr,
       σ'.heap L4 = some (.list .arrayList (lElems σ L4 ++ [.ref w1, .ref w2]) (lMods σ L4 + 2)) ∧
       σ.next ≤ w1 ∧ σ.next ≤ w2 ∧
       σ'.heap w1 = some (.str (vb1J σ c)) ∧ σ'.heap w2 = some (.str (vb2J σ c))) ∧
     σ.next ≤ σ'.next ∧ (∀ x, x < σ.next → x ≠ L1 → x ≠ L4 → σ'.heap x = σ.heap x) ∧
     σ'.inits = σ.inits ∧ σ'.statics = σ.statics)

/-- Statement 18: VBRC-REC1 built in `$r2` (local 3), the id and the balance in `$r6`
(local 4). Locals: `r0` 0, `r1` 8. -/
def vbrcCut18 (args : List Value) (σ0 : Jimple.State) (fr : Frame) (σ : Jimple.State) : Prop :=
  ∀ res c, args = [.ref res, .ref c] → ∃ sb1 sb2 : Addr,
    fr.get 0 = some (.ref res) ∧ fr.get 8 = some (.ref c) ∧
    fr.get 3 = some (.ref sb1) ∧ fr.get 4 = some (.ref sb2) ∧
    σ.heap sb1 = some (.builder "java.lang.StringBuilder" (vb1J σ0 c)) ∧
    σ.heap sb2 = some (.builder "java.lang.StringBuilder"
      (zfJ σ0 c "acctId" 11 false ++ zfJ σ0 c "acctCurrBal" 12 true)) ∧
    σ0.next ≤ sb1 ∧ sb1 < sb2 ∧ sb2 < σ.next ∧
    σ0.next ≤ σ.next ∧ (∀ x, x < σ0.next → σ.heap x = σ0.heap x) ∧
    σ.inits = σ0.inits ∧ σ.statics = σ0.statics

def vbrcInv : Invariants := [(18, vbrcCut18)]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem writeVbrcRecords_vc (L1 L4 : Addr) :
    MethodVC Gen.prog textCallees.env 0 writeVbrcRecordsRef (writeVbrcRecordsSpec L1 L4) vbrcInv
      120 := by
  jverify [writeVbrcRecordsSpec, vbrcInv, vbrcCut18, textCallees, zonedSig, padSig, zonedSpec,
    padSpec, AcctOkB, StrFieldB, LongField, StrOk, vb1J, vb2J, lElems, lMods, sfJ, zfJ, fieldOf,
    fieldLong, argText, acctCls, resCls,
    evalDynamic, concatRecipe_nil', concatRecipe_const, concatRecipe_arg, Native.valueOfArg, JType.isRef, jstrLit, Grows, fixStr_length]

end EquivLean.Modernize.Cbact01c.Java
