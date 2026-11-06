import EquivLean.Modernize.Cbact01c.JavaRunWOut

/-!
# CBACT01C → Java: `writeArrayRecord`

`writeArrayRecord(res, c)` adds to the `arryFileWrites` list `L` of the `Result` a new
`ArrArrayRec`: the record's id, the arrays of balances and cycle debits (`balArr`, `debArr`), four
spaces (`ArrRecJ`); every other object is unchanged. Against the contract of `spaces`; the
constructor is inlined. No loop.
-/

-- JimpleLean 2006Z took `ite_nat_ne` out of `jsimp`: these proofs decide address
-- (dis)equalities with it.
attribute [local jsimp high] Jimple.ite_nat_ne

open Jimple EquivLean EquivLean.Jimple EquivLean.Jimple.Spec EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbact01c.Java

def arrCallees : Contracts := [(spacesSig, spacesSpecF)]

abbrev writeArrayRecordRef : MethodRef :=
  Gen.Cbact01c.«writeArrayRecord(Cbact01c$Result,Cbact01c$AccountRecord)».ref

/-- `writeArrayRecord(res, c)` with `L` the `arryFileWrites` list of `res`. -/
def writeArrayRecordSpec (L : Addr) : Spec := Spec.of
  (fun args σ => ∃ res c fs ys m, args = [.ref res, .ref c] ∧
     σ.heap res = some (.plain resCls fs) ∧ Fields.get fs (resCls, "arryFileWrites") = some (.ref L) ∧
     σ.heap L = some (.list .arrayList ys m) ∧ res < L ∧ L < σ.next ∧ AcctOkB σ c L ∧
     σ.initOf "Cbact01c" = .done ∧ σ.initOf "Cbact01c$ArrArrayRec" = .done)
  (fun args σ r σ' => ∀ res c, args = [.ref res, .ref c] →
     r = none ∧
     (∃ o, σ'.heap L = some (.list .arrayList (lElems σ L ++ [.ref o]) (lMods σ L + 1)) ∧
       σ.next ≤ o ∧ ArrRecJ σ' o σ c σ.next) ∧
     σ.next ≤ σ'.next ∧ (∀ x, x < σ.next → x ≠ L → σ'.heap x = σ.heap x) ∧
     σ'.inits = σ.inits ∧ σ'.statics = σ.statics)

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem writeArrayRecord_vc (L : Addr) :
    MethodVC Gen.prog arrCallees.env 1 writeArrayRecordRef (writeArrayRecordSpec L) [] 120 := by
  jverify [writeArrayRecordSpec, arrCallees, spacesSig, spacesSpecF, AcctOkB, StrFieldB, LongField,
    ArrRecJ, balArr, debArr, lElems, lMods, fieldOf, fieldLong, acctCls, resCls, arrCls,
    inlineFuel, Grows]

end EquivLean.Modernize.Cbact01c.Java
