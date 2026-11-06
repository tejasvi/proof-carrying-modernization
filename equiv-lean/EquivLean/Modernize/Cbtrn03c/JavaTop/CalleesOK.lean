import EquivLean.Modernize.Cbtrn03c.JavaTop.CalAdd11
import EquivLean.Modernize.Cbtrn03c.JavaTop.CalSpaces
import EquivLean.Modernize.Cbtrn03c.JavaTop.CalNum
import EquivLean.Modernize.Cbtrn03c.JavaTop.CalZoned
import EquivLean.Modernize.Cbtrn03c.JavaTop.CalIo
import EquivLean.Modernize.Cbtrn03c.JavaTop.CalFindOK
import EquivLean.Modernize.Cbtrn03c.JavaTop.CalEbcOK
import EquivLean.Modernize.Cbtrn03c.JavaTop.CalRecOK
import EquivLean.Modernize.Cbtrn03c.JavaTop.CalBlank

set_option jimple.modelContracts true

/-!
# CBTRN03C → Java, top layer: the callee contracts

The contracts of `T3X/Callees.lean` and `T3X/Pe.lean` (`zonedSpecT`, `add11SpecT`), each proved in
a `T3X/Cal*.lean` file:

* `spaces_ok`, `blankTran_ok`, `tranRecordText_ok`, `ioStatusLine_ok`, `digits_ok`, `zoned_ok`,
  `add11_ok`, `findXref_ok`, `findTranType_ok`, `findTranCat_ok`;
* `compareEbcdicSpecT` does not hold as stated (a character outside Latin-1: `ebcdic` gives `0x6F`,
  the model's `ebc` 0; `Cal.cmpFrom_counterexample`).  `compareEbcdicL_ok`: the contract with
  Latin-1 strings (`compareEbcdicSpecL`: the precondition with `∀ u ∈ sa, u.toNat < 256` and the
  same for `sb`, the same postcondition); the callers' strings are CP037 texts
  (`Cal.forall_mem_cp037Str_lt`, `Cal.forall_mem_cp037Str_lt_iff`).  `compareEbcdicC_ok`: the
  same for strings given as CP037 texts (`compareEbcdicSpecC`: `σ.heap xa = some (.str (cp037Str
  ba))`, `ba.length = bb.length`, …).
-/

open Jimple EquivLean.Cobol.Rec EquivLean.Jimple

namespace EquivLean.Modernize.Cbtrn03c.Java.Top

/-- The callee contracts, together. -/
theorem callees_ok :
    ContractOK Gen.prog spacesSig spacesSpecT ∧
    ContractOK Gen.prog blankTranSig blankTranSpecT ∧
    ContractOK Gen.prog compareEbcdicSig compareEbcdicSpecL ∧
    ContractOK Gen.prog tranRecordTextSig tranRecordTextSpecT ∧
    ContractOK Gen.prog ioStatusLineSig ioStatusLineSpecT ∧
    ContractOK Gen.prog digitsSig digitsSpecT ∧
    ContractOK Gen.prog zonedSig zonedSpecT ∧
    ContractOK Gen.prog add11Sig add11SpecT ∧
    ContractOK Gen.prog findXrefSig findXrefSpecT ∧
    ContractOK Gen.prog findTranTypeSig findTranTypeSpecT ∧
    ContractOK Gen.prog findTranCatSig findTranCatSpecT :=
  ⟨spaces_ok, blankTran_ok, compareEbcdicL_ok, tranRecordText_ok, ioStatusLine_ok, digits_ok,
    zoned_ok, add11_ok, findXref_ok, findTranType_ok, findTranCat_ok⟩

end EquivLean.Modernize.Cbtrn03c.Java.Top

#print axioms EquivLean.Modernize.Cbtrn03c.Java.Top.spaces_ok
#print axioms EquivLean.Modernize.Cbtrn03c.Java.Top.blankTran_ok
#print axioms EquivLean.Modernize.Cbtrn03c.Java.Top.compareEbcdicL_ok
#print axioms EquivLean.Modernize.Cbtrn03c.Java.Top.compareEbcdicC_ok
#print axioms EquivLean.Modernize.Cbtrn03c.Java.Top.tranRecordText_ok
#print axioms EquivLean.Modernize.Cbtrn03c.Java.Top.ioStatusLine_ok
#print axioms EquivLean.Modernize.Cbtrn03c.Java.Top.digits_ok
#print axioms EquivLean.Modernize.Cbtrn03c.Java.Top.zoned_ok
#print axioms EquivLean.Modernize.Cbtrn03c.Java.Top.add11_ok
#print axioms EquivLean.Modernize.Cbtrn03c.Java.Top.findXref_ok
#print axioms EquivLean.Modernize.Cbtrn03c.Java.Top.findTranType_ok
#print axioms EquivLean.Modernize.Cbtrn03c.Java.Top.findTranCat_ok
#print axioms EquivLean.Modernize.Cbtrn03c.Java.Top.Cal.cmpFrom_counterexample
#print axioms EquivLean.Modernize.Cbtrn03c.Java.Top.callees_ok
