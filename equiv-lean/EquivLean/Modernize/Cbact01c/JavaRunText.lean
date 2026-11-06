import EquivLean.Modernize.Cbact01c.JavaRunCobdat

/-!
# CBACT01C → Java: `accountRecordText`

The record's text (`acctTextJ`), against the contracts of `zoned` and `pad`. No loop.
-/

-- JimpleLean 2006Z took `ite_nat_ne` out of `jsimp`: these proofs decide address
-- (dis)equalities with it.
attribute [local jsimp high] Jimple.ite_nat_ne

open Jimple EquivLean EquivLean.Jimple EquivLean.Jimple.Spec EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbact01c.Java

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem accountRecordText_vc :
    MethodVC Gen.prog textCallees.env 0 accountRecordTextRef accountRecordTextSpec [] 80 := by
  jverify [accountRecordTextSpec, textCallees, zonedSig, padSig, zonedSpec, padSpec, AcctOk,
    StrField, LongField, StrOk, acctTextJ, sfJ, zfJ, fieldOf, fieldLong, argText, Grows, acctCls]

end EquivLean.Modernize.Cbact01c.Java

