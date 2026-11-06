import EquivLean.Modernize.Cbstm03a.Java.RunInv
import EquivLean.Modernize.Cbstm03a.JavaSpec
import EquivLean.Modernize.Cbstm03a.StmBridge

/-!
# CBSTM03A → Java: `trnxROf`, `xrefROf`, `custROf`, `acctROf` from `List FVal`

Shared definitions connecting `JavaStatement`'s `List FVal` records to `Iface3`/`JRun`'s
`TrnxR`, `XrefR`, `CustR`, `AcctR` structures.
-/

open Cobol Cobol.StmCore EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03a.StmBridge EquivLean.Modernize.Cbstm03a.Model

namespace EquivLean.Modernize.Cbstm03a.Java

def jStrOf (v : List EquivLean.Cobol.Rec.FVal) (i : Nat) : JStr := cp037Str (strOf (v.getD i default))
def i64Of (v : List EquivLean.Cobol.Rec.FVal) (i : Nat) : I64 := BitVec.ofInt 64 (numOf (v.getD i default))

def trnxROf (v : List EquivLean.Cobol.Rec.FVal) : TrnxR :=
  ⟨jStrOf v 0, jStrOf v 1, jStrOf v 2, i64Of v 3, jStrOf v 4, jStrOf v 5, i64Of v 6,
   i64Of v 7, jStrOf v 8, jStrOf v 9, jStrOf v 10, jStrOf v 11, jStrOf v 12, jStrOf v 13⟩

def xrefROf (v : List EquivLean.Cobol.Rec.FVal) : XrefR :=
  ⟨jStrOf v 0, i64Of v 1, i64Of v 2, jStrOf v 3⟩

def custROf (v : List EquivLean.Cobol.Rec.FVal) : CustR :=
  ⟨i64Of v 0, jStrOf v 1, jStrOf v 2, jStrOf v 3, jStrOf v 4, jStrOf v 5, jStrOf v 6,
   jStrOf v 7, jStrOf v 8, jStrOf v 9, jStrOf v 10, jStrOf v 11, i64Of v 12, jStrOf v 13,
   jStrOf v 14, jStrOf v 15, jStrOf v 16, i64Of v 17, jStrOf v 18⟩

def acctROf (v : List EquivLean.Cobol.Rec.FVal) : AcctR :=
  ⟨i64Of v 0, jStrOf v 1, i64Of v 2, i64Of v 3, i64Of v 4, jStrOf v 5, jStrOf v 6,
   jStrOf v 7, i64Of v 8, i64Of v 9, jStrOf v 10, jStrOf v 11, jStrOf v 12⟩

end EquivLean.Modernize.Cbstm03a.Java
