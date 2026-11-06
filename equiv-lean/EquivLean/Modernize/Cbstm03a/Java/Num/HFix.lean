import EquivLean.Modernize.Cbstm03a.Java.Iface1

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows fixStr argText StrOk space jstr_empty fixStr_eq_take fixStr_eq_self
  fixStr_eq_append fixStr_length max_zero_of_nonneg)

namespace EquivLean.Modernize.Cbstm03a.Java

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
set_option jimple.modelContracts true in
theorem fix_vc : MethodVC Gen.prog fixCallees.env 0 fixRef fixSpecI [] 40 := by
  jverify [ite_nat_ne, fixSpecI, fixCallees, spacesSig, spacesSpecI, StrOk, argText, strOf, Grows, jstr_empty,
    fixStr_eq_take, fixStr_eq_self, fixStr_eq_append, Option.getD_some, max_zero_of_nonneg]

end EquivLean.Modernize.Cbstm03a.Java

#print axioms EquivLean.Modernize.Cbstm03a.Java.fix_vc
