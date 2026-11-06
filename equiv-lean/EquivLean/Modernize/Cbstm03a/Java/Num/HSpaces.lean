import EquivLean.Modernize.Cbstm03a.Java.Iface1

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows space)

namespace EquivLean.Modernize.Cbstm03a.Java

theorem setWidth_32_space : (32#32 : BitVec 32).setWidth 16 = space := by decide

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem spaces_vc : MethodVC Gen.prog spacesCallees.env 0 spacesRef spacesSpecI [] 20 := by
  jverify [spacesSpecI, spacesCallees, repeatSig, repeatSpec, Grows, setWidth_32_space]

end EquivLean.Modernize.Cbstm03a.Java

#print axioms EquivLean.Modernize.Cbstm03a.Java.spaces_vc
