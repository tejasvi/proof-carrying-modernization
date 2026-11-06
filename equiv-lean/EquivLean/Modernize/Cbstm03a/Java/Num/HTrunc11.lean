import EquivLean.Modernize.Cbstm03a.Java.Num.NumLemmas

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple

namespace EquivLean.Modernize.Cbstm03a.Java

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem trunc11_vc : MethodVC Gen.prog (fun _ => none) 0 trunc11Ref trunc11Spec [] 40 := by
  jverify [trunc11Spec]
  · exact trunc11_neg _ ‹_› ‹_›
  · exact trunc11_pos _ ‹_›

end EquivLean.Modernize.Cbstm03a.Java

#print axioms EquivLean.Modernize.Cbstm03a.Java.trunc11_vc
