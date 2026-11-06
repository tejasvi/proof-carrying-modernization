import EquivLean.Modernize.Cbstm03a.Java.Num.FmtLemmas

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows zpadStr digitChar zpadStr_length)

namespace EquivLean.Modernize.Cbstm03a.Java

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
set_option jimple.modelContracts true in
theorem fmtCurrBal_vc : MethodVC Gen.prog fmtCallees.env 0 fmtCurrBalRef fmtCurrBalSpec [] 60 := by
  jverify [fmtCurrBalSpec, fmtCallees, zeroPadSig, zeroPadSpec, spacesSig, spacesSpecI, Grows, zpadStr_length]
  · exact currStr_neg _ ‹_› ‹_›
  · exact currStr_pos _ ‹_›

end EquivLean.Modernize.Cbstm03a.Java

#print axioms EquivLean.Modernize.Cbstm03a.Java.fmtCurrBal_vc
