import EquivLean.Modernize.Cbstm03a.Java.Num.HZeroPad
import EquivLean.Modernize.Cbstm03a.Java.Num.HRepeat
import EquivLean.Modernize.Cbstm03a.Java.Num.HSpaces
import EquivLean.Modernize.Cbstm03a.Java.Num.HFix
import EquivLean.Modernize.Cbstm03a.Java.Num.HPow10
import EquivLean.Modernize.Cbstm03a.Java.Num.HTrunc11
import EquivLean.Modernize.Cbstm03a.Java.Num.HZu
import EquivLean.Modernize.Cbstm03a.Java.Num.HZs
import EquivLean.Modernize.Cbstm03a.Java.Num.HFmtCurrBal
import EquivLean.Modernize.Cbstm03a.Java.Num.HFmtZ
import EquivLean.Modernize.Cbstm03a.Java.Num.HEbc
import EquivLean.Modernize.Cbstm03a.Java.Num.HEbcCompare
import EquivLean.Modernize.Cbstm03a.Java.Num.HApp
import EquivLean.Modernize.Cbstm03a.Java.Num.HPara2
import EquivLean.Modernize.Cbstm03a.Java.Num.HStar

/-!
# CBSTM03A → Java: the helpers satisfy their contracts

Each `<m>_sat : Sat Gen.prog <m>Ref <spec>` is unconditional: a leaf method's verification conditions give it
directly (`MethodVC.sat`); a method verified against callee contracts is linked with the callees' `Sat`s
(`Contracts.valid_of_ok`, one `jcontract_ok` per table entry, `MethodVC.sat_of_valid`). `para` and `star` are linked
through `paraCalleesB` (`app` with `appSpecB`); `app` satisfies both `appSpec` and `appSpecB`.
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple

namespace EquivLean.Modernize.Cbstm03a.Java

theorem zeroPad_sat : Sat Gen.prog zeroPadRef zeroPadSpec := MethodVC.sat zeroPad_vc
theorem repeat_sat : Sat Gen.prog repeatRef repeatSpec := MethodVC.sat repeat_vc
theorem pow10_sat : Sat Gen.prog pow10Ref pow10Spec := MethodVC.sat pow10_vc
theorem trunc11_sat : Sat Gen.prog trunc11Ref trunc11Spec := MethodVC.sat trunc11_vc
theorem ebc_sat : Sat Gen.prog ebcRef ebcSpec := MethodVC.sat ebc_vc
theorem app_sat : Sat Gen.prog appRef appSpec := MethodVC.sat app_vc
theorem appB_sat : Sat Gen.prog appRef appSpecB := MethodVC.sat app_vcB

theorem spacesCallees_valid : Valid Gen.prog spacesCallees.env := Contracts.valid_of_ok (by
  intro p hp
  simp only [spacesCallees, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl
  exact (by jcontract_ok [repeat_sat]))

theorem spaces_sat : Sat Gen.prog spacesRef spacesSpecI := MethodVC.sat_of_valid spacesCallees_valid spaces_vc

theorem fixCallees_valid : Valid Gen.prog fixCallees.env := Contracts.valid_of_ok (by
  intro p hp
  simp only [fixCallees, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl
  exact (by jcontract_ok [spaces_sat]))

theorem fix_sat : Sat Gen.prog fixRef fixSpecI := MethodVC.sat_of_valid fixCallees_valid fix_vc

theorem zuCallees_valid : Valid Gen.prog zuCallees.env := Contracts.valid_of_ok (by
  intro p hp
  simp only [zuCallees, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact (by jcontract_ok [pow10_sat])
  · exact (by jcontract_ok [zeroPad_sat]))

theorem zu_sat : Sat Gen.prog zuRef zuSpec := MethodVC.sat_of_valid zuCallees_valid zu_vc
theorem zs_sat : Sat Gen.prog zsRef zsSpec := MethodVC.sat_of_valid zuCallees_valid zs_vc

theorem fmtCallees_valid : Valid Gen.prog fmtCallees.env := Contracts.valid_of_ok (by
  intro p hp
  simp only [fmtCallees, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact (by jcontract_ok [zeroPad_sat])
  · exact (by jcontract_ok [spaces_sat]))

theorem fmtCurrBal_sat : Sat Gen.prog fmtCurrBalRef fmtCurrBalSpec := MethodVC.sat_of_valid fmtCallees_valid fmtCurrBal_vc
theorem fmtZ_sat : Sat Gen.prog fmtZRef fmtZSpec := MethodVC.sat_of_valid fmtCallees_valid fmtZ_vc

theorem ebcCompareCallees_valid : Valid Gen.prog ebcCompareCallees.env := Contracts.valid_of_ok (by
  intro p hp
  simp only [ebcCompareCallees, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl
  exact (by jcontract_ok [ebc_sat]))

theorem ebcCompare_sat : Sat Gen.prog ebcCompareRef ebcCompareSpec :=
  MethodVC.sat_of_valid ebcCompareCallees_valid ebcCompare_vc

theorem paraCalleesB_valid : Valid Gen.prog paraCalleesB.env := Contracts.valid_of_ok (by
  intro p hp
  simp only [paraCalleesB, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact (by jcontract_ok [appB_sat])
  · exact (by jcontract_ok [fix_sat]))

theorem para_sat : Sat Gen.prog paraRef paraSpec := MethodVC.sat_of_valid paraCalleesB_valid para_vc
theorem star_sat : Sat Gen.prog starRef starSpec := MethodVC.sat_of_valid paraCalleesB_valid star_vc

end EquivLean.Modernize.Cbstm03a.Java

#print axioms EquivLean.Modernize.Cbstm03a.Java.zeroPad_sat
#print axioms EquivLean.Modernize.Cbstm03a.Java.repeat_sat
#print axioms EquivLean.Modernize.Cbstm03a.Java.pow10_sat
#print axioms EquivLean.Modernize.Cbstm03a.Java.trunc11_sat
#print axioms EquivLean.Modernize.Cbstm03a.Java.ebc_sat
#print axioms EquivLean.Modernize.Cbstm03a.Java.app_sat
#print axioms EquivLean.Modernize.Cbstm03a.Java.appB_sat
#print axioms EquivLean.Modernize.Cbstm03a.Java.spaces_sat
#print axioms EquivLean.Modernize.Cbstm03a.Java.fix_sat
#print axioms EquivLean.Modernize.Cbstm03a.Java.zu_sat
#print axioms EquivLean.Modernize.Cbstm03a.Java.zs_sat
#print axioms EquivLean.Modernize.Cbstm03a.Java.fmtCurrBal_sat
#print axioms EquivLean.Modernize.Cbstm03a.Java.fmtZ_sat
#print axioms EquivLean.Modernize.Cbstm03a.Java.ebcCompare_sat
#print axioms EquivLean.Modernize.Cbstm03a.Java.para_sat
#print axioms EquivLean.Modernize.Cbstm03a.Java.star_sat
