import EquivLean.Modernize.Cbstm03a.Java.Term.Pow10
import EquivLean.Modernize.Cbstm03a.Java.Term.ZeroPad

/-!
# CBSTM03A → Java, termination: `zu`, `zs`, `fmtCurrBal`

No loops: calls of `pow10` (`pow10SpecT`) and `zeroPad` (`zeroPadSpecT`). `a % pow10(n)` may divide by zero as far
as the frame contracts know, so these contracts allow exceptions (with `GrowsT`). Frame contracts (`Cbstm03a`
initialized; `zu`: `n ≥ 0`, `zs`: `n ≥ 1`): a new string of length `n` (`fmtCurrBal`: 13), `GrowsT`.
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows)

namespace EquivLean.Modernize.Cbstm03a.Java.Term

def zuSpecT : Spec := Spec.of
  (fun args σ => ∃ (v : I64) (n : I32), args = [.long v, .int n] ∧ 0 ≤ n.toInt ∧ InitA σ)
  (fun args σ r σ' => ∀ (v : I64) (n : I32), args = [.long v, .int n] →
    StrResL σ r σ' n.toInt.toNat ∧ GrowsT σ σ')
  (fun _ σ e σ' => GrowsT σ σ' ∧ ∃ o, σ'.heap e = some o)

def zsSpecT : Spec := Spec.of
  (fun args σ => ∃ (v : I64) (n : I32), args = [.long v, .int n] ∧ 1 ≤ n.toInt ∧ InitA σ)
  (fun args σ r σ' => ∀ (v : I64) (n : I32), args = [.long v, .int n] →
    StrResL σ r σ' n.toInt.toNat ∧ GrowsT σ σ')
  (fun _ σ e σ' => GrowsT σ σ' ∧ ∃ o, σ'.heap e = some o)

def fmtCurrBalSpecT : Spec := Spec.of (fun args σ => ∃ v : I64, args = [.long v] ∧ InitA σ)
  (fun _ σ r σ' => StrResL σ r σ' 13 ∧ GrowsT σ σ')

def zuCalleesT : Contracts := [(pow10Sig, pow10SpecT), (zeroPadSig, zeroPadSpecT)]

theorem zuCalleesT_ok : ∀ p ∈ zuCalleesT, ContractOK Gen.prog p.1 p.2 := by
  simp only [zuCalleesT, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  exact ⟨pow10_okT, zeroPad_okT⟩
theorem zuCalleesT_term : ∀ p ∈ zuCalleesT, ContractTerm Gen.prog p.1 p.2 := by
  simp only [zuCalleesT, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  exact ⟨pow10_ctermT, zeroPad_ctermT⟩

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem zu_vcT : MethodVC Gen.prog zuCalleesT.env 0 zuRef zuSpecT [] 30 := by
  jverify [ite_nat_ne, findHandler, zuSpecT, zuCalleesT, pow10Sig, pow10SpecT, zeroPadSig, zeroPadSpecT, StrResL, GrowsT, Grows]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem zu_thinT : ThinVC Gen.prog zuCalleesT.env 0 zuRef zuSpecT [] (fun _ _ _ _ _ => 0) 30 := by
  jthin [ite_nat_ne, findHandler, zuSpecT, zuCalleesT, pow10Sig, pow10SpecT, zeroPadSig, zeroPadSpecT, StrResL, GrowsT, Grows]

theorem zu_termT : ∀ args σ, zuSpecT.pre args σ → MTerm Gen.prog zuRef args σ :=
  mterm_of_thin zuCalleesT_ok zuCalleesT_term zu_vcT zu_thinT
theorem zu_satT : Sat Gen.prog zuRef zuSpecT := sat_of_table zuCalleesT_ok zu_vcT

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem zs_vcT : MethodVC Gen.prog zuCalleesT.env 0 zsRef zsSpecT [] 60 := by
  set_option jimple.modelContracts true in
  jverify [ite_nat_ne, findHandler, zsSpecT, zuCalleesT, pow10Sig, pow10SpecT, zeroPadSig, zeroPadSpecT, StrResL, GrowsT, Grows]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem zs_thinT : ThinVC Gen.prog zuCalleesT.env 0 zsRef zsSpecT [] (fun _ _ _ _ _ => 0) 60 := by
  set_option jimple.modelContracts true in
  jthin [ite_nat_ne, findHandler, zsSpecT, zuCalleesT, pow10Sig, pow10SpecT, zeroPadSig, zeroPadSpecT, StrResL, GrowsT, Grows]

theorem zs_termT : ∀ args σ, zsSpecT.pre args σ → MTerm Gen.prog zsRef args σ :=
  mterm_of_thin zuCalleesT_ok zuCalleesT_term zs_vcT zs_thinT
theorem zs_satT : Sat Gen.prog zsRef zsSpecT := sat_of_table zuCalleesT_ok zs_vcT

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem fmtCurrBal_vcT : MethodVC Gen.prog zuCalleesT.env 0 fmtCurrBalRef fmtCurrBalSpecT [] 40 := by
  set_option jimple.modelContracts true in
  jverify [ite_nat_ne, fmtCurrBalSpecT, zuCalleesT, pow10Sig, pow10SpecT, zeroPadSig, zeroPadSpecT, StrResL,
    GrowsT, Grows]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem fmtCurrBal_thinT :
    ThinVC Gen.prog zuCalleesT.env 0 fmtCurrBalRef fmtCurrBalSpecT [] (fun _ _ _ _ _ => 0) 40 := by
  set_option jimple.modelContracts true in
  jthin [ite_nat_ne, fmtCurrBalSpecT, zuCalleesT, pow10Sig, pow10SpecT, zeroPadSig, zeroPadSpecT, StrResL,
    GrowsT, Grows]

theorem fmtCurrBal_termT : ∀ args σ, fmtCurrBalSpecT.pre args σ → MTerm Gen.prog fmtCurrBalRef args σ :=
  mterm_of_thin zuCalleesT_ok zuCalleesT_term fmtCurrBal_vcT fmtCurrBal_thinT
theorem fmtCurrBal_satT : Sat Gen.prog fmtCurrBalRef fmtCurrBalSpecT := sat_of_table zuCalleesT_ok fmtCurrBal_vcT

set_option maxHeartbeats 4000000 in
theorem zu_ctermT : ContractTerm Gen.prog zuSig zuSpecT := by jcontract_term [zu_termT]
set_option maxHeartbeats 4000000 in
theorem zu_okT : ContractOK Gen.prog zuSig zuSpecT := by jcontract_ok [zu_satT]
set_option maxHeartbeats 4000000 in
theorem zs_ctermT : ContractTerm Gen.prog zsSig zsSpecT := by jcontract_term [zs_termT]
set_option maxHeartbeats 4000000 in
theorem zs_okT : ContractOK Gen.prog zsSig zsSpecT := by jcontract_ok [zs_satT]
set_option maxHeartbeats 4000000 in
theorem fmtCurrBal_ctermT : ContractTerm Gen.prog fmtCurrBalSig fmtCurrBalSpecT := by
  jcontract_term [fmtCurrBal_termT]
set_option maxHeartbeats 4000000 in
theorem fmtCurrBal_okT : ContractOK Gen.prog fmtCurrBalSig fmtCurrBalSpecT := by jcontract_ok [fmtCurrBal_satT]

end EquivLean.Modernize.Cbstm03a.Java.Term

#print axioms EquivLean.Modernize.Cbstm03a.Java.Term.zu_ctermT
#print axioms EquivLean.Modernize.Cbstm03a.Java.Term.zu_okT
#print axioms EquivLean.Modernize.Cbstm03a.Java.Term.zs_ctermT
#print axioms EquivLean.Modernize.Cbstm03a.Java.Term.zs_okT
#print axioms EquivLean.Modernize.Cbstm03a.Java.Term.fmtCurrBal_ctermT
#print axioms EquivLean.Modernize.Cbstm03a.Java.Term.fmtCurrBal_okT
