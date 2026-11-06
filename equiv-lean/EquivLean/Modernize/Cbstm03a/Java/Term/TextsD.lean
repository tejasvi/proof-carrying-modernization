import EquivLean.Modernize.Cbstm03a.Java.Term.TextsA

/-!
# CBSTM03A → Java, termination: the record text `acctText`

As `CbATerm.TextsA`: field reads, calls of `fix` (`fixGSpecT`), `zu`, `zs`, `spaces`, one concatenation.
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows)

namespace EquivLean.Modernize.Cbstm03a.Java.Term

abbrev acctSs : List String := ["acctActiveStatus", "acctOpenDate", "acctExpiraionDate", "acctReissueDate",
  "acctAddrZip", "acctGroupId", "filler1"]
abbrev acctLs : List String := ["acctId", "acctCurrBal", "acctCreditLimit", "acctCashCreditLimit",
  "acctCurrCycCredit", "acctCurrCycDebit"]
abbrev acctTextRef : MethodRef := Gen.Cbstm03a.«acctText(Cbstm03a$AccountRecord)».ref
def acctTextSig : MethodSig := ⟨"Cbstm03a", .cls "java.lang.String", "acctText", [.cls "Cbstm03a$AccountRecord"]⟩

set_option maxRecDepth 8000 in
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem acctText_vcT : MethodVC Gen.prog textCalleesT.env 0 acctTextRef
    (textSpecT "Cbstm03a$AccountRecord" acctSs acctLs 300) [] 60 := by
  set_option jimple.modelContracts true in
  jverify [ite_nat_ne, findHandler, textSpecT, RecArg, List.forall_mem_cons, List.not_mem_nil, false_implies,
    implies_true, and_true, textCalleesT, fixSig, fixGSpecT, zuSig, zuSpecT, zsSig, zsSpecT, spacesSig, spacesSpecT,
    StrResL, GrowsT, Grows]
  all_goals jvc [ite_nat_ne, findHandler, textSpecT, RecArg, List.forall_mem_cons, List.not_mem_nil, false_implies,
    implies_true, and_true, textCalleesT, fixSig, fixGSpecT, zuSig, zuSpecT, zsSig, zsSpecT, spacesSig, spacesSpecT,
    StrResL, GrowsT, Grows]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem acctText_thinT : ThinVC Gen.prog textCalleesT.env 0 acctTextRef
    (textSpecT "Cbstm03a$AccountRecord" acctSs acctLs 300) [] (fun _ _ _ _ _ => 0) 60 := by
  set_option jimple.modelContracts true in
  jthin [ite_nat_ne, findHandler, textSpecT, RecArg, List.forall_mem_cons, List.not_mem_nil, false_implies,
    implies_true, and_true, textCalleesT, fixSig, fixGSpecT, zuSig, zuSpecT, zsSig, zsSpecT, spacesSig, spacesSpecT,
    StrResL, GrowsT, Grows]
  all_goals jvc [ite_nat_ne, findHandler, textSpecT, RecArg, List.forall_mem_cons, List.not_mem_nil, false_implies,
    implies_true, and_true, textCalleesT, fixSig, fixGSpecT, zuSig, zuSpecT, zsSig, zsSpecT, spacesSig, spacesSpecT,
    StrResL, GrowsT, Grows]

theorem acctText_termT : ∀ args σ, (textSpecT "Cbstm03a$AccountRecord" acctSs acctLs 300).pre args σ →
    MTerm Gen.prog acctTextRef args σ :=
  mterm_of_thin textCalleesT_ok textCalleesT_term acctText_vcT acctText_thinT
theorem acctText_satT : Sat Gen.prog acctTextRef (textSpecT "Cbstm03a$AccountRecord" acctSs acctLs 300) :=
  sat_of_table textCalleesT_ok acctText_vcT

set_option maxHeartbeats 4000000 in
theorem acctText_ctermT : ContractTerm Gen.prog acctTextSig (textSpecT "Cbstm03a$AccountRecord" acctSs acctLs 300) := by
  jcontract_term [acctText_termT]
set_option maxHeartbeats 4000000 in
theorem acctText_okT : ContractOK Gen.prog acctTextSig (textSpecT "Cbstm03a$AccountRecord" acctSs acctLs 300) := by
  jcontract_ok [acctText_satT]

end EquivLean.Modernize.Cbstm03a.Java.Term

#print axioms EquivLean.Modernize.Cbstm03a.Java.Term.acctText_ctermT
#print axioms EquivLean.Modernize.Cbstm03a.Java.Term.acctText_okT
