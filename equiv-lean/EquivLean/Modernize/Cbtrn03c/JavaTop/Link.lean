import EquivLean.Modernize.Cbtrn03c.JavaTop.PeVC
import EquivLean.Modernize.Cbtrn03c.JavaTop.PdVC
import EquivLean.Modernize.Cbtrn03c.JavaTop.RunVC
import EquivLean.Modernize.Cbtrn03c.JavaProof

set_option jimple.modelContracts true

/-!
# CBTRN03C → Java: `run`'s contract and the generated statement, from the leaf contracts

The top layer (`run`, `processDetail`, `processEnd`) is proved here; the leaves are the helpers'
contracts (`T3X/Cal*.lean`) and the working-state writers' (cir-repin, on `shared/WsRel.lean`).
-/

open Jimple EquivLean.Cobol.Rec EquivLean.Jimple

namespace EquivLean.Modernize.Cbtrn03c.Java.Top

theorem pd_ok (hV : Valid Gen.prog pdCallees.env) :
    ContractOK Gen.prog processDetailSig processDetailSpecM := by
  jcontract_ok [pd_sat hV]

theorem pe_ok (hV : Valid Gen.prog peCallees.env) :
    ContractOK Gen.prog processEndSig processEndSpecM := by
  jcontract_ok [pe_sat hV]

/-- **CBTRN03C → Java: `run` satisfies `runSpec`**, given the leaf contracts. -/
theorem run_sat_of_leaves
    (hzon : ContractOK Gen.prog zonedSig zonedSpecT) (hadd : ContractOK Gen.prog add11Sig add11SpecT)
    (hpt : ContractOK Gen.prog writePageTotalsSig writePageTotalsSpecM)
    (hgt : ContractOK Gen.prog writeGrandTotalsSig writeGrandTotalsSpecM)
    (hat : ContractOK Gen.prog writeAccountTotalsSig writeAccountTotalsSpecM)
    (hwtr : ContractOK Gen.prog writeTransactionReportSig writeTransactionReportSpecM)
    (htxt : ContractOK Gen.prog tranRecordTextSig tranRecordTextSpecT)
    (hfx : ContractOK Gen.prog findXrefSig findXrefSpecT)
    (hio : ContractOK Gen.prog ioStatusLineSig ioStatusLineSpecT)
    (hft : ContractOK Gen.prog findTranTypeSig findTranTypeSpecT)
    (hfc : ContractOK Gen.prog findTranCatSig findTranCatSpecT)
    (hdig : ContractOK Gen.prog digitsSig digitsSpecT)
    (hsp : ContractOK Gen.prog spacesSig spacesSpecT)
    (hbl : ContractOK Gen.prog blankTranSig blankTranSpecT)
    (hcmp : ContractOK Gen.prog compareEbcdicSig compareEbcdicSpecC) :
    Sat Gen.prog runRef runSpec := by
  have hVe : Valid Gen.prog peCallees.env := by
    apply Contracts.valid_of_ok
    simp only [peCallees, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
      and_true]
    exact ⟨hzon, hadd, hpt, hgt⟩
  have hVd : Valid Gen.prog pdCallees.env := by
    apply Contracts.valid_of_ok
    simp only [pdCallees, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
      and_true]
    exact ⟨htxt, hat, hfx, hio, hft, hfc, hdig, hwtr⟩
  have hVr : Valid Gen.prog runCallees.env := by
    apply Contracts.valid_of_ok
    simp only [runCallees, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
      and_true]
    exact ⟨hsp, hbl, hcmp, pd_ok hVd, pe_ok hVe⟩
  exact run_sat hVr

end EquivLean.Modernize.Cbtrn03c.Java.Top

#print axioms EquivLean.Modernize.Cbtrn03c.Java.Top.run_sat_of_leaves
