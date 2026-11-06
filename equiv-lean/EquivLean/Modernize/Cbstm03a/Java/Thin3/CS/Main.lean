import EquivLean.Modernize.Cbstm03a.Java.Thin3.CS.Chain2

/-!
# CBSTM03A → Java: **`createStatement` terminates** for its contract

The termination VC of `createStatement` (straight-line: no cut points) against the callee table `csT` (`stmt`/`html`
on the heap, cbA-term2's `stmtSpecH`/`htmlSpecH`, the other callees by the frozen interfaces) is the entry path
`Thin3.p0`. With the callees' validity and termination (`stmtSpecH`/`htmlSpecH`'s from `fix`'s), `TermVC.mterm`
gives termination of every call satisfying `createStatementSpec`'s precondition.
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple

namespace EquivLean.Modernize.Cbstm03a.Java.Thin3

open EquivLean.Modernize.Cbstm03a.Java

set_option maxRecDepth 20000 in
theorem cs_tvc : TermVC Gen.prog csT.env (fun _ => 0) 1 0 createStatementRef createStatementSpec [] (FT 0) := by
  refine ⟨csBody, rfl, fun args σ0 hpre => ⟨?_, fun p hp => absurd hp (List.not_mem_nil)⟩⟩
  show bodyWP Gen.prog (callWPT Gen.prog (csT.env.below (fun _ => 0) 1) 0) csBody [] (fun _ => True) (FT 0) 0
    (Frame.init true args) σ0
  rw [csT_below]
  exact wpt_elim (p0 args σ0 hpre)

theorem csT_ok (hfix : ContractOK Gen.prog fixSig fixSpecI) (hsp : ContractOK Gen.prog spacesSig spacesSpecI)
    (hrep : ContractOK Gen.prog repeatSig repeatSpec) (happ : ContractOK Gen.prog appSig appSpec)
    (hpara : ContractOK Gen.prog paraSig paraSpec) (hstar : ContractOK Gen.prog starSig starSpec)
    (hfmt : ContractOK Gen.prog fmtCurrBalSig fmtCurrBalSpec)
    (hdz : ContractOK Gen.prog decodeZonedSig decodeZonedSpec) :
    ∀ p ∈ csT, ContractOK Gen.prog p.1 p.2 := by
  simp only [csT, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  exact ⟨stmtH_ok hfix, htmlH_ok hfix, hfix, hsp, hrep, happ, hpara, hstar, hfmt, hdz⟩

theorem csT_term (hfix : ContractOK Gen.prog fixSig fixSpecI) (hfixT : ContractTerm Gen.prog fixSig fixSpecI)
    (hspT : ContractTerm Gen.prog spacesSig spacesSpecI) (hrepT : ContractTerm Gen.prog repeatSig repeatSpec)
    (happT : ContractTerm Gen.prog appSig appSpec) (hparaT : ContractTerm Gen.prog paraSig paraSpec)
    (hstarT : ContractTerm Gen.prog starSig starSpec)
    (hfmtT : ContractTerm Gen.prog fmtCurrBalSig fmtCurrBalSpec)
    (hdzT : ContractTerm Gen.prog decodeZonedSig decodeZonedSpec) :
    ∀ p ∈ csT, ContractTerm Gen.prog p.1 p.2 := by
  simp only [csT, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  exact ⟨stmtH_cterm hfix hfixT, htmlH_cterm hfix hfixT, hfixT, hspT, hrepT, happT, hparaT, hstarT, hfmtT, hdzT⟩

end EquivLean.Modernize.Cbstm03a.Java.Thin3

namespace EquivLean.Modernize.Cbstm03a.Java

open Thin3

/-- **`createStatement` terminates** for its contract, given the validity and termination of the contracts of its
callees in `Iface0`/`Iface1` (`stmt` and `html` are answered by heap-level contracts proved from `fix`'s). -/
theorem createStatement_cterm
    (hfix : ContractOK Gen.prog fixSig fixSpecI) (hfixT : ContractTerm Gen.prog fixSig fixSpecI)
    (hsp : ContractOK Gen.prog spacesSig spacesSpecI) (hspT : ContractTerm Gen.prog spacesSig spacesSpecI)
    (hrep : ContractOK Gen.prog repeatSig repeatSpec) (hrepT : ContractTerm Gen.prog repeatSig repeatSpec)
    (happ : ContractOK Gen.prog appSig appSpec) (happT : ContractTerm Gen.prog appSig appSpec)
    (hpara : ContractOK Gen.prog paraSig paraSpec) (hparaT : ContractTerm Gen.prog paraSig paraSpec)
    (hstar : ContractOK Gen.prog starSig starSpec) (hstarT : ContractTerm Gen.prog starSig starSpec)
    (hfmt : ContractOK Gen.prog fmtCurrBalSig fmtCurrBalSpec)
    (hfmtT : ContractTerm Gen.prog fmtCurrBalSig fmtCurrBalSpec)
    (hdz : ContractOK Gen.prog decodeZonedSig decodeZonedSpec)
    (hdzT : ContractTerm Gen.prog decodeZonedSig decodeZonedSpec) :
    ContractTerm Gen.prog createStatementSig createStatementSpec := by
  have ht : ∀ args σ, createStatementSpec.pre args σ → MTerm Gen.prog createStatementRef args σ :=
    TermVC.mterm (Contracts.valid_of_ok (csT_ok hfix hsp hrep happ hpara hstar hfmt hdz))
      (Contracts.term_of_ok (csT_term hfix hfixT hspT hrepT happT hparaT hstarT hfmtT hdzT) _ _) cs_tvc
  jcontract_term [ht]

end EquivLean.Modernize.Cbstm03a.Java

#print axioms EquivLean.Modernize.Cbstm03a.Java.createStatement_cterm
