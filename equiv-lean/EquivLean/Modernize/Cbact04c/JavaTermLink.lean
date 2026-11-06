-- Termination package by JimpleLean's session: TermPk/Cbact04c/JavaTermLink.lean (sha256 cae9b488b4561d79...); only the module root renamed.
import EquivLean.Modernize.Cbact04c.JavaTermHelpers
import EquivLean.Modernize.Cbact04c.JavaTermCtors
import EquivLean.Modernize.Cbact04c.JavaTermSearch
import EquivLean.Modernize.Cbact04c.JavaRunOks

/-!
# CBACT04C → Java, termination: the callees of `run` terminate

Each helper terminates (`*_term`: its `MethodVC` with its thin VC, `Jimple.TermVC.of_thin`, the
callees' contracts valid as in `JavaRunOks` and terminating); the searches for each choice of
their ghosts (`*_termG`, the ghosts taken from the precondition as `findAcct_sat` does). The
contracts as `run` uses them (`runC`: the `*F` variants) have the preconditions of the helpers'
contracts (`ContractTerm.mono`), so `runC_term`: every contract of `runC` terminates.
-/

open Jimple

namespace EquivLean.Modernize.Cbact04c.Java

/-! ## The arithmetic and string helpers -/

theorem pow10_term : ∀ args σ, pow10Spec.pre args σ → MTerm Gen.prog pow10Ref args σ :=
  TermVC.mterm (r := 1) (Jimple.valid_none _) (contractTerm_none _ _)
    (TermVC.of_thin (SpecEnv.below_const _ _ (by decide)) pow10_vc pow10_thin)

set_option maxHeartbeats 0 in
theorem pow10_cterm : ContractTerm Gen.prog pow10Sig pow10Spec := by jcontract_term [pow10_term]

theorem truncC_term :
    ∀ sig S, (truncC.env.below (fun _ => 0) 1) sig = some S → ContractTerm Gen.prog sig S :=
  Contracts.term_of_ok (by
    simp only [truncC, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
      and_true]
    exact pow10_cterm) _ _

theorem fmtUC_term :
    ∀ sig S, (fmtUC.env.below (fun _ => 0) 1) sig = some S → ContractTerm Gen.prog sig S :=
  Contracts.term_of_ok (by
    simp only [fmtUC, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
      and_true]
    exact pow10_cterm) _ _

theorem trunc_term : ∀ args σ, truncSpec.pre args σ → MTerm Gen.prog truncRef args σ :=
  TermVC.mterm (rank := fun _ => 0) (r := 1) pow10C_valid truncC_term
    (TermVC.of_thin (SpecEnv.below_const _ _ (by decide)) trunc_vc trunc_thin)

/-- (`fmtUC` and `truncC` are the same table: `pow10C_valid` is `fmtU`'s too, as in `fmtU_sat`.) -/
theorem fmtU_term : ∀ args σ, fmtUSpec.pre args σ → MTerm Gen.prog fmtURef args σ :=
  TermVC.mterm (rank := fun _ => 0) (r := 1) pow10C_valid fmtUC_term
    (TermVC.of_thin (SpecEnv.below_const _ _ (by decide)) fmtU_vc fmtU_thin)

set_option maxHeartbeats 0 in
theorem trunc_cterm : ContractTerm Gen.prog truncSig truncSpec := by jcontract_term [trunc_term]
set_option maxHeartbeats 0 in
theorem fmtU_cterm : ContractTerm Gen.prog fmtUSig fmtUSpec := by jcontract_term [fmtU_term]

theorem fmtZonedC_term :
    ∀ sig S, (fmtZonedC.env.below (fun _ => 0) 1) sig = some S → ContractTerm Gen.prog sig S :=
  Contracts.term_of_ok (by
    simp only [fmtZonedC, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
      and_true]
    exact fmtU_cterm) _ _

theorem fmtZoned_term : ∀ args σ, fmtZonedSpec.pre args σ → MTerm Gen.prog fmtZonedRef args σ :=
  TermVC.mterm (rank := fun _ => 0) (r := 1) fmtUC_valid fmtZonedC_term
    (TermVC.of_thin (SpecEnv.below_const _ _ (by decide)) fmtZoned_vc fmtZoned_thin)

set_option maxHeartbeats 0 in
theorem fmtZoned_cterm : ContractTerm Gen.prog fmtZonedSig fmtZonedSpec := by
  jcontract_term [fmtZoned_term]

theorem displayTcbC_term :
    ∀ sig S, (displayTcbC.env.below (fun _ => 0) 1) sig = some S → ContractTerm Gen.prog sig S :=
  Contracts.term_of_ok (by
    simp only [displayTcbC, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
      and_true]
    exact ⟨fmtU_cterm, fmtZoned_cterm⟩) _ _

theorem displayTcb_term : ∀ args σ, displayTcbSpec.pre args σ → MTerm Gen.prog displayTcbRef args σ :=
  TermVC.mterm (rank := fun _ => 0) (r := 1) displayTcbC_valid displayTcbC_term
    (TermVC.of_thin (SpecEnv.below_const _ _ (by decide)) displayTcb_vc displayTcb_thin)

set_option maxHeartbeats 0 in
theorem displayTcb_cterm : ContractTerm Gen.prog displayTcbSig displayTcbSpec := by
  jcontract_term [displayTcb_term]

theorem spaces_term : ∀ args σ, spacesSpec.pre args σ → MTerm Gen.prog spacesRef args σ :=
  TermVC.mterm (r := 1) (Jimple.valid_none _) (contractTerm_none _ _)
    (TermVC.of_thin (SpecEnv.below_const _ _ (by decide)) spaces_vc spaces_thin)

theorem fixLen_term : ∀ args σ, fixLenSpec.pre args σ → MTerm Gen.prog fixLenRef args σ :=
  TermVC.mterm (r := 1) (Jimple.valid_none _) (contractTerm_none _ _)
    (TermVC.of_thin (SpecEnv.below_const _ _ (by decide)) fixLen_vc fixLen_thin)

set_option maxHeartbeats 0 in
theorem spaces_cterm : ContractTerm Gen.prog spacesSig spacesSpec := by jcontract_term [spaces_term]
set_option maxHeartbeats 0 in
theorem fixLen_cterm : ContractTerm Gen.prog fixLenSig fixLenSpec := by jcontract_term [fixLen_term]

/-! ## The searches (ghosts from the precondition, as in `findAcct_sat`, `findDisc_sat`) -/

theorem findAcct_termG (a : Addr) (key : I64) (et : JType) (xs : List Value) :
    ∀ args σ, (findAcctSpecG a key et xs).pre args σ → MTerm Gen.prog findAcctRef args σ :=
  TermVC.mterm (r := 1) (Jimple.valid_none _) (contractTerm_none _ _)
    (TermVC.of_thin (SpecEnv.below_const _ _ (by decide)) (findAcct_vc a key et xs)
      (findAcct_thin a key et xs))

theorem findAcct_term : ∀ args σ, findAcctSpec.pre args σ → MTerm Gen.prog findAcctRef args σ := by
  intro args σ hpre
  obtain ⟨a, key, et, xs, hp⟩ := hpre
  exact findAcct_termG a key et xs args σ hp

theorem findDisc_termG (a : Addr) (len : I32) (gs ts : Addr) (g t : JStr) (cat : I64) (et : JType)
    (xs : List Value) :
    ∀ args σ, (findDiscSpecG a len gs ts g t cat et xs).pre args σ → MTerm Gen.prog findDiscRef args σ :=
  TermVC.mterm (r := 1) (Jimple.valid_none _) (contractTerm_none _ _)
    (TermVC.of_thin (SpecEnv.below_const _ _ (by decide)) (findDisc_vc a len gs ts g t cat et xs)
      (findDisc_thin a len gs ts g t cat et xs))

theorem findDisc_term : ∀ args σ, findDiscSpec.pre args σ → MTerm Gen.prog findDiscRef args σ := by
  intro args σ hpre
  obtain ⟨a, len, gs, ts, g, t, cat, et, xs, hp⟩ := hpre
  exact findDisc_termG a len gs ts g t cat et xs args σ hp

set_option maxHeartbeats 0 in
theorem findAcct_cterm : ContractTerm Gen.prog findAcctSig findAcctSpec := by
  jcontract_term [findAcct_term]
set_option maxHeartbeats 0 in
theorem findDisc_cterm : ContractTerm Gen.prog findDiscSig findDiscSpec := by
  jcontract_term [findDisc_term]

/-! ## The record constructors and copies -/

theorem ctorTC_term : ∀ args σ, ctorTCSpec.pre args σ → MTerm Gen.prog ctorTCRef args σ :=
  TermVC.mterm (r := 1) (Jimple.valid_none _) (contractTerm_none _ _)
    (TermVC.of_thin (SpecEnv.below_const _ _ (by decide)) ctorTC_vc ctorTC_thin)
theorem ctorXC_term : ∀ args σ, ctorXCSpec.pre args σ → MTerm Gen.prog ctorXCRef args σ :=
  TermVC.mterm (r := 1) (Jimple.valid_none _) (contractTerm_none _ _)
    (TermVC.of_thin (SpecEnv.below_const _ _ (by decide)) ctorXC_vc ctorXC_thin)
theorem ctorAC_term : ∀ args σ, ctorACSpec.pre args σ → MTerm Gen.prog ctorACRef args σ :=
  TermVC.mterm (r := 1) (Jimple.valid_none _) (contractTerm_none _ _)
    (TermVC.of_thin (SpecEnv.below_const _ _ (by decide)) ctorAC_vc ctorAC_thin)
theorem ctorDC_term : ∀ args σ, ctorDCSpec.pre args σ → MTerm Gen.prog ctorDCRef args σ :=
  TermVC.mterm (r := 1) (Jimple.valid_none _) (contractTerm_none _ _)
    (TermVC.of_thin (SpecEnv.below_const _ _ (by decide)) ctorDC_vc ctorDC_thin)
theorem ctorRC_term : ∀ args σ, ctorRCSpec.pre args σ → MTerm Gen.prog ctorRCRef args σ :=
  TermVC.mterm (r := 1) (Jimple.valid_none _) (contractTerm_none _ _)
    (TermVC.of_thin (SpecEnv.below_const _ _ (by decide)) ctorRC_vc ctorRC_thin)

/-- `jcontract_term` for a constructor: its call targets as `jcontract_term` finds them; the classes
    a virtual call of it could select (it is an instance method, which `jcontract_term` does not
    handle) enumerated as `jcontract_ok` does. -/
macro "ctor_contract_term " t:term : tactic => `(tactic| (
  refine ⟨?_, ?_⟩
  · intro m ht
    obtain ⟨hsel, hb⟩ := ht
    rcases hsel with h | h | ⟨hs, _⟩
    all_goals first
      | (have hn := congrArg MethodSig.name hs
         simp (config := { decide := true }) only [jground, clinitSig] at hn)
      | (simp (config := { decide := true }) only [jground, reduceCtorEq,
           Program.Target.jimple.injEq] at h
         try subst h
         try simp (config := { decide := true }) only [jground] at hb)
    all_goals exact $t
  · apply forall_progClass_of_mem
    simp (config := { decide := true }) only [jground, List.forall_mem_cons, List.not_mem_nil,
      false_implies, implies_true, and_true, true_implies]
    repeat' constructor
    all_goals exact vterm_of_jimple (by exact rfl) $t))

set_option maxHeartbeats 0 in
theorem ctorTC_cterm : ContractTerm Gen.prog ctorTCSig ctorTCSpec := by ctor_contract_term ctorTC_term
set_option maxHeartbeats 0 in
theorem ctorXC_cterm : ContractTerm Gen.prog ctorXCSig ctorXCSpec := by ctor_contract_term ctorXC_term
set_option maxHeartbeats 0 in
theorem ctorAC_cterm : ContractTerm Gen.prog ctorACSig ctorACSpec := by ctor_contract_term ctorAC_term
set_option maxHeartbeats 0 in
theorem ctorDC_cterm : ContractTerm Gen.prog ctorDCSig ctorDCSpec := by ctor_contract_term ctorDC_term
set_option maxHeartbeats 0 in
theorem ctorRC_cterm : ContractTerm Gen.prog ctorRCSig ctorRCSpec := by ctor_contract_term ctorRC_term

/-- A copy terminates when its constructor's contract does (`copy*C`, one contract each). -/
theorem copyC_term {sig : MethodSig} {S : Spec} (h : ContractTerm Gen.prog sig S) :
    ∀ sig' S', (Contracts.env [(sig, S)]).below (fun _ => 0) 1 sig' = some S' →
      ContractTerm Gen.prog sig' S' :=
  Contracts.term_of_ok (by
    simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
    exact h) _ _

theorem copyTcb_term :
    ∀ args σ, (copySpec "Cbact04c$TranCatBalRecord" keysTC).pre args σ → MTerm Gen.prog copyTcbRef args σ :=
  TermVC.mterm (rank := fun _ => 0) (r := 1) copyTcbC_valid (copyC_term ctorTC_cterm)
    (TermVC.of_thin (SpecEnv.below_const _ _ (by decide)) copyTcb_vc copyTcb_thin)
theorem copyXref_term :
    ∀ args σ, (copySpec "Cbact04c$CardXrefRecord" keysXC).pre args σ → MTerm Gen.prog copyXrefRef args σ :=
  TermVC.mterm (rank := fun _ => 0) (r := 1) copyXrefC_valid (copyC_term ctorXC_cterm)
    (TermVC.of_thin (SpecEnv.below_const _ _ (by decide)) copyXref_vc copyXref_thin)
theorem copyAcct_term :
    ∀ args σ, (copySpec "Cbact04c$AccountRecord" keysAC).pre args σ → MTerm Gen.prog copyAcctRef args σ :=
  TermVC.mterm (rank := fun _ => 0) (r := 1) copyAcctC_valid (copyC_term ctorAC_cterm)
    (TermVC.of_thin (SpecEnv.below_const _ _ (by decide)) copyAcct_vc copyAcct_thin)
theorem copyDis_term :
    ∀ args σ, (copySpec "Cbact04c$DisGroupRecord" keysDC).pre args σ → MTerm Gen.prog copyDisRef args σ :=
  TermVC.mterm (rank := fun _ => 0) (r := 1) copyDisC_valid (copyC_term ctorDC_cterm)
    (TermVC.of_thin (SpecEnv.below_const _ _ (by decide)) copyDis_vc copyDis_thin)
theorem copyTran_term :
    ∀ args σ, (copySpec "Cbact04c$TranRecord" keysRC).pre args σ → MTerm Gen.prog copyTranRef args σ :=
  TermVC.mterm (rank := fun _ => 0) (r := 1) copyTranC_valid (copyC_term ctorRC_cterm)
    (TermVC.of_thin (SpecEnv.below_const _ _ (by decide)) copyTran_vc copyTran_thin)

set_option maxHeartbeats 0 in
theorem copyTcb_cterm :
    ContractTerm Gen.prog copyTcbSig (copySpec "Cbact04c$TranCatBalRecord" keysTC) := by
  jcontract_term [copyTcb_term]
set_option maxHeartbeats 0 in
theorem copyXref_cterm :
    ContractTerm Gen.prog copyXrefSig (copySpec "Cbact04c$CardXrefRecord" keysXC) := by
  jcontract_term [copyXref_term]
set_option maxHeartbeats 0 in
theorem copyAcct_cterm :
    ContractTerm Gen.prog copyAcctSig (copySpec "Cbact04c$AccountRecord" keysAC) := by
  jcontract_term [copyAcct_term]
set_option maxHeartbeats 0 in
theorem copyDis_cterm :
    ContractTerm Gen.prog copyDisSig (copySpec "Cbact04c$DisGroupRecord" keysDC) := by
  jcontract_term [copyDis_term]
set_option maxHeartbeats 0 in
theorem copyTran_cterm :
    ContractTerm Gen.prog copyTranSig (copySpec "Cbact04c$TranRecord" keysRC) := by
  jcontract_term [copyTran_term]

/-! ## The contracts as `run` uses them (`CallSpecs`, `CtorF`: the same preconditions) -/

theorem fixLenF_cterm : ContractTerm Gen.prog fixLenSig fixLenF :=
  ContractTerm.mono fixLen_cterm fun _ _ h => h
theorem displayTcbF_cterm : ContractTerm Gen.prog displayTcbSig displayTcbF :=
  ContractTerm.mono displayTcb_cterm fun _ _ h => h
theorem findAcctF_cterm : ContractTerm Gen.prog findAcctSig findAcctF :=
  ContractTerm.mono findAcct_cterm fun _ _ h => h
theorem findDiscF_cterm : ContractTerm Gen.prog findDiscSig findDiscF :=
  ContractTerm.mono findDisc_cterm fun _ _ h => h
theorem copyF_cterm {sig : MethodSig} {cls : ClassName} {keys : List String}
    (h : ContractTerm Gen.prog sig (copySpec cls keys)) : ContractTerm Gen.prog sig (copyF cls keys) :=
  ContractTerm.mono h fun _ _ h => h
theorem ctorTCF_cterm : ContractTerm Gen.prog ctorTCSig ctorTCF :=
  ContractTerm.mono ctorTC_cterm fun _ _ h => h
theorem ctorXCF_cterm : ContractTerm Gen.prog ctorXCSig ctorXCF :=
  ContractTerm.mono ctorXC_cterm fun _ _ h => h
theorem ctorACF_cterm : ContractTerm Gen.prog ctorACSig ctorACF :=
  ContractTerm.mono ctorAC_cterm fun _ _ h => h
theorem ctorDCF_cterm : ContractTerm Gen.prog ctorDCSig ctorDCF :=
  ContractTerm.mono ctorDC_cterm fun _ _ h => h
theorem ctorRCF_cterm : ContractTerm Gen.prog ctorRCSig ctorRCF :=
  ContractTerm.mono ctorRC_cterm fun _ _ h => h

/-- **Every contract of `runC` terminates.** -/
theorem runC_term :
    ∀ sig S, (runC.env.below (fun _ => 0) 1) sig = some S → ContractTerm Gen.prog sig S :=
  Contracts.term_of_ok (by
    simp only [runC, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
      and_true]
    exact ⟨spaces_cterm, fixLenF_cterm, fmtU_cterm, trunc_cterm, displayTcbF_cterm, findAcctF_cterm,
      findDiscF_cterm, copyF_cterm copyTcb_cterm, copyF_cterm copyXref_cterm,
      copyF_cterm copyAcct_cterm, copyF_cterm copyDis_cterm, copyF_cterm copyTran_cterm,
      ctorTCF_cterm, ctorXCF_cterm, ctorACF_cterm, ctorDCF_cterm, ctorRCF_cterm⟩) _ _

end EquivLean.Modernize.Cbact04c.Java
