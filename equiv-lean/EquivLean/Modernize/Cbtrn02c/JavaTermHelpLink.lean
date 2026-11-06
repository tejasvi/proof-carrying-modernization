-- Termination package by JimpleLean's session: TermPk/Cbtrn02c/JavaTermHelpLink.lean (sha256 fc33d3416c2ecceb...); only the module root renamed.
import EquivLean.Modernize.Cbtrn02c.JavaTermLeafA
import EquivLean.Modernize.Cbtrn02c.JavaTermLeafB
import EquivLean.Modernize.Cbtrn02c.JavaTermLeafC
import EquivLean.Modernize.Cbtrn02c.JavaTermLeafD
import EquivLean.Modernize.Cbtrn02c.JavaTermWt
import EquivLean.Modernize.Cbtrn02c.JavaTermUa
import EquivLean.Modernize.Cbtrn02c.JavaTermUtA
import EquivLean.Modernize.Cbtrn02c.JavaTermUtB
import EquivLean.Modernize.Cbtrn02c.JavaTermPtE
import EquivLean.Modernize.Cbtrn02c.JavaTermPtS
import EquivLean.Modernize.Cbtrn02c.JavaTermVt1
import EquivLean.Modernize.Cbtrn02c.JavaTermVt2
import EquivLean.Modernize.Cbtrn02c.JavaTermVt3
import EquivLean.Modernize.Cbtrn02c.Any.JavaRunM5d
import EquivLean.Modernize.Cbtrn02c.Any.JavaRunVt4
import EquivLean.Modernize.Cbtrn02c.JavaTermTac

/-!
# CBTRN02C → Java, termination: the helpers of `run`

The thin VCs of `writeTransaction` (contract `writeTransactionSpecX`), `updateAccount`,
`updateTcatbal`, `postTransaction` and `validateTran`, assembled from the thin twins of their
segments as the sources' `*_vc` are from the segments. Each helper terminates (`*_term`: its
`MethodVC` with its thin VC, `Jimple.TermVC.of_thin`, the callee contracts valid and terminating);
each contract a caller uses terminates (`*_cterm`, by `jcontract_term`; the `*SpecF` variants have
the preconditions of the proved contracts: `ContractTerm.mono`).
-/

open Jimple

namespace EquivLean.Modernize.Cbtrn02c.Java

/-! ## Thin VCs assembled from the segments -/

set_option maxRecDepth 8000 in
set_option maxHeartbeats 2000000 in
theorem writeTransactionX_thin :
    ThinVC Gen.prog wtCalleesX.env 0 writeTransactionRef writeTransactionSpecX [] (fun _ _ _ _ _ => 0)
      40 := by
  refine ⟨wtBody, rfl, ?_⟩
  intro args σ0 hpre
  have hpre' := hpre
  obtain ⟨r, wT, lK, -, -, -, -, -, -, -, -, -, -, -, -, rfl, -⟩ := hpre'
  refine ⟨?_, fun p hp => by simp at hp⟩
  have h0 : Invariants.inst [] [.ref r, .ref wT, .ref lK] σ0 = [] := rfl
  simp only [h0, List.lookup, List.map_nil]
  dsimp only [jground]
  rw [← WtThinWP_eq [.ref r, .ref wT, .ref lK] σ0]
  exact wt_tentry r wT lK σ0 hpre

set_option maxRecDepth 8000 in
set_option maxHeartbeats 2000000 in
theorem updateAccount_thin :
    ThinVC Gen.prog uaCallees.env 0 updateAccountRef updateAccountSpec [] (fun _ _ _ _ _ => 0) 60 := by
  refine ⟨uaBody, rfl, ?_⟩
  intro args σ0 hpre
  have hpre' := hpre
  obtain ⟨r, d, wA, aD, -, -, -, -, -, -, -, -, -, -, -, -, hargs, -⟩ := hpre'
  subst hargs
  refine ⟨?_, fun p hp => by simp at hp⟩
  have h0 : Invariants.inst [] [.ref r, .ref d, .ref wA, .ref aD] σ0 = [] := rfl
  simp only [h0, List.lookup, List.map_nil]
  dsimp only [jground]
  rw [← UaThinWP_eq [.ref r, .ref d, .ref wA, .ref aD] σ0]
  exact ua_tentry r d wA aD σ0 hpre

theorem utInv_keys (k : Nat) (h1 : k ≠ 21) (h2 : k ≠ 41) (h3 : k ≠ 59) : ∀ p ∈ utInv, p.1 ≠ k := by
  intro p hp
  simp only [utInv, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · exact fun e => h1 e.symm
  · exact fun e => h2 e.symm
  · exact fun e => h3 e.symm

set_option maxRecDepth 8000 in
set_option maxHeartbeats 2000000 in
theorem updateTcatbal_thin :
    ThinVC Gen.prog utCallees.env 0 updateTcatbalRef updateTcatbalSpec utInv utVs 80 := by
  refine ⟨utBody, rfl, ?_⟩
  intro args σ0 hpre
  obtain ⟨r, d, wX, wC, lC, rfl, hP⟩ := hpre
  refine ⟨?_, ?_⟩
  · have h0 : (utInv.inst [.ref r, .ref d, .ref wX, .ref wC, .ref lC] σ0).lookup 0 = none := rfl
    simp only [h0]
    dsimp only [jground]
    rw [← UtThinWPc_eq [.ref r, .ref d, .ref wX, .ref wC, .ref lC] σ0]
    rcases Int.lt_or_le (utIdx σ0 d wX lC) 0 with hn | hp
    · exact ut_tentry_neg r d wX wC lC σ0 _ hP hn
        (lookup_map_key_none _ utInv 1 (utInv_keys 1 (by omega) (by omega) (by omega)))
        (lookup_map_key_none _ utInv 2 (utInv_keys 2 (by omega) (by omega) (by omega)))
        (lookup_map_key_none _ utInv 3 (utInv_keys 3 (by omega) (by omega) (by omega)))
        (lookup_map_key_none _ utInv 4 (utInv_keys 4 (by omega) (by omega) (by omega)))
        (lookup_map_key_none _ utInv 5 (utInv_keys 5 (by omega) (by omega) (by omega)))
        (lookup_map_key_none _ utInv 6 (utInv_keys 6 (by omega) (by omega) (by omega)))
        (lookup_map_key_none _ utInv 7 (utInv_keys 7 (by omega) (by omega) (by omega)))
        (lookup_map_key_none _ utInv 8 (utInv_keys 8 (by omega) (by omega) (by omega)))
        (lookup_map_key_none _ utInv 9 (utInv_keys 9 (by omega) (by omega) (by omega)))
        (lookup_map_key_none _ utInv 10 (utInv_keys 10 (by omega) (by omega) (by omega)))
        (lookup_map_key_none _ utInv 11 (utInv_keys 11 (by omega) (by omega) (by omega)))
        (lookup_map_key_none _ utInv 12 (utInv_keys 12 (by omega) (by omega) (by omega)))
        (lookup_map_key_none _ utInv 13 (utInv_keys 13 (by omega) (by omega) (by omega)))
        (lookup_map_key_none _ utInv 14 (utInv_keys 14 (by omega) (by omega) (by omega)))
        (lookup_map_key_none _ utInv 15 (utInv_keys 15 (by omega) (by omega) (by omega)))
        (lookup_map_key_none _ utInv 16 (utInv_keys 16 (by omega) (by omega) (by omega)))
        (lookup_map_key_none _ utInv 17 (utInv_keys 17 (by omega) (by omega) (by omega))) rfl
    · exact ut_tentry_pos r d wX wC lC σ0 _ hP hp
        (lookup_map_key_none _ utInv 1 (utInv_keys 1 (by omega) (by omega) (by omega)))
        (lookup_map_key_none _ utInv 2 (utInv_keys 2 (by omega) (by omega) (by omega)))
        (lookup_map_key_none _ utInv 3 (utInv_keys 3 (by omega) (by omega) (by omega)))
        (lookup_map_key_none _ utInv 4 (utInv_keys 4 (by omega) (by omega) (by omega)))
        (lookup_map_key_none _ utInv 5 (utInv_keys 5 (by omega) (by omega) (by omega)))
        (lookup_map_key_none _ utInv 6 (utInv_keys 6 (by omega) (by omega) (by omega)))
        (lookup_map_key_none _ utInv 7 (utInv_keys 7 (by omega) (by omega) (by omega)))
        (lookup_map_key_none _ utInv 8 (utInv_keys 8 (by omega) (by omega) (by omega)))
        (lookup_map_key_none _ utInv 9 (utInv_keys 9 (by omega) (by omega) (by omega)))
        (lookup_map_key_none _ utInv 10 (utInv_keys 10 (by omega) (by omega) (by omega)))
        (lookup_map_key_none _ utInv 18 (utInv_keys 18 (by omega) (by omega) (by omega)))
        (lookup_map_key_none _ utInv 19 (utInv_keys 19 (by omega) (by omega) (by omega)))
        (lookup_map_key_none _ utInv 20 (utInv_keys 20 (by omega) (by omega) (by omega))) rfl
  · intro p hp fr σ hI
    rw [← UtThinWPc_eq [.ref r, .ref d, .ref wX, .ref wC, .ref lC] σ0]
    simp only [utInv, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl
    · rcases Int.lt_or_le (utIdx σ0 d wX lC) 0 with hn | hp
      · exact ut_tseg21_neg r d wX wC lC σ0 _ fr σ hP hn hI
          (fun k h1 h2 => lookup_map_key_none _ utInv k (utInv_keys k (by omega) (by omega)
            (by omega))) rfl
      · exact ut_tseg21_pos r d wX wC lC σ0 _ fr σ hP hp hI
          (fun k h1 h2 => lookup_map_key_none _ utInv k (utInv_keys k (by omega) (by omega)
            (by omega))) rfl
    · have hn := (hI r d wX wC lC rfl hP).1
      exact ut_tseg41 r d wX wC lC σ0 _ fr σ hP hn hI
        (fun k h1 h2 => lookup_map_key_none _ utInv k (utInv_keys k (by omega) (by omega)
          (by omega))) rfl
    · have hp := (hI r d wX wC lC rfl hP).1
      exact ut_tseg59 r d wX wC lC σ0 _ fr σ hP hp hI
        (fun k h1 h2 => lookup_map_key_none _ utInv k (utInv_keys k (by omega) (by omega)
          (by omega)))

theorem ptInv_keys (k : Nat) (h1 : k ≠ 36) (h2 : k ≠ 39) (h3 : k ≠ 40) : ∀ p ∈ ptInv, p.1 ≠ k := by
  intro p hp
  simp only [ptInv, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · exact fun e => h1 e.symm
  · exact fun e => h2 e.symm
  · exact fun e => h3 e.symm

set_option maxRecDepth 8000 in
set_option maxHeartbeats 2000000 in
theorem postTransaction_thin :
    ThinVC Gen.prog ptCallees.env 0 postTransactionRef postTransactionSpec ptInv ptVs 80 := by
  refine ⟨ptBody, rfl, ?_⟩
  intro args σ0 hpre
  obtain ⟨p, rfl, hP⟩ := hpre
  refine ⟨?_, ?_⟩
  · have h0 : (ptInv.inst p.args σ0).lookup 0 = none := rfl
    simp only [h0]
    dsimp only [jground]
    rw [← PtThinWPc_eq p.args σ0]
    exact pt_tentry p σ0 _ hP
      (fun k h1 h2 => lookup_map_key_none _ ptInv k (ptInv_keys k (by omega) (by omega) (by omega)))
      rfl
  · intro q hq fr σ hI
    rw [← PtThinWPc_eq p.args σ0]
    simp only [ptInv, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact pt_tseg36 p σ0 _ fr σ hP hI
        (lookup_map_key_none _ ptInv 37 (ptInv_keys 37 (by omega) (by omega) (by omega)))
        (lookup_map_key_none _ ptInv 38 (ptInv_keys 38 (by omega) (by omega) (by omega))) rfl
    · exact pt_tseg39 p σ0 _ fr σ hP hI rfl
    · exact pt_tseg40 p σ0 _ fr σ hP hI
        (lookup_map_key_none _ ptInv 41 (ptInv_keys 41 (by omega) (by omega) (by omega)))

theorem vtInv_keys (k : Nat) (h1 : k ≠ 11) (h2 : k ≠ 17) : ∀ p ∈ vtInv, p.1 ≠ k := by
  intro p hp
  simp only [vtInv, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact fun e => h1 e.symm
  · exact fun e => h2 e.symm

set_option maxRecDepth 8000 in
set_option maxHeartbeats 2000000 in
theorem validateTran_thin :
    ThinVC Gen.prog vtCallees.env 0 validateTranRef validateTranSpec vtInv vtVs 80 := by
  refine ⟨vtBodyC, rfl, ?_⟩
  intro args σ0 hpre
  have hpre0 := hpre
  obtain ⟨d, xA, aD, wX, wA, -, -, -, -, -, rfl, -⟩ := hpre0
  refine ⟨?_, ?_⟩
  · have h0 : (vtInv.inst [.ref d, .ref xA, .ref aD, .ref wX, .ref wA] σ0).lookup 0 = none := rfl
    simp only [h0]
    dsimp only [jground]
    rw [← VtThinWPc_eq [.ref d, .ref xA, .ref aD, .ref wX, .ref wA] σ0]
    exact vt_tseg0 d xA aD wX wA σ0 _ hpre
      (fun k h1 h2 => lookup_map_key_none _ vtInv k (vtInv_keys k (by omega) (by omega))) rfl
  · intro p hp fr σ hI
    rw [← VtThinWPc_eq [.ref d, .ref xA, .ref aD, .ref wX, .ref wA] σ0]
    simp only [vtInv, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact vt_tseg11 d xA aD wX wA σ0 _ fr σ hpre hI
        (fun k h1 h2 => lookup_map_key_none _ vtInv k (vtInv_keys k (by omega) (by omega))) rfl
    · exact vt_tseg17 d xA aD wX wA σ0 _ fr σ hpre hI
        (fun k h1 h2 => lookup_map_key_none _ vtInv k (vtInv_keys k (by omega) (by omega)))

/-! ## The helpers without callee contracts -/

theorem ctorAC_term : ∀ args σ, ctorACSpec.pre args σ → MTerm Gen.prog ctorACRef args σ :=
  TermVC.mterm (r := 1) (Jimple.valid_none _) (contractTerm_none _ _)
    (TermVC.of_thin (SpecEnv.below_const _ _ (by decide)) ctorAC_vc ctorAC_thin)
theorem ctorXR_term : ∀ args σ, ctorXRSpec.pre args σ → MTerm Gen.prog ctorXRRef args σ :=
  TermVC.mterm (r := 1) (Jimple.valid_none _) (contractTerm_none _ _)
    (TermVC.of_thin (SpecEnv.below_const _ _ (by decide)) ctorXR_vc ctorXR_thin)
theorem ctorTC_term : ∀ args σ, ctorTCSpec.pre args σ → MTerm Gen.prog ctorTCRef args σ :=
  TermVC.mterm (r := 1) (Jimple.valid_none _) (contractTerm_none _ _)
    (TermVC.of_thin (SpecEnv.below_const _ _ (by decide)) ctorTC_vc ctorTC_thin)
theorem ctorTR_term : ∀ args σ, ctorTRSpec.pre args σ → MTerm Gen.prog ctorTRRef args σ :=
  TermVC.mterm (r := 1) (Jimple.valid_none _) (contractTerm_none _ _)
    (TermVC.of_thin (SpecEnv.below_const _ _ (by decide)) ctorTR_vc ctorTR_thin)
theorem spaces_term : ∀ args σ, spacesSpec.pre args σ → MTerm Gen.prog spacesRef args σ :=
  TermVC.mterm (r := 1) (Jimple.valid_none _) (contractTerm_none _ _)
    (TermVC.of_thin (SpecEnv.below_const _ _ (by decide)) spaces_vc spaces_thin)
theorem fit_term : ∀ args σ, fitSpec.pre args σ → MTerm Gen.prog fitRef args σ :=
  TermVC.mterm (r := 1) (Jimple.valid_none _) (contractTerm_none _ _)
    (TermVC.of_thin (SpecEnv.below_const _ _ (by decide)) fit_vc fit_thin)
theorem padNum_term : ∀ args σ, padNumSpec.pre args σ → MTerm Gen.prog padNumRef args σ :=
  TermVC.mterm (r := 1) (Jimple.valid_none _) (contractTerm_none _ _)
    (TermVC.of_thin (SpecEnv.below_const _ _ (by decide)) padNum_vc padNum_thin)
theorem db2Timestamp_term :
    ∀ args σ, db2TimestampSpec.pre args σ → MTerm Gen.prog db2TimestampRef args σ :=
  TermVC.mterm (r := 1) (Jimple.valid_none _) (contractTerm_none _ _)
    (TermVC.of_thin (SpecEnv.below_const _ _ (by decide)) db2Timestamp_vc db2Timestamp_thin)
theorem reasonDesc_term : ∀ args σ, reasonDescSpec.pre args σ → MTerm Gen.prog reasonDescRef args σ :=
  TermVC.mterm (r := 1) (Jimple.valid_none _) (contractTerm_none _ _)
    (TermVC.of_thin (SpecEnv.below_const _ _ (by decide)) reasonDesc_vc reasonDesc_thin)
theorem ebcdic_term : ∀ args σ, ebcdicSpec.pre args σ → MTerm Gen.prog ebcdicRef args σ :=
  TermVC.mterm (r := 1) (Jimple.valid_none _) (contractTerm_none _ _)
    (TermVC.of_thin (SpecEnv.below_const _ _ (by decide)) ebcdic_vc ebcdic_thin)
theorem abend_term : ∀ args σ, abendSpec.pre args σ → MTerm Gen.prog abendRef args σ :=
  TermVC.mterm (r := 1) (Jimple.valid_none _) (contractTerm_none _ _)
    (TermVC.of_thin (SpecEnv.below_const _ _ (by decide)) abend_vc abend_thin)
theorem abend22_term : ∀ args σ, abendSpec22.pre args σ → MTerm Gen.prog abendRef args σ :=
  TermVC.mterm (r := 1) (Jimple.valid_none _) (contractTerm_none _ _)
    (TermVC.of_thin (SpecEnv.below_const _ _ (by decide)) abend22i_vc abend22i_thin)
theorem copyTcat_term : ∀ args σ, copyTcatSpec.pre args σ → MTerm Gen.prog copyTcatRef args σ :=
  TermVC.mterm (r := 1) (Jimple.valid_none _) (contractTerm_none _ _)
    (TermVC.of_thin (SpecEnv.below_const _ _ (by decide)) copyTcat_vc copyTcat_thin)
theorem assignTcat_term : ∀ args σ, assignTcatSpec.pre args σ → MTerm Gen.prog assignTcatRef args σ :=
  TermVC.mterm (r := 1) (Jimple.valid_none _) (contractTerm_none _ _)
    (TermVC.of_thin (SpecEnv.below_const _ _ (by decide)) assignTcat_vc assignTcat_thin)
theorem assignXref_term : ∀ args σ, assignXrefSpec.pre args σ → MTerm Gen.prog assignXrefRef args σ :=
  TermVC.mterm (r := 1) (Jimple.valid_none _) (contractTerm_none _ _)
    (TermVC.of_thin (SpecEnv.below_const _ _ (by decide)) assignXref_vc assignXref_thin)
theorem assignAccount_term :
    ∀ args σ, assignAccountSpec.pre args σ → MTerm Gen.prog assignAccountRef args σ :=
  TermVC.mterm (r := 1) (Jimple.valid_none _) (contractTerm_none _ _)
    (TermVC.of_thin (SpecEnv.below_const _ _ (by decide)) assignAccount_vc assignAccount_thin)
theorem findXref_term : ∀ args σ, findXrefSpec.pre args σ → MTerm Gen.prog findXrefRef args σ :=
  TermVC.mterm (r := 1) (Jimple.valid_none _) (contractTerm_none _ _)
    (TermVC.of_thin (SpecEnv.below_const _ _ (by decide)) findXref_vc findXref_thin)
theorem findAccount_term : ∀ args σ, findAccountSpec.pre args σ → MTerm Gen.prog findAccountRef args σ :=
  TermVC.mterm (r := 1) (Jimple.valid_none _) (contractTerm_none _ _)
    (TermVC.of_thin (SpecEnv.below_const _ _ (by decide)) findAccount_vc findAccount_thin)
theorem findTcatbal_term :
    ∀ args σ, findTcatbalSpec.pre args σ → MTerm Gen.prog findTcatbalRef args σ :=
  TermVC.mterm (r := 1) (Jimple.valid_none _) (contractTerm_none _ _)
    (TermVC.of_thin (SpecEnv.below_const _ _ (by decide)) findTcatbal_vc findTcatbal_thin)
theorem findKey_term : ∀ args σ, findKeySpec.pre args σ → MTerm Gen.prog findKeyRef args σ :=
  TermVC.mterm (r := 1) (Jimple.valid_none _) (contractTerm_none _ _)
    (TermVC.of_thin (SpecEnv.below_const _ _ (by decide)) findKey_vc findKey_thin)

-- constructors: instance methods, their virtual implementations enumerated (`jcontract_term_v`)
set_option maxHeartbeats 0 in
theorem ctorAC_cterm : ContractTerm Gen.prog ctorACSig ctorACSpec := by jcontract_term_v [ctorAC_term]
set_option maxHeartbeats 0 in
theorem ctorXR_cterm : ContractTerm Gen.prog ctorXRSig ctorXRSpec := by jcontract_term_v [ctorXR_term]
set_option maxHeartbeats 0 in
theorem ctorTC_cterm : ContractTerm Gen.prog ctorTCSig ctorTCSpec := by jcontract_term_v [ctorTC_term]
set_option maxHeartbeats 0 in
theorem ctorTR_cterm : ContractTerm Gen.prog ctorTRSig ctorTRSpec := by jcontract_term_v [ctorTR_term]
set_option maxHeartbeats 0 in
theorem spaces_cterm : ContractTerm Gen.prog spacesSig spacesSpec := by jcontract_term [spaces_term]
set_option maxHeartbeats 0 in
theorem fit_cterm : ContractTerm Gen.prog fitSig fitSpec := by jcontract_term [fit_term]
set_option maxHeartbeats 0 in
theorem padNum_cterm : ContractTerm Gen.prog padNumSig padNumSpec := by jcontract_term [padNum_term]
set_option maxHeartbeats 0 in
theorem db2Timestamp_cterm : ContractTerm Gen.prog db2TimestampSig db2TimestampSpec := by
  jcontract_term [db2Timestamp_term]
set_option maxHeartbeats 0 in
theorem reasonDesc_cterm : ContractTerm Gen.prog reasonDescSig reasonDescSpec := by
  jcontract_term [reasonDesc_term]
set_option maxHeartbeats 0 in
theorem ebcdic_cterm : ContractTerm Gen.prog ebcdicSig ebcdicSpec := by jcontract_term [ebcdic_term]
set_option maxHeartbeats 0 in
theorem abend_cterm : ContractTerm Gen.prog abendSig abendSpec := by jcontract_term [abend_term]
set_option maxHeartbeats 0 in
theorem abend22_cterm : ContractTerm Gen.prog abendSig abendSpec22 := by jcontract_term [abend22_term]
set_option maxHeartbeats 0 in
theorem copyTcat_cterm : ContractTerm Gen.prog copyTcatSig copyTcatSpec := by
  jcontract_term [copyTcat_term]
set_option maxHeartbeats 0 in
theorem assignTcat_cterm : ContractTerm Gen.prog assignTcatSig assignTcatSpec := by
  jcontract_term [assignTcat_term]
set_option maxHeartbeats 0 in
theorem assignXref_cterm : ContractTerm Gen.prog assignXrefSig assignXrefSpec := by
  jcontract_term [assignXref_term]
set_option maxHeartbeats 0 in
theorem assignAccount_cterm : ContractTerm Gen.prog assignAccountSig assignAccountSpec := by
  jcontract_term [assignAccount_term]
set_option maxHeartbeats 0 in
theorem findXref_cterm : ContractTerm Gen.prog findXrefSig findXrefSpec := by
  jcontract_term [findXref_term]
set_option maxHeartbeats 0 in
theorem findAccount_cterm : ContractTerm Gen.prog findAccountSig findAccountSpec := by
  jcontract_term [findAccount_term]
set_option maxHeartbeats 0 in
theorem findAccount_cterm' : ContractTerm Gen.prog findAccountSig' findAccountSpec := by
  jcontract_term [findAccount_term]
set_option maxHeartbeats 0 in
theorem findTcatbal_cterm : ContractTerm Gen.prog findTcatbalSig findTcatbalSpec := by
  jcontract_term [findTcatbal_term]
set_option maxHeartbeats 0 in
theorem findKey_cterm : ContractTerm Gen.prog findKeySig findKeySpec := by
  jcontract_term [findKey_term]

/-! The `*SpecF` variants: the preconditions of the proved contracts (as in `JavaRunF`). -/

theorem fitF_cterm : ContractTerm Gen.prog fitSig fitSpecF := ContractTerm.mono fit_cterm fun _ _ h => h
theorem db2TimestampF_cterm : ContractTerm Gen.prog db2TimestampSig db2TimestampSpecF :=
  ContractTerm.mono db2Timestamp_cterm fun _ _ h => h
theorem copyTcatF_cterm : ContractTerm Gen.prog copyTcatSig copyTcatSpecF :=
  ContractTerm.mono copyTcat_cterm fun _ _ h => h
theorem assignTcatF_cterm : ContractTerm Gen.prog assignTcatSig assignTcatSpecF :=
  ContractTerm.mono assignTcat_cterm fun _ _ h => h
theorem assignXrefF_cterm : ContractTerm Gen.prog assignXrefSig assignXrefSpecF :=
  ContractTerm.mono assignXref_cterm fun _ _ h => h
theorem assignAccountF_cterm : ContractTerm Gen.prog assignAccountSig assignAccountSpecF :=
  ContractTerm.mono assignAccount_cterm fun _ _ h => h
theorem findXrefF_cterm : ContractTerm Gen.prog findXrefSig findXrefSpecF :=
  ContractTerm.mono findXref_cterm fun _ _ h => h
theorem findAccountF_cterm : ContractTerm Gen.prog findAccountSig findAccountSpecF :=
  ContractTerm.mono findAccount_cterm fun _ _ h => h
theorem findAccountF_cterm' : ContractTerm Gen.prog findAccountSig' findAccountSpecF :=
  ContractTerm.mono findAccount_cterm' fun _ _ h => h
theorem findTcatbalF_cterm : ContractTerm Gen.prog findTcatbalSig findTcatbalSpecF :=
  ContractTerm.mono findTcatbal_cterm fun _ _ h => h
theorem findKeyF_cterm : ContractTerm Gen.prog findKeySig findKeySpecF :=
  ContractTerm.mono findKey_cterm fun _ _ h => h

/-! ## One level of callee contracts -/

theorem zonedSigned_term :
    ∀ args σ, zonedSignedSpec.pre args σ → MTerm Gen.prog zonedSignedRef args σ :=
  TermVC.mterm (rank := fun _ => 0) (r := 1)
    (Contracts.valid_of_ok (by
      intro p hp
      simp only [szCallees, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl
      exact padNum_ok))
    (Contracts.term_of_ok (by
      intro p hp
      simp only [szCallees, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl
      exact padNum_cterm) _ _)
    (TermVC.of_thin (SpecEnv.below_const _ _ (by decide)) zonedSigned_vc zonedSigned_thin)

theorem compareEbcdic_term :
    ∀ args σ, compareEbcdicSpec.pre args σ → MTerm Gen.prog compareEbcdicRef args σ :=
  TermVC.mterm (rank := fun _ => 0) (r := 1)
    (Contracts.valid_of_ok (by
      intro p hp
      simp only [ceCallees, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl
      exact ebcdic_ok))
    (Contracts.term_of_ok (by
      intro p hp
      simp only [ceCallees, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl
      exact ebcdic_cterm) _ _)
    (TermVC.of_thin (SpecEnv.below_const _ _ (by decide)) compareEbcdic_vc compareEbcdic_thin)

theorem copyAccount_term :
    ∀ args σ, copyAccountSpec.pre args σ → MTerm Gen.prog copyAccountRef args σ :=
  TermVC.mterm (rank := fun _ => 0) (r := 1) copyAccountC_valid
    (Contracts.term_of_ok (by
      intro p hp
      simp only [copyAccountC, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl
      exact ctorAC_cterm) _ _)
    (TermVC.of_thin (SpecEnv.below_const _ _ (by decide)) copyAccount_vc copyAccount_thin)

theorem copyTran_term : ∀ args σ, copyTranSpec.pre args σ → MTerm Gen.prog copyTranRef args σ :=
  TermVC.mterm (rank := fun _ => 0) (r := 1) copyTranC_valid
    (Contracts.term_of_ok (by
      intro p hp
      simp only [copyTranC, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl
      exact ctorTR_cterm) _ _)
    (TermVC.of_thin (SpecEnv.below_const _ _ (by decide)) copyTran_vc copyTran_thin)

set_option maxHeartbeats 0 in
theorem zonedSigned_cterm : ContractTerm Gen.prog zonedSignedSig zonedSignedSpec := by
  jcontract_term [zonedSigned_term]
set_option maxHeartbeats 0 in
theorem compareEbcdic_cterm : ContractTerm Gen.prog compareEbcdicSig compareEbcdicSpec := by
  jcontract_term [compareEbcdic_term]
set_option maxHeartbeats 0 in
theorem copyAccount_cterm : ContractTerm Gen.prog copyAccountSig copyAccountSpec := by
  jcontract_term [copyAccount_term]
set_option maxHeartbeats 0 in
theorem copyTran_cterm : ContractTerm Gen.prog copyTranSig copyTranSpec := by
  jcontract_term [copyTran_term]

theorem compareEbcdicF_cterm : ContractTerm Gen.prog compareEbcdicSig compareEbcdicSpecF :=
  ContractTerm.mono compareEbcdic_cterm fun _ _ h => h
theorem copyAccountF_cterm : ContractTerm Gen.prog copyAccountSig copyAccountSpecF :=
  ContractTerm.mono copyAccount_cterm fun _ _ h => h
theorem copyTranF_cterm : ContractTerm Gen.prog copyTranSig copyTranSpecF :=
  ContractTerm.mono copyTran_cterm fun _ _ h => h

/-! ## Two levels -/

theorem dalytranText_term :
    ∀ args σ, dalytranTextSpec.pre args σ → MTerm Gen.prog dalytranTextRef args σ :=
  TermVC.mterm (rank := fun _ => 0) (r := 1)
    (Contracts.valid_of_ok (by
      intro p hp
      simp only [dtCallees, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl
      · exact fitF_ok
      · exact padNum_ok
      · exact zonedSigned_ok))
    (Contracts.term_of_ok (by
      intro p hp
      simp only [dtCallees, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl
      · exact fitF_cterm
      · exact padNum_cterm
      · exact zonedSigned_cterm) _ _)
    (TermVC.of_thin (SpecEnv.below_const _ _ (by decide)) dalytranText_vc dalytranText_thin)

theorem validateTran_term :
    ∀ args σ, validateTranSpec.pre args σ → MTerm Gen.prog validateTranRef args σ :=
  TermVC.mterm (rank := fun _ => 0) (r := 1)
    (Contracts.valid_of_ok (by
      intro p hp
      simp only [vtCallees, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl
      · exact findXrefF_ok
      · exact findAccountF_ok
      · exact assignXrefF_ok
      · exact assignAccountF_ok
      · exact compareEbcdicF_ok))
    (Contracts.term_of_ok (by
      intro p hp
      simp only [vtCallees, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl
      · exact findXrefF_cterm
      · exact findAccountF_cterm
      · exact assignXrefF_cterm
      · exact assignAccountF_cterm
      · exact compareEbcdicF_cterm) _ _)
    (TermVC.of_thin (SpecEnv.below_const _ _ (by decide)) validateTran_vc validateTran_thin)

theorem writeTransactionX_term :
    ∀ args σ, writeTransactionSpecX.pre args σ → MTerm Gen.prog writeTransactionRef args σ :=
  TermVC.mterm (rank := fun _ => 0) (r := 1)
    (Contracts.valid_of_ok (by
      intro p hp
      simp only [wtCalleesX, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl
      · exact findKeyF_ok
      · exact copyTranF_ok
      · exact abend22_ok))
    (Contracts.term_of_ok (by
      intro p hp
      simp only [wtCalleesX, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl
      · exact findKeyF_cterm
      · exact copyTranF_cterm
      · exact abend22_cterm) _ _)
    (TermVC.of_thin (SpecEnv.below_const _ _ (by decide)) writeTransactionX_vc writeTransactionX_thin)

theorem updateAccount_term :
    ∀ args σ, updateAccountSpec.pre args σ → MTerm Gen.prog updateAccountRef args σ :=
  TermVC.mterm (rank := fun _ => 0) (r := 1)
    (Contracts.valid_of_ok (by
      intro p hp
      simp only [uaCallees, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · exact findAccountF_ok'
      · exact copyAccountF_ok))
    (Contracts.term_of_ok (by
      intro p hp
      simp only [uaCallees, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · exact findAccountF_cterm'
      · exact copyAccountF_cterm) _ _)
    (TermVC.of_thin (SpecEnv.below_const _ _ (by decide)) updateAccount_vc updateAccount_thin)

theorem updateTcatbal_term :
    ∀ args σ, updateTcatbalSpec.pre args σ → MTerm Gen.prog updateTcatbalRef args σ :=
  TermVC.mterm (rank := fun _ => 0) (r := 1)
    (Contracts.valid_of_ok (by
      intro p hp
      simp only [utCallees, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
      · exact findTcatbalF_ok
      · exact padNum_ok
      · exact assignTcatF_ok
      · exact spaces_ok
      · exact copyTcatF_ok
      · exact abend_ok))
    (Contracts.term_of_ok (by
      intro p hp
      simp only [utCallees, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
      · exact findTcatbalF_cterm
      · exact padNum_cterm
      · exact assignTcatF_cterm
      · exact spaces_cterm
      · exact copyTcatF_cterm
      · exact abend_cterm) _ _)
    (TermVC.of_thin (SpecEnv.below_const _ _ (by decide)) updateTcatbal_vc updateTcatbal_thin)

set_option maxHeartbeats 0 in
theorem dalytranText_cterm : ContractTerm Gen.prog dalytranTextSig dalytranTextSpec := by
  jcontract_term [dalytranText_term]
set_option maxHeartbeats 0 in
theorem validateTran_cterm : ContractTerm Gen.prog validateTranSig validateTranSpec := by
  jcontract_term [validateTran_term]
set_option maxHeartbeats 0 in
theorem writeTransactionX_cterm : ContractTerm Gen.prog writeTransactionSig writeTransactionSpecX := by
  jcontract_term [writeTransactionX_term]
set_option maxHeartbeats 0 in
theorem updateAccount_cterm : ContractTerm Gen.prog updateAccountSig updateAccountSpec := by
  jcontract_term [updateAccount_term]
set_option maxHeartbeats 0 in
theorem updateTcatbal_cterm : ContractTerm Gen.prog updateTcatbalSig updateTcatbalSpec := by
  jcontract_term [updateTcatbal_term]

/-! ## Three levels: `writeReject`, `postTransaction` -/

theorem writeReject_term :
    ∀ args σ, writeRejectSpec.pre args σ → MTerm Gen.prog writeRejectRef args σ :=
  TermVC.mterm (rank := fun _ => 0) (r := 1)
    (Contracts.valid_of_ok (by
      intro p hp
      simp only [wrCallees, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl
      · exact dalytranText_ok
      · exact padNum_ok
      · exact reasonDesc_ok
      · exact fitF_ok))
    (Contracts.term_of_ok (by
      intro p hp
      simp only [wrCallees, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl
      · exact dalytranText_cterm
      · exact padNum_cterm
      · exact reasonDesc_cterm
      · exact fitF_cterm) _ _)
    (TermVC.of_thin (SpecEnv.below_const _ _ (by decide)) writeReject_vc writeReject_thin)

theorem postTransaction_term :
    ∀ args σ, postTransactionSpec.pre args σ → MTerm Gen.prog postTransactionRef args σ :=
  TermVC.mterm (rank := fun _ => 0) (r := 1)
    (Contracts.valid_of_ok (by
      intro c hc
      simp only [ptCallees, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact db2TimestampF_ok
      · exact updateTcatbal_ok
      · exact updateAccount_ok
      · exact writeTransactionX_ok))
    (Contracts.term_of_ok (by
      intro c hc
      simp only [ptCallees, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact db2TimestampF_cterm
      · exact updateTcatbal_cterm
      · exact updateAccount_cterm
      · exact writeTransactionX_cterm) _ _)
    (TermVC.of_thin (SpecEnv.below_const _ _ (by decide)) postTransaction_vc postTransaction_thin)

set_option maxHeartbeats 0 in
theorem writeReject_cterm : ContractTerm Gen.prog writeRejectSig writeRejectSpec := by
  jcontract_term [writeReject_term]
set_option maxHeartbeats 0 in
theorem postTransaction_cterm : ContractTerm Gen.prog postTransactionSig postTransactionSpec := by
  jcontract_term [postTransaction_term]

end EquivLean.Modernize.Cbtrn02c.Java

#print axioms EquivLean.Modernize.Cbtrn02c.Java.postTransaction_cterm
#print axioms EquivLean.Modernize.Cbtrn02c.Java.validateTran_cterm
#print axioms EquivLean.Modernize.Cbtrn02c.Java.writeReject_cterm
