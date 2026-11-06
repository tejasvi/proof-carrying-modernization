import EquivLean.Modernize.Cbstm03b.Java.CallVC
import EquivLean.Modernize.Cbstm03b.Java.HSpaces
import EquivLean.Modernize.Cbstm03b.Java.HZeroPad
import EquivLean.Modernize.Cbstm03b.Java.HKeySub
import EquivLean.Modernize.Cbstm03b.Java.HFresh

/-!
# CBSTM03B → Java: the link step

Each method was verified against the contracts of its callees; the contracts are instantiated bottom-up:

* the string helpers (verified without callee contracts) satisfy their contracts, `keySub` from its contract for
  fixed ghost values (`keySubG`, the area's fields);
* the contract tables of the file procedures hold (`seqCalleesF` for TRNXFILE and XREFFILE, `custCalleesF` for
  CUSTFILE, `acctCallees` for ACCTFILE);
* `run_sat_of`: `call` satisfies `runSpec` when the four file procedures satisfy `procSpec`.
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open CardDemo.Cbstm03b (ddTrnx ddXref ddCust ddAcct opOpen opRead opReadK opClose stBytes intoBuf)

namespace EquivLean.Modernize.Cbstm03b.Java

/-! ## The helpers -/

theorem spaces_sat : Sat Gen.prog spacesRef spacesSpec := spaces_vc.sat
theorem zeroPad_sat : Sat Gen.prog zeroPadRef zeroPadSpec := zeroPad_vc.sat
theorem fit_sat : Sat Gen.prog fitRef fitSpec := fit_vc.sat
theorem status2_sat : Sat Gen.prog status2Ref status2Spec := status2_vc.sat
theorem status2F_sat : Sat Gen.prog status2Ref status2SpecF := status2F_vc.sat
theorem fitF_sat : Sat Gen.prog fitRef fitSpecF := fitF_vc.sat

/-- `keySub`: for each area of the postcondition, its fields are ghost values of `keySubG`. -/
theorem keySub_sat : Sat Gen.prog keySubRef keySubSpec := by
  intro args σ o hpre hm
  obtain ⟨q0, a0, rfl, hA0, hVa0⟩ := hpre
  -- the contract for the area's own fields
  have hvc : ∀ q a, [Value.ref q0] = [.ref q] → JRecAt Model.LkM03bArea "Cbstm03b$LkM03bArea" σ (.ref q) a →
      Model.LkM03bArea.Valid a → ∃ skey fs key kl, (keySubG q skey fs key kl).post [.ref q0] σ o ∧
        key.take kl.toNat = cp037Str ((Model.aKey a).take (Model.aKeyLn a).toNat) := by
    intro q a hq hA hVa
    obtain ⟨q', fs, dd, op, rc, key, kl, fldt, sdd, sop, src, skey, sfl, hqq, hqh, rfl, -, -, -, hkl, hkl1, hkl2,
      -, -, -, -, -, -, -, gkey, jkey, gkl, -, -⟩ := areaAt_of hA hVa
    cases hqq
    obtain ⟨xk, rfl, hxk⟩ := jkey
    exact ⟨xk, fs, cp037Str key, kl, (keySub_vc q xk fs (cp037Str key) kl).sat [.ref q0] σ o
      ⟨hq, hqh, gkey, hxk, by rw [cp037Str_length]; exact hkl, gkl, hkl1, hkl2⟩ hm, (cp037Str_take key kl.toNat).symm⟩
  cases o with
  | normal r σ' =>
    intro q a hq hA hVa
    obtain ⟨skey, fs, key, kl, ⟨x, h1, h2, h3, h4, h5⟩, he⟩ := hvc q a hq hA hVa
    exact ⟨x, h1, by rw [h2, he], h3, h4, h5⟩
  | exc e σ' =>
    obtain ⟨skey, fs, key, kl, h, -⟩ := hvc q0 a0 rfl hA0 hVa0
    simp only [keySubG, Spec.of] at h
  | wrong msg =>
    obtain ⟨skey, fs, key, kl, h, -⟩ := hvc q0 a0 rfl hA0 hVa0
    simp only [keySubG, Spec.of] at h

theorem spaces_ok : ContractOK Gen.prog spacesSig spacesSpec := by jcontract_ok [spaces_sat]
theorem zeroPad_ok : ContractOK Gen.prog zeroPadSig zeroPadSpec := by jcontract_ok [zeroPad_sat]
theorem fit_ok : ContractOK Gen.prog fitSig fitSpec := by jcontract_ok [fit_sat]
theorem status2_ok : ContractOK Gen.prog status2Sig status2Spec := by jcontract_ok [status2_sat]
theorem keySub_ok : ContractOK Gen.prog keySubSig keySubSpec := by jcontract_ok [keySub_sat]
theorem status2F_ok : ContractOK Gen.prog status2Sig status2SpecF := by jcontract_ok [status2F_sat]
theorem fitF_ok : ContractOK Gen.prog fitSig fitSpecF := by jcontract_ok [fitF_sat]

/-! ## The callee contracts of the file procedures -/

/-- The callee contracts `custProc` is verified against: `status2` and `fit` with fresh results. -/
def custCalleesF : Contracts :=
  [(status2Sig, status2SpecF), (fitSig, fitSpecF), (keySubSig, keySubSpec), (spacesSig, spacesSpec)]

theorem seqCallees_valid : Valid Gen.prog seqCallees.env := Contracts.valid_of_ok (by
  intro p hp
  simp only [seqCallees, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact status2_ok
  · exact fit_ok)

theorem seqCalleesF_valid : Valid Gen.prog seqCalleesF.env := Contracts.valid_of_ok (by
  intro p hp
  simp only [seqCalleesF, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact status2F_ok
  · exact fitF_ok)

theorem custCallees_valid : Valid Gen.prog custCallees.env := Contracts.valid_of_ok (by
  intro p hp
  simp only [custCallees, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · exact status2_ok
  · exact fit_ok
  · exact keySub_ok
  · exact spaces_ok)

theorem custCalleesF_valid : Valid Gen.prog custCalleesF.env := Contracts.valid_of_ok (by
  intro p hp
  simp only [custCalleesF, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · exact status2F_ok
  · exact fitF_ok
  · exact keySub_ok
  · exact spaces_ok)

theorem acctCallees_valid : Valid Gen.prog acctCallees.env := Contracts.valid_of_ok (by
  intro p hp
  simp only [acctCallees, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl
  · exact status2_ok
  · exact fit_ok
  · exact keySub_ok
  · exact spaces_ok
  · exact zeroPad_ok)

/-- A file procedure verified for every choice of ghost values (`procSpecG`) against callee contracts that hold
satisfies `procSpec`. -/
theorem procSat_of_vc {m : MethodRef} {dd : List UInt8} {Γ : SpecEnv} {d : Nat} {A : Invariants} {fuel : Nat}
    (hV : Valid Gen.prog Γ) (h : ∀ oe st q opv oeM s a, MethodVC Gen.prog Γ d m (procSpecG dd oe st q opv oeM s a) A fuel) :
    Sat Gen.prog m (procSpec dd) :=
  procSpec_of_ghost fun oe st q opv oeM s a => MethodVC.sat_of_valid hV (h oe st q opv oeM s a)

/-! ## `call` -/

/-- **CBSTM03B, Java side, from the file procedures**: `call` satisfies `runSpec` when the four file procedures
satisfy their contracts. -/
theorem run_sat_of (ht : Sat Gen.prog trnxProcRef (procSpec ddTrnx)) (hx : Sat Gen.prog xrefProcRef (procSpec ddXref))
    (hc : Sat Gen.prog custProcRef (procSpec ddCust)) (ha : Sat Gen.prog acctProcRef (procSpec ddAcct)) :
    Sat Gen.prog callRef runSpec := by
  have ht' : ContractOK Gen.prog trnxProcSig (procSpec ddTrnx) := by jcontract_ok [ht]
  have hx' : ContractOK Gen.prog xrefProcSig (procSpec ddXref) := by jcontract_ok [hx]
  have hc' : ContractOK Gen.prog custProcSig (procSpec ddCust) := by jcontract_ok [hc]
  have ha' : ContractOK Gen.prog acctProcSig (procSpec ddAcct) := by jcontract_ok [ha]
  have hV : Valid Gen.prog callCallees.env := Contracts.valid_of_ok (by
    intro p hp
    simp only [callCallees, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · exact ht'
    · exact hx'
    · exact hc'
    · exact ha')
  exact runSpec_of_ghost fun oe st q oeM s a => MethodVC.sat_of_valid hV (call_vc oe st q oeM s a)

/-- **The generated statement**, from the file procedures' contracts. -/
theorem statement_of_procs (ht : Sat Gen.prog trnxProcRef (procSpec ddTrnx))
    (hx : Sat Gen.prog xrefProcRef (procSpec ddXref)) (hc : Sat Gen.prog custProcRef (procSpec ddCust))
    (ha : Sat Gen.prog acctProcRef (procSpec ddAcct)) : Statement :=
  statement_of_sat (run_sat_of ht hx hc ha)

end EquivLean.Modernize.Cbstm03b.Java

#print axioms EquivLean.Modernize.Cbstm03b.Java.keySub_sat
#print axioms EquivLean.Modernize.Cbstm03b.Java.seqCalleesF_valid
#print axioms EquivLean.Modernize.Cbstm03b.Java.custCalleesF_valid
#print axioms EquivLean.Modernize.Cbstm03b.Java.custCallees_valid
#print axioms EquivLean.Modernize.Cbstm03b.Java.acctCallees_valid
#print axioms EquivLean.Modernize.Cbstm03b.Java.run_sat_of
#print axioms EquivLean.Modernize.Cbstm03b.Java.statement_of_procs
