import EquivLean.Modernize.Cbstm03a.Java.Iface0
import EquivLean.Modernize.Cbstm03a.Java.Iface1
import EquivLean.Modernize.Cbstm03a.Java.Iface3
import EquivLean.Modernize.Cbstm03a.Java.Term.FmtZ
import EquivLean.Modernize.Cbstm03a.Java.Term.Fix
import EquivLean.Modernize.Cbstm03a.Java.Term.Zu
import EquivLean.Modernize.Cbstm03a.Java.Term.DecodeZoned
import EquivLean.Modernize.Cbstm03a.Java.Term.EbcCompare
import EquivLean.Modernize.Cbstm03a.Java.Term.NoLoop
import EquivLean.Modernize.Cbstm03a.Java.Term.TextsD
import EquivLean.Modernize.Cbstm03a.Java.Term.ParaStar
import EquivLean.Modernize.Cbstm03a.Java.Term.TextsC

/-!
# CBSTM03A → Java, termination: the interface contracts terminate

`<m>_cterm : ContractTerm Gen.prog <m>Sig <m>Spec` for the interface specifications (`CbA.Iface0`,
`CbANum.Iface1`, `CbAText.Iface3`, snapshot `cbA_v2_2155`), from this package's termination contracts
(`Term.<m>_ctermT`) by `ContractTerm.mono`: each interface precondition implies the termination precondition.
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows StrOk)

namespace EquivLean.Modernize.Cbstm03a.Java

set_option maxRecDepth 20000 in
/-- `CP037At`: the static table is an `int` array of length 256. -/
theorem cpOk_of {σ : State} (h : CP037At σ) : Term.InitA σ ∧ Term.CpOk σ := by
  obtain ⟨hi, a, hs, ha⟩ := h
  refine ⟨hi, a, cp037Table.map (BitVec.ofNat 32), hs, ?_, ?_⟩
  · rw [ha, cp037Arr, List.map_map]
    rfl
  · rw [List.length_map]
    rfl

theorem sfld_arg {σ : State} {c : ClassName} {fs : List (FieldKey × Value)} {f : String} {s : JStr}
    (h : SFld σ c fs f s) : ∃ w, Fields.get fs (c, f) = some w ∧ Term.StrArg σ w := by
  obtain ⟨x, h1, h2, h3⟩ := h
  exact ⟨.ref x, h1, Or.inr ⟨x, s, rfl, h2, h3⟩⟩

theorem lfld_arg {c : ClassName} {fs : List (FieldKey × Value)} {f : String} {l : I64} (h : LFld c fs f l) :
    ∃ l' : I64, Fields.get fs (c, f) = some (.long l') := ⟨l, h.1⟩

theorem repeat_cterm : ContractTerm Gen.prog repeatSig repeatSpec :=
  ContractTerm.mono Term.repeat_ctermT fun _ _ h => h
theorem spaces_cterm : ContractTerm Gen.prog spacesSig spacesSpec :=
  ContractTerm.mono Term.spaces_ctermT fun _ _ h => h
theorem spacesI_cterm : ContractTerm Gen.prog spacesSig spacesSpecI :=
  ContractTerm.mono Term.spaces_ctermT fun _ _ h => h
theorem fix_cterm : ContractTerm Gen.prog fixSig fixSpec :=
  ContractTerm.mono Term.fix_ctermT fun _ _ h => h
theorem fixI_cterm : ContractTerm Gen.prog fixSig fixSpecI :=
  ContractTerm.mono Term.fix_ctermT fun _ _ h => h
theorem zeroPad_cterm : ContractTerm Gen.prog zeroPadSig zeroPadSpec :=
  ContractTerm.mono Term.zeroPad_ctermT fun _ _ ⟨v, n, h1, _, h3⟩ => ⟨v, n, h1, h3⟩
theorem pow10_cterm : ContractTerm Gen.prog pow10Sig pow10Spec :=
  ContractTerm.mono Term.pow10_ctermT fun _ _ h => h
theorem zu_cterm : ContractTerm Gen.prog zuSig zuSpec :=
  ContractTerm.mono Term.zu_ctermT fun _ _ ⟨v, n, h1, _, h3, h4⟩ => ⟨v, n, h1, h3, h4⟩
theorem zs_cterm : ContractTerm Gen.prog zsSig zsSpec :=
  ContractTerm.mono Term.zs_ctermT fun _ _ ⟨v, n, h1, _, h3, h4⟩ => ⟨v, n, h1, h3, h4⟩
theorem trunc11_cterm : ContractTerm Gen.prog trunc11Sig trunc11Spec :=
  ContractTerm.mono Term.trunc11_ctermT fun _ _ ⟨v, h1, _⟩ => ⟨v, h1⟩
theorem fmtCurrBal_cterm : ContractTerm Gen.prog fmtCurrBalSig fmtCurrBalSpec :=
  ContractTerm.mono Term.fmtCurrBal_ctermT fun _ _ ⟨v, h1, _, h3⟩ => ⟨v, h1, h3⟩
theorem fmtZ_cterm : ContractTerm Gen.prog fmtZSig fmtZSpec :=
  ContractTerm.mono Term.fmtZ_ctermT fun _ _ ⟨v, h1, _, h3⟩ => ⟨v, h1, h3⟩
theorem decodeZoned_cterm : ContractTerm Gen.prog decodeZonedSig decodeZonedSpec :=
  ContractTerm.mono Term.decodeZoned_ctermT fun _ _ h => h
theorem ebc_cterm : ContractTerm Gen.prog ebcSig ebcSpec :=
  ContractTerm.mono Term.ebc_ctermT fun _ _ ⟨c, h1, h2⟩ => ⟨c, h1, (cpOk_of h2).1, (cpOk_of h2).2⟩
theorem ebcCompare_cterm : ContractTerm Gen.prog ebcCompareSig ebcCompareSpec :=
  ContractTerm.mono Term.ebcCompare_ctermT fun _ _ ⟨av, bv, h1, h2, h3, h4⟩ =>
    ⟨av, bv, h1, h2, h3, (cpOk_of h4).1, (cpOk_of h4).2⟩

theorem xrefText_cterm : ContractTerm Gen.prog xrefTextSig xrefTextSpec := by
  refine ContractTerm.mono Term.xrefText_ctermT fun args σ h => ?_
  obtain ⟨v, t, rfl, hv, hi⟩ := h
  refine ⟨v, rfl, ?_, hi⟩
  cases t with
  | none => exact Or.inl hv
  | some t =>
    obtain ⟨x, rfl, fs, hx, h1, h2, h3, h4⟩ := hv
    refine Or.inr ⟨x, fs, rfl, hx, ?_, ?_⟩
    · simp only [Term.xrefSs, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
      exact ⟨sfld_arg h1, sfld_arg h4⟩
    · simp only [Term.xrefLs, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
      exact ⟨lfld_arg h2, lfld_arg h3⟩

theorem trnxText_cterm : ContractTerm Gen.prog trnxTextSig trnxTextSpec := by
  refine ContractTerm.mono Term.trnxText_ctermT fun args σ h => ?_
  obtain ⟨v, t, rfl, hv, hi⟩ := h
  refine ⟨v, rfl, ?_, hi⟩
  cases t with
  | none => exact Or.inl hv
  | some t =>
    obtain ⟨x, rfl, fs, hx, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := hv
    refine Or.inr ⟨x, fs, rfl, hx, ?_, ?_⟩
    · simp only [Term.trnxSs, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
      exact ⟨sfld_arg h1, sfld_arg h2, sfld_arg h3, sfld_arg h5, sfld_arg h6, sfld_arg h9, sfld_arg h10,
        sfld_arg h11, sfld_arg h12, sfld_arg h13, sfld_arg h14⟩
    · simp only [Term.trnxLs, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
      exact ⟨lfld_arg h4, lfld_arg h7, lfld_arg h8⟩

theorem acctText_cterm : ContractTerm Gen.prog acctTextSig acctTextSpec := by
  refine ContractTerm.mono Term.acctText_ctermT fun args σ h => ?_
  obtain ⟨v, t, rfl, hv, hi⟩ := h
  refine ⟨v, rfl, ?_, hi⟩
  cases t with
  | none => exact Or.inl hv
  | some t =>
    obtain ⟨x, rfl, fs, hx, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := hv
    refine Or.inr ⟨x, fs, rfl, hx, ?_, ?_⟩
    · simp only [Term.acctSs, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
      exact ⟨sfld_arg h2, sfld_arg h6, sfld_arg h7, sfld_arg h8, sfld_arg h11, sfld_arg h12, sfld_arg h13⟩
    · simp only [Term.acctLs, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
      exact ⟨lfld_arg h1, lfld_arg h3, lfld_arg h4, lfld_arg h5, lfld_arg h9, lfld_arg h10⟩

theorem app_cterm : ContractTerm Gen.prog appSig appSpec :=
  ContractTerm.mono Term.app_ctermT fun _ _ h => h
theorem para_cterm : ContractTerm Gen.prog paraSig paraSpec :=
  ContractTerm.mono Term.para_ctermT fun _ _ h => h
theorem star_cterm : ContractTerm Gen.prog starSig starSpec :=
  ContractTerm.mono Term.star_ctermT fun _ _ h => h

theorem sfld_nn {σ : State} {c : ClassName} {fs : List (FieldKey × Value)} {f : String} {s : JStr}
    (h : SFld σ c fs f s) :
    ∃ x s', Fields.get fs (c, f) = some (.ref x) ∧ σ.heap x = some (.str s') ∧ s'.length < 2147483648 := by
  obtain ⟨x, h1, h2, h3⟩ := h
  exact ⟨x, s, h1, h2, h3⟩

theorem custText_cterm : ContractTerm Gen.prog custTextSig custTextSpec := by
  refine ContractTerm.mono Term.custText_ctermT fun args σ h => ?_
  obtain ⟨v, t, rfl, hv, hi⟩ := h
  refine ⟨v, rfl, ?_, hi⟩
  cases t with
  | none => exact Or.inl hv
  | some t =>
    obtain ⟨x, rfl, fs, hx, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
      h19⟩ := hv
    refine Or.inr ⟨x, fs, rfl, hx, ?_, ?_⟩
    · simp only [Term.custSs, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
      exact ⟨sfld_nn h2, sfld_nn h3, sfld_nn h4, sfld_nn h5, sfld_nn h6, sfld_nn h7, sfld_nn h8, sfld_nn h9,
        sfld_nn h10, sfld_nn h11, sfld_nn h12, sfld_nn h14, sfld_nn h15, sfld_nn h16, sfld_nn h17, sfld_nn h19⟩
    · simp only [Term.custLs, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
      exact ⟨lfld_arg h1, lfld_arg h13, lfld_arg h18⟩

end EquivLean.Modernize.Cbstm03a.Java

#print axioms EquivLean.Modernize.Cbstm03a.Java.repeat_cterm
#print axioms EquivLean.Modernize.Cbstm03a.Java.spaces_cterm
#print axioms EquivLean.Modernize.Cbstm03a.Java.spacesI_cterm
#print axioms EquivLean.Modernize.Cbstm03a.Java.fix_cterm
#print axioms EquivLean.Modernize.Cbstm03a.Java.fixI_cterm
#print axioms EquivLean.Modernize.Cbstm03a.Java.zeroPad_cterm
#print axioms EquivLean.Modernize.Cbstm03a.Java.pow10_cterm
#print axioms EquivLean.Modernize.Cbstm03a.Java.zu_cterm
#print axioms EquivLean.Modernize.Cbstm03a.Java.zs_cterm
#print axioms EquivLean.Modernize.Cbstm03a.Java.trunc11_cterm
#print axioms EquivLean.Modernize.Cbstm03a.Java.fmtCurrBal_cterm
#print axioms EquivLean.Modernize.Cbstm03a.Java.fmtZ_cterm
#print axioms EquivLean.Modernize.Cbstm03a.Java.decodeZoned_cterm
#print axioms EquivLean.Modernize.Cbstm03a.Java.ebc_cterm
#print axioms EquivLean.Modernize.Cbstm03a.Java.ebcCompare_cterm
#print axioms EquivLean.Modernize.Cbstm03a.Java.xrefText_cterm
#print axioms EquivLean.Modernize.Cbstm03a.Java.trnxText_cterm
#print axioms EquivLean.Modernize.Cbstm03a.Java.acctText_cterm
#print axioms EquivLean.Modernize.Cbstm03a.Java.app_cterm
#print axioms EquivLean.Modernize.Cbstm03a.Java.para_cterm
#print axioms EquivLean.Modernize.Cbstm03a.Java.star_cterm
#print axioms EquivLean.Modernize.Cbstm03a.Java.custText_cterm
