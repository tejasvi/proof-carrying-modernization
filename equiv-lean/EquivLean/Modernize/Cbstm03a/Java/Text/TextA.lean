import EquivLean.Modernize.Cbstm03a.Java.Text.TextBase

/-!
# CBSTM03A → Java: `acctText`

Verified for every fixed choice of ghost values against `fix`, `spaces` (`Iface0`) and `zu`, `zs` (`Iface1` `zuSpec`,
`zsSpec`), then its contract of `Iface3`.
-/

set_option jimple.modelContracts true

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows fixStr zpadStr argText StrOk space Kept GrowsK grows_split
  growsK_elim grows_refl grows_trans)

namespace EquivLean.Modernize.Cbstm03a.Java.Txt

attribute [-simp] List.reduceReplicate

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem acctText_vc (v : Value) (t : Option AcctR) :
    MethodVC Gen.prog txtCallees.env 0 acctTextRef (acctTextSpecG v t) [] 120 := by
  refine ⟨_, rfl, fun args σ0 hpre => ⟨?_, fun p hp => by simp [Invariants.inst] at hp⟩⟩
  cases t with
  | none =>
    obtain ⟨h0, hv, hI⟩ := hpre
    simp only [AcctAtN] at hv
    simp only [acctTextSpecG, Spec.of, acctTextO]
    jvc [ite_nat_ne, txtCallees, fixSig, spacesSig, zuSig, zsSig, fixSpec, spacesSpec, zuSpec, zsSpec,
      grows_split, StrOk, argText, strOf]
    all_goals first | exact growsK_of (by txt_grows) | simp only [acctTextR, zuI, zsI_eq, List.append_assoc]
  | some tr =>
    obtain ⟨h0, ⟨x, hv, fs, hx, ⟨g1, b1⟩, ⟨a2, g2, h2, l2⟩, ⟨g3, b3⟩, ⟨g4, b4⟩, ⟨g5, b5⟩,
      ⟨a6, g6, h6, l6⟩, ⟨a7, g7, h7, l7⟩, ⟨a8, g8, h8, l8⟩, ⟨g9, b9⟩, ⟨g10, b10⟩, ⟨a11, g11, h11, l11⟩,
      ⟨a12, g12, h12, l12⟩, ⟨a13, g13, h13, l13⟩⟩, hI⟩ := hpre
    simp only [acctTextSpecG, Spec.of, acctTextO]
    jvc [ite_nat_ne, txtCallees, fixSig, spacesSig, zuSig, zsSig, fixSpec, spacesSpec, zuSpec, zsSpec,
      grows_split, StrOk, argText, strOf]
    all_goals first | exact growsK_of (by txt_grows) | simp only [acctTextR, zuI, zsI_eq, List.append_assoc]

theorem acctText_sat (hV : Valid Gen.prog txtCallees.env) : Sat Gen.prog acctTextRef acctTextSpec := by
  intro args σ o hpre hm
  obtain ⟨v, t, h0, h1, h2⟩ := hpre
  have hG := MethodVC.sat_of_valid hV (acctText_vc v t) args σ o ⟨h0, h1, h2⟩ hm
  cases o with
  | normal r σ' =>
    intro v' t' g0 g1
    rw [h0] at g0
    obtain rfl : v = v' := by simpa using g0
    exact MethodVC.sat_of_valid hV (acctText_vc v t') args σ (.normal r σ') ⟨h0, g1, h2⟩ hm
  | exc e σ' => exact hG.elim
  | wrong msg => exact hG.elim

end EquivLean.Modernize.Cbstm03a.Java.Txt

#print axioms EquivLean.Modernize.Cbstm03a.Java.Txt.acctText_vc
#print axioms EquivLean.Modernize.Cbstm03a.Java.Txt.acctText_sat
