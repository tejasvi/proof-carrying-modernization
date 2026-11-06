import EquivLean.Modernize.Cbstm03a.Java.Text.TextBase

/-!
# CBSTM03A → Java: `xrefText` and `trnxText`

Verified for every fixed choice of ghost values against `fix`, `spaces` (`Iface0`) and `zu`, `zs` (`Iface1` `zuSpec`,
`zsSpec`), then their contracts of `Iface3`.
-/

set_option jimple.modelContracts true

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows fixStr zpadStr argText StrOk space Kept GrowsK grows_split
  growsK_elim grows_refl grows_trans)

namespace EquivLean.Modernize.Cbstm03a.Java.Txt

attribute [-simp] List.reduceReplicate

set_option maxRecDepth 8000 in
set_option maxHeartbeats 2000000 in
theorem xrefText_vc (v : Value) (t : Option XrefR) :
    MethodVC Gen.prog txtCallees.env 0 xrefTextRef (xrefTextSpecG v t) [] 80 := by
  refine ⟨_, rfl, fun args σ0 hpre => ⟨?_, fun p hp => by simp [Invariants.inst] at hp⟩⟩
  cases t with
  | none =>
    obtain ⟨h0, hv, hI⟩ := hpre
    simp only [XrefAtN] at hv
    simp only [xrefTextSpecG, Spec.of, xrefTextO]
    jvc [ite_nat_ne, txtCallees, fixSig, spacesSig, zuSig, zsSig, fixSpec, spacesSpec, zuSpec, zsSpec,
      grows_split, StrOk, argText, strOf]
    all_goals first | exact growsK_of (by txt_grows) | simp only [xrefTextR, zuI, zsI_eq, List.append_assoc]
  | some tr =>
    obtain ⟨h0, ⟨x, hv, fs, hx, ⟨a1, g1, h1, l1⟩, ⟨g2, b2⟩, ⟨g3, b3⟩, ⟨a4, g4, h4, l4⟩⟩, hI⟩ := hpre
    simp only [xrefTextSpecG, Spec.of, xrefTextO]
    jvc [ite_nat_ne, txtCallees, fixSig, spacesSig, zuSig, zsSig, fixSpec, spacesSpec, zuSpec, zsSpec,
      grows_split, StrOk, argText, strOf]
    all_goals first | exact growsK_of (by txt_grows) | simp only [xrefTextR, zuI, zsI_eq, List.append_assoc]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem trnxText_vc (v : Value) (t : Option TrnxR) :
    MethodVC Gen.prog txtCallees.env 0 trnxTextRef (trnxTextSpecG v t) [] 120 := by
  refine ⟨_, rfl, fun args σ0 hpre => ⟨?_, fun p hp => by simp [Invariants.inst] at hp⟩⟩
  cases t with
  | none =>
    obtain ⟨h0, hv, hI⟩ := hpre
    simp only [TrnxAtN] at hv
    simp only [trnxTextSpecG, Spec.of, trnxTextO]
    jvc [ite_nat_ne, txtCallees, fixSig, spacesSig, zuSig, zsSig, fixSpec, spacesSpec, zuSpec, zsSpec,
      grows_split, StrOk, argText, strOf]
    all_goals first | exact growsK_of (by txt_grows) | simp only [trnxTextR, zuI, zsI_eq, List.append_assoc]
  | some tr =>
    obtain ⟨h0, ⟨x, hv, fs, hx, ⟨a1, g1, h1, l1⟩, ⟨a2, g2, h2, l2⟩, ⟨a3, g3, h3, l3⟩, ⟨g4, b4⟩,
      ⟨a5, g5, h5, l5⟩, ⟨a6, g6, h6, l6⟩, ⟨g7, b7⟩, ⟨g8, b8⟩, ⟨a9, g9, h9, l9⟩, ⟨a10, g10, h10, l10⟩,
      ⟨a11, g11, h11, l11⟩, ⟨a12, g12, h12, l12⟩, ⟨a13, g13, h13, l13⟩, ⟨a14, g14, h14, l14⟩⟩, hI⟩ := hpre
    simp only [trnxTextSpecG, Spec.of, trnxTextO]
    jvc [ite_nat_ne, txtCallees, fixSig, spacesSig, zuSig, zsSig, fixSpec, spacesSpec, zuSpec, zsSpec,
      grows_split, StrOk, argText, strOf]
    all_goals first | exact growsK_of (by txt_grows) | simp only [trnxTextR, zuI, zsI_eq, List.append_assoc]

theorem xrefText_sat (hV : Valid Gen.prog txtCallees.env) : Sat Gen.prog xrefTextRef xrefTextSpec := by
  intro args σ o hpre hm
  obtain ⟨v, t, h0, h1, h2⟩ := hpre
  have hG := MethodVC.sat_of_valid hV (xrefText_vc v t) args σ o ⟨h0, h1, h2⟩ hm
  cases o with
  | normal r σ' =>
    intro v' t' g0 g1
    rw [h0] at g0
    obtain rfl : v = v' := by simpa using g0
    exact MethodVC.sat_of_valid hV (xrefText_vc v t') args σ (.normal r σ') ⟨h0, g1, h2⟩ hm
  | exc e σ' => exact hG.elim
  | wrong msg => exact hG.elim

theorem trnxText_sat (hV : Valid Gen.prog txtCallees.env) : Sat Gen.prog trnxTextRef trnxTextSpec := by
  intro args σ o hpre hm
  obtain ⟨v, t, h0, h1, h2⟩ := hpre
  have hG := MethodVC.sat_of_valid hV (trnxText_vc v t) args σ o ⟨h0, h1, h2⟩ hm
  cases o with
  | normal r σ' =>
    intro v' t' g0 g1
    rw [h0] at g0
    obtain rfl : v = v' := by simpa using g0
    exact MethodVC.sat_of_valid hV (trnxText_vc v t') args σ (.normal r σ') ⟨h0, g1, h2⟩ hm
  | exc e σ' => exact hG.elim
  | wrong msg => exact hG.elim

end EquivLean.Modernize.Cbstm03a.Java.Txt

#print axioms EquivLean.Modernize.Cbstm03a.Java.Txt.xrefText_vc
#print axioms EquivLean.Modernize.Cbstm03a.Java.Txt.trnxText_vc
#print axioms EquivLean.Modernize.Cbstm03a.Java.Txt.xrefText_sat
#print axioms EquivLean.Modernize.Cbstm03a.Java.Txt.trnxText_sat
