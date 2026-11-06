import EquivLean.Modernize.Cbstm03a.Java.Text.TextBase

/-!
# CBSTM03A → Java: `custText`, three segments

Verified for every fixed choice of ghost values against `fix`, `spaces` (`Iface0`) and `zu`, `zs` (`Iface1` `zuSpec`,
`zsSpec`), with cuts at statement 24 (`$r20 = r.custPhoneNum1`: ten parts computed) and statement 42 (the
concatenation: all nineteen parts computed); then its contract of `Iface3`. Locals: `$l0` 0, `r` 1, `$r0` 2,
`$r2` 3, …, `$r18` 11, `$r20` 12, `$r22` 13, `$r24` 14, `$r25` 15, `$r27` 16, `$r29` 17, `$r31` 18, `$r33` 19,
`$r34` 20.
-/

set_option jimple.modelContracts true

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows fixStr zpadStr argText StrOk space Kept GrowsK grows_split
  growsK_elim grows_refl grows_trans)

namespace EquivLean.Modernize.Cbstm03a.Java.Txt

attribute [-simp] List.reduceReplicate
attribute [-jsimp] Native.valueOfObj_ref

/-- A string argument of the concatenation, looked up in the state before the recipe's allocation (applies only
to a known state: no expansion under the continuation's binder). -/
theorem valueOfObj_str_alloc {P : Program} {σ : State} {a : Addr} {s : JStr} {o : Obj}
    {k : JStr → State → NRes} (h : σ.heap a = some (.str s)) :
    Native.valueOfObj P (.ref a) (σ.alloc o).2 k = k s (σ.alloc o).2 := by
  rw [Native.valueOfObj_ref, State.heap_alloc_of_lt (State.lt_next_of_heap h), h]

/-- The heap of a cut: grown from the entry heap, `inits` and `statics` kept. -/
def CutFrame (σ0 σ : State) : Prop :=
  GrowsK σ0 σ ∧ σ0.next ≤ σ.next ∧ (∀ z, z < σ0.next → σ.heap z = σ0.heap z) ∧ σ.inits = σ0.inits ∧
    σ.statics = σ0.statics

def custInv3 (v : Value) (tr : CustR) : Invariants :=
  [(24, fun _ σ0 fr σ =>
    ∃ (y0 y2 y4 y6 y8 y10 y12 y14 y16 y18 : Addr),
      fr.get 1 = some v ∧ fr.get 2 = some (.ref y0) ∧ fr.get 3 = some (.ref y2) ∧ fr.get 4 = some (.ref y4) ∧
      fr.get 5 = some (.ref y6) ∧ fr.get 6 = some (.ref y8) ∧ fr.get 7 = some (.ref y10) ∧
      fr.get 8 = some (.ref y12) ∧ fr.get 9 = some (.ref y14) ∧ fr.get 10 = some (.ref y16) ∧
      fr.get 11 = some (.ref y18) ∧
      σ.heap y0 = some (.str (zuI tr.custId.toInt 9)) ∧ σ.heap y2 = some (.str (fixStr tr.firstName 25)) ∧
      σ.heap y4 = some (.str (fixStr tr.middleName 25)) ∧ σ.heap y6 = some (.str (fixStr tr.lastName 25)) ∧
      σ.heap y8 = some (.str (fixStr tr.addrLine1 50)) ∧ σ.heap y10 = some (.str (fixStr tr.addrLine2 50)) ∧
      σ.heap y12 = some (.str (fixStr tr.addrLine3 50)) ∧ σ.heap y14 = some (.str (fixStr tr.addrStateCd 2)) ∧
      σ.heap y16 = some (.str (fixStr tr.addrCountryCd 3)) ∧ σ.heap y18 = some (.str (fixStr tr.addrZip 10)) ∧
      GrowsK σ0 σ ∧ σ0.next ≤ σ.next ∧ (∀ z, z < σ0.next → σ.heap z = σ0.heap z) ∧
      σ.inits = σ0.inits ∧ σ.statics = σ0.statics),
   (42, fun _ σ0 fr σ =>
    ∃ (y0 y2 y4 y6 y8 y10 y12 y14 y16 y18 y20 y22 y24 y25 y27 y29 y31 y33 y34 : Addr)
      (s0 s2 s4 s6 s8 s10 s12 s14 s16 s18 s20 s22 s24 s25 s27 s29 s31 s33 s34 : JStr),
      fr.get 2 = some (.ref y0) ∧ fr.get 3 = some (.ref y2) ∧ fr.get 4 = some (.ref y4) ∧
      fr.get 5 = some (.ref y6) ∧ fr.get 6 = some (.ref y8) ∧ fr.get 7 = some (.ref y10) ∧
      fr.get 8 = some (.ref y12) ∧ fr.get 9 = some (.ref y14) ∧ fr.get 10 = some (.ref y16) ∧
      fr.get 11 = some (.ref y18) ∧ fr.get 12 = some (.ref y20) ∧ fr.get 13 = some (.ref y22) ∧
      fr.get 14 = some (.ref y24) ∧ fr.get 15 = some (.ref y25) ∧ fr.get 16 = some (.ref y27) ∧
      fr.get 17 = some (.ref y29) ∧ fr.get 18 = some (.ref y31) ∧ fr.get 19 = some (.ref y33) ∧
      fr.get 20 = some (.ref y34) ∧
      σ.heap y0 = some (.str s0) ∧ σ.heap y2 = some (.str s2) ∧ σ.heap y4 = some (.str s4) ∧
      σ.heap y6 = some (.str s6) ∧ σ.heap y8 = some (.str s8) ∧ σ.heap y10 = some (.str s10) ∧
      σ.heap y12 = some (.str s12) ∧ σ.heap y14 = some (.str s14) ∧ σ.heap y16 = some (.str s16) ∧
      σ.heap y18 = some (.str s18) ∧ σ.heap y20 = some (.str s20) ∧ σ.heap y22 = some (.str s22) ∧
      σ.heap y24 = some (.str s24) ∧ σ.heap y25 = some (.str s25) ∧ σ.heap y27 = some (.str s27) ∧
      σ.heap y29 = some (.str s29) ∧ σ.heap y31 = some (.str s31) ∧ σ.heap y33 = some (.str s33) ∧
      σ.heap y34 = some (.str s34) ∧
      Kept (s0 ++ (s2 ++ (s4 ++ (s6 ++ (s8 ++ (s10 ++ (s12 ++ (s14 ++ (s16 ++ (s18 ++ (s20 ++ (s22 ++ (s24 ++
        (s25 ++ (s27 ++ (s29 ++ (s31 ++ (s33 ++ s34))))))))))))))))) = custTextR tr) ∧
      GrowsK σ0 σ ∧ σ0.next ≤ σ.next ∧ (∀ z, z < σ0.next → σ.heap z = σ0.heap z) ∧
      σ.inits = σ0.inits ∧ σ.statics = σ0.statics)]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem custText_vc_some (v : Value) (tr : CustR) :
    MethodVC Gen.prog txtCallees.env 0 custTextRef (custTextSpecG v (some tr)) (custInv3 v tr) 160 := by
  refine ⟨_, rfl, fun args σ0 hpre => ⟨?_, ?_⟩⟩
  · obtain ⟨h0, ⟨x, hv, fs, hx, ⟨g1, b1⟩, ⟨a2, g2, h2, l2⟩, ⟨a3, g3, h3, l3⟩, ⟨a4, g4, h4, l4⟩,
      ⟨a5, g5, h5, l5⟩, ⟨a6, g6, h6, l6⟩, ⟨a7, g7, h7, l7⟩, ⟨a8, g8, h8, l8⟩, ⟨a9, g9, h9, l9⟩,
      ⟨a10, g10, h10, l10⟩, -, -, -, -, -, -, -, -, -⟩, hI⟩ := hpre
    simp only [custTextSpecG, Spec.of, custTextO, custInv3]
    jvc [ite_nat_ne, txtCallees, fixSig, spacesSig, zuSig, zsSig, fixSpec, spacesSpec, zuSpec, zsSpec,
      grows_split, StrOk, argText, strOf, valueOfObj_str_alloc]
    all_goals first | exact growsK_of (by txt_grows) | simp only [custTextR, zuI, zsI_eq, List.append_assoc]
  · simp only [custInv3, Invariants.inst, List.map_cons, List.map_nil, List.mem_cons, List.mem_singleton,
      forall_eq_or_imp, forall_eq]
    refine ⟨?_, ?_, fun a ha => by simp at ha⟩
    · intro fr σ hinv
      obtain ⟨h0, ⟨x, hv, fs, hx, -, -, -, -, -, -, -, -, -, -, ⟨a11, g11, h11, l11⟩, ⟨a12, g12, h12, l12⟩,
        ⟨g13, b13⟩, ⟨a14, g14, h14, l14⟩, ⟨a15, g15, h15, l15⟩, ⟨a16, g16, h16, l16⟩, ⟨a17, g17, h17, l17⟩,
        ⟨g18, b18⟩, ⟨a19, g19, h19, l19⟩⟩, hI⟩ := hpre
      obtain ⟨y0, y2, y4, y6, y8, y10, y12, y14, y16, y18, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11,
        k0, k2, k4, k6, k8, k10, k12, k14, k16, k18, hgk, hnx, hfr, hin, hst⟩ := hinv
      simp only [custTextSpecG, Spec.of, custTextO]
      jvc [ite_nat_ne, txtCallees, fixSig, spacesSig, zuSig, zsSig, fixSpec, spacesSpec, zuSpec, zsSpec,
        grows_split, StrOk, argText, strOf, valueOfObj_str_alloc]
      all_goals first | exact growsK_of (by txt_grows) | exact Kept.intro (by simp only [custTextR, zuI, zsI_eq, List.append_assoc]) | simp only [custTextR, zuI, zsI_eq, List.append_assoc]
    · intro fr σ hinv
      obtain ⟨h0, -, hI⟩ := hpre
      obtain ⟨y0, y2, y4, y6, y8, y10, y12, y14, y16, y18, y20, y22, y24, y25, y27, y29, y31, y33, y34,
        s0, s2, s4, s6, s8, s10, s12, s14, s16, s18, s20, s22, s24, s25, s27, s29, s31, s33, s34,
        f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19, f20,
        k0, k2, k4, k6, k8, k10, k12, k14, k16, k18, k20, k22, k24, k25, k27, k29, k31, k33, k34,
        hk, hgk, hnx, hfr, hin, hst⟩ := hinv
      simp only [custTextSpecG, Spec.of, custTextO]
      jvc [ite_nat_ne, txtCallees, fixSig, spacesSig, zuSig, zsSig, fixSpec, spacesSpec, zuSpec, zsSpec,
        grows_split, StrOk, argText, strOf, valueOfObj_str_alloc]
      all_goals first | exact growsK_of (by txt_grows) | (simpa only [List.append_assoc] using Kept.elim hk) | simp only [custTextR, zuI, zsI_eq, List.append_assoc]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem custText_vc_none (v : Value) :
    MethodVC Gen.prog txtCallees.env 0 custTextRef (custTextSpecG v none) [] 40 := by
  refine ⟨_, rfl, fun args σ0 hpre => ⟨?_, fun p hp => by simp [Invariants.inst] at hp⟩⟩
  obtain ⟨h0, hv, hI⟩ := hpre
  simp only [CustAtN] at hv
  simp only [custTextSpecG, Spec.of, custTextO]
  jvc [ite_nat_ne, txtCallees, fixSig, spacesSig, zuSig, zsSig, fixSpec, spacesSpec, zuSpec, zsSpec,
    grows_split, StrOk, argText, strOf, valueOfObj_str_alloc]
  all_goals first | exact growsK_of (by txt_grows) | simp only [custTextR, zuI, zsI_eq, List.append_assoc]

theorem custText_sat (hV : Valid Gen.prog txtCallees.env) : Sat Gen.prog custTextRef custTextSpec := by
  have hG : ∀ v t, Sat Gen.prog custTextRef (custTextSpecG v t) := by
    intro v t
    cases t with
    | none => exact MethodVC.sat_of_valid hV (custText_vc_none v)
    | some tr => exact MethodVC.sat_of_valid hV (custText_vc_some v tr)
  intro args σ o hpre hm
  obtain ⟨v, t, h0, h1, h2⟩ := hpre
  have hG0 := hG v t args σ o ⟨h0, h1, h2⟩ hm
  cases o with
  | normal r σ' =>
    intro v' t' g0 g1
    rw [h0] at g0
    obtain rfl : v = v' := by simpa using g0
    exact hG v t' args σ (.normal r σ') ⟨h0, g1, h2⟩ hm
  | exc e σ' => exact hG0.elim
  | wrong msg => exact hG0.elim

end EquivLean.Modernize.Cbstm03a.Java.Txt

#print axioms EquivLean.Modernize.Cbstm03a.Java.Txt.custText_vc_some
#print axioms EquivLean.Modernize.Cbstm03a.Java.Txt.custText_vc_none
#print axioms EquivLean.Modernize.Cbstm03a.Java.Txt.custText_sat
