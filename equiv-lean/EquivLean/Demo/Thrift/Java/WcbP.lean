import EquivLean.Demo.Thrift.Java.Wcb

/-!
# Thrift → Java (T4): the compact list/set header writer `writeCollectionBegin(elemType, size)` (E)

Under the transport contracts and `NoRedeclW` (no application subclass of `TCompactProtocol`
redeclares `writeByteDirect(byte)`, `writeI16(short)`, `readVarint32()`, `writeVarint32(int)`).
`elemType` is a TType with a compact type nibble (`Spec.compactType`), `size ≥ 0`, and
`TCompactProtocol` is initialized with its static table `ttypeToCompactType` as its static
initializer leaves it (`ctTable`).
-/

open Jimple

namespace EquivLean.Demo.Thrift.Java

/-- The contracts the list/set header writer uses. -/
theorem valid_Γ5 (R : TRep) {P : Program} (hF : Contains P [cpC, tpC, ttC, tpeC, teC, twC, trC, tfC])
    (hV : Valid P (tContracts R).env) (hn : NoRedeclW P) : Valid P (Γ5 P R) := by
  obtain ⟨hn1, -, hn3, hn4⟩ := hn
  have hF7 := contains_sub hF mem8_of_mem7
  have hcp : P.findClass cpCls = some cpC := hF.2 cpC (by simp)
  have htp : P.findClass tpCls = some tpC := hF.2 tpC (by simp)
  have hO : P.findClass "java.lang.Object" = none := findClass_of_noShadow hF.1 (by decide)
  have hV2 := valid_Γ2 R hF7 hV hn3 hn4
  intro sig S hS
  unfold Γ5 at hS
  by_cases h1 : sig = wbdSig
  · rw [if_pos h1] at hS
    cases hS
    subst h1
    exact contractOK_cp hcp htp hO rfl rfl rfl (by decide)
      (wbdA_sat R (contains_sub hF mem8_of_mem3) hV) hn1
  · rw [if_neg h1] at hS
    exact hV2 sig S hS

theorem wcb_sat (R : TRep) {P : Program} (hF : Contains P [cpC, tpC, ttC, tpeC, teC, twC, trC, tfC])
    (hV : Valid P (tContracts R).env) (hn : NoRedeclW P) : Sat P wcbRef (wcbSpecI P R) :=
  MethodVC.sat_of_valid (valid_Γ5 R hF hV hn) (wcb_body R P hF)

/-- **E for the list/set header**: `writeCollectionBegin(elemType, size)` (`elemType` a TType with
compact type nibble `c`, `size ≥ 0`) returns normally after appending `Spec.listHeader size c`:
the byte `size << 4 | c` for `size ≤ 14`, else the byte `0xF0 | c` and the varint of `size`. -/
theorem wcb_E (R : TRep) {P : Program}
    (hF : Contains P [cpC, tpC, ttC, tpeC, teC, twC, trC, tfC]) (hV : Valid P (tContracts R).env)
    (hn : NoRedeclW P) {σ : State} {p t tmp ta : Addr} {et sz : I32} {c : Nat} {o : Outcome}
    (hCP : CPAt P R σ p t tmp) (hct : Spec.compactType et.toNat = some c) (hsz : 0 ≤ sz.toInt)
    (hinit : σ.initOf cpCls = .done)
    (hst : σ.static (cpCls, "ttypeToCompactType") = some (.ref ta))
    (hta : σ.heap ta = some (.array (.prim .byte) ctTable))
    (hm : MExec P wcbRef [.ref p, .int et, .int sz] σ o) :
    ∃ σ', o = .normal none σ' ∧ R.sink σ' t = R.sink σ t ++ Spec.listHeader sz.toNat c ∧
      R.src σ' t = R.src σ t ∧ CPAt P R σ' p t tmp ∧ PFrame R σ σ' t tmp := by
  have hle := compactType_le _ _ hct
  have hi : et.toInt = et.toNat := by
    have e := BitVec.toInt_eq_toNat_cond et
    rw [if_pos (by omega)] at e
    exact e
  have hix : et.toInt.toNat = et.toNat := by omega
  have hget := ctTable_get _ _ hct
  rw [← hix] at hget
  have hpost := wcb_sat R hF hV hn [.ref p, .int et, .int sz] σ o
    ⟨p, t, tmp, ta, et, sz, c, rfl, hCP, CPAtH.intro hCP, hsz, by omega,
      by rw [ctTable_length]; omega, hct, Spec.compactType_lt hct, hinit, hst, hta, hget,
      List.getElem?_eq_some_iff.mp hget⟩ hm
  obtain ⟨fs, -, -, -, hp, htr, hte, -⟩ := hCP
  cases o with
  | normal r σ' =>
    simp only [wcbSpecI, Spec.of] at hpost
    unfold wcbN at hpost
    obtain ⟨hr, hk, hs, hC, hW⟩ := hpost p t tmp fs et sz c rfl hp htr hte hct
    subst hr
    exact ⟨σ', rfl, hk, hs, hC, hW⟩
  | exc e σ' => simp only [wcbSpecI, Spec.of] at hpost
  | wrong msg => simp only [wcbSpecI, Spec.of] at hpost

end EquivLean.Demo.Thrift.Java
