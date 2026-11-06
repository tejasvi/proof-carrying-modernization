import EquivLean.Demo.Thrift.Java.Wfb
import EquivLean.Demo.Thrift.Java.Wbd
import EquivLean.Demo.Thrift.Java.Wi16

/-!
# Thrift → Java (T4): the compact field header writer `writeFieldBeginInternal(field, ty)` (E)

Under the transport contracts and `NoRedeclW` (no application subclass of `TCompactProtocol`
redeclares `writeByteDirect(byte)`, `writeI16(short)`, `readVarint32()`, `writeVarint32(int)`).
The type override `ty` is a compact type nibble; the override `-1` (`writeFieldBegin`, which
looks the nibble up in the static table `ttypeToCompactType`) is not covered.
-/

open Jimple

namespace EquivLean.Demo.Thrift.Java

/-- No application subclass of `TCompactProtocol` redeclares the methods the writer calls. -/
def NoRedeclW (P : Program) : Prop :=
  NoRedecl P wbdSig wbdRef ∧ NoRedecl P wi16Sig wi16Ref ∧ NoRedecl P rv32Sig rv32Ref ∧
  NoRedecl P wv32Sig wv32Ref

theorem wbdA_sat (R : TRep) {P : Program} (hF : Contains P [cpC, tpC, ttC])
    (hV : Valid P (tContracts R).env) : Sat P wbdRef (wbdSpecA P R) := by
  have hI := BodyVCP.sat (wbd_body R) hF hV
  intro args σ o hpre hm
  obtain ⟨p, t, tmp, b, hargs, hCP⟩ := hpre
  exact hI args σ o ⟨p, t, tmp, b, hargs, hCP, CPAtH.intro hCP, classOK_of_cpAt hCP⟩ hm

theorem wi16A_sat (R : TRep) {P : Program} (hF : Contains P [cpC, tpC, ttC, tpeC, teC, twC, trC])
    (hV2 : Valid P (Γ2 P R)) : Sat P wi16Ref (wi16SpecA P R) := by
  have hI := BodyVCP.sat (wi16_body R) hF hV2
  intro args σ o hpre hm
  obtain ⟨p, t, tmp, i, hargs, hCP⟩ := hpre
  exact hI args σ o ⟨p, t, tmp, i, hargs, hCP, CPAtH.intro hCP⟩ hm

/-- The contracts the writer uses. -/
theorem valid_Γ4 (R : TRep) {P : Program} (hF : Contains P [cpC, tpC, ttC, tpeC, teC, twC, trC, tfC])
    (hV : Valid P (tContracts R).env) (hn : NoRedeclW P) : Valid P (Γ4 P R) := by
  obtain ⟨hn1, hn2, hn3, hn4⟩ := hn
  have hF7 := contains_sub hF mem8_of_mem7
  have hcp : P.findClass cpCls = some cpC := hF.2 cpC (by simp)
  have htp : P.findClass tpCls = some tpC := hF.2 tpC (by simp)
  have hO : P.findClass "java.lang.Object" = none := findClass_of_noShadow hF.1 (by decide)
  have hV2 := valid_Γ2 R hF7 hV hn3 hn4
  intro sig S hS
  unfold Γ4 at hS
  by_cases h1 : sig = wbdSig
  · rw [if_pos h1] at hS
    cases hS
    subst h1
    exact contractOK_cp hcp htp hO rfl rfl rfl (by decide)
      (wbdA_sat R (contains_sub hF mem8_of_mem3) hV) hn1
  · rw [if_neg h1] at hS
    by_cases h2 : sig = wi16Sig
    · rw [if_pos h2] at hS
      cases hS
      subst h2
      exact contractOK_cp hcp htp hO rfl rfl rfl (by decide) (wi16A_sat R hF7 hV2) hn2
    · rw [if_neg h2] at hS
      by_cases h3 : sig = gctSig
      · rw [if_pos h3] at hS
        cases hS
        exact ⟨fun _ _ _ _ _ hpre _ => (hpre : False).elim,
          fun _ _ _ _ _ _ _ hpre _ => (hpre : False).elim⟩
      · rw [if_neg h3] at hS
        exact hV2 sig S hS

theorem wfb_sat (R : TRep) {P : Program} (hF : Contains P [cpC, tpC, ttC, tpeC, teC, twC, trC, tfC])
    (hV : Valid P (tContracts R).env) (hn : NoRedeclW P) : Sat P wfbRef (wfbSpecI P R) :=
  MethodVC.sat_of_valid (valid_Γ4 R hF hV hn) (wfb_body R P hF)

/-- **E for the field header**: `writeFieldBeginInternal(f, ty)` (`f` a `TField` with id `id`,
`lastFieldId_ = last`, both `short`s, `ty` a compact type nibble) returns normally after appending
`fieldHeader last id ty`, and sets `lastFieldId_ = id`. -/
theorem wfb_E (R : TRep) {P : Program}
    (hF : Contains P [cpC, tpC, ttC, tpeC, teC, twC, trC, tfC]) (hV : Valid P (tContracts R).env)
    (hn : NoRedeclW P) {σ : State} {p t tmp f : Addr} {fs ffs : List (FieldKey × Value)}
    {ty id last : I32} {o : Outcome}
    (hCP : CPAt P R σ p t tmp) (hp : σ.heap p = some (.plain cpCls fs))
    (hlast : Fields.get fs (cpCls, "lastFieldId_") = some (.int last))
    (hf : σ.heap f = some (.plain tfCls ffs)) (hid : Fields.get ffs (tfCls, "id") = some (.int id))
    (hft : f ≠ t) (hftm : f ≠ tmp) (hfp : f ≠ p) (hfo : ¬ R.owns σ t f)
    (hids : JInt.toShort id = id) (hls : JInt.toShort last = last) (hty : ty.toNat < 16)
    (hm : MExec P wfbRef [.ref p, .ref f, .int ty] σ o) :
    ∃ σ', o = .normal none σ' ∧
      R.sink σ' t = R.sink σ t ++ Spec.fieldHeader last.toInt id.toInt ty.toNat ∧
      R.src σ' t = R.src σ t ∧ CPAt P R σ' p t tmp ∧ LastAt σ' p id ∧ WFrame R σ σ' p t tmp := by
  have hpost := wfb_sat R hF hV hn [.ref p, .ref f, .int ty] σ o
    ⟨p, t, tmp, f, ty, id, last, rfl, hCP, CPAtH.intro hCP, ⟨ffs, hf, hid⟩, ⟨fs, hp, hlast⟩,
      Hide.intro ⟨hids, hls, hty⟩, hft, hftm, hfp, hfo⟩ hm
  obtain ⟨_, _, _, _, hp', htr, hte, _⟩ := hCP
  rw [hp] at hp'
  simp only [Option.some.injEq, Obj.plain.injEq, true_and] at hp'
  subst hp'
  cases o with
  | normal r σ' =>
    simp only [wfbSpecI, Spec.of] at hpost
    unfold wfbN at hpost
    obtain ⟨hr, hk, hs, hC, hL, hW⟩ := hpost p t tmp f _ ffs ty id last rfl hp htr hte hlast hf hid
    subst hr
    exact ⟨σ', rfl, hk, hs, hC, hL, hW⟩
  | exc e σ' => simp only [wfbSpecI, Spec.of] at hpost
  | wrong msg => simp only [wfbSpecI, Spec.of] at hpost

/-- **`exDelta15`** (previous id 0, id 15, type I32 = 5): Java takes the short form (`id > last` and
`id - last ≤ 15`, statements 12 and 18) and appends the one byte `0xF5`, as specified. -/
theorem wfb_exDelta15 (R : TRep) {P : Program}
    (hF : Contains P [cpC, tpC, ttC, tpeC, teC, twC, trC, tfC]) (hV : Valid P (tContracts R).env)
    (hn : NoRedeclW P) {σ : State} {p t tmp f : Addr} {fs ffs : List (FieldKey × Value)} {o : Outcome}
    (hCP : CPAt P R σ p t tmp) (hp : σ.heap p = some (.plain cpCls fs))
    (hlast : Fields.get fs (cpCls, "lastFieldId_") = some (.int 0#32))
    (hf : σ.heap f = some (.plain tfCls ffs)) (hid : Fields.get ffs (tfCls, "id") = some (.int 15#32))
    (hft : f ≠ t) (hftm : f ≠ tmp) (hfp : f ≠ p) (hfo : ¬ R.owns σ t f)
    (hm : MExec P wfbRef [.ref p, .ref f, .int 5#32] σ o) :
    Spec.fieldHeader Spec.exDelta15.last Spec.exDelta15.id Spec.exDelta15.ty = [0xF5] ∧
    ∃ σ', o = .normal none σ' ∧ R.sink σ' t = R.sink σ t ++ [0xF5] ∧ R.src σ' t = R.src σ t ∧
      LastAt σ' p 15#32 ∧ CPAt P R σ' p t tmp := by
  obtain ⟨σ', ho, hk, hs, hC, hL, -⟩ := wfb_E R hF hV hn hCP hp hlast hf hid hft hftm hfp hfo
    (by decide) (by decide) (by decide) hm
  refine ⟨Spec.fieldHeader_exDelta15, σ', ho, ?_, hs, hL, hC⟩
  rw [hk]
  exact congrArg _ Spec.fieldHeader_exDelta15

/-- **`exI16Overflow`** (previous id 32767, id −32768, type I32 = 5): Java computes `id - last` in
`int` (statements 10–12: `(int) id <= (int) last`), −65535, takes the long form and appends
`[0x05, 0xFF, 0xFF, 0x03]`, as specified. -/
theorem wfb_exI16Overflow (R : TRep) {P : Program}
    (hF : Contains P [cpC, tpC, ttC, tpeC, teC, twC, trC, tfC]) (hV : Valid P (tContracts R).env)
    (hn : NoRedeclW P) {σ : State} {p t tmp f : Addr} {fs ffs : List (FieldKey × Value)} {o : Outcome}
    (hCP : CPAt P R σ p t tmp) (hp : σ.heap p = some (.plain cpCls fs))
    (hlast : Fields.get fs (cpCls, "lastFieldId_") = some (.int 32767#32))
    (hf : σ.heap f = some (.plain tfCls ffs))
    (hid : Fields.get ffs (tfCls, "id") = some (.int (BitVec.ofInt 32 (-32768))))
    (hft : f ≠ t) (hftm : f ≠ tmp) (hfp : f ≠ p) (hfo : ¬ R.owns σ t f)
    (hm : MExec P wfbRef [.ref p, .ref f, .int 5#32] σ o) :
    Spec.fieldHeader Spec.exI16Overflow.last Spec.exI16Overflow.id Spec.exI16Overflow.ty =
      [0x05, 0xFF, 0xFF, 0x03] ∧
    ∃ σ', o = .normal none σ' ∧ R.sink σ' t = R.sink σ t ++ [0x05, 0xFF, 0xFF, 0x03] ∧
      R.src σ' t = R.src σ t ∧ LastAt σ' p (BitVec.ofInt 32 (-32768)) ∧ CPAt P R σ' p t tmp := by
  obtain ⟨σ', ho, hk, hs, hC, hL, -⟩ := wfb_E R hF hV hn hCP hp hlast hf hid hft hftm hfp hfo
    (by decide) (by decide) (by decide) hm
  refine ⟨Spec.fieldHeader_exI16Overflow, σ', ho, ?_, hs, hL, hC⟩
  rw [hk]
  exact congrArg _ Spec.fieldHeader_exI16Overflow

end EquivLean.Demo.Thrift.Java
