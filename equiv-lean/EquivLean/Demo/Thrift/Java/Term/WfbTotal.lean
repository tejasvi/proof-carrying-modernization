-- Termination package by JimpleLean's session: TermT4/WfbTotal.lean (sha256 81bc0880f5abd179...); only the module root renamed.
import EquivLean.Demo.Thrift.Java.Term.Callee
import EquivLean.Demo.Thrift.Java.Term.Wi16Total
import EquivLean.Demo.Thrift.Java.Term.WfbT

/-!
# Thrift → Java (T4): `writeFieldBeginInternal(TField, byte)` terminates, and is totally correct

From `wfb_body` and its thin twin (`TermVC.of_thinX` with the callee premises `gctX`), against `Γ4`
(`writeByteDirect(byte)`, `writeI16(short)`, `getCompactType(byte)`, the varint methods, the transport),
the transport contracts and `TransportTerm`. The long form makes a protocol call after another, so the
premise is `TRepConc`. The E theorem and the named inputs of the table (rows W1, W2) get total versions.
-/

open Jimple

namespace EquivLean.Demo.Thrift.Java

/-- The contracts the field header writer uses terminate (`getCompactType`'s has no input). -/
theorem Γ4_term (R : TRep) {P : Program} (hF : Contains P [cpC, tpC, ttC, tpeC, teC, twC, trC, tfC])
    (hV : Valid P (tContracts R).env) (hn : NoRedeclW P) (hT : TransportTerm P R) (hR : TRepConc P R) :
    ∀ sig S, Γ4 P R sig = some S → ContractTerm P sig (S.strengthen (gctX sig)) := by
  obtain ⟨hn1, hn2, hn3, hn4⟩ := hn
  have hF7 := contains_sub hF mem8_of_mem7
  have hcp : P.findClass cpCls = some cpC := hF.2 cpC (by simp)
  have htp : P.findClass tpCls = some tpC := hF.2 tpC (by simp)
  have hO : P.findClass "java.lang.Object" = none := findClass_of_noShadow hF.1 (by decide)
  intro sig S hS
  unfold Γ4 at hS
  by_cases e1 : sig = wbdSig
  · rw [if_pos e1] at hS
    cases hS
    subst e1
    exact contractTerm_cp hcp htp hO rfl rfl rfl (by decide)
      (fun args σ hp => wbdA_termR R (contains_sub hF mem8_of_mem3) hV hT hR args σ hp.1) hn1
  · rw [if_neg e1] at hS
    by_cases e2 : sig = wi16Sig
    · rw [if_pos e2] at hS
      cases hS
      subst e2
      exact contractTerm_cp hcp htp hO rfl rfl rfl (by decide)
        (fun args σ hp => wi16A_termR R hF7 hV hn3 hn4 hT hR args σ hp.1) hn2
    · rw [if_neg e2] at hS
      by_cases e3 : sig = gctSig
      · rw [if_pos e3] at hS
        cases hS
        exact contractTerm_false fun _ _ hp => (hp.1 : False)
      · rw [if_neg e3] at hS
        exact ContractTerm.mono (Γ2_term_noX R hF7 hV hn3 hn4 hT hR sig S hS)
          fun _ _ hp => ⟨hp.1, trivial⟩

theorem wfb_termI (R : TRep) {P : Program} (hF : Contains P [cpC, tpC, ttC, tpeC, teC, twC, trC, tfC])
    (hV : Valid P (tContracts R).env) (hn : NoRedeclW P) (hT : TransportTerm P R) (hR : TRepConc P R) :
    ∀ args σ, (wfbSpecI P R).pre args σ → MTerm P wfbRef args σ :=
  TermVC.mterm (rank := fun _ => 0) (r := 1) (Valid.strengthen gctX (valid_Γ4 R hF hV hn))
    (SpecEnv.strengthen_term (Γ4_term R hF hV hn hT hR) _ _)
    (TermVC.of_thinX (SpecEnv.strengthen_below_const _ _ _ (by decide)) (wfb_body R P hF)
      (wfb_thin R P hF))

/-- **`writeFieldBeginInternal(f, ty)`, total correctness.** -/
theorem wfb_total (R : TRep) {P : Program} (hF : Contains P [cpC, tpC, ttC, tpeC, teC, twC, trC, tfC])
    (hV : Valid P (tContracts R).env) (hn : NoRedeclW P) (hT : TransportTerm P R) (hR : TRepConc P R) :
    ∀ args σ, (wfbSpecI P R).pre args σ →
      (∃ o, MExec P wfbRef args σ o) ∧ ∀ o, MExec P wfbRef args σ o → (wfbSpecI P R).post args σ o :=
  fun args σ hpre => ⟨(wfb_termI R hF hV hn hT hR args σ hpre).run,
    fun o ho => wfb_sat R hF hV hn args σ o hpre ho⟩

/-- `writeFieldBeginInternal(f, ty)` terminates on the premises of `wfb_E`. -/
theorem wfb_term_at (R : TRep) {P : Program}
    (hF : Contains P [cpC, tpC, ttC, tpeC, teC, twC, trC, tfC]) (hV : Valid P (tContracts R).env)
    (hn : NoRedeclW P) (hT : TransportTerm P R) (hR : TRepConc P R) {σ : State} {p t tmp f : Addr}
    {fs ffs : List (FieldKey × Value)} {ty id last : I32}
    (hCP : CPAt P R σ p t tmp) (hp : σ.heap p = some (.plain cpCls fs))
    (hlast : Fields.get fs (cpCls, "lastFieldId_") = some (.int last))
    (hf : σ.heap f = some (.plain tfCls ffs)) (hid : Fields.get ffs (tfCls, "id") = some (.int id))
    (hft : f ≠ t) (hftm : f ≠ tmp) (hfp : f ≠ p) (hfo : ¬ R.owns σ t f)
    (hids : JInt.toShort id = id) (hls : JInt.toShort last = last) (hty : ty.toNat < 16) :
    MTerm P wfbRef [.ref p, .ref f, .int ty] σ :=
  wfb_termI R hF hV hn hT hR _ σ
    ⟨p, t, tmp, f, ty, id, last, rfl, hCP, CPAtH.intro hCP, ⟨ffs, hf, hid⟩, ⟨fs, hp, hlast⟩,
      Hide.intro ⟨hids, hls, hty⟩, hft, hftm, hfp, hfo⟩

/-- **E for the field header, total**: `writeFieldBeginInternal(f, ty)` terminates, and every run
    returns normally after appending `fieldHeader last id ty` (`wfb_E`). -/
theorem wfb_E_total (R : TRep) {P : Program}
    (hF : Contains P [cpC, tpC, ttC, tpeC, teC, twC, trC, tfC]) (hV : Valid P (tContracts R).env)
    (hn : NoRedeclW P) (hT : TransportTerm P R) (hR : TRepConc P R) {σ : State} {p t tmp f : Addr}
    {fs ffs : List (FieldKey × Value)} {ty id last : I32}
    (hCP : CPAt P R σ p t tmp) (hp : σ.heap p = some (.plain cpCls fs))
    (hlast : Fields.get fs (cpCls, "lastFieldId_") = some (.int last))
    (hf : σ.heap f = some (.plain tfCls ffs)) (hid : Fields.get ffs (tfCls, "id") = some (.int id))
    (hft : f ≠ t) (hftm : f ≠ tmp) (hfp : f ≠ p) (hfo : ¬ R.owns σ t f)
    (hids : JInt.toShort id = id) (hls : JInt.toShort last = last) (hty : ty.toNat < 16) :
    (∃ o, MExec P wfbRef [.ref p, .ref f, .int ty] σ o) ∧
    ∀ o, MExec P wfbRef [.ref p, .ref f, .int ty] σ o →
    ∃ σ', o = .normal none σ' ∧
      R.sink σ' t = R.sink σ t ++ Spec.fieldHeader last.toInt id.toInt ty.toNat ∧
      R.src σ' t = R.src σ t ∧ CPAt P R σ' p t tmp ∧ LastAt σ' p id ∧ WFrame R σ σ' p t tmp :=
  ⟨(wfb_term_at R hF hV hn hT hR hCP hp hlast hf hid hft hftm hfp hfo hids hls hty).run,
    fun _ hm => wfb_E R hF hV hn hCP hp hlast hf hid hft hftm hfp hfo hids hls hty hm⟩

/-! ## The named inputs (rows W1, W2), total -/

/-- **W1, `exDelta15`, total**: `writeFieldBeginInternal(f, 5)` terminates, and every run appends the one
    byte `0xF5` (`wfb_exDelta15`). -/
theorem wfb_exDelta15_total (R : TRep) {P : Program}
    (hF : Contains P [cpC, tpC, ttC, tpeC, teC, twC, trC, tfC]) (hV : Valid P (tContracts R).env)
    (hn : NoRedeclW P) (hT : TransportTerm P R) (hR : TRepConc P R) {σ : State} {p t tmp f : Addr}
    {fs ffs : List (FieldKey × Value)}
    (hCP : CPAt P R σ p t tmp) (hp : σ.heap p = some (.plain cpCls fs))
    (hlast : Fields.get fs (cpCls, "lastFieldId_") = some (.int 0#32))
    (hf : σ.heap f = some (.plain tfCls ffs)) (hid : Fields.get ffs (tfCls, "id") = some (.int 15#32))
    (hft : f ≠ t) (hftm : f ≠ tmp) (hfp : f ≠ p) (hfo : ¬ R.owns σ t f) :
    (∃ o, MExec P wfbRef [.ref p, .ref f, .int 5#32] σ o) ∧
    ∀ o, MExec P wfbRef [.ref p, .ref f, .int 5#32] σ o →
    Spec.fieldHeader Spec.exDelta15.last Spec.exDelta15.id Spec.exDelta15.ty = [0xF5] ∧
    ∃ σ', o = .normal none σ' ∧ R.sink σ' t = R.sink σ t ++ [0xF5] ∧ R.src σ' t = R.src σ t ∧
      LastAt σ' p 15#32 ∧ CPAt P R σ' p t tmp :=
  ⟨(wfb_term_at R hF hV hn hT hR hCP hp hlast hf hid hft hftm hfp hfo (by decide) (by decide)
      (by decide)).run,
    fun _ hm => wfb_exDelta15 R hF hV hn hCP hp hlast hf hid hft hftm hfp hfo hm⟩

/-- **W2, `exI16Overflow`, total**: `writeFieldBeginInternal(f, 5)` terminates, and every run appends
    `[0x05, 0xFF, 0xFF, 0x03]` (`wfb_exI16Overflow`). -/
theorem wfb_exI16Overflow_total (R : TRep) {P : Program}
    (hF : Contains P [cpC, tpC, ttC, tpeC, teC, twC, trC, tfC]) (hV : Valid P (tContracts R).env)
    (hn : NoRedeclW P) (hT : TransportTerm P R) (hR : TRepConc P R) {σ : State} {p t tmp f : Addr}
    {fs ffs : List (FieldKey × Value)}
    (hCP : CPAt P R σ p t tmp) (hp : σ.heap p = some (.plain cpCls fs))
    (hlast : Fields.get fs (cpCls, "lastFieldId_") = some (.int 32767#32))
    (hf : σ.heap f = some (.plain tfCls ffs))
    (hid : Fields.get ffs (tfCls, "id") = some (.int (BitVec.ofInt 32 (-32768))))
    (hft : f ≠ t) (hftm : f ≠ tmp) (hfp : f ≠ p) (hfo : ¬ R.owns σ t f) :
    (∃ o, MExec P wfbRef [.ref p, .ref f, .int 5#32] σ o) ∧
    ∀ o, MExec P wfbRef [.ref p, .ref f, .int 5#32] σ o →
    Spec.fieldHeader Spec.exI16Overflow.last Spec.exI16Overflow.id Spec.exI16Overflow.ty =
      [0x05, 0xFF, 0xFF, 0x03] ∧
    ∃ σ', o = .normal none σ' ∧ R.sink σ' t = R.sink σ t ++ [0x05, 0xFF, 0xFF, 0x03] ∧
      R.src σ' t = R.src σ t ∧ LastAt σ' p (BitVec.ofInt 32 (-32768)) ∧ CPAt P R σ' p t tmp :=
  ⟨(wfb_term_at R hF hV hn hT hR hCP hp hlast hf hid hft hftm hfp hfo (by decide) (by decide)
      (by decide)).run,
    fun _ hm => wfb_exI16Overflow R hF hV hn hCP hp hlast hf hid hft hftm hfp hfo hm⟩

end EquivLean.Demo.Thrift.Java

#print axioms EquivLean.Demo.Thrift.Java.wfb_total
#print axioms EquivLean.Demo.Thrift.Java.wfb_E_total
#print axioms EquivLean.Demo.Thrift.Java.wfb_exDelta15_total
#print axioms EquivLean.Demo.Thrift.Java.wfb_exI16Overflow_total
