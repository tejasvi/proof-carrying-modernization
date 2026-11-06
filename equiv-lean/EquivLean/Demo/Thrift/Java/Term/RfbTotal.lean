-- Termination package by JimpleLean's session: TermT4/RfbTotal.lean (sha256 3535fe407f68e020...); only the module root renamed.
import EquivLean.Demo.Thrift.Java.Term.Callee
import EquivLean.Demo.Thrift.Java.Term.RfiTotal
import EquivLean.Demo.Thrift.Java.Term.RfbT
import EquivLean.Demo.Thrift.Java.FhRD

/-!
# Thrift → Java (T4): `readFieldBegin()` terminates, and is totally correct

From `rfb_body` and its thin twin (`TermVC.of_thinX`, no extra callee premises), against `Γ3`
(`readByte()`, `getTType(byte)`, `readFieldId(byte)`, the varint methods, the transport), the transport
contracts and `TransportTerm`. `readFieldBegin()` makes a protocol call after another, so its premise is
`TRepConc` (every working transport object has a concrete class); it gives each callee's `TConc`.
The named inputs of the table (rows R1-R3) get total versions: a run exists, and every run ends as the
partial-correctness theorem states.
-/

open Jimple

namespace EquivLean.Demo.Thrift.Java

/-- The contracts `readFieldBegin()` uses terminate. -/
theorem Γ3_term (R : TRep) {P : Program} (hF : Contains P [cpC, tpC, ttC, tpeC, teC, twC, trC, tfC])
    (hV : Valid P (tContracts R).env) (hn : NoRedeclR P) (hT : TransportTerm P R) (hR : TRepConc P R) :
    ∀ sig S, Γ3 P R sig = some S → ContractTerm P sig (S.strengthen (noX sig)) := by
  obtain ⟨hnb, hng, hnf, hn1, hn2⟩ := hn
  have hF7 := contains_sub hF mem8_of_mem7
  have hcp : P.findClass cpCls = some cpC := hF.2 cpC (by simp)
  have htp : P.findClass tpCls = some tpC := hF.2 tpC (by simp)
  have hO : P.findClass "java.lang.Object" = none := findClass_of_noShadow hF.1 (by decide)
  intro sig S hS
  unfold Γ3 at hS
  by_cases e1 : sig = rbSig
  · rw [if_pos e1] at hS
    cases hS
    subst e1
    exact contractTerm_cp hcp htp hO rfl rfl rfl (by decide)
      (fun args σ hp => rbA_termR R (contains_sub hF mem8_of_mem3) hV hT hR args σ hp.1) hnb
  · rw [if_neg e1] at hS
    by_cases e2 : sig = gttSig
    · rw [if_pos e2] at hS
      cases hS
      subst e2
      exact contractTerm_cp hcp htp hO rfl rfl rfl (by decide)
        (fun args σ hp => gtt_term (contains_sub hF mem8_of_gtt) args σ hp.1) hng
    · rw [if_neg e2] at hS
      by_cases e3 : sig = rfiSig
      · rw [if_pos e3] at hS
        cases hS
        subst e3
        exact contractTerm_cp hcp htp hO rfl rfl rfl (by decide)
          (fun args σ hp => rfiA_termR R hF7 hV hn1 hn2 hT hR args σ hp.1) hnf
      · rw [if_neg e3] at hS
        exact Γ2_term_noX R hF7 hV hn1 hn2 hT hR sig S hS

theorem rfb_termI (R : TRep) {P : Program} (hF : Contains P [cpC, tpC, ttC, tpeC, teC, twC, trC, tfC])
    (hV : Valid P (tContracts R).env) (hn : NoRedeclR P) (hT : TransportTerm P R) (hR : TRepConc P R) :
    ∀ args σ, (rfbSpecI P R).pre args σ → MTerm P rfbRef args σ :=
  TermVC.mterm (rank := fun _ => 0) (r := 1) (Valid.strengthen noX (valid_Γ3 R hF hV hn))
    (SpecEnv.strengthen_term (Γ3_term R hF hV hn hT hR) _ _)
    (TermVC.of_thinX (SpecEnv.strengthen_below_const _ _ _ (by decide)) (rfb_body R P hF)
      (rfb_thin R P hF))

/-- **`readFieldBegin()` terminates** on every input of its contract, when every working transport
    object has a concrete class. -/
theorem rfb_term (R : TRep) {P : Program} (hF : Contains P [cpC, tpC, ttC, tpeC, teC, twC, trC, tfC])
    (hV : Valid P (tContracts R).env) (hn : NoRedeclR P) (hT : TransportTerm P R) (hR : TRepConc P R) :
    ∀ args σ, (rfbSpec P R).pre args σ → MTerm P rfbRef args σ := by
  intro args σ hpre
  obtain ⟨p, t, tmp, last, hargs, hCP, hL, hB, h1, h2, h3, hnib⟩ := hpre
  exact rfb_termI R hF hV hn hT hR args σ
    ⟨p, t, tmp, last, hargs, hCP, CPAtH.intro hCP, hL, hB, h1, h2, h3, hnib⟩

/-- **`readFieldBegin()`, total correctness.** -/
theorem rfb_total (R : TRep) {P : Program} (hF : Contains P [cpC, tpC, ttC, tpeC, teC, twC, trC, tfC])
    (hV : Valid P (tContracts R).env) (hn : NoRedeclR P) (hT : TransportTerm P R) (hR : TRepConc P R) :
    ∀ args σ, (rfbSpec P R).pre args σ →
      (∃ o, MExec P rfbRef args σ o) ∧ ∀ o, MExec P rfbRef args σ o → (rfbSpec P R).post args σ o :=
  fun args σ hpre => ⟨(rfb_term R hF hV hn hT hR args σ hpre).run,
    fun o ho => rfb_sat' R hF hV hn args σ o hpre ho⟩

/-- `readFieldBegin()` terminates on a header byte `u` with a known type nibble (the premises of
    `rfb_run`). -/
theorem rfb_term_at (R : TRep) {P : Program}
    (hF : Contains P [cpC, tpC, ttC, tpeC, teC, twC, trC, tfC]) (hV : Valid P (tContracts R).env)
    (hn : NoRedeclR P) (hT : TransportTerm P R) (hR : TRepConc P R) {σ : State} {p t tmp : Addr}
    {fs : List (FieldKey × Value)} {last : I32} {u : UInt8} {rest0 : Bytes}
    (hCP : CPAt P R σ p t tmp) (hp : σ.heap p = some (.plain cpCls fs))
    (hlast : Fields.get fs (cpCls, "lastFieldId_") = some (.int last)) (hB : BoolAt σ p)
    (h1 : σ.initOf tpeCls = .done) (h2 : σ.initOf cpCls = .done) (h3 : σ.initOf tfCls = .done)
    (hsrc : R.src σ t = u :: rest0) (htt : (Spec.ttypeOfCompact (u.toNat % 16)).isSome) :
    MTerm P rfbRef [.ref p] σ := by
  have hnib : NibbleOK (R.src σ t) := by
    intro u' r' h hu'
    rw [hsrc] at h
    simp only [List.cons.injEq] at h
    rw [← h.1]
    exact htt
  exact rfb_term R hF hV hn hT hR [.ref p] σ
    ⟨p, t, tmp, last, rfl, hCP, ⟨fs, hp, hlast⟩, hB, h1, h2, h3, hnib⟩

/-! ## The named inputs (rows R1-R3), total -/

/-- **R2, `exStopNibble` `[0x10]` after id 0, total**: `readFieldBegin()` terminates, and every run
    returns a new `TField` of type 0 with id 1 (`rfb_exStopNibble`). -/
theorem rfb_exStopNibble_total (R : TRep) {P : Program}
    (hF : Contains P [cpC, tpC, ttC, tpeC, teC, twC, trC, tfC]) (hV : Valid P (tContracts R).env)
    (hn : NoRedeclR P) (hT : TransportTerm P R) (hR : TRepConc P R) {σ : State} {p t tmp : Addr}
    {fs : List (FieldKey × Value)} {rest : Bytes} (hCP : CPAt P R σ p t tmp)
    (hp : σ.heap p = some (.plain cpCls fs))
    (hlast : Fields.get fs (cpCls, "lastFieldId_") = some (.int 0#32)) (hB : BoolAt σ p)
    (h1 : σ.initOf tpeCls = .done) (h2 : σ.initOf cpCls = .done) (h3 : σ.initOf tfCls = .done)
    (hsrc : R.src σ t = Spec.exStopNibble ++ rest) :
    (∃ o, MExec P rfbRef [.ref p] σ o) ∧ ∀ o, MExec P rfbRef [.ref p] σ o →
    Spec.readFieldHeader 0 Spec.exStopNibble = none ∧
    ∃ σ' r0 ffs, o = .normal (some (.ref r0)) σ' ∧ σ'.heap r0 = some (.plain tfCls ffs) ∧
      Fields.get ffs (tfCls, "type") = some (.int 0#32) ∧ Fields.get ffs (tfCls, "id") = some (.int 1#32) ∧
      R.src σ' t = rest ∧ R.sink σ' t = R.sink σ t ∧ LastAt σ' p 1#32 ∧ CPAt P R σ' p t tmp := by
  have hs : R.src σ t = (0x10 : UInt8) :: rest := by
    rw [hsrc]
    all_goals rfl
  exact ⟨(rfb_term_at R hF hV hn hT hR hCP hp hlast hB h1 h2 h3 hs (by decide)).run,
    fun _ hm => rfb_exStopNibble R hF hV hn hCP hp hlast hB h1 h2 h3 hsrc hm⟩

/-- **R1, `[0x15]` after id 32767, total**: `readFieldBegin()` terminates, and every run returns a new
    `TField` of type 8 with id −32768 (`rfb_I16Overflow_short`). -/
theorem rfb_I16Overflow_short_total (R : TRep) {P : Program}
    (hF : Contains P [cpC, tpC, ttC, tpeC, teC, twC, trC, tfC]) (hV : Valid P (tContracts R).env)
    (hn : NoRedeclR P) (hT : TransportTerm P R) (hR : TRepConc P R) {σ : State} {p t tmp : Addr}
    {fs : List (FieldKey × Value)} {rest : Bytes} (hCP : CPAt P R σ p t tmp)
    (hp : σ.heap p = some (.plain cpCls fs))
    (hlast : Fields.get fs (cpCls, "lastFieldId_") = some (.int 32767#32)) (hB : BoolAt σ p)
    (h1 : σ.initOf tpeCls = .done) (h2 : σ.initOf cpCls = .done) (h3 : σ.initOf tfCls = .done)
    (hsrc : R.src σ t = [0x15] ++ rest) :
    (∃ o, MExec P rfbRef [.ref p] σ o) ∧ ∀ o, MExec P rfbRef [.ref p] σ o →
    Spec.readFieldHeader 32767 [0x15] = none ∧
    ∃ σ' r0 ffs, o = .normal (some (.ref r0)) σ' ∧ σ'.heap r0 = some (.plain tfCls ffs) ∧
      Fields.get ffs (tfCls, "type") = some (.int 8#32) ∧
      Fields.get ffs (tfCls, "id") = some (.int (BitVec.ofInt 32 (-32768))) ∧
      R.src σ' t = rest ∧ R.sink σ' t = R.sink σ t ∧ LastAt σ' p (BitVec.ofInt 32 (-32768)) ∧
      CPAt P R σ' p t tmp := by
  have hs : R.src σ t = (0x15 : UInt8) :: rest := by
    rw [hsrc]
    all_goals rfl
  exact ⟨(rfb_term_at R hF hV hn hT hR hCP hp hlast hB h1 h2 h3 hs (by decide)).run,
    fun _ hm => rfb_I16Overflow_short R hF hV hn hCP hp hlast hB h1 h2 h3 hsrc hm⟩

/-- **R3, `exIdOutOfRange` `[0x05, 0x80, 0x80, 0x04]` after id 0, total**: `readFieldBegin()`
    terminates, and every run returns a new `TField` of type 8 with id −32768
    (`rfb_exIdOutOfRange`). -/
theorem rfb_exIdOutOfRange_total (R : TRep) {P : Program}
    (hF : Contains P [cpC, tpC, ttC, tpeC, teC, twC, trC, tfC]) (hV : Valid P (tContracts R).env)
    (hn : NoRedeclR P) (hT : TransportTerm P R) (hR : TRepConc P R) {σ : State} {p t tmp : Addr}
    {fs : List (FieldKey × Value)} {rest : Bytes} (hCP : CPAt P R σ p t tmp)
    (hp : σ.heap p = some (.plain cpCls fs))
    (hlast : Fields.get fs (cpCls, "lastFieldId_") = some (.int 0#32)) (hB : BoolAt σ p)
    (h1 : σ.initOf tpeCls = .done) (h2 : σ.initOf cpCls = .done) (h3 : σ.initOf tfCls = .done)
    (hsrc : R.src σ t = Spec.exIdOutOfRange ++ rest) :
    (∃ o, MExec P rfbRef [.ref p] σ o) ∧ ∀ o, MExec P rfbRef [.ref p] σ o →
    Spec.readFieldHeader 0 Spec.exIdOutOfRange = none ∧
    ∃ σ' r0 ffs, o = .normal (some (.ref r0)) σ' ∧ σ'.heap r0 = some (.plain tfCls ffs) ∧
      Fields.get ffs (tfCls, "type") = some (.int 8#32) ∧
      Fields.get ffs (tfCls, "id") = some (.int (BitVec.ofInt 32 (-32768))) ∧
      R.src σ' t = rest ∧ R.sink σ' t = R.sink σ t ∧ LastAt σ' p (BitVec.ofInt 32 (-32768)) ∧
      CPAt P R σ' p t tmp := by
  have hs : R.src σ t = (0x05 : UInt8) :: (Spec.varint 65536 ++ rest) := by
    rw [hsrc]
    all_goals rfl
  exact ⟨(rfb_term_at R hF hV hn hT hR hCP hp hlast hB h1 h2 h3 hs (by decide)).run,
    fun _ hm => rfb_exIdOutOfRange R hF hV hn hCP hp hlast hB h1 h2 h3 hsrc hm⟩

/-! ## D, total -/

/-- **D for the field header, total**: `readFieldBegin()` terminates on `fieldHeader last id ty ++ rest`,
    and every run returns the `TField` of `rfb_D`. -/
theorem rfb_D_total (R : TRep) {P : Program}
    (hF : Contains P [cpC, tpC, ttC, tpeC, teC, twC, trC, tfC]) (hV : Valid P (tContracts R).env)
    (hn : NoRedeclR P) (hT : TransportTerm P R) (hR : TRepConc P R) {σ : State} {p t tmp : Addr}
    {fs : List (FieldKey × Value)} {last id : I32} {ty : Nat} {rest : Bytes}
    (hCP : CPAt P R σ p t tmp) (hp : σ.heap p = some (.plain cpCls fs))
    (hlast : Fields.get fs (cpCls, "lastFieldId_") = some (.int last)) (hB : BoolAt σ p)
    (h1 : σ.initOf tpeCls = .done) (h2 : σ.initOf cpCls = .done) (h3 : σ.initOf tfCls = .done)
    (hty : 1 ≤ ty ∧ ty < 16) (htt : (Spec.ttypeOfCompact ty).isSome)
    (his : JInt.toShort id = id)
    (hsrc : R.src σ t = Spec.fieldHeader last.toInt id.toInt ty ++ rest) :
    (∃ o, MExec P rfbRef [.ref p] σ o) ∧ ∀ o, MExec P rfbRef [.ref p] σ o →
    ∃ tt σ' r0 ffs, Spec.ttypeOfCompact ty = some tt ∧ o = .normal (some (.ref r0)) σ' ∧
      σ'.heap r0 = some (.plain tfCls ffs) ∧
      Fields.get ffs (tfCls, "type") = some (.int (BitVec.ofNat 32 tt)) ∧
      Fields.get ffs (tfCls, "id") = some (.int id) ∧ R.src σ' t = rest ∧
      R.sink σ' t = R.sink σ t ∧ LastAt σ' p id ∧ CPAt P R σ' p t tmp := by
  refine ⟨?_, fun _ hm => rfb_D R hF hV hn hCP hp hlast hB h1 h2 h3 hty htt his hsrc hm⟩
  -- the header's first byte and its type nibble, as `rfb_D` finds them
  obtain ⟨u, rest0, hs, hu, hnib, hfid⟩ : ∃ u rest0, R.src σ t = u :: rest0 ∧ u.toNat ≠ 0 ∧
      u.toNat % 16 = ty ∧ fieldIdJ last (BitVec.signExtend 32 u.toBitVec) rest0 = some (id, rest) := by
    by_cases hd : 1 ≤ id.toInt - last.toInt ∧ id.toInt - last.toInt ≤ 15
    · rw [Spec.fieldHeader_short hd hty.2, List.cons_append, List.nil_append] at hsrc
      have hb : (UInt8.ofNat (16 * (id.toInt - last.toInt).toNat + ty)).toNat =
          16 * (id.toInt - last.toInt).toNat + ty := by
        rw [UInt8.toNat_ofNat']; omega
      have hq : (16 * (id.toInt - last.toInt).toNat + ty) / 16 = (id.toInt - last.toInt).toNat := by
        omega
      refine ⟨_, rest, hsrc, by rw [hb]; omega, by rw [hb]; omega, ?_⟩
      have hm0 : ¬ modJ (BitVec.signExtend 32 (UInt8.ofNat (16 * (id.toInt - last.toInt).toNat + ty)).toBitVec) = 0#32 := by
        rw [modJ_sx, hb, hq]
        exact ofNat32_ne_zero (by omega) (by omega)
      rw [fieldIdJ_short hm0, modJ_sx, hb, hq, short_id his hd]
    · rw [Spec.fieldHeader_long hd, List.cons_append] at hsrc
      have hb : (UInt8.ofNat ty).toNat = ty := by rw [UInt8.toNat_ofNat']; omega
      refine ⟨_, _, hsrc, by rw [hb]; omega, by rw [hb]; omega, ?_⟩
      have hz := Spec.zigzag_lt32 (inI32_toInt id)
      have hm0 : modJ (BitVec.signExtend 32 (UInt8.ofNat ty).toBitVec) = 0#32 := by
        rw [modJ_sx, hb, Nat.div_eq_of_lt hty.2]
      rw [fieldIdJ_long hm0 (Spec.readVarint_varint 5 _ rest (Spec.varint_length_le5 hz)), long_id his]
  exact (rfb_term_at R hF hV hn hT hR hCP hp hlast hB h1 h2 h3 hs (by rw [hnib]; exact htt)).run

/-- **`[0x05, 0x1E]` after id 0 (the long form of `exDelta15`), total**: `readFieldBegin()` terminates,
    and every run returns a new `TField` of type 8 with id 15 (`rfb_exDelta15_long`). -/
theorem rfb_exDelta15_long_total (R : TRep) {P : Program}
    (hF : Contains P [cpC, tpC, ttC, tpeC, teC, twC, trC, tfC]) (hV : Valid P (tContracts R).env)
    (hn : NoRedeclR P) (hT : TransportTerm P R) (hR : TRepConc P R) {σ : State} {p t tmp : Addr}
    {fs : List (FieldKey × Value)} {rest : Bytes} (hCP : CPAt P R σ p t tmp)
    (hp : σ.heap p = some (.plain cpCls fs))
    (hlast : Fields.get fs (cpCls, "lastFieldId_") = some (.int 0#32)) (hB : BoolAt σ p)
    (h1 : σ.initOf tpeCls = .done) (h2 : σ.initOf cpCls = .done) (h3 : σ.initOf tfCls = .done)
    (hsrc : R.src σ t = [0x05, 0x1E] ++ rest) :
    (∃ o, MExec P rfbRef [.ref p] σ o) ∧ ∀ o, MExec P rfbRef [.ref p] σ o →
    Spec.readFieldHeader 0 [0x05, 0x1E] = some (.field 5 15, []) ∧
    ∃ σ' r0 ffs, o = .normal (some (.ref r0)) σ' ∧ σ'.heap r0 = some (.plain tfCls ffs) ∧
      Fields.get ffs (tfCls, "type") = some (.int 8#32) ∧ Fields.get ffs (tfCls, "id") = some (.int 15#32) ∧
      R.src σ' t = rest ∧ R.sink σ' t = R.sink σ t ∧ LastAt σ' p 15#32 ∧ CPAt P R σ' p t tmp := by
  have hs : R.src σ t = (0x05 : UInt8) :: (Spec.varint 30 ++ rest) := by
    rw [hsrc]
    all_goals rfl
  exact ⟨(rfb_term_at R hF hV hn hT hR hCP hp hlast hB h1 h2 h3 hs (by decide)).run,
    fun _ hm => rfb_exDelta15_long R hF hV hn hCP hp hlast hB h1 h2 h3 hsrc hm⟩

end EquivLean.Demo.Thrift.Java

#print axioms EquivLean.Demo.Thrift.Java.rfb_D_total
#print axioms EquivLean.Demo.Thrift.Java.rfb_exDelta15_long_total
#print axioms EquivLean.Demo.Thrift.Java.rfb_total
#print axioms EquivLean.Demo.Thrift.Java.rfb_exStopNibble_total
#print axioms EquivLean.Demo.Thrift.Java.rfb_I16Overflow_short_total
#print axioms EquivLean.Demo.Thrift.Java.rfb_exIdOutOfRange_total
