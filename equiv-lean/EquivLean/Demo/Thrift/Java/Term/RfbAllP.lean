-- Termination package by JimpleLean's session: TermT4/RfbAllP.lean (sha256 4b4591dfc12143c6...); only the module root renamed.
import EquivLean.Demo.Thrift.Java.Term.RfbAllT
import EquivLean.Demo.Thrift.Java.Term.RfbTotal

/-!
# Thrift → Java (T4): `readFieldBegin()` on every header byte, linked, total; the nibbles 14 and 15

`Γ3All`'s contracts are valid (`getTType`'s by `gttAll_sat`) and terminate (`gttAll_term`), so
`readFieldBegin()` satisfies `rfbSpecAll` and is totally correct on it, with the premises of `rfb_total`
(`TransportTerm`, `TRepConc`). The named case: a header byte `≠ 0` whose type nibble is 14 or 15 makes
every run throw a `TProtocolException` (`rfb_nib1415_total`).
-/

open Jimple

namespace EquivLean.Demo.Thrift.Java

/-- The contracts `readFieldBegin()` uses on every header byte are valid. -/
theorem valid_Γ3All (R : TRep) {P : Program} (hF : Contains P [cpC, tpC, ttC, tpeC, teC, twC, trC, tfC])
    (hV : Valid P (tContracts R).env) (hn : NoRedeclR P) : Valid P (Γ3All P R) := by
  obtain ⟨hnb, hng, hnf, hn1, hn2⟩ := hn
  have hF7 := contains_sub hF mem8_of_mem7
  have hcp : P.findClass cpCls = some cpC := hF.2 cpC (by simp)
  have htp : P.findClass tpCls = some tpC := hF.2 tpC (by simp)
  have hO : P.findClass "java.lang.Object" = none := findClass_of_noShadow hF.1 (by decide)
  have hV2 := valid_Γ2 R hF7 hV hn1 hn2
  intro sig S hS
  unfold Γ3All at hS
  by_cases h1 : sig = rbSig
  · rw [if_pos h1] at hS
    cases hS
    subst h1
    exact contractOK_cp hcp htp hO rfl rfl rfl (by decide)
      (rbA_sat R (contains_sub hF mem8_of_mem3) hV) hnb
  · rw [if_neg h1] at hS
    by_cases h2 : sig = gttSig
    · rw [if_pos h2] at hS
      cases hS
      subst h2
      exact contractOK_cp hcp htp hO rfl rfl rfl (by decide)
        (gttAll_sat (contains_sub hF mem8_of_gtt)) hng
    · rw [if_neg h2] at hS
      by_cases h3 : sig = rfiSig
      · rw [if_pos h3] at hS
        cases hS
        subst h3
        exact contractOK_cp hcp htp hO rfl rfl rfl (by decide) (rfiA_sat R hF7 hV2) hnf
      · rw [if_neg h3] at hS
        exact hV2 sig S hS

/-- `readFieldBegin()` satisfies its contract on every header byte. -/
theorem rfbAll_sat (R : TRep) {P : Program} (hF : Contains P [cpC, tpC, ttC, tpeC, teC, twC, trC, tfC])
    (hV : Valid P (tContracts R).env) (hn : NoRedeclR P) : Sat P rfbRef (rfbSpecAll P R) :=
  MethodVC.sat_of_valid (valid_Γ3All R hF hV hn) (rfbAll_body R P hF)

/-- The contracts of `Γ3All` terminate. -/
theorem Γ3All_term (R : TRep) {P : Program} (hF : Contains P [cpC, tpC, ttC, tpeC, teC, twC, trC, tfC])
    (hV : Valid P (tContracts R).env) (hn : NoRedeclR P) (hT : TransportTerm P R) (hR : TRepConc P R) :
    ∀ sig S, Γ3All P R sig = some S → ContractTerm P sig (S.strengthen (noX sig)) := by
  obtain ⟨hnb, hng, hnf, hn1, hn2⟩ := hn
  have hF7 := contains_sub hF mem8_of_mem7
  have hcp : P.findClass cpCls = some cpC := hF.2 cpC (by simp)
  have htp : P.findClass tpCls = some tpC := hF.2 tpC (by simp)
  have hO : P.findClass "java.lang.Object" = none := findClass_of_noShadow hF.1 (by decide)
  intro sig S hS
  unfold Γ3All at hS
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
        (fun args σ hp => gttAll_term (contains_sub hF mem8_of_gtt) args σ hp.1) hng
    · rw [if_neg e2] at hS
      by_cases e3 : sig = rfiSig
      · rw [if_pos e3] at hS
        cases hS
        subst e3
        exact contractTerm_cp hcp htp hO rfl rfl rfl (by decide)
          (fun args σ hp => rfiA_termR R hF7 hV hn1 hn2 hT hR args σ hp.1) hnf
      · rw [if_neg e3] at hS
        exact Γ2_term_noX R hF7 hV hn1 hn2 hT hR sig S hS

theorem rfbAll_termI (R : TRep) {P : Program}
    (hF : Contains P [cpC, tpC, ttC, tpeC, teC, twC, trC, tfC]) (hV : Valid P (tContracts R).env)
    (hn : NoRedeclR P) (hT : TransportTerm P R) (hR : TRepConc P R) :
    ∀ args σ, (rfbSpecAll P R).pre args σ → MTerm P rfbRef args σ :=
  TermVC.mterm (rank := fun _ => 0) (r := 1) (Valid.strengthen noX (valid_Γ3All R hF hV hn))
    (SpecEnv.strengthen_term (Γ3All_term R hF hV hn hT hR) _ _)
    (TermVC.of_thinX (SpecEnv.strengthen_below_const _ _ _ (by decide)) (rfbAll_body R P hF)
      (rfbAll_thin R P hF))

/-- **`readFieldBegin()` on every header byte, total correctness.** -/
theorem rfbAll_total (R : TRep) {P : Program}
    (hF : Contains P [cpC, tpC, ttC, tpeC, teC, twC, trC, tfC]) (hV : Valid P (tContracts R).env)
    (hn : NoRedeclR P) (hT : TransportTerm P R) (hR : TRepConc P R) :
    ∀ args σ, (rfbSpecAll P R).pre args σ →
      (∃ o, MExec P rfbRef args σ o) ∧ ∀ o, MExec P rfbRef args σ o → (rfbSpecAll P R).post args σ o :=
  fun args σ hpre => ⟨(rfbAll_termI R hF hV hn hT hR args σ hpre).run,
    fun o ho => rfbAll_sat R hF hV hn args σ o hpre ho⟩

/-- **A field header byte with type nibble 14 or 15, total**: `readFieldBegin()` terminates, and every
    run throws a `TProtocolException` (`getTType` has no TType for the nibble). -/
theorem rfb_nib1415_total (R : TRep) {P : Program}
    (hF : Contains P [cpC, tpC, ttC, tpeC, teC, twC, trC, tfC]) (hV : Valid P (tContracts R).env)
    (hn : NoRedeclR P) (hT : TransportTerm P R) (hR : TRepConc P R) {σ : State} {p t tmp : Addr}
    {fs : List (FieldKey × Value)} {last : I32} {u : UInt8} {rest : Bytes}
    (hCP : CPAt P R σ p t tmp) (hp : σ.heap p = some (.plain cpCls fs))
    (hlast : Fields.get fs (cpCls, "lastFieldId_") = some (.int last)) (hB : BoolAt σ p)
    (h1 : σ.initOf tpeCls = .done) (h2 : σ.initOf cpCls = .done) (h3 : σ.initOf tfCls = .done)
    (hsrc : R.src σ t = u :: rest) (hu : u.toNat ≠ 0) (hnib : 14 ≤ u.toNat % 16) :
    (∃ o, MExec P rfbRef [.ref p] σ o) ∧ ∀ o, MExec P rfbRef [.ref p] σ o →
      ∃ e σ' fs', o = .exc e σ' ∧ σ'.heap e = some (.plain tpeCls fs') := by
  have hpre : (rfbSpecAll P R).pre [.ref p] σ :=
    ⟨p, t, tmp, last, rfl, hCP, CPAtH.intro hCP, ⟨fs, hp, hlast⟩, hB, h1, h2, h3⟩
  have hnone := ttype_none_of_ge14 hnib
  obtain ⟨fs0, -, -, -, hp0, htr, hte, -⟩ := id hCP
  rw [hp] at hp0
  simp only [Option.some.injEq, Obj.plain.injEq, true_and] at hp0
  subst hp0
  refine ⟨(rfbAll_termI R hF hV hn hT hR _ σ hpre).run, fun o ho => ?_⟩
  have hpost := rfbAll_sat R hF hV hn _ σ o hpre ho
  cases o with
  | normal r σ' =>
    simp only [rfbSpecAll, Spec.of] at hpost
    unfold rfbN at hpost
    obtain ⟨u', rest', hs, -, -, -, hcase⟩ := hpost p t tmp _ last rfl hp htr hte hlast
    rw [hsrc] at hs
    simp only [List.cons.injEq] at hs
    obtain ⟨rfl, -⟩ := hs
    rcases hcase with ⟨h0, -⟩ | ⟨-, tt, -, -, -, -, htt, -⟩
    · exact absurd h0 hu
    · rw [hnone] at htt
      cases htt
  | exc e σ' =>
    simp only [rfbSpecAll, Spec.of] at hpost
    unfold rfbEAll at hpost
    obtain ⟨hbad, -⟩ := hpost
    unfold rfbBad at hbad
    obtain ⟨fs', h⟩ := hbad p t tmp _ rfl hp htr hte ⟨u, rest, hsrc, hu, hnone⟩
    exact ⟨e, σ', fs', rfl, h⟩
  | wrong msg => simp only [rfbSpecAll, Spec.of] at hpost

/-- **A field header with type nibble 14 or 15**: the specification reads it as a field of that type
    (`readFieldHeader`); Java's `readFieldBegin()` terminates, and every run throws a `TProtocolException`
    (`getTType` has no TType for the nibble). -/
theorem rfb_nib1415_spec_total (R : TRep) {P : Program}
    (hF : Contains P [cpC, tpC, ttC, tpeC, teC, twC, trC, tfC]) (hV : Valid P (tContracts R).env)
    (hn : NoRedeclR P) (hT : TransportTerm P R) (hR : TRepConc P R) {σ : State} {p t tmp : Addr}
    {fs : List (FieldKey × Value)} {last id : I32} {ty : Nat} {rest : Bytes}
    (hCP : CPAt P R σ p t tmp) (hp : σ.heap p = some (.plain cpCls fs))
    (hlast : Fields.get fs (cpCls, "lastFieldId_") = some (.int last)) (hB : BoolAt σ p)
    (h1 : σ.initOf tpeCls = .done) (h2 : σ.initOf cpCls = .done) (h3 : σ.initOf tfCls = .done)
    (hty : ty = 14 ∨ ty = 15) (his : JInt.toShort id = id) (hid : Spec.InI16 id.toInt)
    (hsrc : R.src σ t = Spec.fieldHeader last.toInt id.toInt ty ++ rest) :
    Spec.readFieldHeader last.toInt (Spec.fieldHeader last.toInt id.toInt ty ++ rest) =
      some (.field ty id.toInt, rest) ∧
    (∃ o, MExec P rfbRef [.ref p] σ o) ∧ ∀ o, MExec P rfbRef [.ref p] σ o →
      ∃ e σ' fs', o = .exc e σ' ∧ σ'.heap e = some (.plain tpeCls fs') := by
  have hty' : 1 ≤ ty ∧ ty < 16 := by omega
  refine ⟨Spec.readFieldHeader_fieldHeader hty' hid rest, ?_⟩
  -- the header's first byte and its type nibble, as `rfb_D` finds them
  obtain ⟨u, rest0, hs, hu, hnib, -⟩ : ∃ u rest0, R.src σ t = u :: rest0 ∧ u.toNat ≠ 0 ∧
      u.toNat % 16 = ty ∧ fieldIdJ last (BitVec.signExtend 32 u.toBitVec) rest0 = some (id, rest) := by
    by_cases hd : 1 ≤ id.toInt - last.toInt ∧ id.toInt - last.toInt ≤ 15
    · rw [Spec.fieldHeader_short hd hty'.2, List.cons_append, List.nil_append] at hsrc
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
        rw [modJ_sx, hb, Nat.div_eq_of_lt hty'.2]
      rw [fieldIdJ_long hm0 (Spec.readVarint_varint 5 _ rest (Spec.varint_length_le5 hz)), long_id his]
  exact rfb_nib1415_total R hF hV hn hT hR hCP hp hlast hB h1 h2 h3 hs hu (by omega)

end EquivLean.Demo.Thrift.Java

#print axioms EquivLean.Demo.Thrift.Java.rfbAll_total
#print axioms EquivLean.Demo.Thrift.Java.rfb_nib1415_total
#print axioms EquivLean.Demo.Thrift.Java.rfb_nib1415_spec_total
