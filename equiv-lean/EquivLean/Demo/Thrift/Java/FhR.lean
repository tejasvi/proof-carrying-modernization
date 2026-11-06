import EquivLean.Demo.Thrift.Java.Rfb
import EquivLean.Demo.Thrift.Java.Sel

/-!
# Thrift → Java (T4): `readFieldBegin()` linked: the callee contracts are valid

`readFieldBegin()` is verified against the contracts of `readByte()`, `getTType(byte)`,
`readFieldId(byte)`, `readVarint32()` and `writeVarint32(int)` (`Γ3`). Each contract is proved
for the method's body; it is valid in a program where no application subclass of
`TCompactProtocol` redeclares these methods (`NoRedeclR`).
-/

open Jimple

namespace EquivLean.Demo.Thrift.Java

abbrev gttRef' : MethodRef := gttRef

/-- No application subclass of `TCompactProtocol` redeclares the methods `readFieldBegin()` calls. -/
def NoRedeclR (P : Program) : Prop :=
  NoRedecl P rbSig rbRef ∧ NoRedecl P gttSig gttRef ∧ NoRedecl P rfiSig rfiRef ∧
  NoRedecl P rv32Sig rv32Ref ∧ NoRedecl P wv32Sig wv32Ref

theorem mem8_of_mem3 : ∀ d ∈ [cpC, tpC, ttC], d ∈ [cpC, tpC, ttC, tpeC, teC, twC, trC, tfC] := by
  intro d hd
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd ⊢
  rcases hd with h | h | h <;> simp [h]

theorem mem7_of_mem3 : ∀ d ∈ [cpC, tpC, ttC], d ∈ [cpC, tpC, ttC, tpeC, teC, twC, trC] := by
  intro d hd
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd ⊢
  rcases hd with h | h | h <;> simp [h]

theorem mem8_of_mem7 :
    ∀ d ∈ [cpC, tpC, ttC, tpeC, teC, twC, trC], d ∈ [cpC, tpC, ttC, tpeC, teC, twC, trC, tfC] := by
  intro d hd
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd ⊢
  rcases hd with h | h | h | h | h | h | h <;> simp [h]

theorem mem8_of_gtt : ∀ d ∈ [cpC, tpeC, teC], d ∈ [cpC, tpC, ttC, tpeC, teC, twC, trC, tfC] := by
  intro d hd
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd ⊢
  rcases hd with h | h | h <;> simp [h]

/-- The varint contracts. -/
theorem valid_Γ2 (R : TRep) {P : Program} (hF : Contains P [cpC, tpC, ttC, tpeC, teC, twC, trC])
    (hV : Valid P (tContracts R).env) (hn1 : NoRedecl P rv32Sig rv32Ref)
    (hn2 : NoRedecl P wv32Sig wv32Ref) : Valid P (Γ2 P R) := by
  have hcp : P.findClass cpCls = some cpC := hF.2 cpC (by simp)
  have htp : P.findClass tpCls = some tpC := hF.2 tpC (by simp)
  have hO : P.findClass "java.lang.Object" = none := findClass_of_noShadow hF.1 (by decide)
  intro sig S hS
  unfold Γ2 at hS
  by_cases h1 : sig = rv32Sig
  · rw [if_pos h1] at hS
    cases hS
    subst h1
    exact contractOK_cp hcp htp hO rfl rfl rfl (by decide) (rv32A_sat R hF hV) hn1
  · rw [if_neg h1] at hS
    by_cases h2 : sig = wv32Sig
    · rw [if_pos h2] at hS
      cases hS
      subst h2
      exact contractOK_cp hcp htp hO rfl rfl rfl (by decide)
        (wv32A_sat R (contains_sub hF mem7_of_mem3) hV) hn2
    · rw [if_neg h2] at hS
      exact hV sig S hS

/-- `readByte()`'s contract for the callers, from its body. -/
theorem rbA_sat (R : TRep) {P : Program} (hF : Contains P [cpC, tpC, ttC])
    (hV : Valid P (tContracts R).env) : Sat P rbRef (rbSpecA P R) := by
  have hI := BodyVCP.sat (rb_body R) hF hV
  intro args σ o hpre hm
  obtain ⟨p, t, tmp, hargs, hCP⟩ := hpre
  have hpost := hI args σ o ⟨p, t, tmp, hargs, hCP, CPAtH.intro hCP, classOK_of_cpAt hCP⟩ hm
  subst hargs
  cases o with
  | normal r σ' =>
    simp only [rbSpecI, rbSpecA, Spec.of] at hpost ⊢
    unfold rbN at hpost
    intro p' t' tmp' fs hargs hp htr hte
    simp only [List.cons.injEq, Value.ref.injEq, and_true] at hargs
    subst hargs
    obtain ⟨rfl, rfl⟩ := cpAt_fields hCP hp htr hte
    obtain ⟨u, rest, a1, a2, a3, a4, a5, a6, a7⟩ := hpost _ _ _ rfl hCP
    exact ⟨u, rest, a1, a2, a3, a4, CPAtH.intro a5, a6, a7⟩
  | exc e σ' =>
    simp only [rbSpecI, rbSpecA, Spec.of] at hpost ⊢
    unfold rbE at hpost
    intro p' t' tmp' fs hargs hp htr hte
    simp only [List.cons.injEq, Value.ref.injEq, and_true] at hargs
    subst hargs
    obtain ⟨rfl, rfl⟩ := cpAt_fields hCP hp htr hte
    exact hpost _ _ _ rfl hCP
  | wrong msg => simp only [rbSpecI, Spec.of] at hpost

/-- `getTType(b)` on a known nibble, from its body (no callee contracts). -/
theorem gtt_sat {P : Program} (hF : Contains P [cpC, tpeC, teC]) : Sat P gttRef gttSpec :=
  BodyVCP.sat gtt_body hF (fun sig S h => by simp [Contracts.env, List.lookup] at h)

/-- `readFieldId(b)`'s contract for the callers, from its body. -/
theorem rfiA_sat (R : TRep) {P : Program} (hF : Contains P [cpC, tpC, ttC, tpeC, teC, twC, trC])
    (hV2 : Valid P (Γ2 P R)) : Sat P rfiRef (rfiSpecA P R) := by
  have hI := BodyVCP.sat (rfi_body R) hF hV2
  intro args σ o hpre hm
  obtain ⟨p, t, tmp, b, last, hargs, hCP, hL, hB, hin⟩ := hpre
  have hpost := hI args σ o
    ⟨p, t, tmp, b, last, hargs, hCP, CPAtH.intro hCP, classOK_of_cpAt hCP, hL, hB, hin⟩ hm
  cases o with
  | normal r σ' =>
    simp only [rfiSpecI, rfiSpecA, Spec.of] at hpost ⊢
    unfold rfiN at hpost
    intro p' t' tmp' fs b' last' hargs' hp htr hte hlast
    obtain ⟨id, rest, a1, a2, a3, a4, a5, a6, a7⟩ := hpost p' t' tmp' fs b' last' hargs' hp htr hte hlast
    exact ⟨id, rest, a1, a2, a3, a4, a5, CPAtH.intro a6, a7⟩
  | exc e σ' =>
    simp only [rfiSpecI, rfiSpecA, Spec.of] at hpost ⊢
    unfold rfiE at hpost
    exact hpost
  | wrong msg => simp only [rfiSpecI, Spec.of] at hpost

/-- The contracts `readFieldBegin()` uses. -/
theorem valid_Γ3 (R : TRep) {P : Program} (hF : Contains P [cpC, tpC, ttC, tpeC, teC, twC, trC, tfC])
    (hV : Valid P (tContracts R).env) (hn : NoRedeclR P) : Valid P (Γ3 P R) := by
  obtain ⟨hnb, hng, hnf, hn1, hn2⟩ := hn
  have hF7 := contains_sub hF mem8_of_mem7
  have hcp : P.findClass cpCls = some cpC := hF.2 cpC (by simp)
  have htp : P.findClass tpCls = some tpC := hF.2 tpC (by simp)
  have hO : P.findClass "java.lang.Object" = none := findClass_of_noShadow hF.1 (by decide)
  have hV2 := valid_Γ2 R hF7 hV hn1 hn2
  intro sig S hS
  unfold Γ3 at hS
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
        (gtt_sat (contains_sub hF mem8_of_gtt)) hng
    · rw [if_neg h2] at hS
      by_cases h3 : sig = rfiSig
      · rw [if_pos h3] at hS
        cases hS
        subst h3
        exact contractOK_cp hcp htp hO rfl rfl rfl (by decide) (rfiA_sat R hF7 hV2) hnf
      · rw [if_neg h3] at hS
        exact hV2 sig S hS

/-- `readFieldBegin()` satisfies its contract. -/
theorem rfb_sat (R : TRep) {P : Program} (hF : Contains P [cpC, tpC, ttC, tpeC, teC, twC, trC, tfC])
    (hV : Valid P (tContracts R).env) (hn : NoRedeclR P) : Sat P rfbRef (rfbSpecI P R) :=
  MethodVC.sat_of_valid (valid_Γ3 R hF hV hn) (rfb_body R P hF)

end EquivLean.Demo.Thrift.Java
