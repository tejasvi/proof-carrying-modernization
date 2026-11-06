import EquivLean.Modernize.Cbstm03a.Java.Iface1

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows jstr_empty)

namespace EquivLean.Modernize.Cbstm03a.Java

theorem take_eq_rep {α : Type} (w : List α) (c : α) (k : Nat) (h : ∀ x ∈ w, x = c) (hk : k ≤ w.length) :
    w.take k = List.replicate k c :=
  List.eq_replicate_iff.2 ⟨by simp; omega, fun b hb => h b (List.mem_of_mem_take hb)⟩

/-- A length read as an `int` is at most the length. -/
theorem toInt_ofNat32_le (k : Nat) : (BitVec.ofNat 32 k).toInt ≤ k := by
  have h1 := BitVec.toInt_eq_toNat_cond (BitVec.ofNat 32 k)
  rw [BitVec.toNat_ofNat] at h1
  simp only [Nat.reducePow] at h1
  split at h1 <;> omega

theorem le_len_of_le_ofNat {n : Int} {k : Nat} (h : n ≤ (BitVec.ofNat 32 k).toInt) : n ≤ k :=
  Int.le_trans h (toInt_ofNat32_le k)

/-- At the loop head (statement 5): `s` holds `t`, a nonempty text of copies of the character.
Locals: `n` 0, `s` 3. -/
def repeatInv : Invariants := [(5, fun args σ0 fr σ => ∀ (ch n : I32), args = [.int ch, .int n] →
  ∃ sa t, fr.get 0 = some (.int n) ∧ fr.get 3 = some (.ref sa) ∧ σ.heap sa = some (.str t) ∧
    (∀ x ∈ t, x = ch.setWidth 16) ∧ 1 ≤ t.length ∧ 0 < n.toInt ∧ σ0.next ≤ sa ∧ Grows σ0 σ ∧
    σ.inits = σ0.inits ∧ σ.statics = σ0.statics)]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
set_option jimple.modelContracts true in
theorem repeat_vc : MethodVC Gen.prog (fun _ => none) 0 repeatRef repeatSpec repeatInv 40 := by
  jverify [ite_nat_ne, repeatSpec, repeatInv, Grows, jstr_empty, Int.toNat_of_nonpos, List.mem_append, or_imp,
    forall_and, List.mem_singleton, forall_eq]
  · exact take_eq_rep _ _ _ ‹∀ x ∈ _, x = _› (by omega)
  · exact ‹¬ (_ ∧ _)› ⟨by omega, le_len_of_le_ofNat ‹_ ≤ (BitVec.ofNat 32 _).toInt›⟩

end EquivLean.Modernize.Cbstm03a.Java

#print axioms EquivLean.Modernize.Cbstm03a.Java.repeat_vc
