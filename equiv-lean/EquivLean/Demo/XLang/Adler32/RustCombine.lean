import EquivLean.Demo.XLang.Adler32.RustBase

/-!
# zlib adler32 → safe Rust: `adler32_combine` and `adler32_combine64`

`rustCombine` is `adler32_combine_` on numbers, step by step as in the C (`MOD63` and `MOD` are
`% BASE`, then the conditional subtractions).  `adler32_combine__eq`: the generated function
returns `rustCombine` for every argument (so it never panics); the two public wrappers too.
-/

open Aeneas Aeneas.Std EquivLean EquivLean.Aeneas adler32_rs

namespace EquivLean.Demo.XLang.Adler32.Rust

/-- `adler32_combine_(adler1, adler2, len2)` on numbers, as the C computes it. -/
def rustCombine (adler1 adler2 : Nat) (len2 : Int) : Nat :=
  if len2 < 0 then 4294967295
  else
    let rem := (len2 % 65521).toNat
    let sum1 := adler1 % 65536
    let sum2 := rem * sum1 % 65521
    let sum1 := sum1 + adler2 % 65536 + 65521 - 1
    let sum2 := sum2 + adler1 / 65536 % 65536 + adler2 / 65536 % 65536 + 65521 - rem
    let sum1 := if 65521 ≤ sum1 then sum1 - 65521 else sum1
    let sum1 := if 65521 ≤ sum1 then sum1 - 65521 else sum1
    let sum2 := if 131042 ≤ sum2 then sum2 - 131042 else sum2
    let sum2 := if 65521 ≤ sum2 then sum2 - 65521 else sum2
    sum1 ||| shl16N sum2

theorem srem_val {ty : IScalarTy} (x y : IScalar ty) (hx : 0 ≤ x.val) :
    (⟨BitVec.srem x.bv y.bv⟩ : IScalar ty).val = x.val % y.val := by
  show (BitVec.srem x.bv y.bv).toInt = _
  rw [BitVec.toInt_srem]
  exact Int.tmod_eq_emod_of_nonneg hx

theorem base_i64_val : (UScalar.hcast .I64 BASE).val = 65521 := by
  rw [UScalar.hcast_val_eq]
  simp only [BASE]
  decide

theorem shl1_eq' (x : U64) :
    x <<< (1#i32) = .ok (UScalar.ofNatCore (x.val * 2 % 2 ^ 64) (by
      simp only [UScalarTy.U64_numBits_eq]
      exact Nat.mod_lt _ (by decide))) := by
  show UScalar.shiftLeft_IScalar x 1#i32 = _
  simp only [UScalar.shiftLeft_IScalar, UScalar.shiftLeft]
  rw [if_pos (by decide), if_pos (by decide)]
  congr 1
  rw [UScalar.eq_equiv, UScalar.ofNatCore_val_eq]
  have h1 : (1#i32 : I32).toNat = 1 := by decide
  change (x.bv <<< (1#i32 : I32).toNat).toNat = x.val * 2 % 2 ^ 64
  rw [h1, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  rfl

theorem wp_shl1_fresh (x : U64) (Q : Except Error U64 → Prop) :
    wp (x <<< (1#i32)) Q ↔ ∀ z : U64, z.val = x.val * 2 % 2 ^ 64 → Q (.ok z) := by
  rw [shl1_eq', wp_ok]
  exact fresh_of_eq _ _

/-- **`adler32_combine_`** returns `rustCombine` on every argument. -/
theorem adler32_combine__eq (adler1 adler2 : U64) (len2 : I64) :
    ∃ r, adler32_combine_ adler1 adler2 len2 = .ok r ∧
      r.val = rustCombine adler1.val adler2.val len2.val := by
  by_cases hneg : len2.val < 0
  · refine ⟨4294967295#u64, ?_, ?_⟩
    · apply eq_ok_of_wp
      unfold adler32_combine_
      a32_wp
      a32_split'
      all_goals try a32_contra
      all_goals try (exfalso; omega)
      all_goals simp
    · simp only [rustCombine, hneg, _root_.ite_true]
      rfl
  · have hrem := srem_val len2 (UScalar.hcast .I64 BASE) (by omega)
    rw [base_i64_val] at hrem
    have hrem32 : len2.val % 65521 % (2 ^ 32 : Int) = len2.val % 65521 :=
      Int.emod_eq_of_lt (by omega) (by omega)
    have hrem32' : len2.val % 65521 % 4294967296 = len2.val % 65521 :=
      Int.emod_eq_of_lt (by omega) (by omega)
    have hprod : (len2.val % 65521).toNat * (adler1.val % 65536) ≤ 65520 * 65535 :=
      Nat.mul_le_mul (by omega) (by omega)
    apply exists_ok_of_wp
    unfold adler32_combine_
    a32_wp [base_val, base_i64_val, hrem, hrem32, hrem32', wp_shl1_fresh, IScalar.hcast_val_eq,
      Nat.reduceMul, Nat.reducePow, Nat.reduceMod]
    a32_split'
    all_goals try a32_contra
    all_goals try (exfalso; omega)
    all_goals refine ⟨_, rfl, ?_⟩
    all_goals simp only [UScalar.val_or, rustCombine, hneg, _root_.ite_false]
    -- the branch conditions, rewritten to the model's terms, decide the model's `if`s
    all_goals simp only [*] at *
    all_goals simp only [*, _root_.ite_true, _root_.ite_false]

theorem adler32_combine_eq (adler1 adler2 : U64) (len2 : I64) :
    ∃ r, adler32_combine adler1 adler2 len2 = .ok r ∧
      r.val = rustCombine adler1.val adler2.val len2.val := by
  obtain ⟨r, hr, hrv⟩ := adler32_combine__eq adler1 adler2 len2
  exact ⟨r, by unfold adler32_combine; exact hr, hrv⟩

theorem adler32_combine64_eq (adler1 adler2 : U64) (len2 : I64) :
    ∃ r, adler32_combine64 adler1 adler2 len2 = .ok r ∧
      r.val = rustCombine adler1.val adler2.val len2.val := by
  obtain ⟨r, hr, hrv⟩ := adler32_combine__eq adler1 adler2 len2
  exact ⟨r, by unfold adler32_combine64; exact hr, hrv⟩

end EquivLean.Demo.XLang.Adler32.Rust
