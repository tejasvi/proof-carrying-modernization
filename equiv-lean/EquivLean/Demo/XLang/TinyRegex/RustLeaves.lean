import EquivLean.Demo.XLang.TinyRegex.RustBase

/-!
# tiny-regex-c → model, Rust side: the leaf functions below the recursion group

`matchcharclass` (a loop against the model's recursion) and `matchone`, then `scan_fwd` (the
first loop of `matchstar`/`matchplus`) against the model's `advance`.
-/

open Aeneas Aeneas.Std EquivLean EquivLean.Aeneas

namespace EquivLean.Demo.XLang.TinyRegex.Rust

theorem ite_prop_intro {c : Prop} [inst : Decidable c] {P Q : Prop} (h1 : c → P) (h2 : ¬c → Q) :
    if c then P else Q := by
  cases inst with
  | isTrue h => exact h1 h
  | isFalse h => exact h2 h

theorem dite_prop_intro {c : Prop} [inst : Decidable c] {P : c → Prop} {Q : ¬c → Prop}
    (h1 : ∀ h, P h) (h2 : ∀ h, Q h) : dite c P Q := by
  cases inst with
  | isTrue h => exact h1 h
  | isFalse h => exact h2 h

/-- Splits the `if`s of a symbolically executed Rust function (Prop-valued, branch by branch),
without `simp` on the whole goal. -/
macro "rust_split" : tactic => `(tactic| repeat' (first
  | refine ite_prop_intro (fun _ => ?_) (fun _ => ?_)
  | refine dite_prop_intro (fun _ => ?_) (fun _ => ?_)))

/-- The loop of `matchcharclass` is the model's recursion (for a byte `c ≠ 0`, as `matchone`
passes it), from every class index `k`. -/
theorem matchcharclass_loop_eq (re : tiny_regex.Regex) (c : U8) (hc : c.val ≠ 0) :
    ∀ (n : Nat) (k : Usize) (j : Nat), k.val = j → 40 - j = n → ∀ ub,
      loop (fun k1 => tiny_regex.matchcharclass_loop.body re c k1) k =
        Result.ok (matchcharclass (cclArr re) c.val j ub).1 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
  intro k j hkj hn ub
  subst hkj
  rw [loop_unfold, tiny_regex.matchcharclass_loop.body]
  apply eq_ok_of_wp
  generalize hV : (matchcharclass (cclArr re) c.val k.val ub).1 = V
  by_cases hk : 40 ≤ k.val
  · have hk' : ¬ k.val < 40 := by omega
    aeneas_wp [tiny_regex.MAX_CHAR_CLASS_LEN, hk]
    rw [← hV, matchcharclass.eq_1]
    simp only [matchrange_fst_ge re c.val k.val hk, bget_cclArr, cbyte_ge re hk, cclArr_size, hk',
      Bool.false_eq_true, _root_.ite_false, _root_.dite_false, u8_zero_val, Bool.beq_eq_decide_eq,
      hc, decide_false]
    simp
  · have hmax := usize_max_ge
    have hk40 : k.val < 40 := by omega
    have hk1 : k.val + 1 < 2 ^ UScalarTy.Usize.numBits :=
      (UScalar.lt_pow_iff_le_max _).2 (by rw [UScalar.max_USize_eq]; omega)
    have hk2 : k.val + 1 + 1 < 2 ^ UScalarTy.Usize.numBits :=
      (UScalar.lt_pow_iff_le_max _).2 (by rw [UScalar.max_USize_eq]; omega)
    obtain ⟨R1, hR1, hM1⟩ := ex_of_forall (IH (40 - (k.val + 1)) (by omega)
      (UScalar.ofNatCore (k.val + 1) hk1) (k.val + 1) (by simp) rfl)
    obtain ⟨R2, hR2, hM2⟩ := ex_of_forall (IH (40 - (k.val + 2)) (by omega)
      (UScalar.ofNatCore (k.val + 1 + 1) hk2) (k.val + 2) (by simp) rfl)
    aeneas_wp [wp_Array_index_usize, matchrange_eq, cb_eq, matchmetachar_eq, ismetachar_eq,
      tiny_regex.MAX_CHAR_CLASS_LEN, index_ccl]
    have hlen := ccl_length re
    have hs40 : (cbyte re (k.val + 1)).val ≠ 0 → k.val + 1 < 40 := fun h => by
      by_contra hc'; exact h (by rw [cbyte_ge re (by omega)]; rfl)
    rust_split
    all_goals try (exfalso; omega)
    all_goals try (rw [hR1])
    all_goals try (rw [hR2])
    clear IH hR1 hR2
    all_goals (subst hV; rw [matchcharclass.eq_1]; simp only [bget_cclArr, matchmetachar_pair, wp_ok]
               simp_all [Bool.beq_eq_decide_eq, cclArr_size, cclArr_get])
    -- the leaf `\\` followed by the class end: both branches of the model's bounds test are `false`
    split <;> rfl

theorem matchcharclass_eq (re : tiny_regex.Regex) (c : U8) (k : Usize) (ub : Nat)
    (hc : c.val ≠ 0) :
    tiny_regex.matchcharclass re c k = Result.ok (matchcharclass (cclArr re) c.val k.val ub).1 := by
  unfold tiny_regex.matchcharclass tiny_regex.matchcharclass_loop
  exact matchcharclass_loop_eq re c hc _ k k.val rfl rfl ub

/-- `matchone` is the model's (for a byte `c ≠ 0`, as every caller passes it). -/
theorem matchone_eq (re : tiny_regex.Regex) (text : Slice U8) (p : tiny_regex.RegexObj) (c : U8)
    (hc : c.val ≠ 0) :
    tiny_regex.matchone re p c = Result.ok (matchone (ctx re text) (tok p) c.val).1 := by
  apply eq_ok_of_wp
  unfold tiny_regex.matchone
  generalize hV : (matchone (ctx re text) (tok p) c.val).1 = V
  aeneas_wp [matchcharclass_eq re c _ 0 hc, isdigit_eq, matchalphanum_eq, isspace_eq, hcast_i8_val,
    tiny_regex.DOT, tiny_regex.CHAR_CLASS, tiny_regex.INV_CHAR_CLASS, tiny_regex.DIGIT,
    tiny_regex.NOT_DIGIT, tiny_regex.ALPHA, tiny_regex.NOT_ALPHA, tiny_regex.WHITESPACE,
    tiny_regex.NOT_WHITESPACE]
  rust_split
  all_goals (subst hV; simp only [matchone, tok, ctx_B]
             simp_all [DOT, CHAR_CLASS, INV_CHAR_CLASS, DIGIT, NOT_DIGIT, ALPHA, NOT_ALPHA, WHITESPACE,
               NOT_WHITESPACE, Bool.beq_eq_decide_eq])

/-- A text index as a `usize` (wrapping; exact below `2^32`). -/
def usz (n : Nat) : Usize := ⟨BitVec.ofNat _ n⟩

theorem usz_val {n : Nat} (h : n < 2 ^ UScalarTy.Usize.numBits) : (usz n).val = n := by
  simp only [usz, UScalar.val, BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt h

theorem usz_of_val (x : Usize) : usz x.val = x := by
  cases x; simp [usz, UScalar.val]

/-- The model's `advance` result as the Rust pair `(t, ml)`. -/
def advRes (r : Nat × Int × Nat) : Usize × I32 := (usz r.1, toI32 r.2.1)

theorem len_le_max (text : Slice U8) : text.val.length ≤ Usize.max := text.property

/-- `scan_fwd`'s loop is the model's `advance` (the first loop of `matchstar`/`matchplus`). -/
theorem scan_fwd_loop_eq (re : tiny_regex.Regex) (text : Slice U8) (p : tiny_regex.RegexObj) :
    ∀ (n : Nat) (t : Usize) (m : I32) (mZ : Int), text.val.length - t.val = n → m = toI32 mZ →
      ∀ ub, tiny_regex.scan_fwd_loop re p text t m =
        Result.ok (advRes (advance (ctx re text) (tok p) t.val mZ ub)) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
  intro t m mZ hn hm ub
  subst hm
  have hlen := len_le_max text
  unfold tiny_regex.scan_fwd_loop
  rw [loop_unfold]
  simp only []
  rw [tiny_regex.scan_fwd_loop.body]
  apply eq_ok_of_wp
  generalize hV : advRes (advance (ctx re text) (tok p) t.val mZ ub) = V
  by_cases ht : t.val < text.val.length
  · by_cases h0 : (tbyte text t.val).val = 0
    · aeneas_wp [at_eq, ht, h0]
      subst hV
      rw [advance.eq_1]
      simp [ctx_T_size, ht, ctx_T_get, h0, advRes, usz_of_val]
    · have ht1 : t.val + 1 < 2 ^ UScalarTy.Usize.numBits :=
        (UScalar.lt_pow_iff_le_max _).2 (by rw [UScalar.max_USize_eq]; omega)
      obtain ⟨R, hR, hM⟩ := ex_of_forall (IH (text.val.length - (t.val + 1)) (by omega)
        (UScalar.ofNatCore (t.val + 1) ht1) (toI32 (mZ + 1)) (mZ + 1) (by simp) rfl)
      unfold tiny_regex.scan_fwd_loop at hR
      aeneas_wp [at_eq, ht, h0, matchone_eq re text p (tbyte text t.val) h0, toI32_add_one]
      rust_split
      all_goals try (exfalso; omega)
      all_goals try (rw [hR])
      clear IH hR
      all_goals (subst hV; rw [advance.eq_1]
                 simp_all [ctx_T_size, ctx_T_get, advRes, usz_of_val])
  · aeneas_wp [ht]
    subst hV
    rw [advance.eq_1]
    simp only [ctx_T_size, ht, _root_.dite_false]
    split <;> simp [advRes, usz_of_val]

theorem scan_fwd_eq (re : tiny_regex.Regex) (text : Slice U8) (p : tiny_regex.RegexObj)
    (ti : Usize) (ml : I32) (mlZ : Int) (hml : ml = toI32 mlZ) (ub : Nat) :
    tiny_regex.scan_fwd re p text ti ml =
      Result.ok (advRes (advance (ctx re text) (tok p) ti.val mlZ ub)) :=
  scan_fwd_loop_eq re text p _ ti ml mlZ rfl hml ub

end EquivLean.Demo.XLang.TinyRegex.Rust
