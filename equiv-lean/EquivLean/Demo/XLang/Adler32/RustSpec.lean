import EquivLean.Demo.XLang.Adler32.Equiv
import EquivLean.Demo.XLang.Adler32.ModelLemmas
import EquivLean.Demo.XLang.Adler32.RustDefs
import EquivLean.Demo.XLang.Adler32.RustZ
import EquivLean.Demo.XLang.Adler32.RustCombine

/-!
# zlib adler32 → safe Rust: the Rust side, against the model

`rustZ_eq`, `rustCombine_eq`: the Rust side's pure functions (`Rust.rustZ`, `Rust.rustCombine`, which
the generated code returns) are the model's `adler32z` and `combine`.  Hence the plumbing's `RSpec`
for each function: `z_rspec` (`adler32_z`), `run32_rspec` (`adler32`), `cb_rspec`
(`adler32_combine`), `cb64_rspec` (`adler32_combine64`): off the large inputs the Rust run returns
normally (no panic) with the model's value.
-/

open Aeneas Aeneas.Std EquivLean EquivLean.Aeneas

namespace EquivLean.Demo.XLang.Adler32

/-! ## The pure functions are the model -/

theorem rust_sums_eq : ∀ (bs : List Nat) (a s : Nat), Rust.sums bs a s = sums a s bs
  | [], _, _ => rfl
  | b :: bs, a, s => rust_sums_eq bs (a + b) (s + (a + b))

theorem pack_shl (a s : Nat) (h : s < 2 ^ 48) : pack a s = a ||| Rust.shl16N s := by
  rw [Rust.shl16N_eq, Nat.mod_eq_of_lt (by omega)]
  unfold pack
  rw [Nat.shiftLeft_eq]

theorem blocks_snd_lt : ∀ (bs : List Nat) (a s : Nat), a < 65536 → s < 65536 →
    (Rust.blocks bs a s).1 < 65536 ∧ (Rust.blocks bs a s).2.1 < 65536 := by
  intro bs
  induction h : bs.length using Nat.strong_induction_on generalizing bs with
  | _ m IH =>
    intro a s ha hs
    rw [Rust.blocks]
    split_ifs with hN
    · exact IH (bs.drop 5552).length (by simp only [List.length_drop]; omega) _ rfl _ _
        (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide))
        (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide))
    · exact ⟨ha, hs⟩

/-- The blocks and the tail of the Rust `adler32_z` are the model's main path. -/
theorem blocks_tail_eq : ∀ (bs : List Nat) (a s : Nat),
    (if (Rust.blocks bs a s).2.2.length ≠ 0 then
        ((Rust.sums (Rust.blocks bs a s).2.2 (Rust.blocks bs a s).1 (Rust.blocks bs a s).2.1).1 % 65521,
          (Rust.sums (Rust.blocks bs a s).2.2 (Rust.blocks bs a s).1 (Rust.blocks bs a s).2.1).2 % 65521)
      else ((Rust.blocks bs a s).1, (Rust.blocks bs a s).2.1)) = mainPath a s bs := by
  intro bs
  induction h : bs.length using Nat.strong_induction_on generalizing bs with
  | _ m IH =>
    intro a s
    by_cases hN : 5552 ≤ bs.length
    · rw [mainPath_block (by unfold NMAX; exact hN)]
      have e := IH (bs.drop 5552).length (by simp only [List.length_drop]; omega) _ rfl
        ((Rust.sums (bs.take 5552) a s).1 % 65521) ((Rust.sums (bs.take 5552) a s).2 % 65521)
      rw [show NMAX = 5552 from rfl, show BASE = 65521 from rfl, ← rust_sums_eq, ← e]
      conv_lhs => rw [Rust.blocks, dif_pos hN]
    · rw [mainPath_tail (by unfold NMAX; omega)]
      conv_lhs => rw [Rust.blocks, dif_neg hN]
      simp only [rust_sums_eq, BASE]
      split_ifs <;> first | rfl | (exfalso; omega)

/-- **`adler32_z`'s pure function is the model**, on a buffer of `len` bytes or `Z_NULL`. -/
theorem rustZ_eq (adler : Nat) (buf : Option (List Nat)) (len : Nat)
    (hlen : ∀ bs, buf = some bs → len = bs.length) (hb : ∀ bs, buf = some bs → ∀ b ∈ bs, b < 256) :
    Rust.rustZ adler buf len = adler32z adler buf := by
  cases buf with
  | none =>
    simp only [Rust.rustZ, adler32z]
    split_ifs <;> rfl
  | some bs =>
    have hl := hlen bs rfl
    subst hl
    have ha0 : adler % 65536 < 65536 := Nat.mod_lt _ (by decide)
    have hs0 : adler / 65536 % 65536 < 65536 := Nat.mod_lt _ (by decide)
    by_cases h1 : bs.length = 1
    · obtain ⟨b, rfl⟩ := List.length_eq_one_iff.1 h1
      have hb0 : b < 256 := hb [b] rfl b (by simp)
      simp only [Rust.rustZ, adler32z, List.length_singleton, _root_.ite_true,
        Nat.shiftRight_eq_div_pow, Nat.reducePow, lo16, BASE, List.headD_cons, List.getD_cons_zero]
      rw [pack_shl _ _ (by split_ifs <;> omega)]
    · by_cases h16 : bs.length < 16
      · rw [adler32z_short adler bs h1 h16]
        simp only [Rust.rustZ, h1, h16, _root_.ite_false, _root_.ite_true, List.take_length,
          rust_sums_eq, Nat.shiftRight_eq_div_pow, Nat.reducePow, lo16, BASE]
        rw [pack_shl _ _ (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide))]
      · rw [adler32z_long adler bs (by omega)]
        simp only [Rust.rustZ, h1, h16, _root_.ite_false, List.take_length,
          Nat.shiftRight_eq_div_pow, Nat.reducePow, lo16]
        rw [← blocks_tail_eq bs (adler % 65536) (adler / 65536 % 65536)]
        obtain ⟨hb1, hb2⟩ := blocks_snd_lt bs (adler % 65536) (adler / 65536 % 65536) ha0 hs0
        split_ifs
        · exact (pack_shl _ _ (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide))).symm
        · exact (pack_shl _ _ (by omega)).symm

/-- **The combine functions' pure function is the model.** -/
theorem rustCombine_eq (adler1 adler2 : Nat) (len2 : Int) :
    Rust.rustCombine adler1 adler2 len2 = combine adler1 adler2 len2 := by
  have h131 : (65521 : Nat) <<< 1 = 131042 := by decide
  unfold Rust.rustCombine combine
  by_cases hneg : len2 < 0
  · simp only [hneg, _root_.ite_true]
  · simp only [hneg, _root_.ite_false, Nat.shiftRight_eq_div_pow, Nat.reducePow, lo16, BASE, h131,
      Nat.cast_ofNat]
    rw [pack_shl _ _ (by split_ifs <;> omega)]

/-! ## `RSpec` for each function -/

theorem bytes_eq (s : Slice U8) : Rust.bytes s = bytesOf s := rfl

theorem zLen_buf (x : ZInput) : ∀ b, x.2.1 = some b → (zLen x).val = b.val.length := by
  intro b hb
  simp only [zLen, hb, Slice.len_val]

/-- **`adler32_z`**: off the large inputs the Rust run returns normally with the model's value. -/
theorem z_rspec : RSpec zLong zModel zRun := by
  intro x _
  obtain ⟨y, hy, hv⟩ := Rust.adler32_z_eq x.1 x.2.1 (zLen x) (zLen_buf x)
  refine ⟨y, hy, ?_⟩
  rw [hv, rustZ_eq]
  · rfl
  · intro bs hbs
    cases h : x.2.1 with
    | none => simp [h] at hbs
    | some b =>
      simp only [h, Option.map_some, Option.some.injEq] at hbs
      rw [← hbs, zLen_buf x b h, bytes_eq, bytesOf, List.length_map]
  · intro bs hbs
    cases h : x.2.1 with
    | none => simp [h] at hbs
    | some b =>
      simp only [h, Option.map_some, Option.some.injEq] at hbs
      rw [← hbs]
      exact Rust.bytes_lt b

/-- **`adler32`** (`len` as a `uInt`). -/
theorem run32_rspec : RSpec zLong zModel run32 := by
  intro x hL
  simp only [zLong, Nat.not_le] at hL
  have hc : (UScalar.cast .U32 (zLen x)).val = (zLen x).val := by
    rw [UScalar.cast_val_eq]
    exact Nat.mod_eq_of_lt (by simp only [UScalarTy.U32_numBits_eq]; omega)
  obtain ⟨y, hy, hv⟩ := Rust.adler32_eq x.1 x.2.1 (UScalar.cast .U32 (zLen x))
    (fun b hb => by rw [hc]; exact zLen_buf x b hb)
  refine ⟨y, hy, ?_⟩
  rw [hv, hc, rustZ_eq]
  · rfl
  · intro bs hbs
    cases h : x.2.1 with
    | none => simp [h] at hbs
    | some b =>
      simp only [h, Option.map_some, Option.some.injEq] at hbs
      rw [← hbs, zLen_buf x b h, bytes_eq, bytesOf, List.length_map]
  · intro bs hbs
    cases h : x.2.1 with
    | none => simp [h] at hbs
    | some b =>
      simp only [h, Option.map_some, Option.some.injEq] at hbs
      rw [← hbs]
      exact Rust.bytes_lt b

/-- **`adler32_combine`**: on every input. -/
theorem cb_rspec : RSpec cbLong cbModel cbRun := by
  intro x _
  obtain ⟨y, hy, hv⟩ := Rust.adler32_combine_eq x.1 x.2.1 x.2.2
  exact ⟨y, hy, by rw [hv, rustCombine_eq]; rfl⟩

/-- **`adler32_combine64`**: on every input. -/
theorem cb64_rspec : RSpec cbLong cbModel cb64Run := by
  intro x _
  obtain ⟨y, hy, hv⟩ := Rust.adler32_combine64_eq x.1 x.2.1 x.2.2
  exact ⟨y, hy, by rw [hv, rustCombine_eq]; rfl⟩

end EquivLean.Demo.XLang.Adler32
