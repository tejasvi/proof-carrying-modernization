import EquivLean.Demo.XLang.Adler32.CBase

/-!
# zlib adler32 → model, C side: `adler32_combine_`

Total contract (`Returns`, `@[cir_spec]`): for every `adler1`, `adler2` below `2^64` and every 64-bit `len2`, the
call returns the model's `combine adler1 adler2 len2` and changes no block of the caller.  The executor runs every
path of `adler32_combine_` (the sign of `len2`, then each conditional subtraction of `BASE` or `2 BASE`); on each
path the return value `sum1 | (sum2 << 16)` is the model's (`combine_nonneg` writes the model's value the same
way).  The two `%` are unsigned (`Int.tmod`).  `sum1` and `sum2` stay below `2^17` but not always below `2^16`
(when `adler1` or `adler2` is not a valid checksum), so the `|` is taken below `2^64` only (`or_lt_mod`).
The callers `adler32_combine`, `adler32_combine64` and their runs are in `CCombineSpec`.
-/

open CIR EquivLean.Cir
open EquivLean.Demo.Gen.Cir.Adler32.Adler32 (ctx module fn_adler32_combine_2)
open EquivLean.Demo.XLang.Adler32 (combine pack BASE)

set_option maxHeartbeats 40000000
set_option maxRecDepth 100000

namespace EquivLean.Demo.XLang.Adler32.C

/-- `rem * sum1` stays below `2^64`. -/
theorem prod_lt (r s : Int) (hr0 : 0 ≤ r) (hr1 : r < 65521) (hs0 : 0 ≤ s) (hs1 : s < 65536) :
    0 ≤ r * s ∧ r * s < 18446744073709551616 := by
  refine ⟨Int.mul_nonneg hr0 hs0, ?_⟩
  have h := Int.mul_le_mul (show r ≤ 65520 by omega) (show s ≤ 65535 by omega) hs0 (by decide)
  exact Int.lt_of_le_of_lt h (by decide)

theorem toNat_mul_65536 (S : Int) (h : 0 ≤ S) : (S * 65536).toNat = S.toNat * 65536 := by
  rw [Int.toNat_mul h (by decide)]
  rfl

theorem or_lt_mod (x y : Nat) (hx : x < 4294967296) (hy : y < 4294967296) :
    (x ||| y * 65536) % 18446744073709551616 = x ||| y * 65536 := by
  apply Nat.mod_eq_of_lt
  have := Nat.or_lt_two_pow (show x < 2 ^ 64 by omega) (show y * 65536 < 2 ^ 64 by omega)
  omega

/-- `|` on two values below `2^64`, with the result reduced modulo `2^64` (the executor's fact for `|` here). -/
theorem bw_or_mod64 (x y : Int) (hx0 : 0 ≤ x) (hx : x < 2 ^ 64) (hy0 : 0 ≤ y) (hy : y < 2 ^ 64) :
    bitwise false 64 (fun a b => a ||| b) x y = (((x.toNat ||| y.toNat) % 18446744073709551616 : Nat) : Int) := by
  rw [bw_or_int x y hx0 hx hy0 hy, Nat.mod_eq_of_lt]
  have := Nat.or_lt_two_pow (show x.toNat < 2 ^ 64 by omega) (show y.toNat < 2 ^ 64 by omega)
  omega

theorem or_mul_congr {x₁ x₂ y₁ y₂ : Nat} (hx : x₁ = x₂) (hy : y₁ = y₂) :
    ((x₁ ||| y₁ * 65536 : Nat) : Int) = ((x₂ ||| y₂ * 65536 : Nat) : Int) := by
  subst hx; subst hy; rfl

/-- The model's `combine` for `len2 ≥ 0`, written as the C computes it. -/
theorem combine_nonneg (a1 a2 : Nat) (len2 : Int) (h : ¬ len2 < 0) :
    combine a1 a2 len2 =
      ((if 65521 ≤ (if 65521 ≤ a1 % 65536 + a2 % 65536 + 65521 - 1
          then a1 % 65536 + a2 % 65536 + 65521 - 1 - 65521 else a1 % 65536 + a2 % 65536 + 65521 - 1)
        then (if 65521 ≤ a1 % 65536 + a2 % 65536 + 65521 - 1
          then a1 % 65536 + a2 % 65536 + 65521 - 1 - 65521 else a1 % 65536 + a2 % 65536 + 65521 - 1) - 65521
        else (if 65521 ≤ a1 % 65536 + a2 % 65536 + 65521 - 1
          then a1 % 65536 + a2 % 65536 + 65521 - 1 - 65521 else a1 % 65536 + a2 % 65536 + 65521 - 1)) |||
      (if 65521 ≤ (if 131042 ≤ (len2 % 65521).toNat * (a1 % 65536) % 65521 + a1 / 65536 % 65536 +
              a2 / 65536 % 65536 + 65521 - (len2 % 65521).toNat
          then (len2 % 65521).toNat * (a1 % 65536) % 65521 + a1 / 65536 % 65536 + a2 / 65536 % 65536 +
            65521 - (len2 % 65521).toNat - 131042
          else (len2 % 65521).toNat * (a1 % 65536) % 65521 + a1 / 65536 % 65536 + a2 / 65536 % 65536 +
            65521 - (len2 % 65521).toNat)
        then (if 131042 ≤ (len2 % 65521).toNat * (a1 % 65536) % 65521 + a1 / 65536 % 65536 +
              a2 / 65536 % 65536 + 65521 - (len2 % 65521).toNat
          then (len2 % 65521).toNat * (a1 % 65536) % 65521 + a1 / 65536 % 65536 + a2 / 65536 % 65536 +
            65521 - (len2 % 65521).toNat - 131042
          else (len2 % 65521).toNat * (a1 % 65536) % 65521 + a1 / 65536 % 65536 + a2 / 65536 % 65536 +
            65521 - (len2 % 65521).toNat) - 65521
        else (if 131042 ≤ (len2 % 65521).toNat * (a1 % 65536) % 65521 + a1 / 65536 % 65536 +
              a2 / 65536 % 65536 + 65521 - (len2 % 65521).toNat
          then (len2 % 65521).toNat * (a1 % 65536) % 65521 + a1 / 65536 % 65536 + a2 / 65536 % 65536 +
            65521 - (len2 % 65521).toNat - 131042
          else (len2 % 65521).toNat * (a1 % 65536) % 65521 + a1 / 65536 % 65536 + a2 / 65536 % 65536 +
            65521 - (len2 % 65521).toNat)) * 65536) := by
  have h131 : (65521 : Nat) <<< 1 = 131042 := by decide
  have h65 : ((65521 : Nat) : Int) = 65521 := rfl
  simp only [combine, h, _root_.ite_false, land_ffff, shiftRight_16, pack, shiftLeft_16, BASE, h65, h131]

theorem combine_neg (a1 a2 : Nat) (len2 : Int) (h : len2 < 0) : combine a1 a2 len2 = 4294967295 := by
  simp only [combine, h, _root_.ite_true]

/-- `adler32_combine_(adler1, adler2, len2)`: the model's `combine`, for every input. -/
@[cir_spec]
theorem adler32_combine__spec (a1 a2 : Nat) (len2 : Int) (m : Mem) (ha1 : a1 < 2 ^ 64) (ha2 : a2 < 2 ^ 64)
    (hl : -9223372036854775808 ≤ len2 ∧ len2 ≤ 9223372036854775807) :
    Returns ctx "adler32_combine_" [.int a1, .int a2, .int len2] m
      (fun r m' => r = some (.int (combine a1 a2 len2)) ∧ m.next ≤ m'.next ∧
        ∀ b, b < m.next → m'.blocks b = m.blocks b) := by
  have cirH_b1 := bw_and_ffff_mod a1 ha1
  have cirH_b2 := bw_and_ffff_mod a2 ha2
  have cirH_b3 := bw_shr16_and a1 ha1
  have cirH_b4 := bw_shr16_and a2 ha2
  have cirH_or : ∀ x y : Int, 0 ≤ x → x < 2 ^ 64 → 0 ≤ y → y < 2 ^ 64 →
      bitwise false 64 (fun a b => a ||| b) x y = (((x.toNat ||| y.toNat) % 18446744073709551616 : Nat) : Int) :=
    bw_or_mod64
  by_cases hneg : len2 < 0
  · cir_start
    set_option cir.fuel 3000 in cir_run
    all_goals first
      | (rw [combine_neg a1 a2 len2 hneg]; rfl)
      | exact absurd hneg (by with_reducible assumption)
      | omega
  · have cirH_tm : Int.tmod len2 65521 = len2 % 65521 := Int.tmod_eq_emod_of_nonneg (by omega)
    have hr0 : 0 ≤ len2 % 65521 := Int.emod_nonneg _ (by decide)
    have hr1 : len2 % 65521 < 65521 := Int.emod_lt_of_pos _ (by decide)
    obtain ⟨hp0, hp1⟩ := prod_lt (len2 % 65521) ((a1 % 65536 : Nat) : Int) hr0 hr1 (by omega) (by omega)
    have cirH_mr : inRange false 64 (len2 % 65521 * ((a1 % 65536 : Nat) : Int)) = true := by
      rw [inRange_eq_true_iff]; simp only [intMin_u, intMax_u64]; exact ⟨hp0, by omega⟩
    -- the product modulo `BASE` (an unsigned `%`, `Int.tmod`), as one value
    have e2 : len2 % 65521 * ((a1 % 65536 : Nat) : Int) =
        (((len2 % 65521).toNat * (a1 % 65536) : Nat) : Int) := by
      rw [Int.natCast_mul, Int.toNat_of_nonneg hr0]
    obtain ⟨P, hP, hPv⟩ : ∃ P : Nat, Int.tmod (len2 % 65521 * ((a1 % 65536 : Nat) : Int)) 65521 = P ∧
        P = (len2 % 65521).toNat * (a1 % 65536) % 65521 := by
      refine ⟨_, ?_, rfl⟩
      rw [Int.tmod_eq_emod_of_nonneg hp0, e2]
      omega
    have cirH_pm := hP
    clear hp0 hp1 hP e2
    cir_start
    set_option cir.fuel 3000 in cir_run
    -- the paths the executor opened that the facts rule out
    all_goals try (guard_target =ₛ ((4294967295 : Int) = ↑(combine a1 a2 len2)); exfalso; omega)
    all_goals try (guard_target =ₛ False; omega)
    -- the twelve paths: the return value against the model's
    all_goals simp (disch := omega) only [toNat_mul_65536, or_lt_mod]
    all_goals rw [combine_nonneg a1 a2 len2 hneg]
    all_goals refine or_mul_congr ?_ ?_
    all_goals ((repeat' split) <;> omega)

end EquivLean.Demo.XLang.Adler32.C
