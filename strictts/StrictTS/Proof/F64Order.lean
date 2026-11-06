/-
StrictTS proof layer: NaN and the order of doubles.

* **Rounding never produces NaN** (`round_ne_nan`), so `ofNat n` and `ofInt n` are never NaN,
  for every natural number and integer (`ofNat_ne_nan`, `ofInt_ne_nan`, also for literals).
* **`x === x` iff `x` is not NaN** (`numEq_self_iff`, `eq_self_iff`); `Conv.numEq (ofNat n)
  (ofNat n)` and similar self-comparisons reduce to `true` by `simp` (e.g. the postcondition
  `result.length === xs.length`).
* **The IEEE order on non-NaN doubles is a total order**: `x ≤ y` or `x < y` holding makes
  both sides non-NaN (`ne_nan_of_le`, `ne_nan_of_lt`); reflexivity (`le_refl_of_ne_nan`), totality
  (`le_of_not_lt`, `lt_of_not_le`, `le_total`), transitivity (`le_trans`, `lt_of_lt_of_le`, …),
  `x < y → x ≤ y`, antisymmetry up to IEEE equality (`F64.eq`). The comparisons are the `Bool`
  functions `F64.lt`/`le`/`gt`/`ge` behind `Prim.numCmp` (`<`, `<=`, `>`, `>=`) and
  `Conv.numEq` (`===`), stated as `… = true` / `… = false`, the form symbolic execution
  produces; `gt`/`ge` are rewritten to `lt`/`le` with swapped arguments.
-/
import StrictTS.Num.F64Lemmas
import StrictTS.Lib.Conv

namespace StrictTS
namespace F64

/-! ### Rounding never produces NaN -/

theorem mkFin_ne_nan {neg : Bool} {man : Nat} {exp : Int}
    (h : (2^52 ≤ man ∧ man < 2^53 ∧ -1074 ≤ exp ∧ exp ≤ 971) ∨ (man < 2^52 ∧ exp = -1074)) :
    mkFin neg man exp ≠ .nan := by
  rw [mkFin_eq h]; simp

/-- The final step of `round` gives a finite value or an infinity when the rounded significand
lies in the normal range (`[2^52, 2^53]`, a carry included) or is subnormal at the least
exponent. -/
theorem pack_ne_nan (neg : Bool) (man : Nat) (q : Int) (hq : -1074 ≤ q)
    (h : (2 ^ 52 ≤ man ∧ man ≤ 2 ^ 53) ∨ (man ≤ 2 ^ 52 ∧ q = -1074)) : pack neg man q ≠ .nan := by
  unfold pack
  by_cases h53 : man = 2 ^ 53
  · simp only [h53, ite_true]
    split
    · simp
    · exact mkFin_ne_nan (Or.inl ⟨Nat.le_refl _, by decide, by omega, by omega⟩)
  · simp only [h53, ite_false]
    split
    · simp
    · rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact mkFin_ne_nan (Or.inl ⟨h1, by omega, hq, by omega⟩)
      · by_cases h52 : man = 2 ^ 52
        · exact mkFin_ne_nan (Or.inl ⟨by omega, by omega, hq, by omega⟩)
        · exact mkFin_ne_nan (Or.inr ⟨by omega, h2⟩)

theorem rMant_bounds (m s : Nat) (st : Bool) : m >>> s ≤ rMant m s st ∧ rMant m s st ≤ m >>> s + 1 := by
  unfold rMant; split <;> omega

/-- **Rounding never produces NaN**: `round` returns a finite double or an infinity, unless it
is asked to round an exact zero with a sticky bit (`m = 0`, `sticky = true`), which violates its
precondition. -/
theorem round_ne_nan (neg : Bool) (m : Nat) (e : Int) (sticky : Bool) (h : m ≠ 0 ∨ sticky = false) :
    round neg m e sticky ≠ .nan := by
  by_cases h0 : m = 0 ∧ sticky = false
  · rw [h0.1, h0.2, round_zero]; exact mkFin_ne_nan (Or.inr ⟨by decide, rfl⟩)
  have hm : m ≠ 0 := fun hm => by
    rcases h with h | h
    · exact h hm
    · exact h0 ⟨hm, h⟩
  rw [round_eq _ _ _ _ h0]
  have hL1 := two_pow_bitLen_sub_one_le hm
  have hL2 := lt_two_pow_bitLen m
  have hLpos := bitLen_pos hm
  have hqdef : qexp m e = Max.max (e + (bitLen m : Int) - 1 - 52) (-1074) := rfl
  generalize qexp m e = q at hqdef ⊢
  generalize bitLen m = L at hL1 hL2 hLpos hqdef
  split
  · -- at most 53 significant bits above the quantum: exact
    split
    · simp
    · by_cases hn : -1074 ≤ e + (L : Int) - 53
      · have hk : (e - q).toNat = 53 - L := by omega
        rw [hk]
        refine mkFin_ne_nan (Or.inl ⟨?_, ?_, by omega, by omega⟩)
        · calc 2 ^ 52 = 2 ^ (L - 1) * 2 ^ (53 - L) := by rw [← Nat.pow_add]; congr 1; omega
            _ ≤ m * 2 ^ (53 - L) := Nat.mul_le_mul_right _ hL1
        · calc m * 2 ^ (53 - L) < 2 ^ L * 2 ^ (53 - L) :=
                Nat.mul_lt_mul_of_pos_right hL2 (Nat.two_pow_pos _)
            _ = 2 ^ 53 := by rw [← Nat.pow_add]; congr 1; omega
      · have hq : q = -1074 := by omega
        refine mkFin_ne_nan (Or.inr ⟨?_, hq⟩)
        calc m * 2 ^ (e - q).toNat < 2 ^ L * 2 ^ (e - q).toNat :=
              Nat.mul_lt_mul_of_pos_right hL2 (Nat.two_pow_pos _)
          _ = 2 ^ (L + (e - q).toNat) := by rw [← Nat.pow_add]
          _ ≤ 2 ^ 52 := Nat.pow_le_pow_right (by decide) (by omega)
  · -- more bits: drop `s ≥ 1` of them and round
    have hr := rMant_bounds m (q - e).toNat sticky
    generalize rMant m (q - e).toNat sticky = man1 at hr ⊢
    rw [Nat.shiftRight_eq_div_pow] at hr
    by_cases hn : -1074 ≤ e + (L : Int) - 53
    · have hs : (q - e).toNat = L - 53 := by omega
      rw [hs] at hr
      have hlo : 2 ^ 52 ≤ m / 2 ^ (L - 53) := by
        rw [Nat.le_div_iff_mul_le (Nat.two_pow_pos _), ← Nat.pow_add]
        calc 2 ^ (52 + (L - 53)) = 2 ^ (L - 1) := by congr 1; omega
          _ ≤ m := hL1
      have hhi : m / 2 ^ (L - 53) < 2 ^ 53 := by
        rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add]
        calc m < 2 ^ L := hL2
          _ = 2 ^ (53 + (L - 53)) := by congr 1; omega
      exact pack_ne_nan neg man1 q (by omega) (Or.inl ⟨by omega, by omega⟩)
    · have hq : q = -1074 := by omega
      have hhi : m / 2 ^ (q - e).toNat < 2 ^ 52 := by
        rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add]
        calc m < 2 ^ L := hL2
          _ ≤ 2 ^ (52 + (q - e).toNat) := Nat.pow_le_pow_right (by decide) (by omega)
      exact pack_ne_nan neg man1 q (by omega) (Or.inr ⟨by omega, hq⟩)

/-- `F64.ofNat n` (the double nearest to `n`) is never NaN. -/
@[simp] theorem ofNat_ne_nan (n : Nat) : ofNat n ≠ .nan :=
  round_ne_nan false n 0 false (Or.inr rfl)

/-- `F64.ofInt n` (the double nearest to `n`) is never NaN. -/
@[simp] theorem ofInt_ne_nan (n : Int) : ofInt n ≠ .nan :=
  round_ne_nan _ n.natAbs 0 false (Or.inr rfl)

/-- Numeric literals are not NaN. -/
@[simp] theorem lit_ne_nan (n : Nat) : (no_index (OfNat.ofNat n) : F64) ≠ .nan := ofNat_ne_nan n

/-! ### `===` -/

/-- `x === x` iff `x` is not NaN. -/
@[simp] theorem numEq_self_iff (x : F64) : Conv.numEq x x = true ↔ x ≠ .nan := by
  cases x <;> simp [Conv.numEq]

theorem numEq_self {x : F64} (h : x ≠ .nan) : Conv.numEq x x = true := (numEq_self_iff x).2 h

@[simp] theorem numEq_ofNat_self (n : Nat) : Conv.numEq (ofNat n) (ofNat n) = true :=
  numEq_self (ofNat_ne_nan n)

@[simp] theorem numEq_ofInt_self (n : Int) : Conv.numEq (ofInt n) (ofInt n) = true :=
  numEq_self (ofInt_ne_nan n)

/-- Number::equal (`F64.eq`) of a double with itself. -/
@[simp] theorem eq_self_iff (x : F64) : x.eq x = true ↔ x ≠ .nan := by
  cases x with
  | fin x => rw [eq_fin_fin]; simp
  | _ => simp [eq]

/-! ### The order on non-NaN doubles -/

/-- `>` and `>=` are `<` and `<=` with the arguments swapped. -/
theorem gt_eq_lt (x y : F64) : x.gt y = y.lt x := rfl
theorem ge_eq_le (x y : F64) : x.ge y = y.le x := rfl

/-- Case analysis on NaN, the two infinities and finite doubles, comparing finite doubles by
their exact values (`Fin64.sval`). -/
local macro "f64_order" : tactic => `(tactic| (
  try simp only [lt_fin_fin, le_fin_fin, eq_fin_fin] at *
  try simp_all [lt, le, eq]
  try omega))

theorem ne_nan_of_le {x y : F64} (h : x.le y = true) : x ≠ .nan ∧ y ≠ .nan := by
  rcases x with _ | ⟨_ | _⟩ | x <;> rcases y with _ | ⟨_ | _⟩ | y <;> simp_all [le]

theorem ne_nan_of_lt {x y : F64} (h : x.lt y = true) : x ≠ .nan ∧ y ≠ .nan := by
  rcases x with _ | ⟨_ | _⟩ | x <;> rcases y with _ | ⟨_ | _⟩ | y <;> simp_all [lt]

theorem le_refl_of_ne_nan {x : F64} (h : x ≠ .nan) : x.le x = true := by
  rcases x with _ | ⟨_ | _⟩ | x <;> f64_order

@[simp] theorem lt_irrefl (x : F64) : x.lt x = false := by
  rcases x with _ | ⟨_ | _⟩ | x <;> f64_order

theorem le_of_lt {x y : F64} (h : x.lt y = true) : x.le y = true := by
  rcases x with _ | ⟨_ | _⟩ | x <;> rcases y with _ | ⟨_ | _⟩ | y <;> f64_order

/-- **Totality**: for non-NaN doubles, `¬(x < y)` gives `y ≤ x`. -/
theorem le_of_not_lt {x y : F64} (hx : x ≠ .nan) (hy : y ≠ .nan) (h : x.lt y = false) :
    y.le x = true := by
  rcases x with _ | ⟨_ | _⟩ | x <;> rcases y with _ | ⟨_ | _⟩ | y <;> f64_order

theorem lt_of_not_le {x y : F64} (hx : x ≠ .nan) (hy : y ≠ .nan) (h : x.le y = false) :
    y.lt x = true := by
  rcases x with _ | ⟨_ | _⟩ | x <;> rcases y with _ | ⟨_ | _⟩ | y <;> f64_order

theorem not_lt_of_le {x y : F64} (h : x.le y = true) : y.lt x = false := by
  rcases x with _ | ⟨_ | _⟩ | x <;> rcases y with _ | ⟨_ | _⟩ | y <;> f64_order

theorem not_le_of_lt {x y : F64} (h : x.lt y = true) : y.le x = false := by
  rcases x with _ | ⟨_ | _⟩ | x <;> rcases y with _ | ⟨_ | _⟩ | y <;> f64_order

theorem le_total {x y : F64} (hx : x ≠ .nan) (hy : y ≠ .nan) : x.le y = true ∨ y.le x = true := by
  rcases x with _ | ⟨_ | _⟩ | x <;> rcases y with _ | ⟨_ | _⟩ | y <;> f64_order

theorem le_trans {x y z : F64} (h₁ : x.le y = true) (h₂ : y.le z = true) : x.le z = true := by
  rcases x with _ | ⟨_ | _⟩ | x <;> rcases y with _ | ⟨_ | _⟩ | y <;>
    rcases z with _ | ⟨_ | _⟩ | z <;> f64_order

theorem lt_of_lt_of_le {x y z : F64} (h₁ : x.lt y = true) (h₂ : y.le z = true) : x.lt z = true := by
  rcases x with _ | ⟨_ | _⟩ | x <;> rcases y with _ | ⟨_ | _⟩ | y <;>
    rcases z with _ | ⟨_ | _⟩ | z <;> f64_order

theorem lt_of_le_of_lt {x y z : F64} (h₁ : x.le y = true) (h₂ : y.lt z = true) : x.lt z = true := by
  rcases x with _ | ⟨_ | _⟩ | x <;> rcases y with _ | ⟨_ | _⟩ | y <;>
    rcases z with _ | ⟨_ | _⟩ | z <;> f64_order

theorem lt_trans {x y z : F64} (h₁ : x.lt y = true) (h₂ : y.lt z = true) : x.lt z = true :=
  lt_of_lt_of_le h₁ (le_of_lt h₂)

/-- Antisymmetry up to IEEE equality (`+0` and `-0` are equal but different doubles). -/
theorem eq_of_le_of_le {x y : F64} (h₁ : x.le y = true) (h₂ : y.le x = true) : x.eq y = true := by
  rcases x with _ | ⟨_ | _⟩ | x <;> rcases y with _ | ⟨_ | _⟩ | y <;> f64_order

end F64
end StrictTS
