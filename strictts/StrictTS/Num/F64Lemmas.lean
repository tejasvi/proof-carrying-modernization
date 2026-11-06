/-
StrictTS: facts about the binary64 model `StrictTS.F64`.

* `round` depends only on the value it rounds (`round_scale`) and returns representable values
  unchanged (`round_fin`); every finite double is `round x.neg x.mag (-1074)`.
* Safe-integer arithmetic (`|n| ≤ 2^53`) is exact: `add_ofInt`, `sub_ofInt`, `mul_ofInt`,
  comparisons, `floor`/`ceil`/`trunc`/`jsRound`, and `floor_div_ofInt` (JS `Math.floor(a / b)`).
* int32 arithmetic and bitwise operators become `BitVec 32` operations (`@[simp]` lemmas).
-/
import StrictTS.Num.F64

-- Proofs mention `2 ^ 1074` (every finite double is a multiple of `2^-1074`); allow the
-- elaborator to evaluate such powers instead of warning about them.
set_option exponentiation.threshold 2200

namespace StrictTS
namespace F64

/-- Safe integers in the sense of these lemmas: `|n| ≤ 2^53` (every such integer is a double).
An `abbrev`, so `omega` discharges it; use the conditional `@[simp]` lemmas below with
`simp (disch := omega)`. -/
abbrev Safe (n : Int) : Prop := -2^53 ≤ n ∧ n ≤ 2^53

/-! ## `bitLen` -/

theorem bitLen_le_iff (m L : Nat) : bitLen m ≤ L ↔ m < 2 ^ L := by
  unfold bitLen
  split
  · rename_i h; subst h; simp [Nat.two_pow_pos]
  · rename_i h
    have := Nat.log2_lt (k := L) h
    omega

theorem lt_two_pow_bitLen (m : Nat) : m < 2 ^ bitLen m := (bitLen_le_iff m _).1 (Nat.le_refl _)

theorem two_pow_le_of_lt_bitLen {m L : Nat} (h : L < bitLen m) : 2 ^ L ≤ m := by
  have := (not_congr (bitLen_le_iff m L)).1 (by omega)
  omega

theorem bitLen_pos {m : Nat} (h : m ≠ 0) : 0 < bitLen m := by
  unfold bitLen; simp [h]

theorem two_pow_bitLen_sub_one_le {m : Nat} (h : m ≠ 0) : 2 ^ (bitLen m - 1) ≤ m :=
  two_pow_le_of_lt_bitLen (by have := bitLen_pos h; omega)

theorem bitLen_mul_pow (m k : Nat) (h : m ≠ 0) : bitLen (m * 2 ^ k) = bitLen m + k := by
  have hp := bitLen_pos h
  apply Nat.le_antisymm
  · rw [bitLen_le_iff, Nat.pow_add]
    exact Nat.mul_lt_mul_of_pos_right (lt_two_pow_bitLen m) (Nat.two_pow_pos k)
  · have h2 : 2 ^ (bitLen m - 1 + k) ≤ m * 2 ^ k := by
      rw [Nat.pow_add]; exact Nat.mul_le_mul_right _ (two_pow_bitLen_sub_one_le h)
    have h3 : ¬ bitLen (m * 2 ^ k) ≤ bitLen m - 1 + k := by
      rw [bitLen_le_iff]; omega
    omega

theorem bitLen_eq_of_le_of_lt {m L : Nat} (h1 : 2 ^ L ≤ m) (h2 : m < 2 ^ (L + 1)) :
    bitLen m = L + 1 := by
  have hm : m ≠ 0 := by have := Nat.two_pow_pos L; omega
  have a := (bitLen_le_iff m (L + 1)).2 h2
  have b : ¬ bitLen m ≤ L := by rw [bitLen_le_iff]; omega
  omega

/-! ## Structure of `round` -/

/-- Round-up decision of `round` when the low `s` bits of `m` are dropped. -/
def rUp (m s : Nat) (sticky : Bool) : Bool :=
  if sticky then decide (2 ^ (s - 1) ≤ m % 2 ^ s)
  else decide (2 ^ (s - 1) < m % 2 ^ s) || (decide (m % 2 ^ s = 2 ^ (s - 1)) && (m >>> s) % 2 == 1)

/-- Rounded significand before renormalization. -/
def rMant (m s : Nat) (sticky : Bool) : Nat := if rUp m s sticky then (m >>> s) + 1 else m >>> s

/-- Final step of `round`: renormalize a carry to `2^53` and check for overflow. -/
def pack (neg : Bool) (man1 : Nat) (q : Int) : F64 :=
  if (if man1 = 2 ^ 53 then q + 1 else q) > 971 then .inf neg
  else mkFin neg (if man1 = 2 ^ 53 then 2 ^ 52 else man1) (if man1 = 2 ^ 53 then q + 1 else q)

/-- Quantum exponent chosen by `round`. -/
def qexp (m : Nat) (e : Int) : Int := Max.max (e + (bitLen m : Int) - 1 - 52) (-1074)

theorem round_eq (neg : Bool) (m : Nat) (e : Int) (sticky : Bool) (h : ¬(m = 0 ∧ sticky = false)) :
    round neg m e sticky =
      if qexp m e ≤ e then
        (if qexp m e > 971 then .inf neg else mkFin neg (m * 2 ^ (e - qexp m e).toNat) (qexp m e))
      else pack neg (rMant m (qexp m e - e).toNat sticky) (qexp m e) := by
  rw [round]
  simp only [h, ↓reduceIte]
  rfl

theorem round_zero (neg : Bool) (e : Int) : round neg 0 e = mkFin neg 0 (-1074) := by
  simp [round]

theorem rMant_mul_pow_add (m s k : Nat) (st : Bool) (hs : 1 ≤ s) :
    rMant (m * 2 ^ k) (s + k) st = rMant m s st := by
  have hP : 0 < 2 ^ k := Nat.two_pow_pos k
  have hdiv : (m * 2 ^ k) >>> (s + k) = m >>> s := by
    rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow, Nat.pow_add,
      Nat.mul_div_mul_right _ _ hP]
  have hmod : (m * 2 ^ k) % 2 ^ (s + k) = (m % 2 ^ s) * 2 ^ k := by
    rw [Nat.pow_add, Nat.mul_mod_mul_right]
  have hhalf : 2 ^ (s + k - 1) = 2 ^ (s - 1) * 2 ^ k := by
    rw [← Nat.pow_add]; congr 1; omega
  unfold rMant rUp
  rw [hdiv, hmod, hhalf]
  simp only [Nat.mul_le_mul_right_iff hP, Nat.mul_lt_mul_right hP, Nat.mul_right_cancel_iff hP]

theorem rMant_mul_pow_le (m s k : Nat) (_hs : 1 ≤ s) (hk : s ≤ k) :
    rMant (m * 2 ^ k) s false = m * 2 ^ (k - s) := by
  have hk' : 2 ^ k = 2 ^ (k - s) * 2 ^ s := by rw [← Nat.pow_add]; congr 1; omega
  have hdiv : (m * 2 ^ k) >>> s = m * 2 ^ (k - s) := by
    rw [Nat.shiftRight_eq_div_pow, hk', ← Nat.mul_assoc, Nat.mul_div_cancel _ (Nat.two_pow_pos s)]
  have hmod : (m * 2 ^ k) % 2 ^ s = 0 := by
    rw [hk', ← Nat.mul_assoc]; exact Nat.mul_mod_left _ _
  have hh : 0 < 2 ^ (s - 1) := Nat.two_pow_pos _
  unfold rMant rUp
  rw [hdiv, hmod]
  have : (0 = 2 ^ (s - 1)) = False := by simp; omega
  simp [this]

theorem pack_of_ne (neg : Bool) (man : Nat) (q : Int) (h : man ≠ 2 ^ 53) :
    pack neg man q = if q > 971 then .inf neg else mkFin neg man q := by
  simp [pack, h]

theorem round_scale (neg : Bool) (m k : Nat) (e : Int) :
    round neg (m * 2 ^ k) e = round neg m (e + k) := by
  by_cases hm : m = 0
  · subst hm; simp [round]
  have hmk : m * 2 ^ k ≠ 0 := Nat.mul_ne_zero hm (Nat.pos_iff_ne_zero.1 (Nat.two_pow_pos k))
  rw [round_eq _ _ _ _ (by simp [hmk]), round_eq _ _ _ _ (by simp [hm])]
  have hq : qexp (m * 2 ^ k) e = qexp m (e + k) := by
    unfold qexp; rw [bitLen_mul_pow m k hm]; push_cast
    congr 1; omega
  rw [hq]
  have hq1 := Int.le_max_left (e + k + (bitLen m : Int) - 1 - 52) (-1074)
  have hlt := lt_two_pow_bitLen m
  generalize hQ : qexp m (e + k) = q
  have hq1 : e + k + (bitLen m : Int) - 1 - 52 ≤ q := by rw [← hQ]; exact hq1
  by_cases h1 : q ≤ e
  · have h2 : q ≤ e + k := by omega
    simp only [h1, h2, ite_true]
    have : m * 2 ^ k * 2 ^ (e - q).toNat = m * 2 ^ (e + ↑k - q).toNat := by
      rw [Nat.mul_assoc, ← Nat.pow_add]; congr 2; omega
    rw [this]
  · by_cases h2 : q ≤ e + k
    · simp only [h1, h2, ite_true, ite_false]
      rw [rMant_mul_pow_le m _ k (by omega) (by omega)]
      have he : k - (q - e).toNat = (e + ↑k - q).toNat := by omega
      rw [he]
      have hlt2 : m * 2 ^ (e + ↑k - q).toNat < 2 ^ 53 := by
        have : bitLen m + (e + ↑k - q).toNat ≤ 53 := by omega
        calc m * 2 ^ (e + ↑k - q).toNat < 2 ^ bitLen m * 2 ^ (e + ↑k - q).toNat :=
              Nat.mul_lt_mul_of_pos_right hlt (Nat.two_pow_pos _)
          _ = 2 ^ (bitLen m + (e + ↑k - q).toNat) := by rw [Nat.pow_add]
          _ ≤ 2 ^ 53 := Nat.pow_le_pow_right (by decide) this
      rw [pack_of_ne _ _ _ (Nat.ne_of_lt hlt2)]
    · simp only [h1, h2, ite_false]
      have : (q - e).toNat = (q - (e + k)).toNat + k := by omega
      rw [this, rMant_mul_pow_add m _ k false (by omega)]

end F64

/-! ## Exact values: every finite double is a multiple of `2^-1074` -/

namespace Fin64

theorem exp_ge (x : Fin64) : -1074 ≤ x.exp := by rcases x.valid with h | h <;> omega
theorem exp_le (x : Fin64) : x.exp ≤ 971 := by rcases x.valid with h | h <;> omega
theorem man_lt (x : Fin64) : x.man < 2 ^ 53 := by rcases x.valid with h | h <;> omega
theorem exp_of_man_lt {x : Fin64} (h : x.man < 2 ^ 52) : x.exp = -1074 := by
  rcases x.valid with h' | h' <;> omega

/-- `|x| * 2^1074`, a natural number for every finite double. -/
def mag (x : Fin64) : Nat := x.man * 2 ^ (x.exp + 1074).toNat

/-- `x * 2^1074` as an integer. -/
def sval (x : Fin64) : Int := if x.neg then -(x.mag : Int) else x.mag

theorem mag_eq_zero_iff (x : Fin64) : x.mag = 0 ↔ x.man = 0 := by
  unfold mag
  constructor
  · intro h
    rcases Nat.mul_eq_zero.1 h with h | h
    · exact h
    · exact absurd h (Nat.pos_iff_ne_zero.1 (Nat.two_pow_pos _))
  · intro h; simp [h]

theorem intMag_eq (x : Fin64) : x.intMag = x.mag / 2 ^ 1074 := by
  unfold intMag mag
  have := x.exp_ge
  split
  · rename_i h
    rw [Nat.shiftLeft_eq]
    have : (x.exp + 1074).toNat = x.exp.toNat + 1074 := by omega
    rw [this, Nat.pow_add, ← Nat.mul_assoc, Nat.mul_div_cancel _ (Nat.two_pow_pos _)]
  · rename_i h
    rw [Nat.shiftRight_eq_div_pow]
    have h2 : (2 : Nat) ^ 1074 = 2 ^ (x.exp + 1074).toNat * 2 ^ (-x.exp).toNat := by
      rw [← Nat.pow_add]; congr 1; omega
    rw [h2, Nat.mul_comm (2 ^ (x.exp + 1074).toNat), Nat.mul_div_mul_right _ _ (Nat.two_pow_pos _)]

theorem fracMag_eq_zero_iff (x : Fin64) : x.fracMag = 0 ↔ x.mag % 2 ^ 1074 = 0 := by
  unfold fracMag mag
  have := x.exp_ge
  by_cases h : 0 ≤ x.exp
  · have h0 : (-x.exp).toNat = 0 := by omega
    have : (x.exp + 1074).toNat = x.exp.toNat + 1074 := by omega
    rw [h0, this, Nat.pow_add, ← Nat.mul_assoc, Nat.mul_mod_left]
    simp
  · have h2 : (2 : Nat) ^ 1074 = 2 ^ (-x.exp).toNat * 2 ^ (x.exp + 1074).toNat := by
      rw [← Nat.pow_add]; congr 1; omega
    rw [h2, Nat.mul_mod_mul_right, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
    have hp := Nat.two_pow_pos (x.exp + 1074).toNat
    have hm := Nat.div_add_mod x.man (2 ^ (-x.exp).toNat)
    constructor
    · intro h1
      have : x.man % 2 ^ (-x.exp).toNat = 0 := by
        rw [Nat.mul_comm] at hm; omega
      rw [this]; simp
    · intro h1
      have : x.man % 2 ^ (-x.exp).toNat = 0 := by
        rcases Nat.mul_eq_zero.1 h1 with h1 | h1
        · exact h1
        · omega
      rw [Nat.mul_comm] at hm; omega

end Fin64

namespace F64

theorem mkFin_eq {neg : Bool} {man : Nat} {exp : Int}
    (h : (2^52 ≤ man ∧ man < 2^53 ∧ -1074 ≤ exp ∧ exp ≤ 971) ∨ (man < 2^52 ∧ exp = -1074)) :
    mkFin neg man exp = .fin ⟨neg, man, exp, h⟩ := by
  simp only [mkFin, h, ↓reduceDIte]

theorem round_fin (x : Fin64) : round x.neg x.man x.exp = .fin x := by
  by_cases hm : x.man = 0
  · have he : x.exp = -1074 := Fin64.exp_of_man_lt (by omega)
    rw [hm, round_zero, mkFin_eq (Or.inr ⟨by omega, rfl⟩)]
    cases x; simp_all
  · rw [round_eq _ _ _ _ (by simp [hm])]
    have hq : qexp x.man x.exp = x.exp := by
      unfold qexp
      rcases x.valid with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2⟩
      · have := bitLen_eq_of_le_of_lt (L := 52) h1 h2; rw [this]; omega
      · have : bitLen x.man ≤ 52 := (bitLen_le_iff _ _).2 h1; omega
    have h971 := x.exp_le
    rw [hq]
    simp only [Int.le_refl, ite_true, show ¬ x.exp > 971 by omega, ite_false, Int.sub_self,
      Int.toNat_zero, Nat.pow_zero, Nat.mul_one]
    rw [mkFin_eq x.valid]

/-- Every finite double is the rounding of its exact value, scaled to exponent `-1074`. -/
theorem fin_eq_round_mag (x : Fin64) : F64.fin x = round x.neg x.mag (-1074) := by
  rw [Fin64.mag, round_scale]
  have := x.exp_ge
  have : (-1074 : Int) + ((x.exp + 1074).toNat : Nat) = x.exp := by omega
  rw [this, round_fin]

/-- Rounding an integer: the same as rounding its `2^1074` multiple at exponent `-1074`. -/
theorem round_int (s : Bool) (N : Nat) : round s N 0 = round s (N * 2 ^ 1074) (-1074) := by
  rw [round_scale]; rfl

theorem fin_eq_round_intMag (x : Fin64) (h : x.fracMag = 0) :
    F64.fin x = round x.neg x.intMag 0 := by
  rw [round_int, Fin64.intMag_eq, fin_eq_round_mag]
  rw [Fin64.fracMag_eq_zero_iff] at h
  rw [Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero h)]

theorem ofInt_spec (n : Int) (h : Safe n) :
    ∃ x : Fin64, ofInt n = .fin x ∧ x.neg = decide (n < 0) ∧ x.mag = n.natAbs * 2 ^ 1074 := by
  unfold ofInt
  have hN : n.natAbs ≤ 2 ^ 53 := by omega
  generalize decide (n < 0) = s
  generalize n.natAbs = N at hN ⊢
  rcases Nat.lt_or_ge N (2 ^ 53) with hlt | hge
  · by_cases h0 : N = 0
    · subst h0
      refine ⟨⟨s, 0, -1074, Or.inr ⟨by decide, rfl⟩⟩, ?_, rfl, by simp [Fin64.mag]⟩
      rw [round_zero, mkFin_eq]
    · have hL1 := two_pow_bitLen_sub_one_le h0
      have hL2 := lt_two_pow_bitLen N
      have hLle : bitLen N ≤ 53 := (bitLen_le_iff _ _).2 hlt
      have hLpos := bitLen_pos h0
      have hq : qexp N 0 = (bitLen N : Int) - 53 := by unfold qexp; omega
      rw [round_eq _ _ _ _ (by simp [h0]), hq]
      simp only [show (bitLen N : Int) - 53 ≤ 0 by omega, ite_true,
        show ¬ ((bitLen N : Int) - 53 > 971) by omega, ite_false]
      have ht : (0 - ((bitLen N : Int) - 53)).toNat = 53 - bitLen N := by omega
      rw [ht]
      have hv1 : 2 ^ 52 ≤ N * 2 ^ (53 - bitLen N) := by
        calc 2 ^ 52 = 2 ^ (bitLen N - 1) * 2 ^ (53 - bitLen N) := by
              rw [← Nat.pow_add]; congr 1; omega
          _ ≤ N * 2 ^ (53 - bitLen N) := Nat.mul_le_mul_right _ hL1
      have hv2 : N * 2 ^ (53 - bitLen N) < 2 ^ 53 := by
        calc N * 2 ^ (53 - bitLen N) < 2 ^ bitLen N * 2 ^ (53 - bitLen N) :=
              Nat.mul_lt_mul_of_pos_right hL2 (Nat.two_pow_pos _)
          _ = 2 ^ 53 := by rw [← Nat.pow_add]; congr 1; omega
      refine ⟨⟨s, N * 2 ^ (53 - bitLen N), (bitLen N : Int) - 53,
        Or.inl ⟨hv1, hv2, by omega, by omega⟩⟩, mkFin_eq _, rfl, ?_⟩
      simp only [Fin64.mag]
      rw [Nat.mul_assoc, ← Nat.pow_add]; congr 2; omega
  · have : N = 2 ^ 53 := by omega
    subst this
    refine ⟨⟨s, 2 ^ 52, 1, Or.inl ⟨by decide, by decide, by decide, by decide⟩⟩, ?_, rfl, ?_⟩
    · cases s <;> decide +kernel
    · simp only [Fin64.mag]
      have h1 : ((1 : Int) + 1074).toNat = 1 + 1074 := rfl
      rw [h1, Nat.pow_add 2 1 1074, ← Nat.mul_assoc, ← Nat.pow_add]

theorem neg_mkFin (s : Bool) (m : Nat) (e : Int) : neg (mkFin s m e) = mkFin (!s) m e := by
  unfold mkFin; split <;> simp [neg]

theorem neg_round (s : Bool) (m : Nat) (e : Int) (st : Bool) :
    neg (round s m e st) = round (!s) m e st := by
  by_cases h : m = 0 ∧ st = false
  · rcases h with ⟨rfl, rfl⟩; simp [round_zero, neg_mkFin]
  · rw [round_eq _ _ _ _ h, round_eq _ _ _ _ h]
    split
    · split
      · rfl
      · exact neg_mkFin _ _ _
    · unfold pack
      split <;> split <;> first | rfl | exact neg_mkFin _ _ _

end F64

namespace Fin64

theorem minExp_le_left (x y : Fin64) : x.minExp y ≤ x.exp := by
  unfold minExp; split <;> omega

theorem minExp_le_right (x y : Fin64) : x.minExp y ≤ y.exp := by
  unfold minExp; split <;> omega

theorem minExp_ge (x y : Fin64) : -1074 ≤ x.minExp y := by
  have := x.exp_ge; have := y.exp_ge
  unfold minExp; split <;> omega

theorem sint_mul (x : Fin64) (e : Int) (h1 : e ≤ x.exp) (h2 : -1074 ≤ e) :
    x.sint (x.exp - e).toNat * ((2 ^ (e + 1074).toNat : Nat) : Int) = x.sval := by
  have key : (x.man <<< (x.exp - e).toNat) * 2 ^ (e + 1074).toNat = x.mag := by
    rw [Nat.shiftLeft_eq, Nat.mul_assoc, ← Nat.pow_add, mag]
    congr 2; omega
  unfold sint sval
  split
  · rw [Int.neg_mul, ← Int.natCast_mul, key]
  · rw [← Int.natCast_mul, key]

theorem ints_fst_mul (x y : Fin64) :
    (x.ints y).1 * ((2 ^ (x.minExp y + 1074).toNat : Nat) : Int) = x.sval :=
  sint_mul x _ (minExp_le_left x y) (minExp_ge x y)

theorem ints_snd_mul (x y : Fin64) :
    (x.ints y).2 * ((2 ^ (x.minExp y + 1074).toNat : Nat) : Int) = y.sval :=
  sint_mul y _ (minExp_le_right x y) (minExp_ge x y)

theorem sval_eq (x : Fin64) (n : Int) (h1 : x.neg = decide (n < 0))
    (h2 : x.mag = n.natAbs * 2 ^ 1074) : x.sval = n * ((2 ^ 1074 : Nat) : Int) := by
  unfold sval
  rw [h1, h2, Int.natCast_mul]
  by_cases hn : n < 0
  · simp only [hn, decide_true, ite_true]
    rw [← Int.neg_mul]; congr 1; omega
  · simp only [hn, decide_false]
    simp only [Bool.false_eq_true, ite_false]
    congr 1; omega

end Fin64

namespace F64

/-! ## Aligned significands, addition -/

theorem round_scaled (s : Int) (j : Nat) (e : Int) (hj : (-1074 : Int) + j = e) :
    round (decide (s * ((2 ^ j : Nat) : Int) < 0)) (s * ((2 ^ j : Nat) : Int)).natAbs (-1074) =
      round (decide (s < 0)) s.natAbs e := by
  have hp : (0 : Int) < ((2 ^ j : Nat) : Int) := by have := Nat.two_pow_pos j; omega
  have h1 : decide (s * ((2 ^ j : Nat) : Int) < 0) = decide (s < 0) := by
    apply decide_eq_decide.2
    constructor
    · intro h; apply Classical.byContradiction; intro h'
      have : 0 ≤ s * ((2 ^ j : Nat) : Int) := Int.mul_nonneg (by omega) (by omega)
      omega
    · intro h; exact Int.mul_neg_of_neg_of_pos h hp
  rw [h1, Int.natAbs_mul, Int.natAbs_natCast, round_scale, hj]

theorem fin_eq_round_sval (x : Fin64) (h0 : x.man ≠ 0) :
    F64.fin x = round (decide (x.sval < 0)) x.sval.natAbs (-1074) := by
  have hm : x.mag ≠ 0 := fun h => h0 ((Fin64.mag_eq_zero_iff x).1 h)
  have h1 : decide (x.sval < 0) = x.neg := by
    unfold Fin64.sval; cases x.neg <;> simp <;> omega
  have h2 : x.sval.natAbs = x.mag := by unfold Fin64.sval; split <;> simp
  rw [h1, h2, fin_eq_round_mag]

theorem add_fin_fin (x y : Fin64) (hx : x.man ≠ 0) (hy : y.man ≠ 0) :
    F64.fin x + F64.fin y =
      round (decide (x.sval + y.sval < 0)) (x.sval + y.sval).natAbs (-1074) := by
  show add (.fin x) (.fin y) = _
  simp only [add, hx, hy, ite_false]
  rw [← Fin64.ints_fst_mul x y, ← Fin64.ints_snd_mul x y, ← Int.add_mul,
    round_scaled _ _ (x.minExp y) (by have := Fin64.minExp_ge x y; omega)]

theorem ofInt_zero : ofInt 0 = .fin ⟨false, 0, -1074, Or.inr ⟨by decide, rfl⟩⟩ := by decide

theorem ofInt_man_eq_zero {n : Int} {x : Fin64} (h1 : x.mag = n.natAbs * 2 ^ 1074) :
    x.man = 0 ↔ n = 0 := by
  rw [← Fin64.mag_eq_zero_iff, h1]
  constructor
  · intro h
    rcases Nat.mul_eq_zero.1 h with h | h
    · omega
    · exact absurd h (Nat.pos_iff_ne_zero.1 (Nat.two_pow_pos _))
  · intro h; subst h; simp

/-- Exact addition of safe integers (`x + -x` is `+0`). -/
@[simp] theorem add_ofInt {a b : Int} (ha : Safe a) (hb : Safe b) (hab : Safe (a + b)) :
    ofInt a + ofInt b = ofInt (a + b) := by
  obtain ⟨x, hx1, hx2, hx3⟩ := ofInt_spec a ha
  obtain ⟨y, hy1, hy2, hy3⟩ := ofInt_spec b hb
  have hxm := ofInt_man_eq_zero hx3
  have hym := ofInt_man_eq_zero hy3
  by_cases a0 : a = 0
  · subst a0
    rw [Int.zero_add, hx1, hy1]
    show add _ _ = _
    by_cases b0 : b = 0
    · subst b0
      simp only [add, hxm.2 rfl, hym.2 rfl, ite_true, hx2, hy2]
      rw [← hy1]; decide
    · simp only [add, hxm.2 rfl, (not_congr hym).2 b0, ite_true, ite_false]
  · by_cases b0 : b = 0
    · subst b0
      rw [Int.add_zero, hx1, hy1]
      show add _ _ = _
      simp only [add, (not_congr hxm).2 a0, hym.2 rfl, ite_true, ite_false]
    · rw [hx1, hy1, add_fin_fin x y ((not_congr hxm).2 a0) ((not_congr hym).2 b0),
        Fin64.sval_eq x a hx2 hx3, Fin64.sval_eq y b hy2 hy3, ← Int.add_mul,
        round_scaled (a + b) 1074 0 (by omega)]
      rfl


theorem ofInt_fin (n : Int) (h : Safe n) :
    ∃ x : Fin64, ofInt n = .fin x ∧ x.neg = decide (n < 0) ∧ x.mag = n.natAbs * 2 ^ 1074 ∧
      x.fracMag = 0 ∧ x.intMag = n.natAbs := by
  obtain ⟨x, h1, h2, h3⟩ := ofInt_spec n h
  refine ⟨x, h1, h2, h3, ?_, ?_⟩
  · rw [Fin64.fracMag_eq_zero_iff, h3, Nat.mul_mod_left]
  · rw [Fin64.intMag_eq, h3, Nat.mul_div_cancel _ (Nat.two_pow_pos _)]

/-! ## Safe integers: exact conversion -/

/-- Safe integers convert to doubles exactly. -/
@[simp] theorem toInt?_ofInt {n : Int} (h : Safe n) : (ofInt n).toInt? = some n := by
  obtain ⟨x, h1, h2, -, h4, h5⟩ := ofInt_fin n h
  rw [h1]
  simp only [toInt?, h4, h5, h2, ite_true]
  congr 1
  by_cases hn : n < 0 <;> simp [hn] <;> omega

theorem ofInt_inj {a b : Int} (ha : Safe a) (hb : Safe b) (h : ofInt a = ofInt b) : a = b := by
  have := toInt?_ofInt ha
  rw [h, toInt?_ofInt hb] at this
  exact (Option.some.inj this).symm

@[simp] theorem ofInt_inj_iff {a b : Int} (ha : Safe a) (hb : Safe b) :
    ofInt a = ofInt b ↔ a = b :=
  ⟨ofInt_inj ha hb, fun h => h ▸ rfl⟩

theorem ofNat_eq_ofInt (n : Nat) : ofNat n = ofInt n := by
  have : ¬ ((n : Int) < 0) := by omega
  simp [ofNat, ofInt, this]

/-! ## Safe integers: arithmetic -/

/-- Negation of a nonzero integer (no `Safe` needed; `-(ofInt 0)` is `-0`). -/
@[simp] theorem neg_ofInt {n : Int} (h : n ≠ 0) : -(ofInt n) = ofInt (-n) := by
  show neg (round _ _ _) = round _ _ _
  rw [neg_round]
  congr 1
  · by_cases hn : n < 0
    · rw [decide_eq_true hn, decide_eq_false (by omega)]; rfl
    · rw [decide_eq_false hn, decide_eq_true (by omega)]; rfl
  · simp

/-- Exact subtraction of safe integers (`3 - 3` is `+0`). -/
@[simp] theorem sub_ofInt {a b : Int} (ha : Safe a) (hb : Safe b) (hab : Safe (a - b)) :
    ofInt a - ofInt b = ofInt (a - b) := by
  show add (ofInt a) (neg (ofInt b)) = _
  by_cases b0 : b = 0
  · subst b0
    obtain ⟨x, hx1, hx2, hx3⟩ := ofInt_spec a ha
    have hxm := ofInt_man_eq_zero hx3
    rw [Int.sub_zero, hx1, ofInt_zero]
    simp only [neg]
    by_cases a0 : a = 0
    · subst a0
      simp only [add, hxm.2 rfl, ite_true, hx2]
      rw [← hx1]; decide
    · simp only [add, (not_congr hxm).2 a0, ite_false, ite_true]
  · have h1 : neg (ofInt b) = ofInt (-b) := neg_ofInt b0
    rw [h1, Int.sub_eq_add_neg]
    exact add_ofInt (a := a) (b := -b) ha (by omega) (by omega)

theorem mul_fin_fin (x y : Fin64) :
    F64.fin x * F64.fin y = round (x.neg ^^ y.neg) (x.mag * y.mag) (-2148) := by
  show mul (.fin x) (.fin y) = _
  simp only [mul]
  have hx := x.exp_ge
  have hy := y.exp_ge
  have : x.mag * y.mag =
      (x.man * y.man) * 2 ^ ((x.exp + 1074).toNat + (y.exp + 1074).toNat) := by
    simp only [Fin64.mag, Nat.pow_add]
    rw [Nat.mul_assoc, Nat.mul_assoc, Nat.mul_left_comm (2 ^ _) y.man]
  rw [this, round_scale]
  congr 1
  omega

theorem xor_sign (a b : Int) (ha : a ≠ 0) (hb : b ≠ 0) :
    (decide (a < 0) ^^ decide (b < 0)) = decide (a * b < 0) := by
  rcases Int.lt_or_gt_of_ne ha with ha' | ha' <;> rcases Int.lt_or_gt_of_ne hb with hb' | hb'
  · have hp : 0 < a * b := Int.mul_pos_of_neg_of_neg ha' hb'
    rw [decide_eq_true ha', decide_eq_true hb', decide_eq_false (by omega)]; rfl
  · have hp : a * b < 0 := Int.mul_neg_of_neg_of_pos ha' hb'
    rw [decide_eq_true ha', decide_eq_false (by omega), decide_eq_true hp]; rfl
  · have hp : a * b < 0 := Int.mul_neg_of_pos_of_neg ha' hb'
    rw [decide_eq_false (by omega), decide_eq_true hb', decide_eq_true hp]; rfl
  · have hp : 0 < a * b := Int.mul_pos ha' hb'
    rw [decide_eq_false (by omega), decide_eq_false (by omega), decide_eq_false (by omega)]; rfl

/-- Exact multiplication of safe integers with a nonzero product (`0 * -3` is `-0`). -/
@[simp] theorem mul_ofInt {a b : Int} (ha : Safe a) (hb : Safe b) (_hab : Safe (a * b))
    (h0 : a * b ≠ 0) :
    ofInt a * ofInt b = ofInt (a * b) := by
  have a0 : a ≠ 0 := fun h => h0 (by rw [h, Int.zero_mul])
  have b0 : b ≠ 0 := fun h => h0 (by rw [h, Int.mul_zero])
  obtain ⟨x, hx1, hx2, hx3⟩ := ofInt_spec a ha
  obtain ⟨y, hy1, hy2, hy3⟩ := ofInt_spec b hb
  rw [hx1, hy1, mul_fin_fin, hx2, hy2, hx3, hy3, xor_sign a b a0 b0]
  have : a.natAbs * 2 ^ 1074 * (b.natAbs * 2 ^ 1074) = (a * b).natAbs * 2 ^ 2148 := by
    rw [Int.natAbs_mul, show (2 : Nat) ^ 2148 = 2 ^ 1074 * 2 ^ 1074 by rw [← Nat.pow_add]]
    rw [Nat.mul_assoc, Nat.mul_assoc, Nat.mul_left_comm (2 ^ 1074) b.natAbs]
  rw [this, round_scale]
  rfl

/-! ## Safe integers: comparisons -/

theorem pow_minExp_pos (x y : Fin64) : (0 : Int) < ((2 ^ (x.minExp y + 1074).toNat : Nat) : Int) := by
  have := Nat.two_pow_pos (x.minExp y + 1074).toNat; omega

theorem lt_fin_fin (x y : Fin64) : (F64.fin x).lt (F64.fin y) = decide (x.sval < y.sval) := by
  simp only [lt]
  apply decide_eq_decide.2
  rw [← Fin64.ints_fst_mul x y, ← Fin64.ints_snd_mul x y]
  exact (Int.mul_lt_mul_right (pow_minExp_pos x y)).symm

theorem le_fin_fin (x y : Fin64) : (F64.fin x).le (F64.fin y) = decide (x.sval ≤ y.sval) := by
  simp only [le]
  apply decide_eq_decide.2
  rw [← Fin64.ints_fst_mul x y, ← Fin64.ints_snd_mul x y]
  exact (Int.mul_le_mul_right (pow_minExp_pos x y)).symm

theorem eq_fin_fin (x y : Fin64) : (F64.fin x).eq (F64.fin y) = decide (x.sval = y.sval) := by
  simp only [eq]
  apply decide_eq_decide.2
  rw [← Fin64.ints_fst_mul x y, ← Fin64.ints_snd_mul x y]
  exact (Int.mul_eq_mul_right_iff (Int.ne_of_gt (pow_minExp_pos x y))).symm

theorem pow1074_pos : (0 : Int) < ((2 ^ 1074 : Nat) : Int) := by
  have := Nat.two_pow_pos 1074; omega

@[simp] theorem lt_ofInt {a b : Int} (ha : Safe a) (hb : Safe b) :
    (ofInt a).lt (ofInt b) = decide (a < b) := by
  obtain ⟨x, hx1, hx2, hx3⟩ := ofInt_spec a ha
  obtain ⟨y, hy1, hy2, hy3⟩ := ofInt_spec b hb
  rw [hx1, hy1, lt_fin_fin, Fin64.sval_eq x a hx2 hx3, Fin64.sval_eq y b hy2 hy3]
  exact decide_eq_decide.2 (Int.mul_lt_mul_right pow1074_pos)

@[simp] theorem le_ofInt {a b : Int} (ha : Safe a) (hb : Safe b) :
    (ofInt a).le (ofInt b) = decide (a ≤ b) := by
  obtain ⟨x, hx1, hx2, hx3⟩ := ofInt_spec a ha
  obtain ⟨y, hy1, hy2, hy3⟩ := ofInt_spec b hb
  rw [hx1, hy1, le_fin_fin, Fin64.sval_eq x a hx2 hx3, Fin64.sval_eq y b hy2 hy3]
  exact decide_eq_decide.2 (Int.mul_le_mul_right pow1074_pos)

@[simp] theorem eq_ofInt {a b : Int} (ha : Safe a) (hb : Safe b) :
    (ofInt a).eq (ofInt b) = decide (a = b) := by
  obtain ⟨x, hx1, hx2, hx3⟩ := ofInt_spec a ha
  obtain ⟨y, hy1, hy2, hy3⟩ := ofInt_spec b hb
  rw [hx1, hy1, eq_fin_fin, Fin64.sval_eq x a hx2 hx3, Fin64.sval_eq y b hy2 hy3]
  exact decide_eq_decide.2 (Int.mul_eq_mul_right_iff (Int.ne_of_gt pow1074_pos))

@[simp] theorem gt_ofInt {a b : Int} (ha : Safe a) (hb : Safe b) :
    (ofInt a).gt (ofInt b) = decide (a > b) := lt_ofInt hb ha

@[simp] theorem ge_ofInt {a b : Int} (ha : Safe a) (hb : Safe b) :
    (ofInt a).ge (ofInt b) = decide (a ≥ b) := le_ofInt hb ha

/-! ## Safe integers: `floor`, `ceil`, `trunc`, `Math.round` are the identity -/

@[simp] theorem floor_ofInt {n : Int} (h : Safe n) : (ofInt n).floor = ofInt n := by
  obtain ⟨x, hx1, -, -, hx4, -⟩ := ofInt_fin n h
  rw [hx1]; simp [floor, hx4]

@[simp] theorem ceil_ofInt {n : Int} (h : Safe n) : (ofInt n).ceil = ofInt n := by
  obtain ⟨x, hx1, -, -, hx4, -⟩ := ofInt_fin n h
  rw [hx1]; simp [ceil, hx4]

@[simp] theorem trunc_ofInt {n : Int} (h : Safe n) : (ofInt n).trunc = ofInt n := by
  obtain ⟨x, hx1, -, -, hx4, -⟩ := ofInt_fin n h
  rw [hx1]; simp [trunc, hx4]

@[simp] theorem jsRound_ofInt {n : Int} (h : Safe n) : (ofInt n).jsRound = ofInt n := by
  obtain ⟨x, hx1, -, -, hx4, -⟩ := ofInt_fin n h
  rw [hx1]; simp [jsRound, hx4]

/-! ## int32 conversions -/

theorem truncInt_ofInt {n : Int} (h : Safe n) : (ofInt n).truncInt = n := by
  obtain ⟨x, hx1, hx2, -, -, hx5⟩ := ofInt_fin n h
  rw [hx1]; simp only [truncInt, hx2, hx5]
  by_cases hn : n < 0 <;> simp [hn] <;> omega

@[simp] theorem toBitsN_ofInt (w : Nat) {n : Int} (h : Safe n) :
    (ofInt n).toBitsN w = BitVec.ofInt w n := by
  simp only [toBitsN, truncInt_ofInt h]

@[simp] theorem toInt32_ofInt {n : Int} (h : Safe n) : (ofInt n).toInt32 = BitVec.ofInt 32 n :=
  toBitsN_ofInt 32 h

theorem ofInt32_eq (b : BitVec 32) : ofInt32 b = ofInt b.toInt := rfl

theorem ofUint32_eq (b : BitVec 32) : ofUint32 b = ofInt b.toNat := rfl

theorem toInt_bounds (b : BitVec 32) : -2 ^ 31 ≤ b.toInt ∧ b.toInt < 2 ^ 31 := by
  have h1 := BitVec.toInt_lt (x := b)
  have h2 := BitVec.le_toInt b
  exact ⟨h2, h1⟩

theorem safe_toInt (b : BitVec 32) : Safe b.toInt := by
  have := toInt_bounds b; constructor <;> omega

@[simp] theorem toInt32_ofInt32 (b : BitVec 32) : (ofInt32 b).toInt32 = b := by
  rw [ofInt32_eq, toInt32_ofInt (safe_toInt b), BitVec.ofInt_toInt]

@[simp] theorem toInt32_ofUint32 (b : BitVec 32) : (ofUint32 b).toInt32 = b := by
  have := b.isLt
  rw [ofUint32_eq, toInt32_ofInt (by constructor <;> omega), BitVec.ofInt_natCast,
    BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-! ## int32 arithmetic and bitwise operators as `BitVec 32` operations -/

@[simp] theorem toInt32_add_ofInt32 (x y : BitVec 32) :
    (ofInt32 x + ofInt32 y).toInt32 = x + y := by
  have := toInt_bounds x
  have := toInt_bounds y
  rw [ofInt32_eq, ofInt32_eq, add_ofInt (safe_toInt x) (safe_toInt y) (by constructor <;> omega),
    toInt32_ofInt (by constructor <;> omega), BitVec.ofInt_add, BitVec.ofInt_toInt,
    BitVec.ofInt_toInt]

@[simp] theorem toInt32_sub_ofInt32 (x y : BitVec 32) :
    (ofInt32 x - ofInt32 y).toInt32 = x - y := by
  have := toInt_bounds x
  have := toInt_bounds y
  rw [ofInt32_eq, ofInt32_eq, sub_ofInt (safe_toInt x) (safe_toInt y) (by constructor <;> omega),
    toInt32_ofInt (by constructor <;> omega), Int.sub_eq_add_neg, BitVec.ofInt_add,
    BitVec.ofInt_neg, BitVec.ofInt_toInt, BitVec.ofInt_toInt, BitVec.sub_eq_add_neg]

@[simp] theorem imul_ofInt32 (x y : BitVec 32) : imul (ofInt32 x) (ofInt32 y) = ofInt32 (x * y) := by
  simp [imul]

@[simp] theorem band_ofInt32 (x y : BitVec 32) : band (ofInt32 x) (ofInt32 y) = ofInt32 (x &&& y) := by
  simp [band]

@[simp] theorem bor_ofInt32 (x y : BitVec 32) : bor (ofInt32 x) (ofInt32 y) = ofInt32 (x ||| y) := by
  simp [bor]

@[simp] theorem bxor_ofInt32 (x y : BitVec 32) : bxor (ofInt32 x) (ofInt32 y) = ofInt32 (x ^^^ y) := by
  simp [bxor]

@[simp] theorem bnot_ofInt32 (x : BitVec 32) : bnot (ofInt32 x) = ofInt32 (~~~x) := by
  simp [bnot]

@[simp] theorem shl_ofInt32 (x s : BitVec 32) :
    shl (ofInt32 x) (ofInt32 s) = ofInt32 (x <<< (s.toNat % 32)) := by
  simp [shl]

@[simp] theorem sar_ofInt32 (x s : BitVec 32) :
    sar (ofInt32 x) (ofInt32 s) = ofInt32 (x.sshiftRight (s.toNat % 32)) := by
  simp [sar]

@[simp] theorem shr_ofInt32 (x s : BitVec 32) :
    shr (ofInt32 x) (ofInt32 s) = ofUint32 (x >>> (s.toNat % 32)) := by
  simp [shr]

/-! ## Bit patterns -/

@[simp] theorem ofBits_toBits (x : F64) : ofBits (toBits x) = x := by
  cases x with
  | nan => decide
  | inf b => cases b <;> decide
  | fin x =>
    rcases x with ⟨neg, man, exp, valid⟩
    by_cases hs : man < 2 ^ 52
    · have he : exp = -1074 := by rcases valid with h | h <;> omega
      subst he
      have hv : ((if neg then 2^63 else 0) + man) % 2^64 = (if neg then 2^63 else 0) + man := by
        apply Nat.mod_eq_of_lt; split <;> omega
      have h1 : decide (2^63 ≤ (if neg then 2^63 else 0) + man) = neg := by
        cases neg <;> simp <;> omega
      have h2 : ((if neg then 2^63 else 0) + man) >>> 52 % 2048 = 0 := by
        rw [Nat.shiftRight_eq_div_pow]; cases neg <;> simp <;> omega
      have h3 : ((if neg then 2^63 else 0) + man) % 2^52 = man := by
        cases neg <;> simp <;> omega
      simp only [toBits, hs, ite_true, ofBits, BitVec.toNat_ofNat, hv, h1, h2, h3]
      simp [mkFin_eq valid]
    · have hn : 2 ^ 52 ≤ man ∧ man < 2 ^ 53 ∧ -1074 ≤ exp ∧ exp ≤ 971 := by
        rcases valid with h | h
        · exact h
        · omega
      have hv : ((if neg then 2^63 else 0) + (exp + 1075).toNat * 2^52 + (man - 2^52)) % 2^64 =
          (if neg then 2^63 else 0) + (exp + 1075).toNat * 2^52 + (man - 2^52) := by
        apply Nat.mod_eq_of_lt; split <;> omega
      have h1 : decide (2^63 ≤ (if neg then 2^63 else 0) + (exp + 1075).toNat * 2^52 + (man - 2^52))
          = neg := by
        cases neg <;> simp <;> omega
      have h2 : ((if neg then 2^63 else 0) + (exp + 1075).toNat * 2^52 + (man - 2^52)) >>> 52 % 2048
          = (exp + 1075).toNat := by
        rw [Nat.shiftRight_eq_div_pow]; cases neg <;> simp <;> omega
      have h3 : ((if neg then 2^63 else 0) + (exp + 1075).toNat * 2^52 + (man - 2^52)) % 2^52
          = man - 2^52 := by
        cases neg <;> simp <;> omega
      simp only [toBits, hs, ite_false, ofBits, BitVec.toNat_ofNat, hv, h1, h2, h3]
      have h4 : ¬ (exp + 1075).toNat = 2047 := by omega
      have h5 : ¬ (exp + 1075).toNat = 0 := by omega
      have h6 : man - 2 ^ 52 + 2 ^ 52 = man := by omega
      have h7 : (((exp + 1075).toNat : Nat) : Int) - 1075 = exp := by omega
      simp only [h4, h5, ite_false, h6, h7]
      exact mkFin_eq valid


/-! ## Floor division -/

/-- Arithmetic heart of `floor_div_ofInt`: rounding the quotient `A / B` (with `A ≤ 2^53`) to a
53-bit significand never moves it across an integer. `A * 2^k = Q0 * B + ρ`, `Q0 = man0 * S + rem`
(`S = 2^s` dropped bits, `T = 2^(k-s)`), and `up` is the round-up decision. -/
theorem core_arith (A B S H T man0 rem ρ : Nat) (up : Bool)
    (hB : 0 < B) (hH : 0 < H) (hT : 0 < T) (hS : S = 2 * H)
    (h1 : A * (S * T) = (man0 * S + rem) * B + ρ) (hρ : ρ < B) (hrem : rem < S)
    (hman : 2 ^ 52 ≤ man0) (hA : A ≤ 2 ^ 53)
    (hdown : up = false → rem * B + ρ ≤ H * B)
    (hup : up = true → H * B ≤ rem * B + ρ ∧ 0 < rem) :
    (man0 + (if up then 1 else 0)) / T = A / B ∧
      ((man0 + (if up then 1 else 0)) % T = 0 ↔ A % B = 0) := by
  subst hS
  have hdm := Nat.div_add_mod man0 T
  generalize man0 / T = c at hdm
  generalize hd : man0 % T = d at hdm
  have hdT : d < T := hd ▸ Nat.mod_lt _ hT
  subst hdm
  have hP : 0 < 2 * H * T := Nat.mul_pos (Nat.mul_pos (by decide) hH) hT
  generalize hX : (d * (2 * H) + rem) * B + ρ = X
  have hAX : A * (2 * H * T) = c * B * (2 * H * T) + X := by rw [h1, ← hX]; grind
  -- `X < B * P`
  have hXlt : X < B * (2 * H * T) := by
    have e1 : (d + 1) * (2 * H) ≤ T * (2 * H) := Nat.mul_le_mul_right _ hdT
    have e2 : (d * (2 * H) + rem + 1) * B ≤ T * (2 * H) * B := by
      apply Nat.mul_le_mul_right
      have : (d + 1) * (2 * H) = d * (2 * H) + 2 * H := by grind
      omega
    have e3 : (d * (2 * H) + rem + 1) * B = (d * (2 * H) + rem) * B + B := by grind
    have e4 : T * (2 * H) * B = B * (2 * H * T) := by grind
    omega
  -- `A / B = c`
  have hcA : c * B ≤ A := by
    have : c * B * (2 * H * T) ≤ A * (2 * H * T) := by omega
    exact Nat.le_of_mul_le_mul_right this hP
  have hAc : A < (c + 1) * B := by
    have : A * (2 * H * T) < (c + 1) * B * (2 * H * T) := by
      have : (c + 1) * B * (2 * H * T) = c * B * (2 * H * T) + B * (2 * H * T) := by grind
      omega
    exact Nat.lt_of_mul_lt_mul_right this
  have hdiv : A / B = c := Nat.div_eq_of_lt_le hcA hAc
  -- `A % B = 0 ↔ X = 0`
  have hmodA : A % B = A - c * B := by
    have := Nat.div_add_mod A B
    rw [hdiv] at this
    have e : B * c = c * B := Nat.mul_comm B c
    omega
  have hmod : A % B = 0 ↔ X = 0 := by
    rw [hmodA]
    constructor
    · intro h
      have : A = c * B := by omega
      rw [this] at hAX; omega
    · intro h
      rw [h, Nat.add_zero] at hAX
      have := Nat.eq_of_mul_eq_mul_right hP hAX
      omega
  have hX0 : X = 0 → d = 0 ∧ rem = 0 := by
    intro h
    rw [← hX] at h
    have h2 : (d * (2 * H) + rem) * B = 0 := by omega
    rcases Nat.mul_eq_zero.1 h2 with h3 | h3
    · have h4 : d * (2 * H) = 0 := by omega
      rcases Nat.mul_eq_zero.1 h4 with h5 | h5
      · omega
      · omega
    · omega
  -- the identity `X = (A - c * B) * P`
  have hXP : X = (A - c * B) * (2 * H * T) := by
    rw [Nat.sub_mul]; omega
  cases up with
  | false =>
    simp only [Bool.false_eq_true, ite_false, Nat.add_zero]
    have e1 : (T * c + d) / T = c := by
      rw [Nat.add_comm, Nat.add_mul_div_left _ _ hT, Nat.div_eq_of_lt hdT, Nat.zero_add]
    have e2 : (T * c + d) % T = d := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hdT]
    rw [e1, e2, hdiv]
    refine ⟨rfl, ?_⟩
    constructor
    · intro hd0
      apply hmod.2
      apply Classical.byContradiction
      intro hXne
      have hdn := hdown rfl
      have hXe : X = rem * B + ρ := by rw [← hX, hd0]; simp
      -- `X ≥ P` because `X` is a positive multiple of `P`
      have hAc1 : 1 ≤ A - c * B := by
        apply Classical.byContradiction; intro h0
        have : A - c * B = 0 := by omega
        rw [this, Nat.zero_mul] at hXP; exact hXne hXP
      have hPX : 2 * H * T ≤ X := by
        rw [hXP]; exact Nat.le_mul_of_pos_left _ hAc1
      have h2T : 2 * T ≤ B := by
        have : H * (2 * T) ≤ H * B := by
          have e : H * (2 * T) = 2 * H * T := by grind
          omega
        exact Nat.le_of_mul_le_mul_left this hH
      have hcb : c * (2 * T) ≤ c * B := Nat.mul_le_mul_left _ h2T
      have e : c * (2 * T) = 2 * (T * c) := by grind
      omega
    · intro hm
      exact (hX0 (hmod.1 hm)).1
  | true =>
    simp only [ite_true]
    obtain ⟨hHB, hrem0⟩ := hup rfl
    have hXne : X ≠ 0 := by intro h; have := (hX0 h).2; omega
    have hAB : A % B ≠ 0 := fun h => hXne (hmod.1 h)
    have hd1 : d + 1 < T := by
      apply Classical.byContradiction
      intro hdT1
      have hdT' : d + 1 = T := by omega
      -- `X + H * B ≥ T * (2H) * B`
      have hXge : T * (2 * H) * B ≤ X + H * B := by
        have e1 : T * (2 * H) * B = d * (2 * H) * B + 2 * H * B := by rw [← hdT']; grind
        have e2 : X = d * (2 * H) * B + rem * B + ρ := by rw [← hX]; grind
        have e3 : 2 * H * B = H * B + H * B := by grind
        omega
      -- `X + P ≤ B * P` because `A < (c + 1) * B`
      have hXle : X + 2 * H * T ≤ B * (2 * H * T) := by
        have h3 : A - c * B + 1 ≤ B := by
          have : (c + 1) * B = c * B + B := by grind
          omega
        have h4 : (A - c * B + 1) * (2 * H * T) ≤ B * (2 * H * T) := Nat.mul_le_mul_right _ h3
        have h5 : (A - c * B + 1) * (2 * H * T) = (A - c * B) * (2 * H * T) + 2 * H * T := by
          grind
        omega
      have h2T : 2 * T ≤ B := by
        have : H * (2 * T) ≤ H * B := by
          have e1 : B * (2 * H * T) = T * (2 * H) * B := by grind
          have e2 : H * (2 * T) = 2 * H * T := by grind
          omega
        exact Nat.le_of_mul_le_mul_left this hH
      -- `A * P + H * B ≥ 2 * H * B * (man0 + 1)` and then `A ≥ 2 * man0 + 1`
      have k1 : B * H * (2 * (T * c + d) + 1) ≤ A * (2 * H * T) := by
        have e1 : B * H * (2 * (T * c + d) + 1) + H * B = c * B * (2 * H * T) + T * (2 * H) * B := by
          rw [← hdT']; grind
        omega
      have k2 : 2 * T * H * (2 * (T * c + d) + 1) ≤ B * H * (2 * (T * c + d) + 1) := by
        apply Nat.mul_le_mul_right; exact Nat.mul_le_mul_right _ h2T
      have k3 : (2 * (T * c + d) + 1) * (2 * H * T) ≤ A * (2 * H * T) := by
        have e : 2 * T * H * (2 * (T * c + d) + 1) = (2 * (T * c + d) + 1) * (2 * H * T) := by grind
        omega
      have k4 := Nat.le_of_mul_le_mul_right k3 hP
      omega
    have e1 : (T * c + d + 1) / T = c := by
      rw [Nat.add_assoc, Nat.add_comm, Nat.add_mul_div_left _ _ hT, Nat.div_eq_of_lt hd1,
        Nat.zero_add]
    have e2 : (T * c + d + 1) % T = d + 1 := by
      rw [Nat.add_assoc, Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hd1]
    rw [e1, e2, hdiv]
    exact ⟨rfl, by constructor <;> intro h <;> omega⟩


/-! ## `ofFrac`: the quotient form and power-of-two scaling -/

/-- Shift applied by `ofFrac` (the quotient gets 55 or 56 bits). -/
def kf (num den : Nat) : Int := 55 + (bitLen den : Int) - (bitLen num : Int)

/-- `⌊num * 2^k / den⌋` and the remainder, for any integer `k`. -/
def fq (num den : Nat) (k : Int) : Nat := (num * 2 ^ k.toNat) / (den * 2 ^ (-k).toNat)
def fr (num den : Nat) (k : Int) : Nat := (num * 2 ^ k.toNat) % (den * 2 ^ (-k).toNat)

theorem ofFrac_eq (neg : Bool) (num den : Nat) (e : Int) (hd : den ≠ 0) (hn : num ≠ 0) :
    ofFrac neg num den e =
      round neg (fq num den (kf num den)) (e - kf num den) (fr num den (kf num den) != 0) := by
  unfold ofFrac
  simp only [hd, hn, ite_false]
  split
  · rename_i hk
    simp only [fq, fr, kf, Nat.shiftLeft_eq,
      show (-(55 + (bitLen den : Int) - (bitLen num : Int))).toNat = 0 by omega, Nat.pow_zero,
      Nat.mul_one]
  · rename_i hk
    simp only [fq, fr, kf, Nat.shiftLeft_eq,
      show (55 + (bitLen den : Int) - (bitLen num : Int)).toNat = 0 by omega, Nat.pow_zero,
      Nat.mul_one]

theorem fq_norm (num den : Nat) (k : Int) (M : Nat) (hM : 0 ≤ k + M) :
    fq num den k = (num * 2 ^ (k + M).toNat) / (den * 2 ^ M) ∧
      (fr num den k = 0 ↔ (num * 2 ^ (k + M).toNat) % (den * 2 ^ M) = 0) := by
  have e1 : num * 2 ^ (k + M).toNat = num * 2 ^ k.toNat * 2 ^ (M - (-k).toNat) := by
    rw [Nat.mul_assoc, ← Nat.pow_add]; congr 2; omega
  have e2 : den * 2 ^ M = den * 2 ^ (-k).toNat * 2 ^ (M - (-k).toNat) := by
    rw [Nat.mul_assoc, ← Nat.pow_add]; congr 2; omega
  rw [e1, e2, Nat.mul_div_mul_right _ _ (Nat.two_pow_pos _), Nat.mul_mod_mul_right]
  refine ⟨rfl, ?_⟩
  have := Nat.two_pow_pos (M - (-k).toNat)
  constructor
  · intro h; rw [fr] at h; rw [h, Nat.zero_mul]
  · intro h
    rcases Nat.mul_eq_zero.1 h with h | h
    · exact h
    · omega

theorem fq_mul_num (num den i : Nat) (K : Int) :
    fq (num * 2 ^ i) den (K - i) = fq num den K ∧
      (fr (num * 2 ^ i) den (K - i) = 0 ↔ fr num den K = 0) := by
  obtain ⟨a1, a2⟩ := fq_norm (num * 2 ^ i) den (K - i) (i - K).toNat (by omega)
  obtain ⟨b1, b2⟩ := fq_norm num den K (i - K).toNat (by omega)
  have e : num * 2 ^ i * 2 ^ (K - i + ((i - K).toNat : Int)).toNat =
      num * 2 ^ (K + ((i - K).toNat : Int)).toNat := by
    rw [Nat.mul_assoc, ← Nat.pow_add]; congr 2; omega
  rw [e] at a1 a2
  exact ⟨a1.trans b1.symm, a2.trans b2.symm⟩

theorem fq_mul_den (num den j : Nat) (K : Int) :
    fq num (den * 2 ^ j) (K + j) = fq num den K ∧
      (fr num (den * 2 ^ j) (K + j) = 0 ↔ fr num den K = 0) := by
  obtain ⟨a1, a2⟩ := fq_norm num (den * 2 ^ j) (K + j) (-(K + j)).toNat (by omega)
  obtain ⟨b1, b2⟩ := fq_norm num den K ((-(K + j)).toNat + j) (by omega)
  have e1 : (K + j + ((-(K + j)).toNat : Int)).toNat = (K + (((-(K + j)).toNat + j : Nat) : Int)).toNat := by
    omega
  have e2 : den * 2 ^ j * 2 ^ (-(K + j)).toNat = den * 2 ^ ((-(K + j)).toNat + j) := by
    rw [Nat.mul_assoc, ← Nat.pow_add, Nat.add_comm j]
  rw [e1, e2] at a1 a2
  exact ⟨a1.trans b1.symm, a2.trans b2.symm⟩

theorem bne_congr {a b : Nat} (h : a = 0 ↔ b = 0) : (a != 0) = (b != 0) := by
  by_cases hb : b = 0
  · rw [hb, h.2 hb]
  · have ha : a ≠ 0 := fun h' => hb (h.1 h')
    rw [bne_iff_ne.2 ha, bne_iff_ne.2 hb]

theorem ofFrac_mul_num (neg : Bool) (num den i : Nat) (e : Int) (hd : den ≠ 0) (hn : num ≠ 0) :
    ofFrac neg (num * 2 ^ i) den e = ofFrac neg num den (e + i) := by
  have hn' : num * 2 ^ i ≠ 0 := Nat.mul_ne_zero hn (Nat.pos_iff_ne_zero.1 (Nat.two_pow_pos i))
  rw [ofFrac_eq _ _ _ _ hd hn', ofFrac_eq _ _ _ _ hd hn]
  have hk : kf (num * 2 ^ i) den = kf num den - i := by
    unfold kf; rw [bitLen_mul_pow _ _ hn]; push_cast; omega
  rw [hk]
  obtain ⟨h1, h2⟩ := fq_mul_num num den i (kf num den)
  rw [h1, bne_congr h2]
  congr 1; omega

theorem ofFrac_mul_den (neg : Bool) (num den j : Nat) (e : Int) (hd : den ≠ 0) (hn : num ≠ 0) :
    ofFrac neg num (den * 2 ^ j) e = ofFrac neg num den (e - j) := by
  have hd' : den * 2 ^ j ≠ 0 := Nat.mul_ne_zero hd (Nat.pos_iff_ne_zero.1 (Nat.two_pow_pos j))
  rw [ofFrac_eq _ _ _ _ hd' hn, ofFrac_eq _ _ _ _ hd hn]
  have hk : kf num (den * 2 ^ j) = kf num den + j := by
    unfold kf; rw [bitLen_mul_pow _ _ hd]; push_cast; omega
  rw [hk]
  obtain ⟨h1, h2⟩ := fq_mul_den num den j (kf num den)
  rw [h1, bne_congr h2]
  congr 1; omega

theorem neg_ofFrac (s : Bool) (num den : Nat) (e : Int) :
    neg (ofFrac s num den e) = ofFrac (!s) num den e := by
  unfold ofFrac
  by_cases hd : den = 0
  · simp [hd, neg]
  · by_cases hn : num = 0
    · simp only [hd, hn, ite_true, ite_false, zero]; exact neg_mkFin _ _ _
    · simp only [hd, hn, ite_false]
      split <;> exact neg_round _ _ _ _


theorem div_ofInt (a b : Int) (ha : Safe a) (hb : Safe b) (a0 : a ≠ 0) (b0 : b ≠ 0) :
    ofInt a / ofInt b = ofFrac (decide (a < 0) ^^ decide (b < 0)) a.natAbs b.natAbs 0 := by
  obtain ⟨x, hx1, hx2, hx3⟩ := ofInt_spec a ha
  obtain ⟨y, hy1, hy2, hy3⟩ := ofInt_spec b hb
  have hxm : x.man ≠ 0 := (not_congr (ofInt_man_eq_zero hx3)).2 a0
  have hym : y.man ≠ 0 := (not_congr (ofInt_man_eq_zero hy3)).2 b0
  rw [hx1, hy1]
  show div (.fin x) (.fin y) = _
  simp only [div, hym, ite_false]
  rw [hx2, hy2]
  generalize (decide (a < 0) ^^ decide (b < 0)) = s
  have hA0 : a.natAbs ≠ 0 := by omega
  have hB0 : b.natAbs ≠ 0 := by omega
  have ex := x.exp_ge
  have ey := y.exp_ge
  have hx : x.man * 2 ^ (x.exp + 1074).toNat = a.natAbs * 2 ^ 1074 := hx3
  have hy : y.man * 2 ^ (y.exp + 1074).toNat = b.natAbs * 2 ^ 1074 := hy3
  calc ofFrac s x.man y.man (x.exp - y.exp)
      = ofFrac s (x.man * 2 ^ (x.exp + 1074).toNat) y.man
          (x.exp - y.exp - ((x.exp + 1074).toNat : Nat)) := by
        rw [ofFrac_mul_num _ _ _ _ _ hym hxm] <;> first | rfl | (congr 1; omega)
    _ = ofFrac s a.natAbs y.man (x.exp - y.exp - ((x.exp + 1074).toNat : Nat) + 1074) := by
        rw [hx, ofFrac_mul_num _ _ _ _ _ hym hA0] <;> first | rfl | (congr 1; omega)
    _ = ofFrac s a.natAbs (y.man * 2 ^ (y.exp + 1074).toNat) 1074 := by
        rw [ofFrac_mul_den _ _ _ _ _ hym hA0] <;> first | rfl | (congr 1; omega)
    _ = ofFrac s a.natAbs b.natAbs 0 := by
        rw [hy, ofFrac_mul_den _ _ _ _ _ hB0 hA0] <;> first | rfl | (congr 1; omega)

theorem mag_div_mod (man1 t : Nat) (ht : t ≤ 1074) :
    (man1 * 2 ^ (1074 - t)) / 2 ^ 1074 = man1 / 2 ^ t ∧
      ((man1 * 2 ^ (1074 - t)) % 2 ^ 1074 = 0 ↔ man1 % 2 ^ t = 0) := by
  have e : (2 : Nat) ^ 1074 = 2 ^ t * 2 ^ (1074 - t) := by rw [← Nat.pow_add]; congr 1; omega
  rw [e, Nat.mul_div_mul_right _ _ (Nat.two_pow_pos _), Nat.mul_mod_mul_right]
  refine ⟨rfl, ?_⟩
  have := Nat.two_pow_pos (1074 - t)
  constructor
  · intro h
    rcases Nat.mul_eq_zero.1 h with h | h
    · exact h
    · omega
  · intro h; rw [h, Nat.zero_mul]

/-- Rounding `A / B` (`1 ≤ A, B ≤ 2^53`) keeps its integer part and its integrality. -/
theorem ofFrac_intMag (A B : Nat) (hA1 : 1 ≤ A) (hA : A ≤ 2 ^ 53) (hB1 : 1 ≤ B) (hB : B ≤ 2 ^ 53) :
    ∃ r : Fin64, ofFrac false A B 0 = .fin r ∧ r.neg = false ∧ r.intMag = A / B ∧
      (r.fracMag = 0 ↔ A % B = 0) := by
  by_cases hspec : A = 2 ^ 53 ∧ B = 1
  · obtain ⟨rfl, rfl⟩ := hspec
    exact ⟨⟨false, 2 ^ 52, 1, Or.inl ⟨by decide, by decide, by decide, by decide⟩⟩,
      by decide +kernel, rfl, by decide +kernel, by decide +kernel⟩
  have hA0 : A ≠ 0 := by omega
  have hB0 : B ≠ 0 := by omega
  rw [ofFrac_eq _ _ _ _ hB0 hA0]
  have hLA1 := two_pow_bitLen_sub_one_le hA0
  have hLA2 := lt_two_pow_bitLen A
  have hLB1 := two_pow_bitLen_sub_one_le hB0
  have hLB2 := lt_two_pow_bitLen B
  have hLApos := bitLen_pos hA0
  have hLBpos := bitLen_pos hB0
  have hLA : bitLen A ≤ 54 := (bitLen_le_iff _ _).2 (by omega)
  have hLB : bitLen B ≤ 54 := (bitLen_le_iff _ _).2 (by omega)
  have hK3 : 3 ≤ kf A B := by
    unfold kf
    apply Classical.byContradiction
    intro h
    have h1 : bitLen A = 54 := by omega
    have h2 : bitLen B = 1 := by omega
    apply hspec
    rw [h1] at hLA1; rw [h2] at hLB2
    simp only [Nat.reduceSub, Nat.reducePow] at hLA1 hLB2
    constructor <;> omega
  have hKle : kf A B ≤ 108 := by unfold kf; omega
  have hKdef : kf A B + bitLen A = 55 + bitLen B := by unfold kf; omega
  generalize kf A B = K at hK3 hKle hKdef ⊢
  obtain ⟨k, rfl⟩ : ∃ k : Nat, K = (k : Int) := ⟨K.toNat, by omega⟩
  have hkdef : k + bitLen A = 55 + bitLen B := by omega
  simp only [fq, fr, Int.toNat_natCast, show (-(k : Int)).toNat = 0 by omega, Nat.pow_zero,
    Nat.mul_one]
  -- the quotient has 55 or 56 bits
  have hlo : 2 ^ 54 * B < A * 2 ^ k := by
    calc 2 ^ 54 * B < 2 ^ 54 * 2 ^ bitLen B := Nat.mul_lt_mul_of_pos_left hLB2 (Nat.two_pow_pos _)
      _ = 2 ^ (bitLen A - 1) * 2 ^ k := by rw [← Nat.pow_add, ← Nat.pow_add]; congr 1; omega
      _ ≤ A * 2 ^ k := Nat.mul_le_mul_right _ hLA1
  have hhi : A * 2 ^ k < 2 ^ 56 * B := by
    calc A * 2 ^ k < 2 ^ bitLen A * 2 ^ k := Nat.mul_lt_mul_of_pos_right hLA2 (Nat.two_pow_pos _)
      _ = 2 ^ 56 * 2 ^ (bitLen B - 1) := by rw [← Nat.pow_add, ← Nat.pow_add]; congr 1; omega
      _ ≤ 2 ^ 56 * B := Nat.mul_le_mul_left _ hLB1
  have hQlo : 2 ^ 54 ≤ A * 2 ^ k / B := (Nat.le_div_iff_mul_le (by omega)).2 (by omega)
  have hQhi : A * 2 ^ k / B < 2 ^ 56 := (Nat.div_lt_iff_lt_mul (by omega)).2 hhi
  have hdecomp := Nat.div_add_mod (A * 2 ^ k) B
  have hρB : A * 2 ^ k % B < B := Nat.mod_lt _ (by omega)
  generalize A * 2 ^ k / B = Q0 at hQlo hQhi hdecomp ⊢
  generalize A * 2 ^ k % B = ρ at hρB hdecomp ⊢
  have hQ0 : Q0 ≠ 0 := by omega
  have hLQ1 := two_pow_bitLen_sub_one_le hQ0
  have hLQ2 := lt_two_pow_bitLen Q0
  have hLQlo : 55 ≤ bitLen Q0 := by
    apply Classical.byContradiction; intro h
    have : Q0 < 2 ^ 54 := (bitLen_le_iff _ _).1 (by omega)
    omega
  have hLQhi : bitLen Q0 ≤ 56 := (bitLen_le_iff _ _).2 hQhi
  rw [round_eq _ _ _ _ (by simp [hQ0])]
  obtain ⟨s, hs⟩ : ∃ s, bitLen Q0 = s + 53 := ⟨bitLen Q0 - 53, by omega⟩
  have hq : qexp Q0 (0 - (k : Int)) = (s : Int) - k := by unfold qexp; omega
  rw [hq]
  simp only [show ¬ ((s : Int) - k ≤ 0 - k) by omega, ite_false]
  have hst : ((s : Int) - k - (0 - k)).toNat = s := by omega
  rw [hst]
  rw [hs] at hLQ1 hLQ2
  have hs23 : 2 ≤ s ∧ s ≤ 3 := by omega
  -- significand bounds
  have hman_lo : 2 ^ 52 ≤ Q0 / 2 ^ s := by
    apply (Nat.le_div_iff_mul_le (Nat.two_pow_pos s)).2
    rw [← Nat.pow_add]
    have : 52 + s = s + 53 - 1 := by omega
    rw [this]; exact hLQ1
  have hman_hi : Q0 / 2 ^ s < 2 ^ 53 := by
    apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos s)).2
    rw [← Nat.pow_add, Nat.add_comm]; exact hLQ2
  have hqd := Nat.div_add_mod Q0 (2 ^ s)
  have hremlt : Q0 % 2 ^ s < 2 ^ s := Nat.mod_lt _ (Nat.two_pow_pos s)
  have hH : 0 < 2 ^ (s - 1) := Nat.two_pow_pos _
  have hSH : 2 ^ s = 2 * 2 ^ (s - 1) := by
    rw [← Nat.pow_succ']; congr 1; omega
  -- round-up decision
  have hupdown : (rUp Q0 s (ρ != 0) = false → Q0 % 2 ^ s * B + ρ ≤ 2 ^ (s - 1) * B) ∧
      (rUp Q0 s (ρ != 0) = true → 2 ^ (s - 1) * B ≤ Q0 % 2 ^ s * B + ρ ∧ 0 < Q0 % 2 ^ s) := by
    unfold rUp
    by_cases hρ0 : ρ = 0
    · subst hρ0
      simp only [bne_self_eq_false, Bool.false_eq_true, ite_false, Nat.add_zero]
      constructor
      · intro h
        have h1 : ¬ (2 ^ (s - 1) < Q0 % 2 ^ s) := by
          intro h'; simp [h'] at h
        exact Nat.mul_le_mul_right _ (by omega)
      · intro h
        have h1 : 2 ^ (s - 1) ≤ Q0 % 2 ^ s := by
          rcases Bool.or_eq_true_iff.1 h with h' | h'
          · have := of_decide_eq_true h'; omega
          · have := of_decide_eq_true (Bool.and_eq_true_iff.1 h').1; omega
        exact ⟨Nat.mul_le_mul_right _ h1, by omega⟩
    · have hρ' : (ρ != 0) = true := bne_iff_ne.2 hρ0
      simp only [hρ', ite_true]
      constructor
      · intro h
        have h1 : Q0 % 2 ^ s < 2 ^ (s - 1) := by
          have := of_decide_eq_false h; omega
        have h2 : (Q0 % 2 ^ s + 1) * B ≤ 2 ^ (s - 1) * B := Nat.mul_le_mul_right _ h1
        have e : (Q0 % 2 ^ s + 1) * B = Q0 % 2 ^ s * B + B := by grind
        omega
      · intro h
        have h1 : 2 ^ (s - 1) ≤ Q0 % 2 ^ s := of_decide_eq_true h
        have h2 := Nat.mul_le_mul_right B h1
        exact ⟨by omega, by omega⟩
  -- the arithmetic core
  have hcore := core_arith A B (2 ^ s) (2 ^ (s - 1)) (2 ^ (k - s)) (Q0 / 2 ^ s) (Q0 % 2 ^ s) ρ
    (rUp Q0 s (ρ != 0)) (by omega) hH (Nat.two_pow_pos _) hSH
    (by
      have e1 : 2 ^ s * 2 ^ (k - s) = 2 ^ k := by rw [← Nat.pow_add]; congr 1; omega
      have e2 : Q0 / 2 ^ s * 2 ^ s + Q0 % 2 ^ s = Q0 := by
        rw [Nat.mul_comm]; exact hqd
      rw [e1, e2]; rw [Nat.mul_comm Q0 B]; omega)
    hρB hremlt hman_lo hA hupdown.1 hupdown.2
  have hrm : rMant Q0 s (ρ != 0) = Q0 / 2 ^ s + (if rUp Q0 s (ρ != 0) then 1 else 0) := by
    unfold rMant; rw [Nat.shiftRight_eq_div_pow]; split <;> rfl
  rw [hrm]
  have hm1 : 2 ^ 52 ≤ Q0 / 2 ^ s + (if rUp Q0 s (ρ != 0) then 1 else 0) ∧
      Q0 / 2 ^ s + (if rUp Q0 s (ρ != 0) then 1 else 0) ≤ 2 ^ 53 := by
    split <;> omega
  generalize Q0 / 2 ^ s + (if rUp Q0 s (ρ != 0) then 1 else 0) = man1 at hcore hm1 ⊢
  have hks : s ≤ k := by omega
  have ht : k - s ≤ 1074 := by omega
  obtain ⟨c1, c2⟩ := mag_div_mod man1 (k - s) ht
  rw [hcore.1] at c1
  rw [hcore.2] at c2
  unfold pack
  by_cases hcarry : man1 = 2 ^ 53
  · simp only [hcarry, ite_true]
    rw [ite_eq_right (by omega)]
    refine ⟨⟨false, 2 ^ 52, (s : Int) - k + 1, Or.inl ⟨by decide, by decide, by omega, by omega⟩⟩,
      mkFin_eq _, rfl, ?_, ?_⟩
    · rw [Fin64.intMag_eq, Fin64.mag, ← c1, hcarry]
      congr 1
      have e : ((s : Int) - k + 1 + 1074).toNat = 1 + (1074 - (k - s)) := by omega
      rw [e, Nat.pow_add, ← Nat.mul_assoc]
      rfl
    · rw [Fin64.fracMag_eq_zero_iff, Fin64.mag, ← c2, hcarry]
      have e : ((s : Int) - k + 1 + 1074).toNat = 1 + (1074 - (k - s)) := by omega
      rw [e, Nat.pow_add, ← Nat.mul_assoc]
      rfl
  · simp only [hcarry, ite_false]
    rw [ite_eq_right (by omega)]
    refine ⟨⟨false, man1, (s : Int) - k, Or.inl ⟨hm1.1, by omega, by omega, by omega⟩⟩,
      mkFin_eq _, rfl, ?_, ?_⟩
    · rw [Fin64.intMag_eq, Fin64.mag, ← c1]
      have e : ((s : Int) - k + 1074).toNat = 1074 - (k - s) := by omega
      rw [e]
    · rw [Fin64.fracMag_eq_zero_iff, Fin64.mag, ← c2]
      have e : ((s : Int) - k + 1074).toNat = 1074 - (k - s) := by omega
      rw [e]

theorem ofInt_natCast (n : Nat) : ofInt (n : Int) = round false n 0 := by
  unfold ofInt
  rw [decide_eq_false (by omega), Int.natAbs_natCast]

theorem ofInt_neg_natCast (n : Nat) (h : n ≠ 0) : ofInt (-(n : Int)) = round true n 0 := by
  unfold ofInt
  rw [decide_eq_true (by omega)]
  congr 1
  omega

theorem ceil_div_aux (A B : Nat) (hA : 1 ≤ A) (hB : 1 ≤ B) :
    (A - 1) / B + 1 = if A % B = 0 then A / B else A / B + 1 := by
  have h1 := Nat.div_add_mod (A - 1) B
  have h2 := Nat.mod_lt (A - 1) (show 0 < B by omega)
  generalize (A - 1) / B = q at h1
  generalize (A - 1) % B = r at h1 h2
  by_cases hr : r + 1 = B
  · have hA' : A = B * (q + 1) := by
      have : B * (q + 1) = B * q + B := by grind
      omega
    have e1 : A % B = 0 := by rw [hA']; exact Nat.mul_mod_right _ _
    have e2 : A / B = q + 1 := by rw [hA', Nat.mul_div_cancel_left _ (by omega)]
    simp [e1, e2]
  · have hA' : A = (r + 1) + B * q := by omega
    have e1 : A % B = r + 1 := by
      rw [hA', Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
    have e2 : A / B = q := by
      rw [hA', Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt (by omega), Nat.zero_add]
    simp [e1, e2]

theorem fdiv_same_sign (a b : Int) (a0 : a ≠ 0) (b0 : b ≠ 0) (h : (a < 0) = (b < 0)) :
    Int.fdiv a b = ((a.natAbs / b.natAbs : Nat) : Int) := by
  rcases a with m | m <;> rcases b with n | n
  · cases m with
    | zero => exact absurd rfl a0
    | succ m =>
      cases n with
      | zero => exact absurd rfl b0
      | succ n => rfl
  · exfalso; simp at h; omega
  · exfalso; simp at h; omega
  · rfl

theorem fdiv_opp_sign (a b : Int) (a0 : a ≠ 0) (b0 : b ≠ 0) (h : (a < 0) ≠ (b < 0)) :
    Int.fdiv a b = -(((a.natAbs - 1) / b.natAbs + 1 : Nat) : Int) := by
  rcases a with m | m <;> rcases b with n | n
  · exfalso; simp at h; omega
  · cases m with
    | zero => exact absurd rfl a0
    | succ m =>
      show Int.negSucc (m / (n + 1)) = -(((m + 1 - 1) / (n + 1) + 1 : Nat) : Int)
      rw [Nat.add_sub_cancel, Int.negSucc_eq, Int.natCast_add, Int.natCast_one]
  · cases n with
    | zero => exact absurd rfl b0
    | succ n =>
      show Int.negSucc (m / (n + 1)) = -(((m + 1 - 1) / (n + 1) + 1 : Nat) : Int)
      rw [Nat.add_sub_cancel, Int.negSucc_eq, Int.natCast_add, Int.natCast_one]
  · exfalso; simp at h

/-- **`Math.floor(a / b)` on safe integers is floor division.** The rounded quotient never
crosses an integer because `|a| ≤ 2^53`. (`0 / negative` is `-0`, hence the side condition.) -/
@[simp] theorem floor_div_ofInt {a b : Int} (ha : Safe a) (hb : Safe b) (hb0 : b ≠ 0)
    (h : a ≠ 0 ∨ 0 < b) : (ofInt a / ofInt b).floor = ofInt (Int.fdiv a b) := by
  by_cases a0 : a = 0
  · subst a0
    have hbpos : 0 < b := by omega
    obtain ⟨y, hy1, hy2, hy3⟩ := ofInt_spec b hb
    have hym : y.man ≠ 0 := (not_congr (ofInt_man_eq_zero hy3)).2 hb0
    have hfd : Int.fdiv 0 b = 0 := by
      rcases b with n | n
      · rfl
      · rfl
    rw [hfd, ofInt_zero, hy1]
    show (div _ _).floor = _
    simp only [div, hym, ite_false, hy2, decide_eq_false (show ¬ b < 0 by omega)]
    simp only [ofFrac, hym, ite_true, ite_false]
    decide
  · rw [div_ofInt a b ha hb a0 hb0]
    have hA1 : 1 ≤ a.natAbs := by omega
    have hA : a.natAbs ≤ 2 ^ 53 := by omega
    have hB1 : 1 ≤ b.natAbs := by omega
    have hB : b.natAbs ≤ 2 ^ 53 := by omega
    obtain ⟨r, hr1, hr2, hr3, hr4⟩ := ofFrac_intMag _ _ hA1 hA hB1 hB
    by_cases hs : (a < 0) = (b < 0)
    · have hx : (decide (a < 0) ^^ decide (b < 0)) = false := by
        by_cases ha' : a < 0
        · have hb' : b < 0 := hs ▸ ha'
          simp [ha', hb']
        · have hb' : ¬ b < 0 := hs ▸ ha'
          simp [ha', hb']
      rw [hx, hr1, fdiv_same_sign a b a0 hb0 hs]
      simp only [floor]
      rw [ofInt_natCast]
      split
      · rename_i hf
        rw [fin_eq_round_intMag r hf, hr2, hr3]
      · rw [hr2, hr3]
        rfl
    · have hx : (decide (a < 0) ^^ decide (b < 0)) = true := by
        by_cases ha' : a < 0
        · have hb' : ¬ b < 0 := fun hb' => hs (by simp [ha', hb'])
          simp [ha', hb']
        · have hb' : b < 0 := by
            apply Classical.byContradiction; intro hb'; exact hs (by simp [ha', hb'])
          simp [ha', hb']
      have hn := neg_ofFrac false a.natAbs b.natAbs 0
      simp only [Bool.not_false] at hn
      rw [hx, fdiv_opp_sign a b a0 hb0 hs, ceil_div_aux _ _ hA1 hB1, ← hn, hr1]
      have hnr : neg (.fin r) = .fin ⟨true, r.man, r.exp, r.valid⟩ := by simp [neg, hr2]
      rw [hnr]
      generalize hr' : (⟨true, r.man, r.exp, r.valid⟩ : Fin64) = r'
      have hf' : r'.fracMag = r.fracMag := by rw [← hr']; rfl
      have hi' : r'.intMag = r.intMag := by rw [← hr']; rfl
      have hn' : r'.neg = true := by rw [← hr']
      simp only [floor]
      by_cases hm : a.natAbs % b.natAbs = 0
      · have hf : r'.fracMag = 0 := by rw [hf']; exact hr4.2 hm
        have hpos : 0 < a.natAbs / b.natAbs :=
          Nat.div_pos (Nat.le_of_dvd (by omega) (Nat.dvd_of_mod_eq_zero hm)) (by omega)
        rw [ite_eq_left hf, fin_eq_round_intMag r' hf, hn', hi', hr3, ite_eq_left hm,
          ofInt_neg_natCast _ (by omega)]
      · have hf : r'.fracMag ≠ 0 := fun h => hm (hr4.1 (hf' ▸ h))
        rw [ite_eq_right hf, hn', ite_eq_left rfl, hi', hr3, ite_eq_right hm,
          ofInt_neg_natCast _ (by omega)]

/-! ### Number::exponentiate: the cases ECMA-262 fixes

`F64.pow approx x y` (the semantics of `**` and `Math.pow`, with `approx = I.pow`) consults the
implementation only where `powSpec? x y = none`. -/

theorem pow_of_powSpec {f : F64 → F64 → F64} {x y v : F64} (h : powSpec? x y = some v) : pow f x y = v := by
  simp [pow, h]

theorem pow_of_powSpec_none {f : F64 → F64 → F64} {x y : F64} (h : powSpec? x y = none) :
    pow f x y = f x y := by
  simp [pow, h]

/-- `x ** NaN = NaN`. -/
@[simp] theorem pow_nan_right (f : F64 → F64 → F64) (x : F64) : pow f x .nan = .nan := by
  simp [pow, powSpec?, isNaN]

/-- `x ** ±0 = 1` for every `x`, NaN included. -/
theorem pow_zero_right (f : F64 → F64 → F64) (x y : F64) (hy : y.isZero = true) : pow f x y = one := by
  cases y with
  | nan => simp [isZero] at hy
  | inf b => simp [isZero] at hy
  | fin a => simp [pow, powSpec?, isNaN, hy]

@[simp] theorem pow_ofNat_zero (f : F64 → F64 → F64) (x : F64) : pow f x (ofNat 0) = one :=
  pow_zero_right f x _ (by decide)

/-- `NaN ** y = NaN` unless `y` is NaN or a zero. -/
theorem pow_nan_left (f : F64 → F64 → F64) (y : F64) (h1 : y.isNaN = false) (h2 : y.isZero = false) :
    pow f .nan y = .nan := by
  simp [pow, powSpec?, h1, h2]

end F64
end StrictTS
