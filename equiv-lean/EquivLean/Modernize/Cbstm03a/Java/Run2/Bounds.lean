import EquivLean.Modernize.Cbstm03a.Java.Run2.Defs

/-!
# CBSTM03A → Java `run`, the load loop: the table offsets stay above `-2^31`

`memWrite`'s precondition (interfaces v3) needs `-2^31 < off`; with counters in `0 … 9999` the card offset
`(cr - 1) × 3356` and the entry offsets `(cr - 1) × 3356 + 16 + (tr - 1) × 334` (and `+ 16`) are at least `-3674`.
-/

open Jimple

namespace EquivLean.Modernize.Cbstm03a.Java.Seg2

theorem bmod64_eq {v : Int} (h0 : -9223372036854775808 ≤ v) (h1 : v < 9223372036854775808) :
    v.bmod (2 ^ 64) = v := Int.bmod_eq_of_le (by norm_num; omega) (by norm_num; omega)

theorem sub1_toInt {c : I64} (h0 : 0 ≤ c.toInt) (h1 : c.toInt < 10000) : (c - 1).toInt = c.toInt - 1 := by
  rw [BitVec.toInt_sub, show (1 : I64).toInt = 1 by decide]
  exact bmod64_eq (by omega) (by omega)

theorem cardOff_toInt {c : I64} (h0 : 0 ≤ c.toInt) (h1 : c.toInt < 10000) :
    (cardOffJ c).toInt = (c.toInt - 1) * 3356 := by
  unfold cardOffJ
  rw [BitVec.toInt_mul, sub1_toInt h0 h1, show (3356 : I64).toInt = 3356 by decide]
  exact bmod64_eq (by omega) (by omega)

theorem tranOff_toInt {c t : I64} (hc0 : 0 ≤ c.toInt) (hc1 : c.toInt < 10000) (ht0 : 0 ≤ t.toInt)
    (ht1 : t.toInt < 10000) :
    (tranOffJ c t).toInt = (c.toInt - 1) * 3356 + 16 + (t.toInt - 1) * 334 := by
  unfold tranOffJ
  have hm1 : ((c - 1) * 3356 : I64).toInt = (c.toInt - 1) * 3356 := cardOff_toInt hc0 hc1
  have hm2 : ((t - 1) * 334 : I64).toInt = (t.toInt - 1) * 334 := by
    rw [BitVec.toInt_mul, sub1_toInt ht0 ht1, show (334 : I64).toInt = 334 by decide]
    exact bmod64_eq (by omega) (by omega)
  have e16 : (16 : I64).toInt = 16 := by decide
  have hA : ((c - 1) * 3356 + 16 : I64).toInt = (c.toInt - 1) * 3356 + 16 := by
    rw [BitVec.toInt_add, hm1, e16]
    exact bmod64_eq (by omega) (by omega)
  rw [BitVec.toInt_add, hA, hm2]
  exact bmod64_eq (by omega) (by omega)

theorem cardOff_lb {c : I64} (h0 : 0 ≤ c.toInt) (h1 : c.toInt < 10000) : -2147483648 < (cardOffJ c).toInt := by
  rw [cardOff_toInt h0 h1]; omega

theorem tranOff_lb {c t : I64} (hc0 : 0 ≤ c.toInt) (hc1 : c.toInt < 10000) (ht0 : 0 ≤ t.toInt)
    (ht1 : t.toInt < 10000) : -2147483648 < (tranOffJ c t).toInt := by
  rw [tranOff_toInt hc0 hc1 ht0 ht1]; omega

theorem tranOff16_lb {c t : I64} (hc0 : 0 ≤ c.toInt) (hc1 : c.toInt < 10000) (ht0 : 0 ≤ t.toInt)
    (ht1 : t.toInt < 10000) : -2147483648 < (tranOffJ c t + 16).toInt := by
  have e16 : (16 : I64).toInt = 16 := by decide
  have hv := bmod64_eq (v := (c.toInt - 1) * 3356 + 16 + (t.toInt - 1) * 334 + 16) (by omega) (by omega)
  rw [BitVec.toInt_add, tranOff_toInt hc0 hc1 ht0 ht1, e16, hv]; omega

end EquivLean.Modernize.Cbstm03a.Java.Seg2

namespace EquivLean.Modernize.Cbstm03a.Java.Seg2

/-- The executor's normal form of the bound: a small value is its own `bmod 2^64`. -/
theorem bm_lb {v : Int} (h0 : -2147483648 < v) (h1 : v < 9223372036854775808) :
    -2147483648 < v.bmod 18446744073709551616 := by
  have h := bmod64_eq (v := v) (by omega) (by omega)
  show -2147483648 < v.bmod (2 ^ 64)
  rw [h]; exact h0

theorem tranOff_range {c t : I64} (hc0 : 0 ≤ c.toInt) (hc1 : c.toInt < 10000) (ht0 : 0 ≤ t.toInt)
    (ht1 : t.toInt < 10000) : -3674 ≤ (tranOffJ c t).toInt ∧ (tranOffJ c t).toInt < 100000000 := by
  rw [tranOff_toInt hc0 hc1 ht0 ht1]; omega

end EquivLean.Modernize.Cbstm03a.Java.Seg2
