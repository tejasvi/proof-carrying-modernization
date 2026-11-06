import EquivLean.Bridge.Aeneas.SpecAuto
import EquivLean.Bridge.Aeneas.CobolRec

/-!
# Aeneas (Rust) bridge: decimal digits and Latin-1 bytes

Helpers for the Rust translations of the CardDemo programs (the Headline A interface: numeric
fields as `i64`, alphanumeric fields as `[u8; n]` of Latin-1 bytes, DISPLAY lines as `Vec<u8>`).

* A numeric DISPLAY field `PIC 9(n)` shows its `n` low decimal digits, zero-padded:
  `zeroPad n v`, the bytes of `EquivLean.Cobol.Rec.zpad n v` (`zeroPad_val`).  Its digits from
  the left (`zeroPad_take_succ`) serve a loop that appends them with a falling power of ten; its
  digits from the right (`zeroPad_succ_left`, `set_mid`) serve a loop that fills a buffer from its
  end.  `aeneas_spec` does not generate the arithmetic invariants of such loops.
* CP037 is a bijection on bytes: the Latin-1 byte of a character is the CP037 text of its EBCDIC
  byte (`cp037_roundtrip`, `latin1_text`), so an alphanumeric field displays as its bytes.
-/

open Aeneas Aeneas.Std

namespace EquivLean.Aeneas

open EquivLean.Cobol.Rec (zpad cp037Code ebcdicOfLatin1)
open Cobol.Digits (toDigits)

/-! ## Decimal digits -/

/-- Digit `j` (from the left) of the `n` digits of `v`. -/
theorem toDigits_getElem (n v j : Nat) (h : j < n) :
    (toDigits 10 n v)[j]'(by simpa using h) = v / 10 ^ (n - 1 - j) % 10 := by
  induction n generalizing v j with
  | zero => omega
  | succ n ih =>
    simp only [toDigits]
    by_cases hj : j < n
    · rw [List.getElem_append_left (by simpa using hj), ih (v / 10) j hj]
      rw [Nat.div_div_eq_div_mul, ← Nat.pow_succ']
      congr 3
      omega
    · have : j = n := by omega
      subst this
      rw [List.getElem_append_right (by simp)]
      simp

/-- A code point as a byte. -/
def byteOf (d : Nat) : U8 := ⟨BitVec.ofNat 8 d⟩

/-- The `n` zero-padded digits of `v`, as Latin-1 bytes. -/
def zeroPad (n v : Nat) : List U8 := (zpad n v).map byteOf

theorem zeroPad_length (n v : Nat) : (zeroPad n v).length = n := by
  simp [zeroPad, zpad]

theorem zeroPad_take_succ (n v j : Nat) (h : j < n) :
    (zeroPad n v).take (j + 1) =
      (zeroPad n v).take j ++ [byteOf (48 + v / 10 ^ (n - 1 - j) % 10)] := by
  rw [take_succ_of_lt (by rw [zeroPad_length]; exact h)]
  congr 2
  simp only [zeroPad, zpad, List.getElem_map, toDigits_getElem n v j h]

theorem byteOf_val (a : Nat) (h : a < 256) : (byteOf a).val = a := by
  simp [byteOf, UScalar.val, Nat.mod_eq_of_lt h]


theorem zeroPad_val (n v : Nat) : (zeroPad n v).map UScalar.val = zpad n v := by
  simp only [zeroPad, zpad, List.map_map]
  apply List.map_congr_left
  intro e he
  have := Cobol.Digits.toDigits_lt (by decide) n v e he
  simp only [Function.comp_apply]
  rw [byteOf_val _ (by omega)]


/-- The digits of `x` grow on the left: digit `i` (from the right) in front of the `i` low ones. -/
theorem toDigits_succ_left (i x : Nat) :
    toDigits 10 (i + 1) x = [x / 10 ^ i % 10] ++ toDigits 10 i x := by
  apply List.ext_getElem
  · simp
  · intro j h1 h2
    rw [toDigits_getElem (i + 1) x j (by simpa using h1)]
    cases j with
    | zero => simp
    | succ j =>
      simp only [List.singleton_append, List.getElem_cons_succ]
      rw [toDigits_getElem i x j (by simp at h1; omega)]
      have : i + 1 - 1 - (j + 1) = i - 1 - j := by omega
      rw [this]

theorem zeroPad_succ_left (i x : Nat) :
    zeroPad (i + 1) x = [byteOf (48 + x / 10 ^ i % 10)] ++ zeroPad i x := by
  simp only [zeroPad, zpad, toDigits_succ_left, List.map_append, List.map_cons, List.map_nil]

/-- Writing at the end of a run of `k + 1` copies. -/
theorem set_replicate_end {α : Type _} (k : Nat) (a c : α) (rest : List α) :
    (List.replicate (k + 1) a ++ rest).set k c = List.replicate k a ++ [c] ++ rest := by
  rw [List.replicate_succ', List.append_assoc, List.set_append_right _ _ (by simp)]
  simp

/-- Writing the digit in front of the digits already written. -/
theorem set_mid {α : Type _} (d i : Nat) (hi : i < d) (Z R : List α) (a c : α) :
    (List.replicate (d - i) a ++ Z ++ R).set (d - 1 - i) c =
      List.replicate (d - 1 - i) a ++ ([c] ++ Z) ++ R := by
  obtain ⟨k, hk⟩ : ∃ k, d - i = k + 1 := ⟨d - 1 - i, by omega⟩
  have hk' : d - 1 - i = k := by omega
  rw [hk, hk', List.append_assoc, set_replicate_end]
  simp

/-! ## Latin-1 bytes and CP037 -/

/-- CP037 decodes the EBCDIC byte of every Latin-1 code point back to it. -/
theorem cp037_roundtrip : ∀ n : Fin 256, cp037Code (ebcdicOfLatin1 n.val) = n.val := by
  decide +kernel

/-- The Latin-1 bytes of an alphanumeric field are the CP037 text of its EBCDIC bytes. -/
theorem latin1_text (l : List U8) :
    (l.map fun u => ebcdicOfLatin1 u.val).map cp037Code = l.map UScalar.val := by
  rw [List.map_map]
  apply List.map_congr_left
  intro u _
  have h := cp037_roundtrip ⟨u.val, by have := u.hBounds; simpa using this⟩
  simp only [Function.comp_apply]
  exact h

/-! ## Field values -/

/-- An unsigned numeric field (`PIC 9(n)`) holds a nonnegative value: `push_unsigned`-style helpers
can take its absolute value without overflow. -/
theorem num_nonneg {f : EquivLean.Cobol.Rec.Field} (hu : EquivLean.Cobol.Rec.UnsignedDisplay f)
    {v : Int} (hv : f.Valid (.num v)) : 0 ≤ v := by
  obtain ⟨fmt, hk, -, -, hh, -⟩ := hv
  obtain ⟨-, hs⟩ := hu fmt hk
  unfold Cobol.NumFmt.Holds at hh
  simp only [hs, Bool.false_eq_true, ↓reduceIte] at hh
  split_ifs at hh
  · exact hh.1
  · exact hh.2 trivial

end EquivLean.Aeneas
