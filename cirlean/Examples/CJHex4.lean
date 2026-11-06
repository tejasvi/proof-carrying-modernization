import CIR
import Examples.Gen.CJStrings
import Examples.CJLib

/-!
  cJSON's `parse_hex4` (`Examples/cpp/cjstrings.c`): a loop over four hexadecimal
  digits that builds an `unsigned int` with `h << 4`. The loop variables `h`
  (`unsigned`) and `i` (`size_t`) are `Nat`s.

  `cir_loop` adds, for every unsigned variable, the obligation that its next value
  is in range; here the next `h` is `wrap false 32 ((h + d) * 16)`, and the range of
  a `wrap` is not known to `cir_close` (it only knows `wrap_u32_self`, for a
  value already in range). Nine leftover goals `(wrap false 32 …).toNat <
  4294967296` are closed by `wrap_ranges; omega` (`CJLib.lean`). The failed
  attempts of `cir_close` on them take most of the 10 minutes.
-/

open CIR Gen.CJStrings Examples.CJ

set_option maxHeartbeats 40000000

namespace Examples.CJHex4

/-- `parse_hex4(input)` reads four characters (an invalid digit returns 0 at once,
so four readable characters are enough) and returns an unsigned value. -/
theorem parse_hex4_ub (b i0 : Nat) (xs : List Int) (k : BlockKind) (ty : Ty) (m : Mem)
    (hb : b < m.next) (ha : m.blocks b = some ⟨k, true, ty, .arr (xs.map .int)⟩)
    (hn : i0 + 4 ≤ xs.length) (h63 : xs.length < 2 ^ 63) (hxs : ∀ x ∈ xs, 0 ≤ x ∧ x ≤ 255)
    (hty : ∃ es tlen, ty = .array (.int es 8) tlen) :
    Returns ctx "parse_hex4" [.ptr (.loc b [.idx i0])] m
      (fun r m' => (∃ h : Nat, r = some (.int h) ∧ h < 4294967296) ∧ Frame m m' []) := by
  obtain ⟨es, tlen, rfl⟩ := hty
  cir_start
  cir_vcg
  cir_loop (fun h i => i ≤ 4 ∧ h < 4294967296) (fun h i => 4 - i)
  all_goals cir_vcg
  all_goals (cir_strip_mdata; wrap_ranges; omega)

end Examples.CJHex4
