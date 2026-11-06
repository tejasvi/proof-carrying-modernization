import CIR
import Examples.Gen.CJStrings

/-!
  `parse_hex4` with the tight result `h < 65536` (not in `Examples.lean`: 16 minutes
  on one core, 986 core-seconds). The invariant is the bound of each digit count,
  `h ≤ 0, 240, 4080, 65520, 65535` after `0 … 4` digits, as implications on `i`;
  `cir_vcg` closes every goal (the bounds make the unsigned conversions identities),
  but each of the sixteen arithmetic goals carries four implications and `omega`
  splits on all of them.
-/

open CIR Gen.CJStrings

set_option maxHeartbeats 40000000

namespace Examples.CJHex4Tight

theorem parse_hex4_spec (b i0 : Nat) (xs : List Int) (k : BlockKind) (ty : Ty) (m : Mem)
    (hb : b < m.next) (ha : m.blocks b = some ⟨k, true, ty, .arr (xs.map .int)⟩)
    (hn : i0 + 4 ≤ xs.length) (h63 : xs.length < 2 ^ 63) (hxs : ∀ x ∈ xs, 0 ≤ x ∧ x ≤ 255)
    (hty : ∃ es tlen, ty = .array (.int es 8) tlen) :
    Returns ctx "parse_hex4" [.ptr (.loc b [.idx i0])] m
      (fun r m' => (∃ h : Nat, r = some (.int h) ∧ h < 65536) ∧ Frame m m' []) := by
  obtain ⟨es, tlen, rfl⟩ := hty
  cir_start
  cir_vcg
  cir_loop (fun h i => i ≤ 4 ∧ (i = 0 → h = 0) ∧ (i = 1 → h ≤ 240) ∧ (i = 2 → h ≤ 4080) ∧
      (i = 3 → h ≤ 65520) ∧ (i = 4 → h ≤ 65535)) (fun h i => 4 - i)
  all_goals cir_vcg

end Examples.CJHex4Tight
