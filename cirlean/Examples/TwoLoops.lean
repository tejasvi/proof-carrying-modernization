import CIR
import Examples.Gen.TwoLoops

/-!
  Two loops in one function (`Examples/cpp/twoloops.c`). The second loop runs
  in the first loop's exit state, which is abstract: the variables the second
  loop reads or writes through (`p`, set before the first loop) are found
  through the first loop's facts (its frame and entry state, which the second
  loop's own `cirH_frame`, `σ₀`, … shadow by name), and the array written
  through `p` is the caller's.
-/

open CIR Gen.TwoLoops

set_option maxHeartbeats 4000000

namespace Examples.TwoLoops

/-- `fill_after_count(a, n)` counts to `n`, then writes `7` into the first
`count` elements of `a`. -/
theorem fill_after_count_spec (b : Nat) (xs : List Val) (k : BlockKind) (ty : Ty) (m : Mem) (n : Int)
    (hb : b < m.next) (ha : m.blocks b = some ⟨k, true, ty, .arr xs⟩) (hk : k ≠ .readonly)
    (hn : 0 ≤ n ∧ n ≤ 2147483647 ∧ n.toNat ≤ xs.length)
    (hty : ∃ es tlen, ty = .array (.int es 32) tlen) :
    Returns ctx "fill_after_count" [.ptr (.loc b [.idx 0]), .int n] m
      (fun r m' => r = some (.int n) ∧ Frame m m' [b]) := by
  obtain ⟨es, tlen, rfl⟩ := hty
  cir_start
  cir_vcg
  cir_loop (fun i count => 0 ≤ i ∧ i ≤ n ∧ count = i) (fun i count => n - i)
  · cir_vcg
    cir_loop (fun j p => 0 ≤ j ∧ j ≤ n ∧ p.length = xs.length) (fun j p => n - j)
    all_goals cir_vcg
  · cir_vcg

end Examples.TwoLoops
