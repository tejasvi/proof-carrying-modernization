import CIR
import Examples.Gen.PtrArgs

/-!
  Loops that write through pointer parameters (`Examples/cpp/ptrargs.c`).
  A binder that names a pointer variable the loop does not assign stands for
  what the loop changes through it, by the variable's type:
  * `T*` (not a `std::vector`/`std::string`): the elements of the array it
    points into, a `List Val` (`fill_buf`, `copy_nonspace`);
  * `T**`: the element index of the pointer it points to, a `Nat`
    (`skip_spaces`, the shape of cJSON's `skip_oneline_comment(char **input)`).
  The block is the pointer's target at loop entry. Distinct caller blocks
  are stated as hypotheses (`b ≠ p`).
-/

open CIR Gen.PtrArgs

set_option maxHeartbeats 4000000

namespace Examples.PtrArgs

/-- `fill_buf(buf, n, c)` writes `n` characters through `buf`. -/
theorem fill_buf_spec (b i0 : Nat) (xs : List Val) (k : BlockKind) (ty : Ty) (m : Mem) (n c : Int)
    (hb : b < m.next) (ha : m.blocks b = some ⟨k, true, ty, .arr xs⟩) (hk : k ≠ .readonly)
    (hn : 0 ≤ n ∧ n ≤ 2147483647 ∧ i0 + n.toNat ≤ xs.length) (hc : -128 ≤ c ∧ c ≤ 127)
    (hty : ∃ es tlen, ty = .array (.int es 8) tlen) :
    Returns ctx "fill_buf" [.ptr (.loc b [.idx i0]), .int n, .int c] m
      (fun r m' => r = none ∧ Frame m m' [b]) := by
  obtain ⟨es, tlen, rfl⟩ := hty
  cir_start
  cir_vcg
  cir_loop (fun i buf => 0 ≤ i ∧ i ≤ n ∧ buf.length = xs.length) (fun i buf => n - i)
  all_goals cir_vcg

/-- `skip_spaces(&p)` moves the caller's pointer `p` (block `p`) past spaces. -/
theorem skip_spaces_spec (b i0 n : Nat) (xs : List Int) (k : BlockKind) (ty : Ty) (m : Mem)
    (p : Nat) (pk : BlockKind) (pty : Ty)
    (hb : b < m.next) (ha : m.blocks b = some ⟨k, true, ty, .arr (xs.map .int)⟩)
    (hp : p < m.next) (hpa : m.blocks p = some ⟨pk, true, pty, .ptr (.loc b [.idx i0])⟩) (hpk : pk ≠ .readonly)
    (hin : i0 ≤ n) (hn : n < xs.length) (hz : xs[n]? = some 0) (hxs : ∀ x ∈ xs, -128 ≤ x ∧ x ≤ 127) (hbp : b ≠ p)
    (hty : ∃ es tlen, ty = .array (.int es 8) tlen) (hpty : ∃ t, pty = .ptr t) :
    Returns ctx "skip_spaces" [.ptr (.loc p [])] m (fun r m' => r = none ∧ Frame m m' [p]) := by
  obtain ⟨es, tlen, rfl⟩ := hty
  obtain ⟨t, rfl⟩ := hpty
  cir_start
  cir_vcg
  cir_loop (fun input => i0 ≤ input ∧ input ≤ n) (fun input => n - input)
  all_goals cir_vcg

/-- `copy_nonspace(s, out, n)` copies at most `n` characters. -/
theorem copy_nonspace_spec (bs bo : Nat) (xs : List Int) (ys : List Val) (ks ko : BlockKind) (ts to : Ty)
    (m : Mem) (n : Int)
    (hbs : bs < m.next) (hs : m.blocks bs = some ⟨ks, true, ts, .arr (xs.map .int)⟩)
    (hbo : bo < m.next) (ho : m.blocks bo = some ⟨ko, true, to, .arr ys⟩) (hko : ko ≠ .readonly)
    (hd : bs ≠ bo) (hn : 0 ≤ n ∧ n ≤ 2147483647 ∧ n.toNat ≤ xs.length ∧ n.toNat ≤ ys.length)
    (hxs : ∀ x ∈ xs, -128 ≤ x ∧ x ≤ 127)
    (hts : ∃ es tlen, ts = .array (.int es 8) tlen) (hto : ∃ es tlen, to = .array (.int es 8) tlen) :
    Returns ctx "copy_nonspace" [.ptr (.loc bs [.idx 0]), .ptr (.loc bo [.idx 0]), .int n] m
      (fun r m' => (∃ k, r = some (.int k) ∧ 0 ≤ k ∧ k ≤ n) ∧ Frame m m' [bo]) := by
  obtain ⟨es, tlen, rfl⟩ := hts
  obtain ⟨eo, olen, rfl⟩ := hto
  cir_start
  cir_vcg
  cir_loop (fun i k out => 0 ≤ i ∧ i ≤ n ∧ 0 ≤ k ∧ k ≤ i ∧ out.length = ys.length) (fun i k out => n - i)
  all_goals cir_vcg

end Examples.PtrArgs
