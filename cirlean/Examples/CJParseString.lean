import CIR
import Examples.Gen.CJStrings
import CIR.Logic.CJString

/-!
  cJSON's `parse_string` (`Examples/cpp/cjstrings.c`, the function unchanged),
  the paths that do not reach the copy loop.

  Both theorems below are checked by Lean's kernel. They used to be rejected
  with `(kernel) deep recursion detected` while `Res.ok_bind` was proved by
  `rfl`: simp then used it as a definitional step, the kernel compared
  `Res.ok v >>= f` with `f v` (both binds) by unfolding both, and its
  recursor reduction evaluated the range test of the `size_t` store
  `input_buffer->offset = …`, `inRange false 64 v` with `v = n + 1`
  symbolic, which recurses on the literal `2^64`. `ok_bind` now has a proof
  term (`CIR/Semantics/Basic.lean`). This file is not part of `Examples.lean`.

  The scan loop of `parse_string` is proved with the kernel in `CJScan.lean`
  (`string_scan_spec`, the same loop and checks as a function of its own).
  Here it runs inside the real function: `input_end` (`const unsigned char *`,
  moved by the loop) and `skipped_bytes` (`size_t`) are the binders, and the
  invariant is the same.

  What is open (scratch runs T2, T3, T5, U1 in `~/cirlean_work/scratch/strings/`):
  1. After the scan loop above and `cir_vcg`, the only goal left is the copy loop
     (`while (input_pointer < input_end)`): `malloc` through
     `input_buffer->hooks.allocate` (`.fn "malloc"`, once the module declares it:
     `global_hooks = { malloc, free, realloc }` in `cjstrings.c`) has run.
  2. (Addressed since `fa25900`, `Examples/TwoLoops.lean`: `cir_loop` follows
     the first loop's frame facts to the slots written before it; not yet
     re-run on this copy loop.) Formerly: that is the function's second loop,
     and `cir_loop` did not see the
     variables last written before the first loop: `slotBlockTy?` follows the
     `upd` chain of the loop-entry state only back to the first loop's exit
     state, which is abstract (`cirH_frame`). The binder `output` (a `T*` local
     pointing at the `malloc`ed block) is then taken for a `std::vector` slot
     (`Val.vec cir_gen2 …`, entry goals `∃ g, False`, body goals `False`), and
     with `(output_pointer : Ptr) input_pointer (mem : Mem)` the entry goal for
     the unmoved slot of `input_pointer` stays
     `σ₀✝.mem.blocks (m.next + 3) = Option.map (fun blk => {…, val :=
     ptrMove blk.val (ptrIdx blk.val)}) (σ₀✝.mem.blocks (m.next + 3))`:
     its value is behind the first loop's `cirH_frame : ∀ b, b ∉ [...] → b <
     σ₀✝.mem.next → σ.mem.blocks b = σ₀✝.mem.blocks b`, which nothing instantiates.
  3. Even with that fixed, the invariant needs the escape accounting: the
     block has `E - off - s + 1` bytes (`s` the first loop's `skipped_bytes`) and
     the copy loop writes at most one byte per input byte, `\uXXXX` consuming 6
     (at most 3 written) and a surrogate pair 12 (4 written); its pairing of
     backslashes differs from the scan's after a `\u`, so the proof needs a ghost
     function for the scan's pairs, not only `s ≤ E - (off + 1)`.
  4. `utf16_literal_to_utf8` (run with `parse_hex4` as a `@[cir_spec]`): `cir_vcg`
     stops at the `for` loop that encodes the bytes on each of 23 paths (the
     loop must be handled 23 times). The loop writes `(*output_pointer)[k]` through
     an `unsigned char **` parameter: `cir_loop` reads the binder `output_pointer`
     as the element index of a pointer that the loop moves, there is no binder
     for the array behind `*output_pointer`, so its block cannot leave the loop's
     frame.
-/

open CIR Gen.CJStrings

set_option maxHeartbeats 40000000

namespace Examples.CJParseString

/-- Not a string: the character at the offset is not a quote. The function
fails (returns 0) and sets `offset` to the character after it (`fail:` sets it
from `input_pointer`). -/
theorem parse_string_not_quote (itemp : Ptr) (b bc : Nat) (kb kc : BlockKind) (tyc : Ty) (xs : List Int)
    (len off depth : Nat) (hooks : Val) (m : Mem) (hkb : kb ≠ .readonly)
    (hb : b < m.next)
    (hbb : m.blocks b = some ⟨kb, true, .record "parse_buffer",
      .agg [.ptr (.loc bc [.idx 0]), .int len, .int off, .int depth, hooks]⟩)
    (hc : bc < m.next) (hcc : m.blocks bc = some ⟨kc, true, tyc, .arr (xs.map .int)⟩)
    (hlen : len ≤ xs.length) (hoff : off < len) (h63 : len < 2 ^ 63)
    (hxs : ∀ x ∈ xs, 0 ≤ x ∧ x ≤ 255) (hbc : b ≠ bc)
    (hq : ∃ x, xs[off]? = some x ∧ x ≠ 34)
    (htyc : ∃ es tlen, tyc = .array (.int es 8) tlen) :
    Returns ctx "parse_string" [.ptr itemp, .ptr (.loc b [])] m
      (fun r m' => r = some (.int 0) ∧
        m'.blocks b = some ⟨kb, true, .record "parse_buffer",
          .agg [.ptr (.loc bc [.idx 0]), .int len, .int (off + 1), .int depth, hooks]⟩ ∧
        Frame m m' [b]) := by
  obtain ⟨es, tlen, rfl⟩ := htyc
  cir_start
  cir_vcg

/-- An unterminated string: a quote, then no further quote. The scan loop runs
to the end of the buffer (the last character may be a backslash: it fails
earlier), and the function fails with `offset = off + 1`. -/
theorem parse_string_unterminated (itemp : Ptr) (b bc : Nat) (kb kc : BlockKind) (tyc : Ty) (xs : List Int)
    (len off depth : Nat) (hooks : Val) (m : Mem) (hkb : kb ≠ .readonly)
    (hb : b < m.next)
    (hbb : m.blocks b = some ⟨kb, true, .record "parse_buffer",
      .agg [.ptr (.loc bc [.idx 0]), .int len, .int off, .int depth, hooks]⟩)
    (hc : bc < m.next) (hcc : m.blocks bc = some ⟨kc, true, tyc, .arr (xs.map .int)⟩)
    (hlen : len ≤ xs.length) (hoff : off < len) (h63 : len < 2 ^ 63)
    (hxs : ∀ x ∈ xs, 0 ≤ x ∧ x ≤ 255) (hbc : b ≠ bc)
    (hq : xs[off]? = some 34)
    (hnq : ∀ j : Nat, off < j → j < len → ∃ x, xs[j]? = some x ∧ x ≠ 34)
    (htyc : ∃ es tlen, tyc = .array (.int es 8) tlen) :
    Returns ctx "parse_string" [.ptr itemp, .ptr (.loc b [])] m
      (fun r m' => r = some (.int 0) ∧
        m'.blocks b = some ⟨kb, true, .record "parse_buffer",
          .agg [.ptr (.loc bc [.idx 0]), .int len, .int (off + 1), .int depth, hooks]⟩ ∧
        Frame m m' [b]) := by
  obtain ⟨es, tlen, rfl⟩ := htyc
  cir_start
  cir_vcg
  cir_loop (fun input_end skipped_bytes => off + 1 ≤ input_end ∧ input_end ≤ len ∧
      skipped_bytes ≤ input_end - (off + 1))
    (fun input_end skipped_bytes => len - input_end)
  all_goals cir_vcg

/-- The contract of `utf16_literal_to_utf8` that `parse_string` needs. -/
def Utf16Spec : Prop := ∀ (bi i e : Nat) (xs : List Int) (ki : BlockKind) (tyi : Ty) (p : Nat) (pk : BlockKind)
    (pty : Ty) (bo o : Nat) (ys : List Val) (ko : BlockKind) (tyo : Ty) (m : Mem),
    bi < m.next → m.blocks bi = some ⟨ki, true, tyi, .arr (xs.map .int)⟩ → i ≤ e → e ≤ xs.length →
    p < m.next → m.blocks p = some ⟨pk, true, pty, .ptr (.loc bo [.idx o])⟩ → pk ≠ .readonly →
    bo < m.next → m.blocks bo = some ⟨ko, true, tyo, .arr ys⟩ → ko ≠ .readonly →
    (e < i + 6 ∨ o + 4 ≤ ys.length) → p ≠ bi → p ≠ bo → bi ≠ bo →
    Returns ctx "utf16_literal_to_utf8" [.ptr (.loc bi [.idx i]), .ptr (.loc bi [.idx e]), .ptr (.loc p [])] m
      (fun r m' =>
        (∃ sl : Nat, r = some (.int sl) ∧ (sl = 0 ∨ sl = 6 ∨ sl = 12) ∧ (sl ≠ 0 → i + sl ≤ e)) ∧
        (∃ o' : Nat, m'.blocks p = some ⟨pk, true, pty, .ptr (.loc bo [.idx o'])⟩ ∧ o ≤ o' ∧ o' ≤ o + 4 ∧
          (r = some (.int 0) → o' ≤ o) ∧ (r = some (.int 6) → o' ≤ o + 3)) ∧
        (∃ ys' : List Val, m'.blocks bo = some ⟨ko, true, tyo, .arr ys'⟩ ∧ ys'.length = ys.length) ∧
        Frame m m' [p, bo])

set_option hygiene false in
macro "scan_esc_close" : tactic => `(tactic| (
  obtain ⟨_, _, _, hIH⟩ := cirH_user
  have h92 : wrap true 32 (xs[input_end]'(by omega)) = 92 := by simpa using ‹wrap true 32 _ = 92›
  have := hIH _ _ (ScanFrom.esc_byte hxs (by omega) h92 ‹ScanFrom xs (input_end + 2) _ _›)
  first
  | (rwa [show ∀ a b : Nat, a + 1 + b = a + (b + 1) from fun a b => by omega] at this)
  | (rw [show (wrap false 64 (↑skipped_bytes + 1)).toNat = skipped_bytes + 1 by
        rw [wrap_of_bounds (by decide) (by simp only [intMin_u, intMax_u64]; omega)]; omega]
     rwa [show ∀ a b : Nat, a + 1 + b = a + (b + 1) from fun a b => by omega] at this)))

set_option hygiene false in
macro "scan_plain_close" : tactic => `(tactic| (
  obtain ⟨_, _, _, hIH⟩ := cirH_user
  have h92 : ¬ wrap true 32 (xs[input_end]'(by omega)) = 92 := by simpa using ‹¬ wrap true 32 _ = 92›
  exact hIH _ _ (ScanFrom.plain_byte hxs (by omega) cirH_br0 h92 ‹ScanFrom xs (input_end + 1) _ _›)))

set_option hygiene false in
/-- The copy loop's obligations with the window invariant: arithmetic; the
next copy position for a plain character, an escape (possibly one past the
stop after a misaligned `\u`), and `\u` (any digits); the loop entry. -/
macro "copy_close2" : tactic => `(tactic| (
  cir_strip_mdata
  first
  | omega
  | (-- plain character
     have hlt : input_pointer < input_end := by omega
     left
     rcases hq with hq | hq <;> subst q
     · have hS1 := hS.step_plain_byte hxs hlt (by omega) ‹¬ wrap true 32 _ = 92›
       exact ⟨input_pointer + 1, k, Or.inl rfl, hS1, by have := hS1.bound; omega⟩
     · exact ⟨input_pointer + 1, k, Or.inl rfl, hS, by omega⟩)
  | (-- an escape pair
     have hlt : input_pointer < input_end := by omega
     have h92 := Classical.not_not.mp ‹¬¬ wrap true 32 _ = 92›
     -- (`cir_run` may already have normalized `(↑p + 2).toNat` to `p + 2`)
     try rw [show ((input_pointer : Int) + 2).toNat = input_pointer + 2 by omega]
     by_cases h2 : input_pointer + 2 ≤ input_end
     · left
       obtain ⟨j, k', hj, hS', hk', hw⟩ := hS.window (input_pointer + 2 - q) (by omega)
       refine ⟨q + (input_pointer + 2 - q) + j, k', by omega, hS', ?_⟩
       have := hS'.bound; omega
     · right
       rcases hq with hq | hq <;> subst q
       · exfalso; have := (hS.step_esc_byte hxs hlt (by omega) h92).2.2; omega
       · have hk0 : k = 0 := by
           have he : input_pointer + 1 = input_end := by omega
           rw [he] at hS; exact hS.at_end
         omega)
  | (-- `\u`: any digits
     have hsl0 : cir_w_cirH_post0a ≠ 0 := by omega
     have hsle := cirH_post0apbb hsl0
     try rw [show ((input_pointer : Int) + (cir_w_cirH_post0a : Int)).toNat = input_pointer + cir_w_cirH_post0a by omega]
     left
     obtain ⟨j, k', hj, hS', hk', hw⟩ := hS.window (input_pointer + cir_w_cirH_post0a - q) (by omega)
     refine ⟨q + (input_pointer + cir_w_cirH_post0a - q) + j, k', by omega, hS', ?_⟩
     have := hS'.bound
     rcases cirH_post0apba with h0 | h6 | h12
     · omega
     · subst h6; have ho := cirH_post0bapbbbb rfl; omega
     · subst h12; omega)
  | (-- the loop entry
     left
     obtain ⟨h1, h2, h3, hIH⟩ := cirH_user
     have hS0 := hIH _ _ (ScanFrom.quote_byte hxs (by omega) (Classical.not_not.mp cirH_br0))
     exact ⟨off + 1, skipped_bytes, Or.inl (by omega), by simpa using hS0, by omega⟩)))

/-- `parse_string` has no undefined behaviour on any input: whatever the
characters after the offset, the scan, the allocation and the copy loop stay in
bounds (given the contract of `utf16_literal_to_utf8`). The scan loop keeps the
ghost scan `ScanFrom` from the opening quote; the copy loop's position is on a
scan boundary or one character inside an escape pair (a `\u` with invalid
digits consumes six characters: `parse_hex4` returns 0), and the bytes written
stay within `allocation_length` (`ScanFrom.window`). -/
theorem parse_string_noub (hutf : Utf16Spec) (ib : Nat) (iv : List Val) (b bc : Nat) (kb kc : BlockKind) (tyc : Ty)
    (xs : List Int) (len off depth : Nat) (m : Mem) (hkb : kb ≠ .readonly)
    (hib : ib < m.next) (hiv : m.blocks ib = some ⟨.heap, true, .record "cJSON", .agg iv⟩)
    (hivl : iv.length = 8)
    (hb : b < m.next)
    (hbb : m.blocks b = some ⟨kb, true, .record "parse_buffer",
      .agg [.ptr (.loc bc [.idx 0]), .int len, .int off, .int depth,
        .agg [.ptr (.fn "malloc"), .ptr (.fn "free"), .ptr (.fn "realloc")]]⟩)
    (hc : bc < m.next) (hcc : m.blocks bc = some ⟨kc, true, tyc, .arr (xs.map .int)⟩)
    (hlen : len ≤ xs.length) (hoff : off < len) (h63 : len < 2 ^ 63)
    (hxs : ∀ x ∈ xs, 0 ≤ x ∧ x ≤ 255) (hbc : b ≠ bc) (hbi : b ≠ ib) (hci : bc ≠ ib)
    (hwf : m.WF) (htyc : ∃ es tlen, tyc = .array (.int es 8) tlen) :
    Returns ctx "parse_string" [.ptr (.loc ib []), .ptr (.loc b [])] m
      (fun r _ => ∃ v, r = some (.int v)) := by
  obtain ⟨es, tlen, rfl⟩ := htyc
  cir_start
  cir_vcg
  cir_loop (fun input_end skipped_bytes => off + 1 ≤ input_end ∧ input_end ≤ len ∧
      skipped_bytes ≤ input_end - (off + 1) ∧
      ∀ e k, ScanFrom xs input_end e k → ScanFrom xs (off + 1) e (k + skipped_bytes))
    (fun input_end skipped_bytes => len - input_end)
  all_goals cir_vcg
  all_goals (try scan_esc_close)
  all_goals (try scan_plain_close)
  -- the copy loop
  all_goals (try cir_loop (fun input_pointer output_pointer (output : List Val) =>
      off + 1 ≤ input_pointer ∧ output.length = input_end - off - skipped_bytes + 1 ∧
      ((∃ q k, (q = input_pointer ∨ q = input_pointer + 1) ∧ ScanFrom xs q input_end k ∧
          output_pointer + ((input_end - input_pointer) - k) ≤ input_end - off - skipped_bytes) ∨
       (input_end < input_pointer ∧ input_pointer ≤ input_end + 1 ∧
          output_pointer ≤ input_end - off - skipped_bytes)))
    (fun input_pointer output_pointer (output : List Val) => input_end + 1 - input_pointer))
  -- the copy loop's body and exit: the scan facts first, then execution only
  all_goals (try (obtain ⟨hip1, hlen', ⟨q, k, hq, hS, hbud⟩ | ⟨hc1, hc2, hc3⟩⟩ := cirH_user
                  all_goals (try (have hB := hS.bound
                                  have hL := hS.lt_length))))
  all_goals (try cir_run)
  all_goals copy_close2


end Examples.CJParseString
