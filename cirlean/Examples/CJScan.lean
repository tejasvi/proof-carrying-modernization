import CIR
import Examples.Gen.CJScan

/-!
  The scan for the closing quote in cJSON's `parse_string`
  (`Examples/cpp/cjscan.c`: the loop and the checks around it are cJSON 1.7.19's
  text, unchanged; the allocation and the copy loop of `parse_string` are cut
  and the allocation length is returned).

  The loop variable `input_end` is a `const unsigned char *` local that the loop
  moves (`input_end++`, twice on an escape sequence): `cir_loop` names it by its
  element index, a `Nat`, in the array of the buffer's content; `skipped_bytes`
  (`size_t`) is a `Nat`. The invariant is the three bounds that make every read
  and the final subtraction defined; `cir_vcg` proves the rest, including the
  existential witnesses of the postcondition.
-/

open CIR Gen.CJScan

set_option maxHeartbeats 40000000

namespace Examples.CJScan

/-- `string_scan(buffer)` for a buffer with `offset < length` (the caller has
checked `can_access_at_index(buffer, 0)`): it has no undefined behaviour, leaves
the buffer as it is, and returns either 0 (not a string, an unterminated string,
a backslash as the last character) or `E - offset - s`, where `E` is the index of
the closing quote (`off + 1 ≤ E < len`, `xs[E] = '"'`) and `s ≤ E - (off + 1)` is
the number of escape sequences skipped. -/
theorem string_scan_spec (b bc : Nat) (kb kc : BlockKind) (tyc : Ty) (xs : List Int)
    (len off depth : Nat) (hooks : Val) (m : Mem)
    (hb : b < m.next)
    (hbb : m.blocks b = some ⟨kb, true, .record "parse_buffer",
      .agg [.ptr (.loc bc [.idx 0]), .int len, .int off, .int depth, hooks]⟩)
    (hc : bc < m.next) (hcc : m.blocks bc = some ⟨kc, true, tyc, .arr (xs.map .int)⟩)
    (hlen : len ≤ xs.length) (hoff : off < len) (h63 : len < 2 ^ 63)
    (hxs : ∀ x ∈ xs, 0 ≤ x ∧ x ≤ 255)
    (htyc : ∃ es tlen, tyc = .array (.int es 8) tlen) :
    Returns ctx "string_scan" [.ptr (.loc b [])] m
      (fun r m' => (∃ n : Int, r = some (.int n) ∧
          (n ≠ 0 → ∃ E s : Nat, off + 1 ≤ E ∧ E < len ∧ xs[E]? = some 34 ∧ s ≤ E - (off + 1) ∧
            n = ↑E - ↑off - ↑s)) ∧
        m'.blocks b = m.blocks b ∧ Frame m m' []) := by
  obtain ⟨es, tlen, rfl⟩ := htyc
  cir_start
  cir_vcg
  cir_loop (fun input_end skipped_bytes => off + 1 ≤ input_end ∧ input_end ≤ len ∧
      skipped_bytes ≤ input_end - (off + 1))
    (fun input_end skipped_bytes => len - input_end)
  all_goals cir_vcg

end Examples.CJScan
