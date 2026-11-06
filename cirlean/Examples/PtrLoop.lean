import CIR
import Examples.Gen.PtrLoop

/-!
  Loops whose variable is a pointer walking a string
  (`Examples/cpp/ptrloop.c`). `cir_loop` names a pointer variable `p : T*` by
  its element index: the invariant `fun p => …` takes `p : Nat`, and the
  pointer is the one at loop entry moved to that element of the same array
  (`PtrSlot`). The string is `xs[i..]`, terminated at `n`, in a block `b` of
  any kind; `∀ x ∈ xs, …` gives the characters' range, which `cir_close`
  instantiates at each character read.
-/

open CIR Gen.PtrLoop

set_option maxHeartbeats 4000000

namespace Examples.PtrLoop

/-- `str_len(s)` is the length of the string. -/
theorem str_len_spec (b i n : Nat) (xs : List Int) (k : BlockKind) (ty : Ty) (m : Mem)
    (hb : b < m.next) (ha : m.blocks b = some ⟨k, true, ty, .arr (xs.map .int)⟩)
    (hin : i ≤ n) (hn : n < xs.length) (hz : xs[n]? = some 0)
    (hnz : ∀ j, i ≤ j → j < n → xs[j]? ≠ some 0) (hsmall : n - i < 2 ^ 31)
    (hxs : ∀ x ∈ xs, -128 ≤ x ∧ x ≤ 127)
    (hty : ∃ es tlen, ty = .array (.int es 8) tlen) :
    Returns ctx "str_len" [.ptr (.loc b [.idx i])] m
      (fun v m' => v = some (.int ((n : Int) - i)) ∧ Frame m m' []) := by
  obtain ⟨es, tlen, rfl⟩ := hty
  cir_start
  cir_vcg
  cir_loop (fun p => i ≤ p ∧ p ≤ n) (fun p => n - p)
  all_goals cir_vcg

/-- `count_char(s, c)` counts at most the string's characters. -/
theorem count_char_spec (b i e : Nat) (c : Int) (xs : List Int) (k : BlockKind) (ty : Ty) (m : Mem)
    (hb : b < m.next) (ha : m.blocks b = some ⟨k, true, ty, .arr (xs.map .int)⟩)
    (hie : i ≤ e) (he : e < xs.length) (hz : xs[e]? = some 0) (hsmall : e - i < 2 ^ 31)
    (hxs : ∀ x ∈ xs, -128 ≤ x ∧ x ≤ 127) (hc : -128 ≤ c ∧ c ≤ 127)
    (hty : ∃ es tlen, ty = .array (.int es 8) tlen) :
    Returns ctx "count_char" [.ptr (.loc b [.idx i]), .int c] m
      (fun v m' => (∃ r, v = some (.int r) ∧ 0 ≤ r ∧ r ≤ (e : Int) - i) ∧ Frame m m' []) := by
  obtain ⟨es, tlen, rfl⟩ := hty
  cir_start
  cir_vcg
  cir_loop (fun s n => i ≤ s ∧ s ≤ e ∧ 0 ≤ n ∧ n ≤ (s : Int) - i) (fun s n => e - s)
  all_goals cir_vcg

/-- `has_char(c, str)`: the increment in a do-while condition
(`while (*str++ != '\0')`, as tiny-regex-c's `matchcharclass`). -/
theorem has_char_spec (b i n : Nat) (c : Int) (xs : List Int) (k : BlockKind) (ty : Ty) (m : Mem)
    (hb : b < m.next) (ha : m.blocks b = some ⟨k, true, ty, .arr (xs.map .int)⟩)
    (hin : i ≤ n) (hn : n < xs.length) (hz : xs[n]? = some 0)
    (hxs : ∀ x ∈ xs, -128 ≤ x ∧ x ≤ 127) (hc : -128 ≤ c ∧ c ≤ 127)
    (hty : ∃ es tlen, ty = .array (.int es 8) tlen) :
    Returns ctx "has_char" [.int c, .ptr (.loc b [.idx i])] m
      (fun v m' => (v = some (.int 0) ∨ v = some (.int 1)) ∧ Frame m m' []) := by
  obtain ⟨es, tlen, rfl⟩ := hty
  cir_start
  cir_vcg
  cir_loop (fun str => i ≤ str ∧ str ≤ n) (fun str => n - str)
  all_goals cir_vcg

end Examples.PtrLoop
