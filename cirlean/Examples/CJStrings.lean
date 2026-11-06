import CIR
import Examples.Gen.CJStrings
import Examples.CJLib

/-!
  cJSON's buffer walking functions (`Examples/cpp/cjstrings.c`: cJSON 1.7.19's
  `buffer_skip_whitespace` and `skip_utf8_bom`, unchanged except for `static`;
  the same file has `parse_hex4`, `utf16_literal_to_utf8` and `parse_string`:
  see `CJHex4.lean`, `CJParseString.lean`, `CJScan.lean`). Each theorem says that
  the function has no undefined behaviour under natural preconditions on the
  buffer, and what it leaves in it. Build: `lake build Examples.CJStrings`
  (460 s on one core; not in `Examples.lean`).

  The buffer `parse_buffer { content; length; offset; depth; hooks }` is a
  record block `b`, `content` points to the start of a char array block `bc`
  (`xs`, the characters as `unsigned char`: `∀ x ∈ xs, 0 ≤ x ∧ x ≤ 255`) with
  `length ≤ xs.length`. The members of a record are numbered from 0: the loop
  variable `buffer->offset` of `buffer_skip_whitespace` is the binder
  `buffer_2`.

  Preconditions that `cir_vcg` asks for and a C programmer would not state:
  * `len < 2 ^ 63`: indexing with a `size_t` (`content + offset`) converts the
    index to a signed 64-bit offset, whose range is checked;
  * `off < 2 ^ 64` for a stored `size_t` that the proof does not otherwise
    bound: members read from memory must be in the range of their type (the
    VCG does not assume it for `.int off`);
  * the content block must be alive, even on a path that only compares
    `buffer->content` with NULL;
  * `2 ≤ m.next` for `skip_utf8_bom`: the string literal `"\xEF\xBB\xBF"` is
    block 1 of the module (`global_hooks` is block 0) and the VCG splits on
    whether it is the next fresh block (`Module.globals.length ≤ m.next`).

  What the VCG does not do yet (each is a step or a lemma below):
  1. an existential over a `Nat` for a stored `size_t` (`∃ off' : Nat,
     σ.fieldInt b 2 = ↑off' ∧ …`) gets no witness (`cir_exists_inst` finds
     witnesses for equations between applications of the same function): the
     leftover is `∃ off', σ.fieldInt b 2 = ↑off' ∧ …` (witness
     `(σ.fieldInt b 2).toNat`); state it over `Int`;
  2. a top-level `∨` in a postcondition is left (`(A ∧ Frame …) ∨ False`):
     state implications;
  3. an invariant `∀ j, lo ≤ j → j < i → P j` extended to `i + 1` (a loop that
     scans), and `xs[(↑(0 + f).toNat + 0).toNat]` read by the code against
     `xs[f.toNat]` stated in the specification (index normal form): the
     manual steps of `skip_whitespace_spec`; the goals
     `∃ x, xs[j]? = some x ∧ x ≤ 32` (j < f + 1) and `f + 1 = ↑len ∨ 32 < xs[f.toNat]`
     are left, the hypotheses carry `σ.fieldInt b 2 + 1` with metadata
     (`cir_strip_mdata` before `omega`);
  4. a symbolic list in `strncmp` (`Std.strncmpVals 3 (List.drop … (List.map
     Val.int xs)) [-17, -69, -65, 0]` does not reduce): destructure the list
     first (`rcases xs with _ | ⟨x0, _ | ⟨x1, _ | ⟨x2, rest⟩⟩⟩`), one lemma per
     case (a `<;>` over the cases exceeded the heartbeat budget of the whole
     declaration);
  5. the range of an unsigned conversion (`wrap_u_range` in `CJLib.lean`, used
     in `CJHex4.lean`).
-/

open CIR Gen.CJStrings Examples.CJ

set_option maxHeartbeats 40000000

namespace Examples.CJStrings

/-- `buffer_skip_whitespace(buffer)`: moves `offset` to the first character
above 32 at or after it, or to `length - 1` when there is none (it is the last
character); a buffer at its end is left as it is. The buffer is returned. -/
theorem skip_whitespace_spec (b bc : Nat) (kb kc : BlockKind) (tyc : Ty) (xs : List Int)
    (len off depth : Nat) (hooks : Val) (m : Mem) (hkb : kb ≠ .readonly)
    (hb : b < m.next)
    (hbb : m.blocks b = some ⟨kb, true, .record "parse_buffer",
      .agg [.ptr (.loc bc [.idx 0]), .int len, .int off, .int depth, hooks]⟩)
    (hc : bc < m.next) (hcc : m.blocks bc = some ⟨kc, true, tyc, .arr (xs.map .int)⟩)
    (hlen : len ≤ xs.length) (hoff : off ≤ len) (h63 : len < 2 ^ 63)
    (hxs : ∀ x ∈ xs, 0 ≤ x ∧ x ≤ 255) (hbc : b ≠ bc)
    (htyc : ∃ es tlen, tyc = .array (.int es 8) tlen) :
    Returns ctx "buffer_skip_whitespace" [.ptr (.loc b [])] m
      (fun r m' => r = some (.ptr (.loc b [])) ∧ ∃ off' : Int,
        m'.blocks b = some ⟨kb, true, .record "parse_buffer",
          .agg [.ptr (.loc bc [.idx 0]), .int len, .int off', .int depth, hooks]⟩ ∧
        off ≤ off' ∧ off' ≤ len ∧
        (off < len → off' < len ∧
          (∀ j : Nat, off ≤ j → j < off' → ∃ x, xs[j]? = some x ∧ x ≤ 32) ∧
          (off' + 1 = len ∨ ∃ x, xs[off'.toNat]? = some x ∧ 32 < x)) ∧
        Frame m m' [b]) := by
  obtain ⟨es, tlen, rfl⟩ := htyc
  cir_start
  cir_vcg
  cir_loop (fun buffer_2 => off ≤ buffer_2 ∧ buffer_2 ≤ len ∧
      ∀ j : Nat, off ≤ j → j < buffer_2 → ∃ x, xs[j]? = some x ∧ x ≤ 32)
    (fun buffer_2 => len - buffer_2)
  all_goals cir_vcg
  -- the invariant at the next character: the new index is the one just read
  · rename_i j hj1 hj2
    simp only [Int.zero_add, Int.add_zero, Int.toNat_natCast] at *
    cir_strip_mdata
    rcases Nat.lt_or_ge j (σ.fieldInt b 2).toNat with h | h
    · exact cirH_user.2.2 j hj1 (by omega)
    · have hj : j = (σ.fieldInt b 2).toNat := by omega
      subst hj
      have hlt : (σ.fieldInt b 2).toNat < xs.length := by omega
      cir_elems
      cir_unwrap
      exact ⟨xs[(σ.fieldInt b 2).toNat]'hlt, List.getElem?_eq_getElem hlt, by omega⟩
  -- the character at the new offset is above 32
  · simp only [Int.zero_add, Int.add_zero, Int.toNat_natCast] at *
    cir_strip_mdata
    cir_elems
    cir_unwrap
    omega

/-- Without undefined behaviour, only: the same function with the weak
postcondition (the buffer is returned, only block `b` changes) is closed by
`cir_vcg` alone, after the loop's two-conjunct invariant. -/
theorem skip_whitespace_ub (b bc : Nat) (kb kc : BlockKind) (tyc : Ty) (xs : List Int)
    (len off depth : Nat) (hooks : Val) (m : Mem) (hkb : kb ≠ .readonly)
    (hb : b < m.next)
    (hbb : m.blocks b = some ⟨kb, true, .record "parse_buffer",
      .agg [.ptr (.loc bc [.idx 0]), .int len, .int off, .int depth, hooks]⟩)
    (hc : bc < m.next) (hcc : m.blocks bc = some ⟨kc, true, tyc, .arr (xs.map .int)⟩)
    (hlen : len ≤ xs.length) (hoff : off ≤ len) (h63 : len < 2 ^ 63)
    (hxs : ∀ x ∈ xs, 0 ≤ x ∧ x ≤ 255) (hbc : b ≠ bc)
    (htyc : ∃ es tlen, tyc = .array (.int es 8) tlen) :
    Returns ctx "buffer_skip_whitespace" [.ptr (.loc b [])] m
      (fun r m' => r = some (.ptr (.loc b [])) ∧ ∃ off' : Int,
        m'.blocks b = some ⟨kb, true, .record "parse_buffer",
          .agg [.ptr (.loc bc [.idx 0]), .int len, .int off', .int depth, hooks]⟩ ∧
        off ≤ off' ∧ off' ≤ len ∧ (off < len → off' < len) ∧
        Frame m m' [b]) := by
  obtain ⟨es, tlen, rfl⟩ := htyc
  cir_start
  cir_vcg
  cir_loop (fun buffer_2 => off ≤ buffer_2 ∧ buffer_2 ≤ len) (fun buffer_2 => len - buffer_2)
  all_goals cir_vcg

/-! ### `skip_utf8_bom` -/

/-- `skip_utf8_bom` on a buffer with a non-zero offset: returns NULL. -/
theorem skip_bom_off (b bc : Nat) (kb kc : BlockKind) (tyc : Ty) (xs : List Int)
    (len off depth : Nat) (hooks : Val) (m : Mem)
    (hb : b < m.next)
    (hbb : m.blocks b = some ⟨kb, true, .record "parse_buffer",
      .agg [.ptr (.loc bc [.idx 0]), .int len, .int off, .int depth, hooks]⟩)
    (hc : bc < m.next) (hcc : m.blocks bc = some ⟨kc, true, tyc, .arr (xs.map .int)⟩)
    (hoff64 : off < 2 ^ 64) (hoff : off ≠ 0) :
    Returns ctx "skip_utf8_bom" [.ptr (.loc b [])] m
      (fun r m' => r = some (.ptr .null) ∧ m'.blocks b = m.blocks b ∧ Frame m m' []) := by
  cir_start
  cir_vcg

/-- Offset 0 and at most 4 characters: no BOM test (`can_access_at_index(buffer, 4)`
fails). -/
theorem skip_bom_short (b bc : Nat) (kb kc : BlockKind) (tyc : Ty) (xs : List Int)
    (len depth : Nat) (hooks : Val) (m : Mem)
    (hb : b < m.next)
    (hbb : m.blocks b = some ⟨kb, true, .record "parse_buffer",
      .agg [.ptr (.loc bc [.idx 0]), .int len, .int 0, .int depth, hooks]⟩)
    (hc : bc < m.next) (hcc : m.blocks bc = some ⟨kc, true, tyc, .arr (xs.map .int)⟩)
    (hlen4 : len ≤ 4) :
    Returns ctx "skip_utf8_bom" [.ptr (.loc b [])] m
      (fun r m' => r = some (.ptr (.loc b [])) ∧ m'.blocks b = m.blocks b ∧ Frame m m' [b]) := by
  cir_start
  cir_vcg

/-- Offset 0 and more than 4 characters: `strncmp` on the first three, against the
string literal `"\xEF\xBB\xBF"` (`cir_ro_globals`). The characters are the head of the
list so that the model's `strncmp` reduces. -/
theorem skip_bom_main (b bc : Nat) (kb kc : BlockKind) (tyc : Ty) (x0 x1 x2 : Int) (rest : List Int)
    (len depth : Nat) (hooks : Val) (m : Mem) (hkb : kb ≠ .readonly)
    (hb : b < m.next)
    (hbb : m.blocks b = some ⟨kb, true, .record "parse_buffer",
      .agg [.ptr (.loc bc [.idx 0]), .int len, .int 0, .int depth, hooks]⟩)
    (hc : bc < m.next) (hcc : m.blocks bc = some ⟨kc, true, tyc, .arr ((x0 :: x1 :: x2 :: rest).map .int)⟩)
    (hlen4 : 4 < len) (h63 : len < 2 ^ 63)
    (h0 : 0 ≤ x0 ∧ x0 ≤ 255) (h1 : 0 ≤ x1 ∧ x1 ≤ 255) (h2 : 0 ≤ x2 ∧ x2 ≤ 255)
    (hg : 2 ≤ m.next) (hro : Module.RoGlobals module m)
    (htyc : ∃ es tlen, tyc = .array (.int es 8) tlen) :
    Returns ctx "skip_utf8_bom" [.ptr (.loc b [])] m
      (fun r m' =>
        r = some (.ptr (.loc b [])) ∧ ∃ off' : Int,
          (off' = 3 ↔ (x0 = 239 ∧ x1 = 187 ∧ x2 = 191)) ∧ (off' = 0 ∨ off' = 3) ∧
          m'.blocks b = some ⟨kb, true, .record "parse_buffer",
            .agg [.ptr (.loc bc [.idx 0]), .int len, .int off', .int depth, hooks]⟩ ∧
        Frame m m' [b]) := by
  obtain ⟨es, tlen, rfl⟩ := htyc
  cir_ro_globals hro
  cir_start
  cir_vcg

/-- `skip_utf8_bom(buffer)`: NULL unless the offset is 0; otherwise the buffer, with
the offset moved by 3 exactly when more than 4 characters are readable and the
buffer starts with `EF BB BF`. -/
theorem skip_utf8_bom_spec (b bc : Nat) (kb kc : BlockKind) (tyc : Ty) (xs : List Int)
    (len off depth : Nat) (hooks : Val) (m : Mem) (hkb : kb ≠ .readonly)
    (hb : b < m.next)
    (hbb : m.blocks b = some ⟨kb, true, .record "parse_buffer",
      .agg [.ptr (.loc bc [.idx 0]), .int len, .int off, .int depth, hooks]⟩)
    (hc : bc < m.next) (hcc : m.blocks bc = some ⟨kc, true, tyc, .arr (xs.map .int)⟩)
    (hlen : len ≤ xs.length) (h63 : len < 2 ^ 63) (hoff64 : off < 2 ^ 64)
    (hxs : ∀ x ∈ xs, 0 ≤ x ∧ x ≤ 255)
    (hg : 2 ≤ m.next) (hro : Module.RoGlobals module m)
    (htyc : ∃ es tlen, tyc = .array (.int es 8) tlen) :
    Returns ctx "skip_utf8_bom" [.ptr (.loc b [])] m
      (fun r m' =>
        (off ≠ 0 → r = some (.ptr .null) ∧ m'.blocks b = m.blocks b) ∧
        (off = 0 → r = some (.ptr (.loc b [])) ∧ ∃ off' : Int,
          (off' = 3 ↔ (4 < len ∧ xs.take 3 = [239, 187, 191])) ∧ (off' = 0 ∨ off' = 3) ∧
          m'.blocks b = some ⟨kb, true, .record "parse_buffer",
            .agg [.ptr (.loc bc [.idx 0]), .int len, .int off', .int depth, hooks]⟩) ∧
        Frame m m' [b]) := by
  by_cases hoff0 : off = 0
  · subst hoff0
    by_cases h4 : 4 < len
    · rcases xs with _ | ⟨x0, _ | ⟨x1, _ | ⟨x2, rest⟩⟩⟩
      · simp at hlen; omega
      · simp at hlen; omega
      · simp at hlen; omega
      · have h0 := hxs x0 (by simp)
        have h1 := hxs x1 (by simp)
        have h2 := hxs x2 (by simp)
        refine returns_mono (skip_bom_main b bc kb kc tyc x0 x1 x2 rest len depth hooks m hkb hb hbb
          hc hcc h4 h63 h0 h1 h2 hg hro htyc) ?_
        rintro r m' ⟨hr, off', hoff', hoff'', hbl, hfr⟩
        refine ⟨fun h => absurd rfl h, fun _ => ⟨hr, off', ?_, hoff'', hbl⟩, hfr⟩
        rw [hoff']
        simp [h4]
    · refine returns_mono (skip_bom_short b bc kb kc tyc xs len depth hooks m hb hbb hc hcc (by omega)) ?_
      rintro r m' ⟨hr, hbl, hfr⟩
      refine ⟨fun h => absurd rfl h, fun _ => ⟨hr, 0, ?_, Or.inl rfl, ?_⟩, hfr⟩
      · simp; omega
      · rw [hbl]; exact hbb
  · refine returns_mono (skip_bom_off b bc kb kc tyc xs len off depth hooks m hb hbb hc hcc hoff64 hoff0) ?_
    rintro r m' ⟨hr, hbl, hfr⟩
    refine ⟨fun _ => ⟨hr, hbl⟩, fun h => absurd h hoff0, ?_⟩
    exact ⟨hfr.1, fun b' hb' hlt => hfr.2 b' (by simp) hlt⟩

end Examples.CJStrings
