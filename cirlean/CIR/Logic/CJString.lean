import CIR.Logic.Exec

/-!
  The scan of cJSON's `parse_string` as a ghost relation, for the accounting
  of its copy loop.

  `parse_string` first scans the input from the character after the opening
  quote to the first quote that no backslash escapes, counting the escape
  pairs (`skipped_bytes`: a backslash and the character after it), and
  allocates `(input_end - start) - skipped_bytes + 1` bytes. The copy loop then
  writes at most one byte per input byte outside escapes, one byte per escape
  pair, at most 3 bytes for `\uXXXX` (6 input bytes, one pair) and 4 for a
  surrogate pair (12 input bytes, two pairs). `ScanFrom xs p e k` states that
  the scan started at `p` stops at the quote at `e` after `k` pairs; the copy
  loop's invariant keeps `ScanFrom xs input_pointer e k` with
  `output_pointer + ((e - input_pointer) - k) ≤ allocation_length`.
-/

namespace CIR

/-- The scan of `parse_string` started at `p` stops at the quote at `e` (the
first quote not escaped by a backslash), having counted `k` escape pairs. -/
inductive ScanFrom (xs : List Int) : Nat → Nat → Nat → Prop
  | quote {p : Nat} : xs[p]? = some 34 → ScanFrom xs p p 0
  | plain {p e k : Nat} {c : Int} : xs[p]? = some c → c ≠ 34 → c ≠ 92 →
      ScanFrom xs (p + 1) e k → ScanFrom xs p e k
  | esc {p e k : Nat} : xs[p]? = some 92 → p + 1 < xs.length →
      ScanFrom xs (p + 2) e k → ScanFrom xs p e (k + 1)

namespace ScanFrom

variable {xs : List Int}

/-- The scan stops at or after its start, and each pair takes two characters. -/
theorem bound {p e k : Nat} (h : ScanFrom xs p e k) : p ≤ e ∧ 2 * k ≤ e - p := by
  induction h with
  | quote _ => omega
  | plain _ _ _ _ ih => omega
  | esc _ _ _ ih => omega

theorem lt_length {p e k : Nat} (h : ScanFrom xs p e k) : e < xs.length := by
  induction h with
  | quote hq =>
    rename_i p
    exact (List.getElem?_eq_some_iff.mp hq).1
  | plain _ _ _ _ ih => exact ih
  | esc _ _ _ ih => exact ih

theorem at_end {e k : Nat} (h : ScanFrom xs e e k) : k = 0 := by
  cases h with
  | quote _ => rfl
  | plain _ _ _ h' => have := h'.bound; omega
  | esc _ _ h' => have := h'.bound; omega

/-- A character before the stop that is no backslash: the scan goes on at the
next one. -/
theorem step_plain {p e k : Nat} {c : Int} (h : ScanFrom xs p e k) (hp : p < e)
    (hc : xs[p]? = some c) (hc92 : c ≠ 92) : ScanFrom xs (p + 1) e k ∧ c ≠ 34 := by
  cases h with
  | quote _ => omega
  | plain hc' h34 _ h' =>
    rw [hc] at hc'
    cases hc'
    exact ⟨h', h34⟩
  | esc h92 _ _ =>
    rw [hc] at h92
    cases h92
    exact absurd rfl hc92

/-- A backslash before the stop: one pair, and the scan goes on two characters
later, at or before the stop. -/
theorem step_esc {p e k : Nat} (h : ScanFrom xs p e k) (hp : p < e) (hc : xs[p]? = some 92) :
    1 ≤ k ∧ ScanFrom xs (p + 2) e (k - 1) ∧ p + 2 ≤ e := by
  cases h with
  | quote hq => omega
  | plain hc' _ h92 _ =>
    rw [hc] at hc'
    cases hc'
    exact absurd rfl h92
  | esc _ _ h' =>
    refine ⟨by omega, by simpa using h', ?_⟩
    exact h'.bound.1

/-- Characters `p, …, p + n - 1` before the stop, none a backslash: the scan
goes on at `p + n` with the same count. -/
theorem step_plains {p e k : Nat} (n : Nat) (h : ScanFrom xs p e k) (hn : p + n ≤ e)
    (hc : ∀ j, p ≤ j → j < p + n → ∃ c, xs[j]? = some c ∧ c ≠ 92) : ScanFrom xs (p + n) e k := by
  induction n generalizing p with
  | zero => simpa using h
  | succ n ih =>
    obtain ⟨c, hcj, hc92⟩ := hc p (Nat.le_refl _) (by omega)
    have h1 := (h.step_plain (by omega) hcj hc92).1
    have := ih h1 (by omega) (fun j hj1 hj2 => hc j (by omega) (by omega))
    rwa [show p + 1 + n = p + (n + 1) by omega] at this

/-- `\uXXXX` before the stop (no backslash among the four digits): one pair,
and the scan goes on six characters later. -/
theorem step_u6 {p e k : Nat} (h : ScanFrom xs p e k) (hp : p + 6 ≤ e) (hc : xs[p]? = some 92)
    (hd : ∀ j, p + 2 ≤ j → j < p + 6 → ∃ c, xs[j]? = some c ∧ c ≠ 92) :
    1 ≤ k ∧ ScanFrom xs (p + 6) e (k - 1) := by
  obtain ⟨hk, h2, _⟩ := h.step_esc (by omega) hc
  refine ⟨hk, ?_⟩
  have := step_plains 4 h2 (by omega) (fun j h1 h2 => hd j h1 h2)
  simpa using this

/-- A surrogate pair `\uXXXX\uXXXX` before the stop (no backslash among the
digits): two pairs, and the scan goes on twelve characters later. -/
theorem step_u12 {p e k : Nat} (h : ScanFrom xs p e k) (hp : p + 12 ≤ e) (hc : xs[p]? = some 92)
    (hc6 : xs[p + 6]? = some 92)
    (hd : ∀ j, p + 2 ≤ j → j < p + 12 → j ≠ p + 6 → j ≠ p + 7 → ∃ c, xs[j]? = some c ∧ c ≠ 92) :
    2 ≤ k ∧ ScanFrom xs (p + 12) e (k - 2) := by
  obtain ⟨hk, h6⟩ := h.step_u6 (by omega) hc (fun j h1 h2 => hd j h1 (by omega) (by omega) (by omega))
  obtain ⟨hk', h8, _⟩ := h6.step_esc (by omega) hc6
  have := step_plains 4 h8 (by omega) (fun j h1 h2 => hd j (by omega) (by omega) (by omega) (by omega))
  refine ⟨by omega, ?_⟩
  have e1 : p + 6 + 2 + 4 = p + 12 := by omega
  rw [e1] at this
  simpa [show k - 1 - 1 = k - 2 by omega] using this

/-- The scan over any `n` characters from `q` (before the stop): it stands at
`q + n`, or one further inside an escape pair (`j = 1`), and the pairs it
counted fit in those characters. The copy loop of `parse_string` does not
always move along the scan's pairs (`\u` with invalid digits is consumed as
six characters, since `parse_hex4` then returns 0), so its invariant allows
both positions. -/
theorem window {q e k : Nat} (h : ScanFrom xs q e k) (n : Nat) (hn : q + n ≤ e) :
    ∃ j k', (j = 0 ∨ j = 1) ∧ ScanFrom xs (q + n + j) e k' ∧ k' ≤ k ∧ 2 * (k - k') ≤ n + j := by
  induction n using Nat.strongRecOn generalizing q k with
  | _ n ih =>
    match n with
    | 0 => exact ⟨0, k, Or.inl rfl, by simpa using h, Nat.le_refl _, by simp⟩
    | n + 1 =>
      cases h with
      | quote _ => omega
      | plain _ _ _ h' =>
        obtain ⟨j, k', hj, hS, hk, h2⟩ := ih n (by omega) h' (by omega)
        exact ⟨j, k', hj, by rwa [show q + 1 + n + j = q + (n + 1) + j by omega] at hS, hk, by omega⟩
      | esc _ _ h' =>
        rename_i k0 _ _
        match n with
        | 0 => exact ⟨1, k0, Or.inr rfl, by simpa using h', by omega, by omega⟩
        | n + 1 =>
          obtain ⟨j, k', hj, hS, hk, h2⟩ := ih n (by omega) h' (by have := h'.bound; omega)
          exact ⟨j, k', hj, by rwa [show q + 2 + n + j = q + (n + 1 + 1) + j by omega] at hS,
            by omega, by omega⟩

/-! Steps stated over the characters as `parse_string` reads them (an
`unsigned char` converted to `int`). -/

theorem wrap_byte {x : Int} (h0 : 0 ≤ x) (h1 : x ≤ 255) : wrap true 32 x = x :=
  wrap_of_bounds (by decide) ⟨by rw [intMin_s32]; omega, by rw [intMax_s32]; omega⟩

theorem plain_byte {p e k : Nat} (hxs : ∀ x ∈ xs, 0 ≤ x ∧ x ≤ 255) (hp : p < xs.length)
    (h34 : ¬ wrap true 32 xs[p] = 34) (h92 : ¬ wrap true 32 xs[p] = 92)
    (h : ScanFrom xs (p + 1) e k) : ScanFrom xs p e k := by
  have hb := hxs _ (List.getElem_mem hp)
  rw [wrap_byte hb.1 hb.2] at h34 h92
  exact ScanFrom.plain (List.getElem?_eq_getElem hp) h34 h92 h

theorem esc_byte {p e k : Nat} (hxs : ∀ x ∈ xs, 0 ≤ x ∧ x ≤ 255) (hp : p + 1 < xs.length)
    (h92 : wrap true 32 (xs[p]'(by omega)) = 92) (h : ScanFrom xs (p + 2) e k) :
    ScanFrom xs p e (k + 1) := by
  have hb := hxs _ (List.getElem_mem (show p < xs.length by omega))
  rw [wrap_byte hb.1 hb.2] at h92
  exact ScanFrom.esc (by rw [List.getElem?_eq_getElem (by omega)]; exact congrArg some h92) hp h

theorem quote_byte {p : Nat} (hxs : ∀ x ∈ xs, 0 ≤ x ∧ x ≤ 255) (hp : p < xs.length)
    (h34 : wrap true 32 xs[p] = 34) : ScanFrom xs p p 0 := by
  have hb := hxs _ (List.getElem_mem hp)
  rw [wrap_byte hb.1 hb.2] at h34
  exact ScanFrom.quote (by rw [List.getElem?_eq_getElem hp]; exact congrArg some h34)

theorem getElem?_of_byte {p : Nat} {c : Int} (hxs : ∀ x ∈ xs, 0 ≤ x ∧ x ≤ 255) (hp : p < xs.length)
    (h : wrap true 32 xs[p] = c) : xs[p]? = some c := by
  have hb := hxs _ (List.getElem_mem hp)
  rw [wrap_byte hb.1 hb.2] at h
  rw [List.getElem?_eq_getElem hp, h]

theorem step_plain_byte {p e k : Nat} (hxs : ∀ x ∈ xs, 0 ≤ x ∧ x ≤ 255) (h : ScanFrom xs p e k)
    (hp : p < e) (hpl : p < xs.length) (h92 : ¬ wrap true 32 xs[p] = 92) : ScanFrom xs (p + 1) e k := by
  have hb := hxs _ (List.getElem_mem hpl)
  rw [wrap_byte hb.1 hb.2] at h92
  exact (h.step_plain hp (List.getElem?_eq_getElem hpl) h92).1

theorem step_esc_byte {p e k : Nat} (hxs : ∀ x ∈ xs, 0 ≤ x ∧ x ≤ 255) (h : ScanFrom xs p e k)
    (hp : p < e) (hpl : p < xs.length) (h92 : wrap true 32 xs[p] = 92) :
    1 ≤ k ∧ ScanFrom xs (p + 2) e (k - 1) ∧ p + 2 ≤ e :=
  h.step_esc hp (getElem?_of_byte hxs hpl h92)

/-- Before the stop there is room for at least one byte. -/
theorem budget_pos {p e k : Nat} (h : ScanFrom xs p e k) (hp : p < e) : 1 ≤ (e - p) - k := by
  have := h.bound; omega

/-- With six characters before the stop, `\uXXXX` has room for four bytes. -/
theorem budget_u {p e k : Nat} (h : ScanFrom xs p e k) (hp : p + 6 ≤ e) : 3 ≤ (e - p) - k := by
  have := h.bound; omega

end ScanFrom

end CIR
