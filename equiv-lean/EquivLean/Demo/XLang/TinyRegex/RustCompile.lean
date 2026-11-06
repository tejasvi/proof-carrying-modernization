import EquivLean.Demo.XLang.TinyRegex.RustDefs
import EquivLean.Bridge.Aeneas.Tactic
import EquivLean.Bridge.Aeneas.SpecAuto

/-!
# tiny-regex-c → Rust: `re_compile`

`re_compile pattern` is `ok r`, where `r` is `none` exactly when the model's `compile` of the
pattern's bytes is `none`, and otherwise its objects and class buffer are the model's arrays
(`tok` of each object, the value of each byte); every compiled regex ends with an `UNUSED`
entry at index 29 (`WF`, needed by the matcher group).

Both loops are proved with a functional invariant: the model's result from the current state
(index, class-buffer index, arrays) is the model's result from the start.
-/

open Aeneas Aeneas.Std EquivLean EquivLean.Aeneas

namespace EquivLean.Demo.XLang.TinyRegex.Rust

/-! ## Values -/

/-- The bytes of a pattern or a text as the model's array. -/
def pat (s : Slice U8) : _root_.Array Nat := (s.val.map (·.val)).toArray

/-- `objs` as the model's array. -/
def absP (a : Std.Array tiny_regex.RegexObj 30#usize) : _root_.Array Tok := (a.val.map tok).toArray

/-- `ccl_buf` as the model's array. -/
def absB (a : Std.Array U8 40#usize) : _root_.Array Nat := (a.val.map (·.val)).toArray

/-- A compiled regex as the model's pair. -/
def absRe (re : tiny_regex.Regex) : _root_.Array Tok × _root_.Array Nat :=
  (absP re.objs, absB re.ccl_buf)

theorem ctx_eq (re : tiny_regex.Regex) (text : Slice U8) :
    ctx re text = ⟨absP re.objs, absB re.ccl_buf, pat text⟩ := rfl

theorem pat_size (s : Slice U8) : (pat s).size = s.val.length := by simp [pat]

/-- `at(s, i)`: the byte at `i`, 0 past the end. -/
def atv (s : Slice U8) (i : Usize) : U8 := if h : i.val < s.val.length then s.val[i.val] else 0#u8

theorem wp_at (s : Slice U8) (i : Usize) (Q : Except Error U8 → Prop) :
    wp (tiny_regex.«at» s i) Q ↔ Q (.ok (atv s i)) := by
  unfold tiny_regex.«at» atv
  aeneas_wp
  by_cases h : i.val < s.val.length <;> simp [h]

/-- `at` reads the model's `rd` value (the model's past-the-end reads are 0 as well). -/
theorem atv_val (s : Slice U8) (i : Usize) : (atv s i).val = (rd (pat s) i.val).1 := by
  unfold atv rd
  by_cases h : i.val < s.val.length
  · have h' : i.val < (pat s).size := by rw [pat_size]; exact h
    rw [dite_eq_left h, dite_eq_left h']
    simp [pat]
  · have h' : ¬ i.val < (pat s).size := by rw [pat_size]; exact h
    rw [dite_eq_right h, dite_eq_right h']
    split_ifs <;> rfl

theorem rd_pos {P : _root_.Array Nat} {i : Nat} (h : (rd P i).1 ≠ 0) : i < P.size := by
  unfold rd at h
  split_ifs at h with h1
  · exact h1
  all_goals exact absurd rfl h

/-! ## Writes -/

theorem absB_set (a : Std.Array U8 40#usize) (k : Usize) (x : U8) :
    absB (a.set k x) = (absB a).set! k.val x.val := by
  simp only [absB, Aeneas.Std.Array.set_val_eq, List.map_set, Array.set!,
    List.setIfInBounds_toArray]

theorem absB_from (a : Std.Array U8 40#usize) (k : Nat) (x : U8) (h) :
    absB (Std.Array.from (a.val.set k x) h) = (absB a).set! k x.val := by
  simp only [absB, Aeneas.Std.Array.from_val, List.map_set, Array.set!,
    List.setIfInBounds_toArray]

theorem absP_set (a : Std.Array tiny_regex.RegexObj 30#usize) (k : Usize)
    (x : tiny_regex.RegexObj) : absP (a.set k x) = (absP a).set! k.val (tok x) := by
  simp only [absP, Aeneas.Std.Array.set_val_eq, List.map_set, Array.set!,
    List.setIfInBounds_toArray]

theorem absP_from (a : Std.Array tiny_regex.RegexObj 30#usize) (k : Nat)
    (x : tiny_regex.RegexObj) (h) :
    absP (Std.Array.from (a.val.set k x) h) = (absP a).set! k (tok x) := by
  simp only [absP, Aeneas.Std.Array.from_val, List.map_set, Array.set!,
    List.setIfInBounds_toArray]

theorem absP_get (a : Std.Array tiny_regex.RegexObj 30#usize) (k : Nat) (hk : k < a.val.length) :
    (absP a)[k]! = tok a.val[k] := by
  simp only [absP, List.getElem!_toArray]
  rw [getElem!_pos (a.val.map tok) k (by simpa using hk)]
  simp

theorem get!_set!_self {α : Type _} [Inhabited α] (A : _root_.Array α) (k : Nat) (x : α)
    (hk : k < A.size) : (A.set! k x)[k]! = x := by
  rw [getElem!_pos (A.set! k x) k (by simpa [Array.set!] using hk)]
  simp [Array.set!]

theorem set!_set!_self {α : Type _} (A : _root_.Array α) (k : Nat) (x y : α) :
    (A.set! k x).set! k y = A.set! k y := by
  simp only [Array.set!, Array.setIfInBounds_setIfInBounds]

theorem absP_size (a : Std.Array tiny_regex.RegexObj 30#usize) : (absP a).size = 30 := by
  simp [absP]

theorem absB_size (a : Std.Array U8 40#usize) : (absB a).size = 40 := by
  simp [absB]

/-! ## `compile_class` -/

/-- The model's `[..]` copy, then `compStep`'s `ccl_buf[ccl_bufidx++] = 0` (`return 0` when the
buffer is full). -/
def cclFin (P : _root_.Array Nat) (i b : Nat) (B : _root_.Array Nat) :
    Option (Nat × Nat × _root_.Array Nat) :=
  match (cclCopy P i b B).1 with
  | none => none
  | some (i', b', B') => if 40 ≤ b' then none else some (i', b' + 1, B'.set! b' 0)

/-- One step of `cclFin` (the pattern index is inside the pattern). -/
theorem cclFin_step (P : _root_.Array Nat) (i b : Nat) (B : _root_.Array Nat) (hi : i < P.size) :
    cclFin P i b B =
      if (rd P (i + 1)).1 = 93 then (if 40 ≤ b then none else some (i + 1, b + 1, B.set! b 0))
      else if (rd P (i + 1)).1 = 0 then (if 40 ≤ b then none else some (i + 1, b + 1, B.set! b 0))
      else if (rd P (i + 1)).1 = 92 then
        if 39 ≤ b then none
        else if (rd P (i + 2)).1 = 0 then none
        else cclFin P (i + 2) (b + 2) ((B.set! b 92).set! (b + 1) (rd P (i + 2)).1)
      else if 40 ≤ b then none
      else cclFin P (i + 1) (b + 1) (B.set! b (rd P (i + 1)).1) := by
  unfold cclFin
  rw [cclCopy]
  by_cases h1 : i + 1 < P.size
  · have e1 : (rd P (i + 1)).1 = P[i + 1] := by simp [rd, h1]
    rw [e1, dite_eq_left h1]
    by_cases h93 : P[i + 1] = 93
    · simp [h93]
    by_cases h0 : P[i + 1] = 0
    · simp [h0]
    by_cases h92 : P[i + 1] = 92
    · simp only [h92, MAXCCL]
      by_cases hb : 39 ≤ b
      · simp [hb]
      by_cases h2 : i + 2 < P.size
      · have e2 : (rd P (i + 2)).1 = P[i + 2] := by simp [rd, h2]
        rw [e2]
        by_cases hc : P[i + 2] = 0 <;> simp [hb, h2, hc]
      · have h2' : i + 2 = P.size := by omega
        have e2 : (rd P (i + 2)).1 = 0 := by simp [rd, h2']
        rw [e2]
        simp [hb, h2']
    · by_cases hb : 40 ≤ b <;> simp [h93, h0, h92, MAXCCL, hb]
  · have h1' : i + 1 = P.size := by omega
    have e1 : (rd P (i + 1)).1 = 0 := by simp [rd, h1']
    rw [e1, dite_eq_right h1]
    simp [h1']

/-- The Rust result of `compile_class` against the model's `cclFin`. -/
def CclOk (r : Option (Usize × Usize) × Std.Array U8 40#usize) :
    Option (Nat × Nat × _root_.Array Nat) → Prop
  | none => r.1 = none
  | some (i', b', B') => ∃ i2 b2, r.1 = some (i2, b2) ∧ i2.val = i' ∧ b2.val = b' ∧ absB r.2 = B'

set_option maxHeartbeats 4000000 in
theorem compile_class_loop_spec (s : Slice U8) (buf : Std.Array U8 40#usize) (i b : Usize)
    (hi : i.val < s.val.length) :
    wp (tiny_regex.compile_class_loop s buf i b)
      (fun o => ∃ r, o = .ok r ∧ CclOk r (cclFin (pat s) i.val b.val (absB buf))) := by
  unfold tiny_regex.compile_class_loop
  refine wp_loop (loop_shape _)
    (fun st => st.2.1.val < s.val.length ∧
      cclFin (pat s) st.2.1.val st.2.2.val (absB st.1) = cclFin (pat s) i.val b.val (absB buf))
    (fun st => s.val.length - st.2.1.val) ?_ _ ⟨hi, rfl⟩
  simp only [Prod.forall]
  intro buf' i' b' hinv
  obtain ⟨hi', hinv⟩ := hinv
  rw [← hinv]
  clear hinv
  have hiP : i'.val < (pat s).size := by rw [pat_size]; exact hi'
  have hsl : s.val.length ≤ Usize.max := s.property
  have hlen : buf'.val.length = 40 := by simp
  have hge : ¬ s.val.length ≤ i'.val := by omega
  have hov : i'.val + 1 ≤ Usize.max := by omega
  simp only [tiny_regex.compile_class_loop.body]
  rw [cclFin_step _ _ _ _ hiP]
  by_cases h93 : (rd (pat s) (i'.val + 1)).1 = 93
  · aeneas_wp [wp_at, atv_val, array_update_eq, tiny_regex.MAX_CHAR_CLASS_LEN, hlen, loopCls_done,
      loopCls_cont, loopCls_error, hge, hov, h93]
    by_cases hb : 40 ≤ b'.val
    · simp only [hb, _root_.ite_true]
      exact ⟨_, rfl, rfl⟩
    · have hb' : b'.val < 40 := by omega
      have hov2 : b'.val + 1 ≤ Usize.max := by scalar_tac
      simp only [hb, hb', hov2, _root_.ite_false, _root_.dite_true]
      exact ⟨_, rfl, _, _, rfl, by simp, by simp, by simp [absB_from]⟩
  by_cases h0 : (rd (pat s) (i'.val + 1)).1 = 0
  · aeneas_wp [wp_at, atv_val, array_update_eq, tiny_regex.MAX_CHAR_CLASS_LEN, hlen, loopCls_done,
      loopCls_cont, loopCls_error, hge, hov, h93, h0]
    by_cases hb : 40 ≤ b'.val
    · simp only [hb, _root_.ite_true]
      exact ⟨_, rfl, rfl⟩
    · have hb' : b'.val < 40 := by omega
      have hov2 : b'.val + 1 ≤ Usize.max := by scalar_tac
      simp only [hb, hb', hov2, _root_.ite_false, _root_.dite_true]
      exact ⟨_, rfl, _, _, rfl, by simp, by simp, by simp [absB_from]⟩
  have hi1 : i'.val + 1 < s.val.length := by
    have := rd_pos h0
    rw [pat_size] at this
    exact this
  by_cases h92 : (rd (pat s) (i'.val + 1)).1 = 92
  · aeneas_wp [wp_at, atv_val, array_update_eq, tiny_regex.MAX_CHAR_CLASS_LEN, hlen, loopCls_done,
      loopCls_cont, loopCls_error, hge, hov, h93, h0, h92, Nat.reduceSub, Nat.add_assoc,
      Nat.reduceAdd, Nat.reduceEqDiff, ↓reduceIte]
    by_cases hb : 39 ≤ b'.val
    · simp only [hb, _root_.ite_true]
      exact ⟨_, rfl, rfl⟩
    have hov3 : i'.val + 2 ≤ Usize.max := by omega
    simp only [hb, hov3, _root_.ite_false, _root_.dite_true]
    by_cases h2 : (rd (pat s) (i'.val + 2)).1 = 0
    · simp only [h2, _root_.ite_true]
      exact ⟨_, rfl, rfl⟩
    have hi2 : i'.val + 2 < s.val.length := by
      have := rd_pos h2
      rw [pat_size] at this
      exact this
    have hb' : b'.val < 40 := by omega
    have hb1 : b'.val + 1 < 40 := by omega
    have hov2 : b'.val + 1 ≤ Usize.max := by scalar_tac
    have hov4 : b'.val + 2 ≤ Usize.max := by scalar_tac
    simp only [h2, hb', hb1, hov2, hov4, _root_.ite_false, _root_.dite_true,
      Aeneas.Std.Array.from_val, List.length_set, hlen]
    refine ⟨⟨hi2, ?_⟩, by omega⟩
    simp only [absB, Aeneas.Std.Array.from_val, List.map_set, Array.set!, List.setIfInBounds_toArray,
      atv_val, UScalar.ofNatCore_val_eq, h92]
  · aeneas_wp [wp_at, atv_val, array_update_eq, tiny_regex.MAX_CHAR_CLASS_LEN, hlen, loopCls_done,
      loopCls_cont, loopCls_error, hge, hov, h93, h0, h92]
    by_cases hb : 40 ≤ b'.val
    · simp only [hb, _root_.ite_true]
      exact ⟨_, rfl, rfl⟩
    have hb' : b'.val < 40 := by omega
    have hov2 : b'.val + 1 ≤ Usize.max := by scalar_tac
    simp only [hb, hb', hov2, _root_.ite_false, _root_.dite_true]
    refine ⟨⟨hi1, ?_⟩, by omega⟩
    simp only [absB, Aeneas.Std.Array.from_val, List.map_set, Array.set!, List.setIfInBounds_toArray,
      atv_val, UScalar.ofNatCore_val_eq]

/-! ## The model's compile loop, one step at a time (first components) -/

theorem compLoop_fst_end {P : _root_.Array Nat} {i j b : Nat} {re : _root_.Array Tok}
    {buf : _root_.Array Nat} {ub : Nat} (h : ¬ ((rd P i).1 ≠ 0 ∧ j + 1 < 30)) :
    (compLoop P i j b re buf ub).1 = some (re.set! j { re[j]! with type := 0 }, buf) := by
  rw [compLoop]
  rcases hr : rd P i with ⟨c, u⟩
  have h' : ¬ (c ≠ 0 ∧ j + 1 < MAXOBJ) := by
    have e : (rd P i).1 = c := by rw [hr]
    rw [e] at h
    exact h
  dsimp only
  rw [dite_eq_right h']
  rfl

theorem compLoop_fst_none {P : _root_.Array Nat} {i j b : Nat} {re : _root_.Array Tok}
    {buf : _root_.Array Nat} {ub : Nat} (h : (rd P i).1 ≠ 0 ∧ j + 1 < 30)
    (hs : (compStep P i j b re buf (rd P i).1).1 = none) :
    (compLoop P i j b re buf ub).1 = none := by
  rw [compLoop]
  rcases hr : rd P i with ⟨c, u⟩
  have e : (rd P i).1 = c := by rw [hr]
  rw [e] at h hs
  have h' : c ≠ 0 ∧ j + 1 < MAXOBJ := h
  dsimp only
  rw [dite_eq_left h']
  rcases hc : compStep P i j b re buf c with ⟨_ | ⟨i', b', re', buf'⟩, u'⟩
  · rfl
  · rw [hc] at hs
    exact absurd hs (by simp)

theorem compLoop_fst_none2 {P : _root_.Array Nat} {i j b : Nat} {re : _root_.Array Tok}
    {buf : _root_.Array Nat} {ub : Nat} {i' b' : Nat} {re' : _root_.Array Tok}
    {buf' : _root_.Array Nat} (h : (rd P i).1 ≠ 0 ∧ j + 1 < 30)
    (hs : (compStep P i j b re buf (rd P i).1).1 = some (i', b', re', buf'))
    (hci : (rd P i').1 = 0) :
    (compLoop P i j b re buf ub).1 = none := by
  rw [compLoop]
  rcases hr : rd P i with ⟨c, u⟩
  have e : (rd P i).1 = c := by rw [hr]
  rw [e] at h hs
  have h' : c ≠ 0 ∧ j + 1 < MAXOBJ := h
  dsimp only
  rw [dite_eq_left h']
  rcases hc : compStep P i j b re buf c with ⟨_ | ⟨i2, b2, re2, buf2⟩, u'⟩
  · rfl
  · rw [hc] at hs
    simp only [Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hs
    dsimp only
    rw [ite_eq_left (by simp [hci])]

theorem compLoop_fst_step {P : _root_.Array Nat} {i j b : Nat} {re : _root_.Array Tok}
    {buf : _root_.Array Nat} {ub : Nat} {i' b' : Nat} {re' : _root_.Array Tok}
    {buf' : _root_.Array Nat} (h : (rd P i).1 ≠ 0 ∧ j + 1 < 30)
    (hs : (compStep P i j b re buf (rd P i).1).1 = some (i', b', re', buf'))
    (hci : (rd P i').1 ≠ 0) :
    ∃ ub', (compLoop P i j b re buf ub).1 = (compLoop P (i' + 1) (j + 1) b' re' buf' ub').1 := by
  rw [compLoop]
  rcases hr : rd P i with ⟨c, u⟩
  have e : (rd P i).1 = c := by rw [hr]
  rw [e] at h hs
  have h' : c ≠ 0 ∧ j + 1 < MAXOBJ := h
  dsimp only
  rw [dite_eq_left h']
  rcases hc : compStep P i j b re buf c with ⟨_ | ⟨i2, b2, re2, buf2⟩, u'⟩
  · rw [hc] at hs
    exact absurd hs (by simp)
  · rw [hc] at hs
    simp only [Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hs
    dsimp only
    rw [ite_eq_right (by simp [hci])]
    exact ⟨_, rfl⟩

/-- The metacharacters `^ $ . * + ?`: the entry's type. -/
theorem compStep_meta (P : _root_.Array Nat) (i j b : Nat) (re : _root_.Array Tok)
    (buf : _root_.Array Nat) (c K : Nat)
    (hK : (c = 94 ∧ K = 2) ∨ (c = 36 ∧ K = 3) ∨ (c = 46 ∧ K = 1) ∨ (c = 42 ∧ K = 5) ∨
      (c = 43 ∧ K = 6) ∨ (c = 63 ∧ K = 4)) :
    (compStep P i j b re buf c).1 = some (i, b, re.set! j { re[j]! with type := K }, buf) := by
  rcases hK with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simp [compStep, BEGIN, END, DOT, STAR, PLUS, QUESTIONMARK]

/-- Any other character: a `CHAR` entry. -/
theorem compStep_char (P : _root_.Array Nat) (i j b : Nat) (re : _root_.Array Tok)
    (buf : _root_.Array Nat) (c : Nat) (h94 : c ≠ 94) (h36 : c ≠ 36) (h46 : c ≠ 46) (h42 : c ≠ 42)
    (h43 : c ≠ 43) (h63 : c ≠ 63) (h92 : c ≠ 92) (h91 : c ≠ 91) :
    (compStep P i j b re buf c).1 =
      some (i, b, re.set! j { re[j]! with type := 7, ch := c }, buf) := by
  simp [compStep, h94, h36, h46, h42, h43, h63, h92, h91, CHAR]

/-- `\`: the escaped character (none at the end of the pattern). -/
theorem compStep_esc (P : _root_.Array Nat) (i j b : Nat) (re : _root_.Array Tok)
    (buf : _root_.Array Nat) :
    (compStep P i j b re buf 92).1 =
      if (rd P (i + 1)).1 ≠ 0 then
        some (i + 1, b,
          if (rd P (i + 1)).1 = 100 then re.set! j { re[j]! with type := 10 }
          else if (rd P (i + 1)).1 = 68 then re.set! j { re[j]! with type := 11 }
          else if (rd P (i + 1)).1 = 119 then re.set! j { re[j]! with type := 12 }
          else if (rd P (i + 1)).1 = 87 then re.set! j { re[j]! with type := 13 }
          else if (rd P (i + 1)).1 = 115 then re.set! j { re[j]! with type := 14 }
          else if (rd P (i + 1)).1 = 83 then re.set! j { re[j]! with type := 15 }
          else re.set! j { re[j]! with type := 7, ch := (rd P (i + 1)).1 }, buf)
      else some (i, b, re, buf) := by
  unfold compStep
  rcases hr : rd P (i + 1) with ⟨c1, u⟩
  by_cases h0 : c1 = 0
  · simp [h0]
  · simp [h0, DIGIT, NOT_DIGIT, ALPHA, NOT_ALPHA, WHITESPACE, NOT_WHITESPACE, CHAR]

/-- The finalized class copy inside `compStep` (`[`, `[^`). -/
theorem cclCopy_match_fst (P : _root_.Array Nat) (i b : Nat) (buf : _root_.Array Nat)
    (re : _root_.Array Tok) (j begin u1 : Nat) :
    (match cclCopy P i b buf with
      | (none, u3) => ((none : Option (Nat × Nat × _root_.Array Tok × _root_.Array Nat)), u1 ||| u3)
      | (some (i, bidx, buf), u3) =>
        if bidx ≥ MAXCCL then (none, u1 ||| u3)
        else (some (i, bidx + 1, re.set! j { re[j]! with ccl := begin }, buf.set! bidx 0),
          u1 ||| u3)).1 =
      match cclFin P i b buf with
      | none => none
      | some (i', b', B') => some (i', b', re.set! j { re[j]! with ccl := begin }, B') := by
  unfold cclFin
  rcases cclCopy P i b buf with ⟨_ | ⟨i', b', B'⟩, u3⟩
  · rfl
  · simp only [MAXCCL, ge_iff_le]
    split_ifs <;> rfl

/-- `[`: a class (`[^`: an inverted class). -/
theorem compStep_cls (P : _root_.Array Nat) (i j b : Nat) (re : _root_.Array Tok)
    (buf : _root_.Array Nat) :
    (compStep P i j b re buf 91).1 =
      if (rd P (i + 1)).1 = 94 then
        if (rd P (i + 2)).1 = 0 then none
        else match cclFin P (i + 1) b buf with
          | none => none
          | some (i', b', B') =>
            some (i', b', (re.set! j { re[j]! with type := 9 }).set! j
              { (re.set! j { re[j]! with type := 9 })[j]! with ccl := b }, B')
      else match cclFin P i b buf with
        | none => none
        | some (i', b', B') =>
          some (i', b', (re.set! j { re[j]! with type := 8 }).set! j
            { (re.set! j { re[j]! with type := 8 })[j]! with ccl := b }, B') := by
  unfold compStep
  simp only [show (91 == 94) = false from rfl, show (91 == 36) = false from rfl,
    show (91 == 46) = false from rfl, show (91 == 42) = false from rfl,
    show (91 == 43) = false from rfl, show (91 == 63) = false from rfl,
    show (91 == 92) = false from rfl, show (91 == 91) = true from rfl, Bool.false_eq_true,
    _root_.ite_false, _root_.ite_true, INV_CHAR_CLASS, CHAR_CLASS]
  rcases hr : rd P (i + 1) with ⟨c1, u1⟩
  simp only []
  by_cases h94 : c1 = 94
  · subst h94
    simp only [beq_self_eq_true, _root_.ite_true]
    rcases hr2 : rd P (i + 2) with ⟨c2, u2⟩
    by_cases h0 : c2 = 0
    · subst h0
      simp
    · simp only [h0, beq_iff_eq, _root_.ite_false]
      exact cclCopy_match_fst _ _ _ _ _ _ _ _
  · simp only [h94, beq_iff_eq, _root_.ite_false]
    exact cclCopy_match_fst _ _ _ _ _ _ _ _

/-! ## The Rust entries -/

@[simp] theorem UNUSED_val : tiny_regex.UNUSED.val = 0 := by simp [tiny_regex.UNUSED]
@[simp] theorem DOT_val : tiny_regex.DOT.val = 1 := by simp [tiny_regex.DOT]
@[simp] theorem BEGIN_val : tiny_regex.BEGIN.val = 2 := by simp [tiny_regex.BEGIN]
@[simp] theorem END_val : tiny_regex.END.val = 3 := by simp [tiny_regex.END]
@[simp] theorem QUESTIONMARK_val : tiny_regex.QUESTIONMARK.val = 4 := by
  simp [tiny_regex.QUESTIONMARK]
@[simp] theorem STAR_val : tiny_regex.STAR.val = 5 := by simp [tiny_regex.STAR]
@[simp] theorem PLUS_val : tiny_regex.PLUS.val = 6 := by simp [tiny_regex.PLUS]
@[simp] theorem CHAR_val : tiny_regex.CHAR.val = 7 := by simp [tiny_regex.CHAR]
@[simp] theorem CHAR_CLASS_val : tiny_regex.CHAR_CLASS.val = 8 := by simp [tiny_regex.CHAR_CLASS]
@[simp] theorem INV_CHAR_CLASS_val : tiny_regex.INV_CHAR_CLASS.val = 9 := by
  simp [tiny_regex.INV_CHAR_CLASS]
@[simp] theorem DIGIT_val : tiny_regex.DIGIT.val = 10 := by simp [tiny_regex.DIGIT]
@[simp] theorem NOT_DIGIT_val : tiny_regex.NOT_DIGIT.val = 11 := by simp [tiny_regex.NOT_DIGIT]
@[simp] theorem ALPHA_val : tiny_regex.ALPHA.val = 12 := by simp [tiny_regex.ALPHA]
@[simp] theorem NOT_ALPHA_val : tiny_regex.NOT_ALPHA.val = 13 := by simp [tiny_regex.NOT_ALPHA]
@[simp] theorem WHITESPACE_val : tiny_regex.WHITESPACE.val = 14 := by simp [tiny_regex.WHITESPACE]
@[simp] theorem NOT_WHITESPACE_val : tiny_regex.NOT_WHITESPACE.val = 15 := by
  simp [tiny_regex.NOT_WHITESPACE]

/-- `&mut a[i]` for an array (read the element, write it back). -/
theorem array_index_mut_usize_eq {α : Type _} {n : Usize} (a : Std.Array α n) (i : Usize) :
    Std.Array.index_mut_usize a i =
      if h : i.val < a.val.length then .ok (a.val[i.val], Std.Array.set a i)
      else .fail .arrayOutOfBounds := by
  unfold Std.Array.index_mut_usize
  rw [array_index_usize_eq]
  split <;> simp

/-- `a[i] = x` for an array, as Aeneas' `set`. -/
theorem array_update_eq' {α : Type _} {n : Usize} (a : Std.Array α n) (i : Usize) (x : α) :
    Std.Array.update a i x =
      if i.val < a.val.length then .ok (a.set i x) else .fail .arrayOutOfBounds := by
  rw [array_update_eq]
  split <;> simp_all [Std.Array.set]

/-- The entry `obj` reads past the end. -/
abbrev obj0 : tiny_regex.RegexObj := ⟨0#u8, 0#u8, 0#usize⟩

theorem sent_set (a : Std.Array tiny_regex.RegexObj 30#usize) (j : Usize)
    (x : tiny_regex.RegexObj) (hsent : ∀ k, j.val < k → (a.val.getD k obj0).kind.val = 0) :
    ∀ k, j.val + 1 < k → ((a.set j x).val.getD k obj0).kind.val = 0 := by
  intro k hk
  rw [Aeneas.Std.Array.set_val_eq, List.getD_eq_getElem?_getD, List.getElem?_set_ne (by omega),
    ← List.getD_eq_getElem?_getD]
  exact hsent k (by omega)

theorem absP_set_kind (a : Std.Array tiny_regex.RegexObj 30#usize) (j : Usize)
    (hj : j.val < a.val.length) (k : U8) :
    absP (a.set j { a.val[j.val] with kind := k }) =
      (absP a).set! j.val { (absP a)[j.val]! with type := k.val } := by
  rw [absP_set, absP_get _ _ hj]
  rfl

theorem absP_set_kind_ch (a : Std.Array tiny_regex.RegexObj 30#usize) (j : Usize)
    (hj : j.val < a.val.length) (k c : U8) :
    absP (a.set j { a.val[j.val] with kind := k, ch := c }) =
      (absP a).set! j.val { (absP a)[j.val]! with type := k.val, ch := c.val } := by
  rw [absP_set, absP_get _ _ hj]
  rfl

theorem absP_set_self (a : Std.Array tiny_regex.RegexObj 30#usize) (j : Usize)
    (hj : j.val < a.val.length) : absP (a.set j a.val[j.val]) = absP a := by
  simp only [absP, Aeneas.Std.Array.set_val_eq, List.set_getElem_self]

theorem absP_set_cls (a : Std.Array tiny_regex.RegexObj 30#usize) (j : Usize)
    (hj : j.val < a.val.length) (k : U8) (c : Usize) :
    absP (a.set j { a.val[j.val] with kind := k, ccl := c }) =
      ((absP a).set! j.val { (absP a)[j.val]! with type := k.val }).set! j.val
        { ((absP a).set! j.val { (absP a)[j.val]! with type := k.val })[j.val]! with
          ccl := c.val } := by
  have hjP : j.val < (absP a).size := by rw [absP_size]; simpa using hj
  rw [get!_set!_self _ _ _ hjP, set!_set!_self, absP_set, absP_get _ _ hj]
  rfl

theorem rd_fst_of_ge {P : _root_.Array Nat} {i : Nat} (h : P.size ≤ i) : (rd P i).1 = 0 := by
  unfold rd
  split_ifs <;> omega

/-! ## The compile loop -/

/-- `re_compile`'s result against the model's `T`: `none` for `none`, the model's arrays
otherwise, with the `UNUSED` entry at index 29. -/
def CompOk (T : Option (_root_.Array Tok × _root_.Array Nat))
    (o : Except Error (Option tiny_regex.Regex)) : Prop :=
  ∃ r, o = .ok r ∧ r.map absRe = T ∧ ∀ re, r = some re → WF re

/-- The loop invariant: the pattern index is at most the length, `j` is an index, the entries
after `j` are `UNUSED`, and the model's loop from here gives `T`. -/
def LoopInv (s : Slice U8) (T : Option (_root_.Array Tok × _root_.Array Nat))
    (st : Std.Array tiny_regex.RegexObj 30#usize × Std.Array U8 40#usize × Usize × Usize ×
      Usize) : Prop :=
  st.2.2.2.1.val ≤ s.val.length ∧ st.2.2.2.2.val < 30 ∧
    (∀ k, st.2.2.2.2.val < k → (st.1.val.getD k obj0).kind.val = 0) ∧
    ∃ ub, (compLoop (pat s) st.2.2.2.1.val st.2.2.2.2.val st.2.2.1.val (absP st.1) (absB st.2.1)
      ub).1 = T

theorem ne_of_val {c v : U8} {n : Nat} (hv : v.val = n) (h : c = v → False) : c.val ≠ n :=
  fun h' => h (UScalar.eq_of_val_eq (h'.trans hv.symm))

theorem rd_of_atv {s : Slice U8} {x : Usize} {v : U8} {n m : Nat} (h : v = atv s x)
    (hv : v.val = n) (hx : x.val = m) : (rd (pat s) m).1 = n := by
  rw [← hx, ← atv_val, ← h, hv]

/-- The end of the loop: the `UNUSED` entry at `j`. -/
theorem sentinel_ok (s : Slice U8) (a : Std.Array tiny_regex.RegexObj 30#usize)
    (a1 : Std.Array U8 40#usize) (bufidx i j : Usize) (ub : Nat) (hj : j.val < a.val.length)
    (hsent : ∀ k, j.val < k → (a.val.getD k obj0).kind.val = 0)
    (hend : ¬ ((rd (pat s) i.val).1 ≠ 0 ∧ j.val + 1 < 30)) :
    CompOk (compLoop (pat s) i.val j.val bufidx.val (absP a) (absB a1) ub).1
      (.ok (some ⟨a.set j { a.val[j.val] with kind := tiny_regex.UNUSED }, a1⟩)) := by
  refine ⟨_, rfl, ?_, ?_⟩
  · rw [compLoop_fst_end hend]
    simp only [Option.map_some, absRe, Option.some.injEq, Prod.mk.injEq, and_true]
    rw [absP_set_kind _ _ hj]
    simp
  · intro re hre
    simp only [Option.some.injEq] at hre
    subst hre
    unfold WF
    simp only [Aeneas.Std.Array.set_val_eq]
    have hl : a.val.length = 30 := by simp
    by_cases hj29 : j.val = 29
    · rw [List.getD_eq_getElem?_getD, List.getElem?_set]
      simp [hj29, hl]
    · rw [List.getD_eq_getElem?_getD, List.getElem?_set_ne (by omega),
        ← List.getD_eq_getElem?_getD]
      exact hsent 29 (by omega)

set_option maxHeartbeats 8000000 in
theorem re_compile_loop_spec (s : Slice U8) (a : Std.Array tiny_regex.RegexObj 30#usize)
    (a1 : Std.Array U8 40#usize) (bufidx i j : Usize)
    (T : Option (_root_.Array Tok × _root_.Array Nat)) (h : LoopInv s T (a, a1, bufidx, i, j)) :
    wp (tiny_regex.re_compile_loop s a a1 bufidx i j) (CompOk T) := by
  unfold tiny_regex.re_compile_loop
  refine wp_loop (loop_shape _) (LoopInv s T) (fun st => 30 - st.2.2.2.2.val) ?_ _ h
  simp only [Prod.forall]
  intro a a1 bufidx i j hinv
  obtain ⟨hi, hj, hsent, ub, hT⟩ := hinv
  dsimp only at hi hj hsent hT
  subst hT
  have hsl : s.val.length ≤ Usize.max := s.property
  have hlen : a.val.length = 30 := by simp
  have hlen1 : a1.val.length = 40 := by simp
  have hjl : j.val < a.val.length := by omega
  simp only [tiny_regex.re_compile_loop.body]
  by_cases hlt : i.val < s.val.length
  swap
  · have hend : ¬ ((rd (pat s) i.val).1 ≠ 0 ∧ j.val + 1 < 30) := by
      rw [rd_fst_of_ge (by rw [pat_size]; omega)]
      simp
    aeneas_wp [array_index_usize_eq, array_update_eq', hlt, hjl, loopCls_done, loopCls_cont,
      loopCls_error]
    exact sentinel_ok s a a1 bufidx i j ub hjl hsent hend
  by_cases hz : (rd (pat s) i.val).1 = 0
  · have hend : ¬ ((rd (pat s) i.val).1 ≠ 0 ∧ j.val + 1 < 30) := by simp [hz]
    aeneas_wp [wp_at, atv_val, hz, array_index_usize_eq, array_update_eq', hlt, hjl, loopCls_done,
      loopCls_cont, loopCls_error]
    exact sentinel_ok s a a1 bufidx i j ub hjl hsent hend
  by_cases hjj : j.val + 1 < 30
  swap
  · have hend : ¬ ((rd (pat s) i.val).1 ≠ 0 ∧ j.val + 1 < 30) := by simp [hjj]
    have hovj : j.val + 1 ≤ Usize.max := by scalar_tac
    aeneas_wp [wp_at, atv_val, hz, array_index_usize_eq, array_update_eq', hlt, hjl, hjj, hovj,
      tiny_regex.MAX_REGEXP_OBJECTS, loopCls_done, loopCls_cont, loopCls_error]
    exact sentinel_ok s a a1 bufidx i j ub hjl hsent hend
  have hov : i.val + 1 ≤ Usize.max := by omega
  have hovj : j.val + 1 ≤ Usize.max := by scalar_tac
  aeneas_wp [wp_at, atv_val, hz, array_index_usize_eq, hlt, hjl, hjj, hovj,
    tiny_regex.MAX_REGEXP_OBJECTS, not_false_eq_true]
  generalize hcv : atv s i = c
  split
  · -- `^`
    have hc : (rd (pat s) i.val).1 = 94 := by rw [← atv_val, hcv]; rfl
    aeneas_wp [array_index_mut_usize_eq, hjl, hov, loopCls_cont]
    simp only [LoopInv, UScalar.ofNatCore_val_eq]
    refine ⟨⟨by omega, hjj, sent_set a j _ hsent, ?_⟩, by omega⟩
    obtain ⟨ub', hub'⟩ := compLoop_fst_step (ub := ub) ⟨hz, hjj⟩
      (compStep_meta _ _ _ _ _ _ _ 2 (by simp [hc])) hz
    refine ⟨ub', ?_⟩
    rw [hub', absP_set_kind _ _ hjl, BEGIN_val]
  · -- `$`
    have hc : (rd (pat s) i.val).1 = 36 := by rw [← atv_val, hcv]; rfl
    aeneas_wp [array_index_mut_usize_eq, hjl, hov, loopCls_cont]
    simp only [LoopInv, UScalar.ofNatCore_val_eq]
    refine ⟨⟨by omega, hjj, sent_set a j _ hsent, ?_⟩, by omega⟩
    obtain ⟨ub', hub'⟩ := compLoop_fst_step (ub := ub) ⟨hz, hjj⟩
      (compStep_meta _ _ _ _ _ _ _ 3 (by simp [hc])) hz
    refine ⟨ub', ?_⟩
    rw [hub', absP_set_kind _ _ hjl, END_val]
  · -- `.`
    have hc : (rd (pat s) i.val).1 = 46 := by rw [← atv_val, hcv]; rfl
    aeneas_wp [array_index_mut_usize_eq, hjl, hov, loopCls_cont]
    simp only [LoopInv, UScalar.ofNatCore_val_eq]
    refine ⟨⟨by omega, hjj, sent_set a j _ hsent, ?_⟩, by omega⟩
    obtain ⟨ub', hub'⟩ := compLoop_fst_step (ub := ub) ⟨hz, hjj⟩
      (compStep_meta _ _ _ _ _ _ _ 1 (by simp [hc])) hz
    refine ⟨ub', ?_⟩
    rw [hub', absP_set_kind _ _ hjl, DOT_val]
  · -- `*`
    have hc : (rd (pat s) i.val).1 = 42 := by rw [← atv_val, hcv]; rfl
    aeneas_wp [array_index_mut_usize_eq, hjl, hov, loopCls_cont]
    simp only [LoopInv, UScalar.ofNatCore_val_eq]
    refine ⟨⟨by omega, hjj, sent_set a j _ hsent, ?_⟩, by omega⟩
    obtain ⟨ub', hub'⟩ := compLoop_fst_step (ub := ub) ⟨hz, hjj⟩
      (compStep_meta _ _ _ _ _ _ _ 5 (by simp [hc])) hz
    refine ⟨ub', ?_⟩
    rw [hub', absP_set_kind _ _ hjl, STAR_val]
  · -- `+`
    have hc : (rd (pat s) i.val).1 = 43 := by rw [← atv_val, hcv]; rfl
    aeneas_wp [array_index_mut_usize_eq, hjl, hov, loopCls_cont]
    simp only [LoopInv, UScalar.ofNatCore_val_eq]
    refine ⟨⟨by omega, hjj, sent_set a j _ hsent, ?_⟩, by omega⟩
    obtain ⟨ub', hub'⟩ := compLoop_fst_step (ub := ub) ⟨hz, hjj⟩
      (compStep_meta _ _ _ _ _ _ _ 6 (by simp [hc])) hz
    refine ⟨ub', ?_⟩
    rw [hub', absP_set_kind _ _ hjl, PLUS_val]
  · -- `?`
    have hc : (rd (pat s) i.val).1 = 63 := by rw [← atv_val, hcv]; rfl
    aeneas_wp [array_index_mut_usize_eq, hjl, hov, loopCls_cont]
    simp only [LoopInv, UScalar.ofNatCore_val_eq]
    refine ⟨⟨by omega, hjj, sent_set a j _ hsent, ?_⟩, by omega⟩
    obtain ⟨ub', hub'⟩ := compLoop_fst_step (ub := ub) ⟨hz, hjj⟩
      (compStep_meta _ _ _ _ _ _ _ 4 (by simp [hc])) hz
    refine ⟨ub', ?_⟩
    rw [hub', absP_set_kind _ _ hjl, QUESTIONMARK_val]
  · -- `\\`
    have hc : (rd (pat s) i.val).1 = 92 := by rw [← atv_val, hcv]; rfl
    aeneas_wp [wp_at, atv_val, hov, hz, array_index_mut_usize_eq, hjl, loopCls_cont, loopCls_done]
    by_cases he : (rd (pat s) (i.val + 1)).1 = 0
    · -- `\\` at the end: the entry is left as it was
      simp only [he, not_true_eq_false, _root_.ite_false, LoopInv, UScalar.ofNatCore_val_eq]
      refine ⟨⟨by omega, hjj, sent_set a j _ hsent, ?_⟩, by omega⟩
      have hs : (compStep (pat s) i.val j.val bufidx.val (absP a) (absB a1)
          (rd (pat s) i.val).1).1 = some (i.val, bufidx.val, absP a, absB a1) := by
        rw [hc, compStep_esc]
        simp [he]
      obtain ⟨ub', hub'⟩ := compLoop_fst_step (ub := ub) ⟨hz, hjj⟩ hs hz
      refine ⟨ub', ?_⟩
      rw [hub', absP_set_self _ _ hjl]
    simp only [he, not_false_eq_true, _root_.ite_true]
    have hi1 : i.val + 1 < s.val.length := by
      have := rd_pos he
      rwa [pat_size] at this
    have hov2 : i.val + 1 + 1 ≤ Usize.max := by omega
    have hx : (UScalar.ofNatCore (i.val + 1) (by scalar_tac) : Usize).val = i.val + 1 := by simp
    set e := atv s (UScalar.ofNatCore (i.val + 1) (by scalar_tac)) with hev
    clear_value e
    split
    · have hc1 : (rd (pat s) (i.val + 1)).1 = 100 := rd_of_atv hev rfl hx
      aeneas_wp [wp_at, atv_val, he, hov2, loopCls_cont]
      simp only [LoopInv, UScalar.ofNatCore_val_eq]
      refine ⟨⟨by omega, hjj, sent_set a j _ hsent, ?_⟩, by omega⟩
      have hs : (compStep (pat s) i.val j.val bufidx.val (absP a) (absB a1)
          (rd (pat s) i.val).1).1 = some (i.val + 1, bufidx.val,
            (absP a).set! j.val { (absP a)[j.val]! with type := 10 }, absB a1) := by
        rw [hc, compStep_esc]
        simp [hc1]
      obtain ⟨ub', hub'⟩ := compLoop_fst_step (ub := ub) ⟨hz, hjj⟩ hs he
      refine ⟨ub', ?_⟩
      rw [hub', absP_set_kind _ _ hjl, DIGIT_val]
    · have hc1 : (rd (pat s) (i.val + 1)).1 = 68 := rd_of_atv hev rfl hx
      aeneas_wp [wp_at, atv_val, he, hov2, loopCls_cont]
      simp only [LoopInv, UScalar.ofNatCore_val_eq]
      refine ⟨⟨by omega, hjj, sent_set a j _ hsent, ?_⟩, by omega⟩
      have hs : (compStep (pat s) i.val j.val bufidx.val (absP a) (absB a1)
          (rd (pat s) i.val).1).1 = some (i.val + 1, bufidx.val,
            (absP a).set! j.val { (absP a)[j.val]! with type := 11 }, absB a1) := by
        rw [hc, compStep_esc]
        simp [hc1]
      obtain ⟨ub', hub'⟩ := compLoop_fst_step (ub := ub) ⟨hz, hjj⟩ hs he
      refine ⟨ub', ?_⟩
      rw [hub', absP_set_kind _ _ hjl, NOT_DIGIT_val]
    · have hc1 : (rd (pat s) (i.val + 1)).1 = 119 := rd_of_atv hev rfl hx
      aeneas_wp [wp_at, atv_val, he, hov2, loopCls_cont]
      simp only [LoopInv, UScalar.ofNatCore_val_eq]
      refine ⟨⟨by omega, hjj, sent_set a j _ hsent, ?_⟩, by omega⟩
      have hs : (compStep (pat s) i.val j.val bufidx.val (absP a) (absB a1)
          (rd (pat s) i.val).1).1 = some (i.val + 1, bufidx.val,
            (absP a).set! j.val { (absP a)[j.val]! with type := 12 }, absB a1) := by
        rw [hc, compStep_esc]
        simp [hc1]
      obtain ⟨ub', hub'⟩ := compLoop_fst_step (ub := ub) ⟨hz, hjj⟩ hs he
      refine ⟨ub', ?_⟩
      rw [hub', absP_set_kind _ _ hjl, ALPHA_val]
    · have hc1 : (rd (pat s) (i.val + 1)).1 = 87 := rd_of_atv hev rfl hx
      aeneas_wp [wp_at, atv_val, he, hov2, loopCls_cont]
      simp only [LoopInv, UScalar.ofNatCore_val_eq]
      refine ⟨⟨by omega, hjj, sent_set a j _ hsent, ?_⟩, by omega⟩
      have hs : (compStep (pat s) i.val j.val bufidx.val (absP a) (absB a1)
          (rd (pat s) i.val).1).1 = some (i.val + 1, bufidx.val,
            (absP a).set! j.val { (absP a)[j.val]! with type := 13 }, absB a1) := by
        rw [hc, compStep_esc]
        simp [hc1]
      obtain ⟨ub', hub'⟩ := compLoop_fst_step (ub := ub) ⟨hz, hjj⟩ hs he
      refine ⟨ub', ?_⟩
      rw [hub', absP_set_kind _ _ hjl, NOT_ALPHA_val]
    · have hc1 : (rd (pat s) (i.val + 1)).1 = 115 := rd_of_atv hev rfl hx
      aeneas_wp [wp_at, atv_val, he, hov2, loopCls_cont]
      simp only [LoopInv, UScalar.ofNatCore_val_eq]
      refine ⟨⟨by omega, hjj, sent_set a j _ hsent, ?_⟩, by omega⟩
      have hs : (compStep (pat s) i.val j.val bufidx.val (absP a) (absB a1)
          (rd (pat s) i.val).1).1 = some (i.val + 1, bufidx.val,
            (absP a).set! j.val { (absP a)[j.val]! with type := 14 }, absB a1) := by
        rw [hc, compStep_esc]
        simp [hc1]
      obtain ⟨ub', hub'⟩ := compLoop_fst_step (ub := ub) ⟨hz, hjj⟩ hs he
      refine ⟨ub', ?_⟩
      rw [hub', absP_set_kind _ _ hjl, WHITESPACE_val]
    · have hc1 : (rd (pat s) (i.val + 1)).1 = 83 := rd_of_atv hev rfl hx
      aeneas_wp [wp_at, atv_val, he, hov2, loopCls_cont]
      simp only [LoopInv, UScalar.ofNatCore_val_eq]
      refine ⟨⟨by omega, hjj, sent_set a j _ hsent, ?_⟩, by omega⟩
      have hs : (compStep (pat s) i.val j.val bufidx.val (absP a) (absB a1)
          (rd (pat s) i.val).1).1 = some (i.val + 1, bufidx.val,
            (absP a).set! j.val { (absP a)[j.val]! with type := 15 }, absB a1) := by
        rw [hc, compStep_esc]
        simp [hc1]
      obtain ⟨ub', hub'⟩ := compLoop_fst_step (ub := ub) ⟨hz, hjj⟩ hs he
      refine ⟨ub', ?_⟩
      rw [hub', absP_set_kind _ _ hjl, NOT_WHITESPACE_val]
    · rename_i _ x100 x68 x119 x87 x115 x83
      have hce : (rd (pat s) (i.val + 1)).1 = e.val := rd_of_atv hev rfl hx
      have n100 := ne_of_val (n := 100) rfl x100
      have n68 := ne_of_val (n := 68) rfl x68
      have n119 := ne_of_val (n := 119) rfl x119
      have n87 := ne_of_val (n := 87) rfl x87
      have n115 := ne_of_val (n := 115) rfl x115
      have n83 := ne_of_val (n := 83) rfl x83
      rw [← hce] at n100 n68 n119 n87 n115 n83
      aeneas_wp [wp_at, atv_val, he, hov2, loopCls_cont]
      simp only [LoopInv, UScalar.ofNatCore_val_eq]
      refine ⟨⟨by omega, hjj, sent_set a j _ hsent, ?_⟩, by omega⟩
      have hs : (compStep (pat s) i.val j.val bufidx.val (absP a) (absB a1)
          (rd (pat s) i.val).1).1 = some (i.val + 1, bufidx.val,
            (absP a).set! j.val { (absP a)[j.val]! with type := 7, ch := (rd (pat s) (i.val + 1)).1 },
            absB a1) := by
        rw [hc, compStep_esc]
        simp [he, n100, n68, n119, n87, n115, n83]
      obtain ⟨ub', hub'⟩ := compLoop_fst_step (ub := ub) ⟨hz, hjj⟩ hs he
      refine ⟨ub', ?_⟩
      rw [hub', absP_set_kind_ch _ _ hjl, CHAR_val, hce]
  · -- `[`
    have hc : (rd (pat s) i.val).1 = 91 := by rw [← atv_val, hcv]; rfl
    aeneas_wp [wp_at, atv_val, hov, array_index_mut_usize_eq, hjl, loopCls_cont, loopCls_done]
    by_cases h94 : (rd (pat s) (i.val + 1)).1 = 94
    · -- `[^`
      have hi1 : i.val + 1 < s.val.length := by
        have := rd_pos (P := pat s) (i := i.val + 1) (by rw [h94]; decide)
        rwa [pat_size] at this
      have hov2 : i.val + 1 + 1 ≤ Usize.max := by omega
      simp only [h94, _root_.ite_true, hov2, _root_.dite_true]
      by_cases h2 : (rd (pat s) (i.val + 1 + 1)).1 = 0
      · have h2' : (rd (pat s) (i.val + 2)).1 = 0 := h2
        simp only [h2, _root_.ite_true]
        have hs : (compStep (pat s) i.val j.val bufidx.val (absP a) (absB a1)
            (rd (pat s) i.val).1).1 = none := by
          rw [hc, compStep_cls]
          simp [h94, h2']
        exact ⟨none, rfl, (compLoop_fst_none ⟨hz, hjj⟩ hs).symm, by simp⟩
      have h2' : ¬ (rd (pat s) (i.val + 2)).1 = 0 := h2
      simp only [h2, _root_.ite_false]
      refine wp_mono (compile_class_loop_spec s a1 _ bufidx (by simpa using hi1)) ?_
      rintro o ⟨⟨o1, a2⟩, rfl, hr⟩
      simp only [UScalar.ofNatCore_val_eq] at hr
      rcases hcf : cclFin (pat s) (i.val + 1) bufidx.val (absB a1) with _ | ⟨i', b', B'⟩
      · rw [hcf] at hr
        simp only [CclOk] at hr
        subst hr
        aeneas_wp [loopCls_done]
        have hs : (compStep (pat s) i.val j.val bufidx.val (absP a) (absB a1)
            (rd (pat s) i.val).1).1 = none := by
          rw [hc, compStep_cls]
          simp [h94, h2', hcf]
        exact ⟨none, rfl, (compLoop_fst_none ⟨hz, hjj⟩ hs).symm, by simp⟩
      · rw [hcf] at hr
        obtain ⟨i2, b2, ho1, hi2, hb2, hB⟩ := hr
        simp only at ho1 hB
        subst ho1
        have hs : (compStep (pat s) i.val j.val bufidx.val (absP a) (absB a1)
            (rd (pat s) i.val).1).1 = some (i', b',
              ((absP a).set! j.val { (absP a)[j.val]! with type := 9 }).set! j.val
                { ((absP a).set! j.val { (absP a)[j.val]! with type := 9 })[j.val]! with
                  ccl := bufidx.val }, B') := by
          rw [hc, compStep_cls]
          simp [h94, h2', hcf]
        aeneas_wp [wp_at, atv_val, hi2, array_index_mut_usize_eq, hjl, loopCls_cont, loopCls_done]
        by_cases h3 : (rd (pat s) i').1 = 0
        · simp only [h3, _root_.ite_true]
          exact ⟨none, rfl, (compLoop_fst_none2 ⟨hz, hjj⟩ hs h3).symm, by simp⟩
        · have hi3 : i' < s.val.length := by
            have := rd_pos h3
            rwa [pat_size] at this
          have hov3 : i' + 1 ≤ Usize.max := by omega
          simp only [h3, _root_.ite_false, hov3, _root_.dite_true, LoopInv,
            UScalar.ofNatCore_val_eq]
          refine ⟨⟨by omega, hjj, sent_set a j _ hsent, ?_⟩, by omega⟩
          obtain ⟨ub', hub'⟩ := compLoop_fst_step (ub := ub) ⟨hz, hjj⟩ hs h3
          refine ⟨ub', ?_⟩
          rw [hub', absP_set_cls _ _ hjl, INV_CHAR_CLASS_val, hB, hb2]
    · -- `[` without `^`
      simp only [h94, _root_.ite_false]
      refine wp_mono (compile_class_loop_spec s a1 i bufidx hlt) ?_
      rintro o ⟨⟨o1, a2⟩, rfl, hr⟩
      rcases hcf : cclFin (pat s) i.val bufidx.val (absB a1) with _ | ⟨i', b', B'⟩
      · rw [hcf] at hr
        simp only [CclOk] at hr
        subst hr
        aeneas_wp [loopCls_done]
        have hs : (compStep (pat s) i.val j.val bufidx.val (absP a) (absB a1)
            (rd (pat s) i.val).1).1 = none := by
          rw [hc, compStep_cls]
          simp [h94, hcf]
        exact ⟨none, rfl, (compLoop_fst_none ⟨hz, hjj⟩ hs).symm, by simp⟩
      · rw [hcf] at hr
        obtain ⟨i2, b2, ho1, hi2, hb2, hB⟩ := hr
        simp only at ho1 hB
        subst ho1
        have hs : (compStep (pat s) i.val j.val bufidx.val (absP a) (absB a1)
            (rd (pat s) i.val).1).1 = some (i', b',
              ((absP a).set! j.val { (absP a)[j.val]! with type := 8 }).set! j.val
                { ((absP a).set! j.val { (absP a)[j.val]! with type := 8 })[j.val]! with
                  ccl := bufidx.val }, B') := by
          rw [hc, compStep_cls]
          simp [h94, hcf]
        aeneas_wp [wp_at, atv_val, hi2, array_index_mut_usize_eq, hjl, loopCls_cont, loopCls_done]
        by_cases h3 : (rd (pat s) i').1 = 0
        · simp only [h3, _root_.ite_true]
          exact ⟨none, rfl, (compLoop_fst_none2 ⟨hz, hjj⟩ hs h3).symm, by simp⟩
        · have hi3 : i' < s.val.length := by
            have := rd_pos h3
            rwa [pat_size] at this
          have hov3 : i' + 1 ≤ Usize.max := by omega
          simp only [h3, _root_.ite_false, hov3, _root_.dite_true, LoopInv,
            UScalar.ofNatCore_val_eq]
          refine ⟨⟨by omega, hjj, sent_set a j _ hsent, ?_⟩, by omega⟩
          obtain ⟨ub', hub'⟩ := compLoop_fst_step (ub := ub) ⟨hz, hjj⟩ hs h3
          refine ⟨ub', ?_⟩
          rw [hub', absP_set_cls _ _ hjl, CHAR_CLASS_val, hB, hb2]
  · -- any other character
    rename_i _ x94 x36 x46 x42 x43 x63 x92 x91
    have hcc : (rd (pat s) i.val).1 = c.val := by rw [← atv_val, hcv]
    have n94 := ne_of_val (n := 94) rfl x94
    have n36 := ne_of_val (n := 36) rfl x36
    have n46 := ne_of_val (n := 46) rfl x46
    have n42 := ne_of_val (n := 42) rfl x42
    have n43 := ne_of_val (n := 43) rfl x43
    have n63 := ne_of_val (n := 63) rfl x63
    have n92 := ne_of_val (n := 92) rfl x92
    have n91 := ne_of_val (n := 91) rfl x91
    rw [← hcc] at n94 n36 n46 n42 n43 n63 n92 n91
    aeneas_wp [array_index_mut_usize_eq, hjl, hov, loopCls_cont]
    simp only [LoopInv, UScalar.ofNatCore_val_eq]
    refine ⟨⟨by omega, hjj, sent_set a j _ hsent, ?_⟩, by omega⟩
    obtain ⟨ub', hub'⟩ := compLoop_fst_step (ub := ub) ⟨hz, hjj⟩
      (compStep_char _ _ _ _ _ _ _ n94 n36 n46 n42 n43 n63 n92 n91) hz
    refine ⟨ub', ?_⟩
    rw [hub', absP_set_kind_ch _ _ hjl, CHAR_val, hcc]

/-! ## `re_compile` -/

/-- (a) `re_compile pattern` is `ok r`, where `r` is the model's `compile` of the pattern's bytes
(`none` for `none`; otherwise `tok` of each object and the value of each class-buffer byte),
and every compiled regex has the `UNUSED` entry at index 29 (`WF`). For every pattern. -/
theorem re_compile_eq (pattern : Slice U8) :
    ∃ r, tiny_regex.re_compile pattern = .ok r ∧ r.map absRe = (compile (pat pattern)).1 ∧
      ∀ re, r = some re → WF re := by
  apply exists_ok_of_wp
  unfold tiny_regex.re_compile
  refine re_compile_loop_spec pattern _ _ _ _ _ _ ⟨by simp, by simp, ?_, 0, ?_⟩
  · intro k hk
    simp only [Aeneas.Std.Array.repeat_val, List.getD_eq_getElem?_getD, List.getElem?_replicate]
    split_ifs <;> rfl
  · have hP : absP (Std.Array.repeat 30#usize ⟨0#u8, 0#u8, 0#usize⟩) = Array.replicate MAXOBJ {} := by
      simp only [absP, Aeneas.Std.Array.repeat_val, List.map_replicate]
      rfl
    have hB : absB (Std.Array.repeat 40#usize 0#u8) = Array.replicate MAXCCL 0 := by
      simp only [absB, Aeneas.Std.Array.repeat_val, List.map_replicate]
      rfl
    simp only [hP, hB, compile]
    rfl

end EquivLean.Demo.XLang.TinyRegex.Rust
