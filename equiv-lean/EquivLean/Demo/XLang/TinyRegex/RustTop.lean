import EquivLean.Demo.XLang.TinyRegex.RustCompile

/-!
# tiny-regex-c → Rust: `re_matchp`, `re_match`, no panic

For every pattern and every text shorter than 2^28 bytes, `re_matchp` and `re_match` return
`ok (ret, ml)` with the model's return value and final `matchlength` (`toI32`: wrapped to `i32`,
as the Rust wraps; the value itself when it is an `i32`, e.g. when the model reports no
overflow). The matcher group (`matchpattern` and its helpers, `RustMatch.lean`) enters as the
hypothesis `MatchSpec`: the statement of its theorem `matchpattern_eq`.

The search loop of `re_matchp` is proved with a functional invariant: `idx + 1 = ti`, and the
model's `searchLoop` from `ti` with the current `matchlength` gives the final result.
-/

open Aeneas Aeneas.Std EquivLean EquivLean.Aeneas

namespace EquivLean.Demo.XLang.TinyRegex.Rust

/-- The matcher group's theorem (`matchpattern_eq`, `RustMatch.lean`), as a proposition. -/
def MatchSpec : Prop :=
  ∀ (re : tiny_regex.Regex) (text : Slice U8) (pi ti : Usize) (ml : I32) (mlZ : Int) (ub : Nat),
    WF re → pi.val < 30 → ti.val ≤ text.length → text.length < 2 ^ 28 → ml = toI32 mlZ →
    tiny_regex.matchpattern re pi text ti ml =
      .ok (res (mpLoop (ctx re text) mlZ pi.val ti.val mlZ ub))

/-! ## `i32` values -/

theorem toI32_ofVal (x : I32) : toI32 x.val = x := by
  rcases x with ⟨bv⟩
  simp [toI32, IScalar.val]

theorem toI32_val_inRange (v : Int) (h1 : -2 ^ 31 ≤ v) (h2 : v < 2 ^ 31) : (toI32 v).val = v := by
  show (BitVec.ofInt 32 v).toInt = v
  rw [BitVec.toInt_ofInt]
  exact Int.bmod_eq_of_le_mul_two (by omega) (by omega)

theorem toI32_eq_of_val {x : I32} {v : Int} (h1 : -2 ^ 31 ≤ v) (h2 : v < 2 ^ 31) (hx : x.val = v) :
    toI32 v = x :=
  IScalar.eq_of_val_eq (by rw [toI32_val_inRange v h1 h2, hx])

theorem absP_getD (a : Std.Array tiny_regex.RegexObj 30#usize) (k : Nat) (hk : k < a.val.length) :
    (absP a).getD k {} = tok a.val[k] := by
  have hk' : k < 30 := by simpa using hk
  simp [absP, Array.getD, hk']

/-! ## The search loop -/

/-- The search loop's state `(idx, ti, ml)`: `ti` is at most the length, `idx + 1 = ti`, and the
model's search from `ti` with the matchlength gives `R` (return value and matchlength). -/
def SearchInv (re : tiny_regex.Regex) (text : Slice U8) (R : Int × Int × Nat)
    (st : I32 × Usize × I32) : Prop :=
  st.2.1.val ≤ text.val.length ∧ st.1.val + 1 = (st.2.1.val : Int) ∧
    ∃ mlZ ub, st.2.2 = toI32 mlZ ∧ (searchLoop (ctx re text) st.2.1.val mlZ ub).1 = R.1 ∧
      (searchLoop (ctx re text) st.2.1.val mlZ ub).2.1 = R.2.1

set_option maxHeartbeats 4000000 in
theorem re_matchp_loop_spec (hM : MatchSpec) (re : tiny_regex.Regex) (text : Slice U8)
    (hwf : WF re) (hlen : text.val.length < 2 ^ 28) (idx : I32) (ti : Usize) (ml : I32)
    (R : Int × Int × Nat) (h : SearchInv re text R (idx, ti, ml)) :
    wp (tiny_regex.re_matchp_loop re text idx ti ml)
      (fun o => o = .ok (toI32 R.1, toI32 R.2.1)) := by
  unfold tiny_regex.re_matchp_loop
  refine wp_loop (loop_shape _) (SearchInv re text R)
    (fun st => text.val.length + 1 - st.2.1.val) ?_ _ h
  simp only [Prod.forall]
  intro idx ti ml hinv
  obtain ⟨hti, hidx, mlZ, ub, hml, hR1, hR2⟩ := hinv
  dsimp only at hti hidx hml hR1 hR2
  have hmp : tiny_regex.matchpattern re 0#usize text ti ml =
      .ok (res (mpLoop (ctx re text) mlZ 0 ti.val mlZ (ub ||| chk ti.val))) :=
    hM re text 0#usize ti ml mlZ (ub ||| chk ti.val) hwf (by simp) hti hlen hml
  have hidx1 : (core.num.I32.wrapping_add idx 1#i32).val = ti.val := by
    rw [core.num.I32.wrapping_add_val_eq, IScalar.ofInt_val_eq,
      Int.bmod_eq_of_le_mul_two (by omega) (by omega)]
    omega
  have hti1 : toI32 (ti.val : Int) = core.num.I32.wrapping_add idx 1#i32 :=
    toI32_eq_of_val (by omega) (by omega) hidx1
  rw [searchLoop] at hR1 hR2
  simp only [tiny_regex.re_matchp_loop.body, hmp]
  generalize mpLoop (ctx re text) mlZ 0 ti.val mlZ (ub ||| chk ti.val) = m at hR1 hR2
  aeneas_wp [wp_at, atv_val, res, loopCls_done, loopCls_cont, loopCls_error]
  by_cases hlt : ti.val < text.val.length
  · have hlt' : ti.val < (ctx re text).T.size := by
      rw [ctx_eq]
      simpa [pat_size] using hlt
    have hc : (ctx re text).T[ti.val] = (rd (pat text) ti.val).1 := by
      simp [rd, ctx_eq, pat_size, hlt]
    have hge : ¬ text.val.length ≤ ti.val := by omega
    simp only [hlt', hc, _root_.dite_true] at hR1 hR2
    cases hok : m.ok
    · simp only [hok, Bool.false_eq_true, _root_.ite_false] at hR1 hR2
      by_cases h0 : (rd (pat text) ti.val).1 = 0
      · simp only [h0, bne_self_eq_false, Bool.false_eq_true, _root_.ite_false] at hR1 hR2
        simp only [h0, _root_.ite_true]
        rw [← hR1, ← hR2]
        rfl
      · have hov : ti.val + 1 ≤ Usize.max := by scalar_tac
        simp only [h0, bne_iff_ne, ne_eq, not_false_eq_true, _root_.ite_true] at hR1 hR2
        simp only [h0, hge, hov, Bool.false_eq_true, _root_.ite_false, _root_.dite_true,
          SearchInv, UScalar.ofNatCore_val_eq]
        refine ⟨⟨?_, ?_, m.ml, m.ub, rfl, hR1, hR2⟩, ?_⟩
        · omega
        · rw [hidx1]
          omega
        · omega
    · simp only [hok, _root_.ite_true] at hR1 hR2
      by_cases h0 : (rd (pat text) ti.val).1 = 0
      · simp only [h0, beq_self_eq_true, _root_.ite_true] at hR1 hR2
        simp only [h0, _root_.ite_true]
        rw [← hR1, ← hR2]
        rfl
      · simp only [h0, beq_iff_eq, _root_.ite_false] at hR1 hR2
        simp only [h0, _root_.ite_false, _root_.ite_true]
        rw [← hR1, ← hR2, hti1]
  · have hle : text.val.length ≤ ti.val := by omega
    have hlt' : ¬ ti.val < (ctx re text).T.size := by
      rw [ctx_eq]
      simpa [pat_size] using hlt
    have h0 : (rd (pat text) ti.val).1 = 0 := rd_fst_of_ge (by rw [pat_size]; exact hle)
    simp only [hlt', _root_.dite_false] at hR1 hR2
    cases hok : m.ok
    · simp only [h0, hle, Bool.false_eq_true, _root_.ite_false, _root_.ite_true]
      rw [← hR1, ← hR2]
      rfl
    · simp only [h0, _root_.ite_true]
      rw [← hR1, ← hR2]
      rfl

/-! ## `re_matchp`, `re_match` -/

/-- (b) `re_matchp`: the model's return value and matchlength, for every regex that satisfies
`WF` (every `re_compile` result does) and every text shorter than 2^28 bytes. -/
theorem re_matchp_eq (hM : MatchSpec) (cp : Option tiny_regex.Regex) (text : Slice U8) (ub : Nat)
    (hwf : ∀ re, cp = some re → WF re) (hlen : text.val.length < 2 ^ 28) :
    tiny_regex.re_matchp cp text =
      .ok (toI32 (reMatchp (cp.map absRe) (pat text) ub).1,
        toI32 (reMatchp (cp.map absRe) (pat text) ub).2.1) := by
  cases cp with
  | none => rfl
  | some re =>
    have hw := hwf re rfl
    have hl : re.objs.val.length = 30 := by simp
    unfold tiny_regex.re_matchp
    simp only [Option.map_some, reMatchp]
    have hC : (⟨(absRe re).1, (absRe re).2, pat text⟩ : Ctx) = ctx re text := rfl
    rw [hC, absRe, absP_getD _ 0 (by omega)]
    apply eq_ok_of_wp
    simp only [tiny_regex.obj]
    aeneas_wp [array_index_usize_eq, hl, tiny_regex.MAX_REGEXP_OBJECTS]
    by_cases hb : re.objs.val[0].kind.val = 2
    · have hmp : tiny_regex.matchpattern re 1#usize text 0#usize 0#i32 =
          .ok (res (mpLoop (ctx re text) 0 1 0 0 ub)) :=
        hM re text 1#usize 0#usize 0#i32 0 ub hw (by simp) (by simp) hlen rfl
      simp only [hb, BEGIN_val, _root_.ite_true, hmp, tok]
      aeneas_wp [res]
      cases (mpLoop (ctx re text) 0 1 0 0 ub).ok <;> rfl
    · simp only [hb, BEGIN_val, _root_.ite_false, tok, beq_iff_eq, BEGIN]
      exact re_matchp_loop_spec hM re text hw hlen _ _ _ _
        ⟨by simp, by simp, 0, ub, rfl, rfl, rfl⟩

/-- (b) `re_match`: the model's return value and matchlength, for every pattern and every text
shorter than 2^28 bytes. -/
theorem re_match_eq (hM : MatchSpec) (pattern text : Slice U8) (hlen : text.val.length < 2 ^ 28) :
    tiny_regex.re_match pattern text =
      .ok (toI32 (reMatch (pattern.val.map (·.val)) (text.val.map (·.val))).1,
        toI32 (reMatch (pattern.val.map (·.val)) (text.val.map (·.val))).2.1) := by
  obtain ⟨r, hr, hT, hW⟩ := re_compile_eq pattern
  unfold tiny_regex.re_match reMatch
  rw [hr]
  have hp : (pattern.val.map (·.val)).toArray = pat pattern := rfl
  have ht : (text.val.map (·.val)).toArray = pat text := rfl
  rw [hp, ht]
  rcases hc : compile (pat pattern) with ⟨cp, ub⟩
  rw [hc] at hT
  simp only at hT
  subst hT
  simp only [Aeneas.Std.bind_ok]
  cases r with
  | none => exact re_matchp_eq hM none text ub hW hlen
  | some re => exact re_matchp_eq hM (some re) text ub hW hlen

/-- (c) No panic: `re_match` returns normally on every pattern and every text shorter than
2^28 bytes. -/
theorem re_match_ok (hM : MatchSpec) (pattern text : Slice U8) (hlen : text.val.length < 2 ^ 28) :
    ∃ v, tiny_regex.re_match pattern text = .ok v :=
  ⟨_, re_match_eq hM pattern text hlen⟩

end EquivLean.Demo.XLang.TinyRegex.Rust
