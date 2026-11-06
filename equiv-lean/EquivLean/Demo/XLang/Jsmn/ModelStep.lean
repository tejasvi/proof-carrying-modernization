import EquivLean.Demo.XLang.Jsmn.ModelLemmas

/-!
# jsmn model: `step` by byte class, and the well-formedness the C side reads with

For the C side's proof of `jsmn_parse`'s loop (cir-repin's requests):

* `step_open`, `step_close_none`, `step_close_some`, `step_quote`, `step_ws`, `step_colon`,
  `step_comma`, `step_prim`: one turn of the loop for each class of the byte at `pos`, with the
  class as plain equalities or inequalities on `byteAt js st.pos`.
* `lastOpen_zero`, `lastOpen_succ`, `lastOpenCont_zero`, `lastOpenCont_succ`: one step of the
  backward searches.
* `WF` (the invariant `Inv`): `wf_init`, `wf_step`, and the bounds `WF.len_n`, `WF.pos_le`,
  `WF.sup`, `WF.tok` (every token: a known type, `start` and `end` in `-1 .. js.length`,
  `0 ≤ size ≤ toknext`).
* The loop itself unfolds by `mainLoop_eq` (`ModelLemmas`).
-/

namespace EquivLean.Demo.XLang.Jsmn

/-! ## The backward searches, one step -/

theorem lastOpen_zero (toks : List Tok) : lastOpen toks 0 = none := rfl

theorem lastOpen_succ (toks : List Tok) (i : Nat) :
    lastOpen toks (i + 1) = if isOpen (toks.getD i dflt) then some i else lastOpen toks i := rfl

theorem lastOpenCont_zero (toks : List Tok) : lastOpenCont toks 0 = none := rfl

theorem lastOpenCont_succ (toks : List Tok) (i : Nat) :
    lastOpenCont toks (i + 1) =
      if ((toks.getD i dflt).type = ARRAY ∨ (toks.getD i dflt).type = OBJECT) ∧
          isOpen (toks.getD i dflt) then some i
      else lastOpenCont toks i := rfl

/-! ## `step` by byte class -/

section
variable {js : List Nat} {n : Nat} {st : St}

/-- `{` or `[`: `JSMN_ERROR_NOMEM` at capacity, else a new open token, a child of `toksuper`,
which becomes `toksuper`. -/
theorem step_open (hc : byteAt js st.pos = 123 ∨ byteAt js st.pos = 91) :
    step js n st =
      if n ≤ st.toks.length then .error ERROR_NOMEM
      else .ok ⟨st.pos + 1,
        bumpSup st.toks st.sup ++
          [⟨if byteAt js st.pos = 123 then OBJECT else ARRAY, st.pos, -1, 0⟩],
        st.toks.length⟩ := by
  unfold step
  dsimp only
  rw [ite_eq_left hc]

/-- `}` or `]` with no open token: `JSMN_ERROR_INVAL`. -/
theorem step_close_none (hc : byteAt js st.pos = 125 ∨ byteAt js st.pos = 93)
    (hi : lastOpen st.toks st.toks.length = none) : step js n st = .error ERROR_INVAL := by
  unfold step
  dsimp only
  rw [ite_eq_right (by omega), ite_eq_left hc, hi]

/-- `}` or `]` with the last open token at `i`: `JSMN_ERROR_INVAL` if its type does not match,
else it is closed at `pos + 1` and `toksuper` becomes the open token below it (or -1). -/
theorem step_close_some {i : Nat} (hc : byteAt js st.pos = 125 ∨ byteAt js st.pos = 93)
    (hi : lastOpen st.toks st.toks.length = some i) :
    step js n st =
      if (st.toks.getD i dflt).type ≠ (if byteAt js st.pos = 125 then OBJECT else ARRAY) then
        .error ERROR_INVAL
      else
        .ok ⟨st.pos + 1, st.toks.set i { st.toks.getD i dflt with stop := st.pos + 1 },
          match lastOpen st.toks i with
          | some j => j
          | none => -1⟩ := by
  unfold step
  dsimp only
  rw [ite_eq_right (by omega), ite_eq_left hc, hi]
  rfl

/-- `"`: `jsmn_parse_string`, then `tokens[toksuper].size++` and `pos++`. -/
theorem step_quote (hc : byteAt js st.pos = 34) :
    step js n st =
      match parseString js n st with
      | .error e => .error e
      | .ok st' => .ok ⟨st'.pos + 1, bumpSup st'.toks st'.sup, st'.sup⟩ := by
  unfold step
  dsimp only
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left hc]
  rfl

/-- Whitespace: `pos++`. -/
theorem step_ws
    (hc : byteAt js st.pos = 9 ∨ byteAt js st.pos = 13 ∨ byteAt js st.pos = 10 ∨
      byteAt js st.pos = 32) :
    step js n st = .ok ⟨st.pos + 1, st.toks, st.sup⟩ := by
  unfold step
  dsimp only
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left hc]

/-- `:`: `toksuper = toknext - 1`, `pos++`. -/
theorem step_colon (hc : byteAt js st.pos = 58) :
    step js n st = .ok ⟨st.pos + 1, st.toks, (st.toks.length : Int) - 1⟩ := by
  unfold step
  dsimp only
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
    ite_eq_right (by omega), ite_eq_left hc]

/-- `,`: after a key or a value (`toksuper` not an object or array), `toksuper` goes back to the
last open object or array, if any; `pos++`. -/
theorem step_comma (hc : byteAt js st.pos = 44) :
    step js n st =
      if st.sup ≠ -1 ∧ (st.toks.getD st.sup.toNat dflt).type ≠ ARRAY ∧
          (st.toks.getD st.sup.toNat dflt).type ≠ OBJECT then
        .ok ⟨st.pos + 1, st.toks,
          match lastOpenCont st.toks st.toks.length with
          | some i => i
          | none => st.sup⟩
      else .ok ⟨st.pos + 1, st.toks, st.sup⟩ := by
  unfold step
  dsimp only
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
    ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left hc]
  rfl

/-- Any other byte: `jsmn_parse_primitive`, then `tokens[toksuper].size++` and `pos++`. -/
theorem step_prim (h1 : byteAt js st.pos ≠ 123) (h2 : byteAt js st.pos ≠ 91)
    (h3 : byteAt js st.pos ≠ 125) (h4 : byteAt js st.pos ≠ 93) (h5 : byteAt js st.pos ≠ 34)
    (h6 : byteAt js st.pos ≠ 9) (h7 : byteAt js st.pos ≠ 13) (h8 : byteAt js st.pos ≠ 10)
    (h9 : byteAt js st.pos ≠ 32) (h10 : byteAt js st.pos ≠ 58) (h11 : byteAt js st.pos ≠ 44) :
    step js n st =
      match parsePrimitive js n st with
      | .error e => .error e
      | .ok st' => .ok ⟨st'.pos + 1, bumpSup st'.toks st'.sup, st'.sup⟩ := by
  unfold step
  dsimp only
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
    ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
  rfl

end

/-! ## Well-formedness -/

/-- The well-formedness the C side reads with: the invariant `Inv`. -/
def WF (js : List Nat) (n : Nat) (st : St) : Prop := Inv js n st

theorem wf_init (js : List Nat) (n : Nat) : WF js n St.init := inv_init js n

/-- Every turn of the loop keeps `WF` (no bound on the text or on `n` is needed). -/
theorem wf_step {js : List Nat} {n : Nat} {st st' : St} (h : step js n st = .ok st')
    (hl : live js st.pos) (hw : WF js n st) : WF js n st' := step_inv hw hl h

theorem WF.len_n {js : List Nat} {n : Nat} {st : St} (hw : WF js n st) : st.toks.length ≤ n :=
  Inv.len_n hw

theorem WF.pos_le {js : List Nat} {n : Nat} {st : St} (hw : WF js n st) : st.pos ≤ js.length :=
  Inv.pos_le hw

theorem WF.len_pos {js : List Nat} {n : Nat} {st : St} (hw : WF js n st) :
    st.toks.length ≤ st.pos := Inv.len_pos hw

theorem WF.sup {js : List Nat} {n : Nat} {st : St} (hw : WF js n st) :
    st.sup = -1 ∨ (0 ≤ st.sup ∧ st.sup < st.toks.length) := Inv.sup hw

/-- Every token: a known type, `start` and `end` in `-1 .. js.length`, `0 ≤ size ≤ toknext`. -/
theorem WF.tok {js : List Nat} {n : Nat} {st : St} (hw : WF js n st) :
    ∀ t ∈ st.toks, (t.type = OBJECT ∨ t.type = ARRAY ∨ t.type = STRING ∨ t.type = PRIMITIVE) ∧
      -1 ≤ t.start ∧ t.start ≤ js.length ∧ -1 ≤ t.stop ∧ t.stop ≤ js.length ∧
      0 ≤ t.size ∧ t.size ≤ st.toks.length := by
  intro t ht
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp ht
  have hp := Inv.pos_le hw
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := Inv.toks hw k hk
  refine ⟨h1, by omega, by omega, ?_, ?_, h5, h6⟩
  · rcases h4 with h4 | h4 <;> omega
  · rcases h4 with h4 | h4 <;> omega

end EquivLean.Demo.XLang.Jsmn
