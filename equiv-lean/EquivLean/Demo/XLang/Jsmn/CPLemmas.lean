import EquivLean.Demo.XLang.Jsmn.CPDefs

/-!
# jsmn → model, C side: list facts for the main loop's token updates

`incSize` as a `List.set`, the token array after the writes of a `{`/`[` turn (`tokArr_open`), and the field
ranges the executor needs when it reads a token of a well-formed state (`tok_ranges`).
-/

open CIR EquivLean.Cir
open EquivLean.Demo.XLang.Jsmn (St Tok byteAt live step mainLoop incSize bumpSup dflt)

namespace EquivLean.Demo.XLang.Jsmn.C

theorem getD_mem {α : Type} {l : List α} {i : Nat} (h : i < l.length) (d : α) : l.getD i d ∈ l := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  exact List.getElem_mem h

instance : Inhabited Tok := ⟨dflt⟩

theorem incSize_eq (toks : List Tok) (i : Nat) :
    incSize toks i = toks.set i { toks.getD i dflt with size := (toks.getD i dflt).size + 1 } := by
  unfold incSize
  rw [List.modify_eq_set, List.getD_eq_getElem?_getD]
  rfl

theorem mem_set_or {α : Type} {l : List α} {i : Nat} {a b : α} (h : a ∈ l.set i b) : a ∈ l ∨ a = b :=
  List.mem_or_eq_of_mem_set h

/-- The token array after a `{`/`[` turn: the new record written at `toknext` (in two steps) around the size
update of the parent `i`. -/
theorem tokArr_open (ts : List Tok) (n i : Nat) (hi : i < ts.length) (hL : ts.length < n) (a1 : Val)
    (t' t : Tok) :
    (((tokArr ts n).set ts.length a1).set i (tokV t')).set ts.length (tokV t) = tokArr (ts.set i t' ++ [t]) n := by
  have h1 : (((tokArr ts n).set ts.length a1).set i (tokV t')).set ts.length (tokV t) =
      ((tokArr ts n).set ts.length (tokV t)).set i (tokV t') := by
    rw [List.set_comm _ _ (by omega : i ≠ ts.length), List.set_set]
  rw [h1, tokArr_push ts n t hL, tokArr_set _ n i t' (by simp; omega), List.set_append_left _ _ (by omega)]

theorem tokArr_open0 (ts : List Tok) (n : Nat) (hL : ts.length < n) (a1 : Val) (t : Tok) :
    ((tokArr ts n).set ts.length a1).set ts.length (tokV t) = tokArr (ts ++ [t]) n := by
  rw [List.set_set, tokArr_push ts n t hL]

/-- `tokArr_open` with the records written out, as the executor leaves them. -/
theorem tokArr_open' (ts : List Tok) (n i : Nat) (hi : i < ts.length) (hL : ts.length < n) (a1 : Val)
    (ty st en sz ty' st' en' sz' : Int) :
    (((tokArr ts n).set ts.length a1).set i (.agg [.int ty', .int st', .int en', .int sz'])).set ts.length
        (.agg [.int ty, .int st, .int en, .int sz]) =
      tokArr (ts.set i ⟨ty', st', en', sz'⟩ ++ [⟨ty, st, en, sz⟩]) n :=
  tokArr_open ts n i hi hL a1 ⟨ty', st', en', sz'⟩ ⟨ty, st, en, sz⟩

theorem tokArr_push1 (ts : List Tok) (n : Nat) (hL : ts.length < n) (ty st en sz : Int) :
    (tokArr ts n).set ts.length (.agg [.int ty, .int st, .int en, .int sz]) = tokArr (ts ++ [⟨ty, st, en, sz⟩]) n :=
  tokArr_push ts n ⟨ty, st, en, sz⟩ hL

theorem tokArr_open0' (ts : List Tok) (n : Nat) (hL : ts.length < n) (a1 : Val) (ty st en sz : Int) :
    ((tokArr ts n).set ts.length a1).set ts.length (.agg [.int ty, .int st, .int en, .int sz]) =
      tokArr (ts ++ [⟨ty, st, en, sz⟩]) n :=
  tokArr_open0 ts n hL a1 ⟨ty, st, en, sz⟩

theorem bumpSup_length (toks : List Tok) (sup : Int) : (bumpSup toks sup).length = toks.length := by
  unfold bumpSup incSize; split <;> simp

theorem bumpSup_neg (toks : List Tok) : bumpSup toks (-1) = toks := by
  unfold bumpSup; simp

theorem bumpSup_eq (toks : List Tok) (sup : Int) (h : sup ≠ -1) :
    bumpSup toks sup = toks.set sup.toNat
      ⟨(toks.getD sup.toNat dflt).type, (toks.getD sup.toNat dflt).start, (toks.getD sup.toNat dflt).stop,
        (toks.getD sup.toNat dflt).size + 1⟩ := by
  unfold bumpSup; rw [if_neg h, incSize_eq]

/-- The field ranges of a token of a well-formed state, as the executor needs them for a read. -/
theorem tok_ranges {js : List Nat} {n : Nat} {st : St} (hwf : Jsmn.WF js n st) {i : Nat}
    (hi : i < st.toks.length) :
    ((st.toks.getD i dflt).type = 1 ∨ (st.toks.getD i dflt).type = 2 ∨ (st.toks.getD i dflt).type = 4 ∨
      (st.toks.getD i dflt).type = 8) ∧
    -1 ≤ (st.toks.getD i dflt).start ∧ (st.toks.getD i dflt).start ≤ js.length ∧
    -1 ≤ (st.toks.getD i dflt).stop ∧ (st.toks.getD i dflt).stop ≤ js.length ∧
    0 ≤ (st.toks.getD i dflt).size ∧ (st.toks.getD i dflt).size ≤ st.toks.length :=
  hwf.tok _ (getD_mem hi dflt)

end EquivLean.Demo.XLang.Jsmn.C
