import EquivLean.Demo.Gen.Cir.Jsmn.Jsmn
import EquivLean.Demo.XLang.TinyRegex.CPartial
import EquivLean.Demo.XLang.Jsmn.Model

/-!
# jsmn → model, C side: shared definitions

* `for` loops in a hypothesis by an invariant (`holds_for_name`, `holds_for_inv`; partial correctness, as
  `holds_while_inv` of `TinyRegex/CPartial.lean`).
* The JSON text `js` (the model's byte list) is a block of `char`s holding the bytes (`js.map (.int ·)`). jsmn
  reads it through `const char*`: cirlean's `char` load of a byte `x` gives `x - 256 * (x / 128)` (`load_s8`, one
  value without a case split on `x < 128`), and the tests jsmn makes against ASCII constants are linear in `x`.
  Element reads are normalized to the model's `byteAt js i` (`getElem_eq_byteAt`).
* The token array: the model's tokens so far (`tokV`), then fresh records (`tokArr`); the parser (`parserV`).
* The run: `cMem js n` (the parser, the text and `n` tokens in blocks 0, 1, 2), `cRun js n` (`jsmn_run`, i.e.
  `jsmn_init` and one `jsmn_parse`), and `toksOf`, the first tokens of the array in a memory.
-/

open CIR EquivLean.Cir
open EquivLean.Demo.XLang.Jsmn (Tok St byteAt)
open EquivLean.Demo.Gen.Cir.Jsmn.Jsmn (ctx module)

set_option linter.deprecated false

namespace EquivLean.Demo.XLang.Jsmn.C

/-- Name the state at the head of a `for` loop in a hypothesis. -/
theorem holds_for_name {ctx : Ctx} {c b s : Region} {cl : Option (CleanupKind × Region)} {σ₀ : State}
    {K : Step × State → Prop} (hs : (evalFor ctx c b s cl σ₀).holds K) :
    ∃ t, t = σ₀ ∧ (evalFor ctx c b s cl t).holds K := ⟨σ₀, rfl, hs⟩

/-- A `for` loop in a hypothesis, by an invariant (partial correctness, no variant). -/
theorem holds_for_inv {ctx : Ctx} {c b s : Region} {cl : Option (CleanupKind × Region)} {σ₀ : State}
    {K : Step × State → Prop} (hs : (evalFor ctx c b s cl σ₀).holds K) (Inv : State → Prop)
    (Post : Step × State → Prop) (h0 : Inv σ₀)
    (hstep : ∀ σ, Inv σ → pholds (forIter ctx c b s cl σ) (fun r => match r with
      | .inl o => Post o
      | .inr σ' => Inv σ')) :
    ∃ a, Post a ∧ K a := by
  have hl := pholds_loop (loopShape_for ctx c b s cl) (terminates_for ctx c b s cl) Inv Post
    (fun σ hσ r hr => by have h := hstep σ hσ r hr; cases r <;> exact h) σ₀ h0
  obtain ⟨a, -, hp, hk⟩ := holds_pspec_elim hs hl
  exact ⟨a, hp, hk⟩

/-! ### Bytes read through `const char*` -/

/-- cirlean's `char` load (`loadTy`, as the executor unfolds it) of a byte `0 ≤ x ≤ 255` reads the `char`
value `x - 256 * (x / 128)` (linear in `x`, for `omega`), without a case split on `x < 128`. -/
theorem load_s8 (x : Int) (h1 : 0 ≤ x) (h2 : x ≤ 255) :
    (if inRange true 8 x = true then (Res.ok (Val.int x) : Res Val)
      else if inRange false 8 x = true then Res.ok (Val.int (wrap true 8 x))
      else Res.ub "read of an indeterminate or ill-typed value") = Res.ok (Val.int (x - 256 * (x / 128))) := by
  by_cases h : x < 128
  · have h3 : inRange true 8 x = true := by rw [inRange_eq_true_iff]; simp only [intMin_s8, intMax_s8]; omega
    simp only [h3, ite_true]
    congr 2; omega
  · have h3 : inRange true 8 x = false := by rw [inRange_eq_false_iff]; simp only [intMin_s8, intMax_s8]; omega
    have h4 : inRange false 8 x = true := by rw [inRange_eq_true_iff]; simp only [intMin_u, intMax_u8]; omega
    simp only [h3, h4, Bool.false_eq_true, ite_false, ite_true]
    congr 2
    unfold wrap
    simp only [Bool.true_and, decide_eq_true_eq]
    have hp : (2 : Int) ^ 8 = 256 := by decide
    have hp7 : (2 : Int) ^ (8 - 1) = 128 := by decide
    rw [hp, hp7]
    have hm : x % 256 = x := Int.emod_eq_of_lt h1 (by omega)
    rw [hm]
    simp only [show (128 : Int) ≤ x by omega, ite_true]
    omega

/-- The `char` value converted to `int` keeps its value. -/
theorem wrap_s8 (x : Int) (h1 : 0 ≤ x) (h2 : x ≤ 255) :
    wrap true 32 (x - 256 * (x / 128)) = x - 256 * (x / 128) :=
  wrap_of_bounds (by decide) (by simp only [intMin_s32, intMax_s32]; omega)

/-- Element reads of the text, as the model names them (no proof term in the index). -/
theorem getElem_eq_byteAt {js : List Nat} {i : Nat} (h : i < js.length) : js[i] = byteAt js i := by
  simp [byteAt, List.getD_eq_getElem?_getD, h]

theorem byteAt_lt {js : List Nat} (hjs : ∀ b ∈ js, b < 256) (i : Nat) : byteAt js i < 256 := by
  unfold byteAt
  rw [List.getD_eq_getElem?_getD]
  cases h : js[i]? with
  | none => simp
  | some x => simpa using hjs x (List.mem_of_getElem? h)

/-- `load_s8` and `wrap_s8` at the byte `byteAt js i`. -/
theorem load_byte {js : List Nat} (hjs : ∀ b ∈ js, b < 256) (i : Nat) :
    (if inRange true 8 ((byteAt js i : Nat) : Int) = true then (Res.ok (Val.int (byteAt js i)) : Res Val)
      else if inRange false 8 ((byteAt js i : Nat) : Int) = true then
        Res.ok (Val.int (wrap true 8 ((byteAt js i : Nat) : Int)))
      else Res.ub "read of an indeterminate or ill-typed value") =
      Res.ok (Val.int ((byteAt js i : Int) - 256 * ((byteAt js i : Int) / 128))) :=
  load_s8 _ (by omega) (by have := byteAt_lt hjs i; omega)

/-- `load_byte` after the executor has decided the inner test (`inRange false 8` of a byte). -/
theorem load_byte2 {js : List Nat} (hjs : ∀ b ∈ js, b < 256) (i : Nat) :
    (if inRange true 8 ((byteAt js i : Nat) : Int) = true then (Res.ok (Val.int (byteAt js i)) : Res Val)
      else Res.ok (Val.int (wrap true 8 ((byteAt js i : Nat) : Int)))) =
      Res.ok (Val.int ((byteAt js i : Int) - 256 * ((byteAt js i : Int) / 128))) := by
  have h := load_byte hjs i
  have h4 : inRange false 8 ((byteAt js i : Nat) : Int) = true := by
    rw [inRange_eq_true_iff]; simp only [intMin_u, intMax_u8]; have := byteAt_lt hjs i; omega
  simp only [h4, ite_true] at h
  exact h

theorem wrap_byte {js : List Nat} (hjs : ∀ b ∈ js, b < 256) (i : Nat) :
    wrap true 32 ((byteAt js i : Int) - 256 * ((byteAt js i : Int) / 128)) =
      (byteAt js i : Int) - 256 * ((byteAt js i : Int) / 128) :=
  wrap_s8 _ (by omega) (by have := byteAt_lt hjs i; omega)

/-! ### Tokens and the parser -/

/-- A token as a value of record `jsmntok` (type, start, end, size). -/
def tokV (t : Tok) : Val := .agg [.int t.type, .int t.start, .int t.stop, .int t.size]

/-- A fresh `jsmntok` record (indeterminate fields). -/
def tok0 : Val := .agg [.undef, .undef, .undef, .undef]

/-- The token array of `n` records: the tokens so far, then fresh records. -/
def tokArr (ts : List Tok) (n : Nat) : List Val := ts.map tokV ++ List.replicate (n - ts.length) tok0

/-- The parser as a value of record `jsmn_parser`: `pos`, `toknext`, `toksuper`. -/
def parserV (pos toknext : Nat) (toksuper : Int) : Val := .agg [.int pos, .int toknext, .int toksuper]

theorem tokArr_length (ts : List Tok) (n : Nat) (h : ts.length ≤ n) : (tokArr ts n).length = n := by
  simp [tokArr]; omega

theorem tokArr_get_lt (ts : List Tok) (n i : Nat) (h : i < ts.length) :
    (tokArr ts n)[i]? = some (tokV (ts.getD i Jsmn.dflt)) := by
  unfold tokArr
  rw [List.getElem?_append_left (by simpa using h)]
  simp [List.getD_eq_getElem?_getD, h]

theorem tokArr_get_next (ts : List Tok) (n : Nat) (h : ts.length < n) :
    (tokArr ts n)[ts.length]? = some tok0 := by
  unfold tokArr
  rw [List.getElem?_append_right (by simp)]
  simp only [List.length_map, Nat.sub_self]
  rw [List.getElem?_replicate]
  simp; omega

theorem tokArr_push (ts : List Tok) (n : Nat) (t : Tok) (h : ts.length < n) :
    (tokArr ts n).set ts.length (tokV t) = tokArr (ts ++ [t]) n := by
  obtain ⟨k, hk⟩ : ∃ k, n - ts.length = k + 1 := ⟨n - ts.length - 1, by omega⟩
  have hk2 : n - (ts.length + 1) = k := by omega
  unfold tokArr
  rw [hk, List.replicate_succ, List.set_append_right _ _ (by simp)]
  simp [hk2]

theorem tokArr_set (ts : List Tok) (n i : Nat) (t : Tok) (h : i < ts.length) :
    (tokArr ts n).set i (tokV t) = tokArr (ts.set i t) n := by
  unfold tokArr
  rw [List.set_append_left _ _ (by simpa using h)]
  simp [List.map_set]

/-! ### The run -/

/-- The memory of a run: the module's initial memory (no globals), then the parser (block 0, on the caller's
stack, fresh), the text `js` (block 1, read-only, `js.length` `char`s) and the token array (block 2, on the
caller's stack, `n` fresh records). -/
def cMem (js : List Nat) (n : Nat) : Mem :=
  (((module.initMem.alloc .stack (.record "jsmn_parser") (.agg [.undef, .undef, .undef])).2.alloc .readonly
    (.array (.int true 8) js.length) (.arr (js.map fun b : Nat => Val.int (b : Int)))).2.alloc .stack
    (.array (.record "jsmntok") n) (.arr (List.replicate n tok0))).2

/-- `jsmn_run(&parser, js, js.length, tokens, n)`: `jsmn_init` and one `jsmn_parse` call. -/
def cRun (js : List Nat) (n : Nat) : Res (Exit × Mem) :=
  evalCall ctx "jsmn_run"
    [.ptr (.loc 0 []), .ptr (.loc 1 [.idx 0]), .int js.length, .ptr (.loc 2 [.idx 0]), .int n] (cMem js n)

/-- A `jsmntok` record as a token (`none` if a field is not an integer). -/
def tokOf : Val → Option Tok
  | .agg [.int ty, .int st, .int en, .int sz] => some ⟨ty, st, en, sz⟩
  | _ => none

/-- The first `k` tokens of the token array (block 2) in a memory. -/
def toksOf (m : Mem) (k : Nat) : Option (List Tok) :=
  match m.blocks 2 with
  | some ⟨_, _, _, .arr vs⟩ => if k ≤ vs.length then (vs.take k).mapM tokOf else none
  | _ => none

theorem tokOf_tokV (t : Tok) : tokOf (tokV t) = some t := rfl

theorem mapM_tokOf : ∀ ts : List Tok, (ts.map tokV).mapM tokOf = some ts
  | [] => rfl
  | t :: ts => by simp [List.mapM_cons, tokOf_tokV, mapM_tokOf ts]

theorem toksOf_tokArr (m : Mem) (kd : BlockKind) (al : Bool) (ty : Ty) (ts : List Tok) (n : Nat)
    (h : m.blocks 2 = some ⟨kd, al, ty, .arr (tokArr ts n)⟩) (hn : ts.length ≤ n) :
    toksOf m ts.length = some ts := by
  unfold toksOf
  rw [h]
  simp only
  rw [if_pos (by rw [tokArr_length ts n hn]; exact hn)]
  have ht : (tokArr ts n).take ts.length = ts.map tokV := by
    unfold tokArr; simp
  rw [ht]
  exact mapM_tokOf ts

end EquivLean.Demo.XLang.Jsmn.C
