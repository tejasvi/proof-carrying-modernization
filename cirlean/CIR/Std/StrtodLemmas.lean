import Lean
import CIR.Std.Models
import CIR.Std.FloatNaN

/-!
  Facts for proofs over symbolic C strings and `strtod` input (cJSON's
  `parse_number`: a buffer of characters from `[0-9+-eE.]` and a terminator):
  * reading a C string whose characters are known to be nonzero
    (`findIdx?_isNulVal`, through `readCStr`);
  * the characters `strtod` consumes lie within the string
    (`strtodWith_snd_le`), so its end pointer stays in the array;
  * no NaN comes out of input without an `n`/`N` (`strtodWith_ne_nan`), so
    the conversion of the result to `int` after cJSON's range tests is
    defined (`floatToInt_i32_ok`, `CIR/Std/FloatNaN.lean`).
-/

namespace CIR.Std

theorem length_takeWhile_le' {α : Type} (p : α → Bool) (l : List α) : (l.takeWhile p).length ≤ l.length := by
  have := congrArg List.length (List.takeWhile_append_dropWhile (p := p) (l := l))
  simp only [List.length_append] at this
  omega

/-- The subterms `(l.takeWhile p).length` of `e` (without loose bound variables). -/
partial def takeWhileLengths (e : Lean.Expr) (acc : Array Lean.Expr) : Array Lean.Expr :=
  let acc := if e.isAppOfArity ``List.length 2 && (e.getArg! 1).isAppOfArity ``List.takeWhile 3 &&
      !e.hasLooseBVars && !acc.contains e then acc.push e else acc
  match e with
  | .app f a => takeWhileLengths a (takeWhileLengths f acc)
  | .lam _ t b _ | .forallE _ t b _ => takeWhileLengths b (takeWhileLengths t acc)
  | .letE _ t v b _ => takeWhileLengths b (takeWhileLengths v (takeWhileLengths t acc))
  | .mdata _ b | .proj _ _ b => takeWhileLengths b acc
  | _ => acc

open Lean Meta Elab Tactic in
/-- For every `(l.takeWhile p).length` in the goal and the hypotheses, the
fact that it is at most `l.length` (for `omega`). -/
elab "takewhile_facts" : tactic => withMainContext do
  let mut terms : Array Expr := takeWhileLengths (← instantiateMVars (← getMainTarget)) #[]
  for d in (← getLCtx) do
    unless d.isImplementationDetail do
      terms := takeWhileLengths (← instantiateMVars d.type) terms
  for e in terms do
    let tw := e.getArg! 1
    let pf ← mkAppM ``length_takeWhile_le' #[tw.getArg! 1, tw.getArg! 2]
    let (_, g) ← (← (← getMainGoal).assert `htw (← inferType pf) pf).intro1P
    replaceMainGoal [g]
theorem length_of_drop_eq_cons' {α : Type} {cs r : List α} {n : Nat} {c : α} (h : cs.drop n = c :: r) :
    n + 1 + r.length = cs.length := by
  have := congrArg List.length h
  simp only [List.length_drop, List.length_cons] at this
  omega

open Lean Meta Elab Tactic in
/-- For every hypothesis `l.drop n = c :: r`, the fact `n + 1 + r.length = l.length`. -/
elab "drop_facts" : tactic => withMainContext do
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    let some (_, lhs, rhs) := ty.eq? | continue
    unless lhs.isAppOfArity ``List.drop 3 && rhs.isAppOfArity ``List.cons 3 do continue
    let pf ← mkAppM ``length_of_drop_eq_cons' #[d.toExpr]
    let (_, g) ← (← (← getMainGoal).assert `hdrop (← inferType pf) pf).intro1P
    replaceMainGoal [g]

macro "len_close" : tactic => `(tactic| (
  (try simp only [List.length_drop, List.length_cons, List.length_nil, Prod.fst, Prod.snd] at *)
  takewhile_facts
  drop_facts
  (try simp only [List.length_drop, List.length_cons, List.length_nil] at *)
  omega))

theorem matchWord_le (cs w : List Int) : matchWord cs w ≤ cs.length := by
  induction cs generalizing w with
  | nil => cases w <;> simp [matchWord]
  | cons c cs ih =>
    cases w with
    | nil => simp [matchWord]
    | cons x ws =>
      simp only [matchWord, List.length_cons]
      split
      · have := ih ws; omega
      · omega

theorem length_of_drop_eq_cons {cs r : List Int} {n : Nat} {c : Int} (h : cs.drop n = c :: r) :
    n + 1 + r.length = cs.length := by
  have := congrArg List.length h
  simp only [List.length_drop, List.length_cons] at this
  omega

theorem hexPrefix_length {cs : List Int} (h : hexPrefix cs = true) : 2 ≤ cs.length := by
  unfold hexPrefix at h
  split at h
  · simp
  · simp at h

theorem fpSubject_fst_le (cs : List Int) : (fpSubject cs).1 ≤ cs.length := by
  have hi := matchWord_le cs [105, 110, 102, 105, 110, 105, 116, 121]
  have hn := matchWord_le cs [110, 97, 110]
  unfold fpSubject
  simp only
  split
  · split
    · omega
    · split <;> simp <;> omega
  · split
    · split
      · simp
      · split
        · rename_i rest h
          have hl := length_of_drop_eq_cons h
          split
          · rename_i hk
            simp only
            have h1 : ∀ k, (rest.drop k).head? = some 41 → k < rest.length := fun k hk' => by
              apply Nat.lt_of_not_le
              intro hle
              rw [List.drop_eq_nil_of_le hle] at hk'
              simp at hk'
            have := h1 _ (by simpa using hk)
            omega
          · simp only
            takewhile_facts
            omega
        · simp only
          omega
    · generalize hhex : hexPrefix cs = hex
      have h2 : hex = true → 2 ≤ cs.length := fun h => hexPrefix_length (hhex ▸ h)
      cases hex <;> (try have := h2 rfl) <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
        (repeat' split) <;> len_close

/-- The subterms `fpSubject l` of `e`. -/
partial def fpSubjects (e : Lean.Expr) (acc : Array Lean.Expr) : Array Lean.Expr :=
  let acc := if e.isAppOfArity ``fpSubject 1 && !e.hasLooseBVars && !acc.contains e then acc.push e else acc
  match e with
  | .app f a => fpSubjects a (fpSubjects f acc)
  | .lam _ t b _ | .forallE _ t b _ => fpSubjects b (fpSubjects t acc)
  | .letE _ t v b _ => fpSubjects b (fpSubjects v (fpSubjects t acc))
  | .mdata _ b | .proj _ _ b => fpSubjects b acc
  | _ => acc

open Lean Meta Elab Tactic in
/-- For every `fpSubject l` in the goal, `(fpSubject l).1 ≤ l.length`. -/
elab "fpsubject_facts" : tactic => withMainContext do
  for e in fpSubjects (← instantiateMVars (← getMainTarget)) #[] do
    let pf ← mkAppM ``fpSubject_fst_le #[e.getArg! 0]
    let (_, g) ← (← (← getMainGoal).assert `hfp (← inferType pf) pf).intro1P
    replaceMainGoal [g]

/-- The characters `strtod` consumes lie within the string: its end pointer
stays in the array. -/
theorem strtodWith_snd_le (round : Bool → Nat → Nat → Float) (cs : List Int) :
    (strtodWith round cs).2 ≤ cs.length := by
  unfold strtodWith
  simp only
  (repeat' split) <;> fpsubject_facts <;> len_close

/-! ### C strings with symbolic characters -/

@[simp] theorem findIdx?_isNulVal {cs : List Int} {rest : List Val} (h : ∀ c ∈ cs, c ≠ 0) :
    (cs.map Val.int ++ Val.int 0 :: rest).findIdx? isNulVal = some cs.length := by
  induction cs with
  | nil => simp [List.findIdx?_cons, isNulVal]
  | cons c cs ih =>
    have hc : c ≠ 0 := h c (by simp)
    have ih' := ih (fun d hd => h d (by simp [hd]))
    simp [List.findIdx?_cons, isNulVal, hc, ih']

@[simp] theorem findIdx?_isNulVal' {cs rest : List Int} (h : ∀ c ∈ cs, c ≠ 0) :
    ((cs ++ 0 :: rest).map Val.int).findIdx? isNulVal = some cs.length := by
  rw [List.map_append, List.map_cons]
  exact findIdx?_isNulVal h

@[simp] theorem take_map_int_append (cs : List Int) (r : List Val) :
    (cs.map Val.int ++ r).take cs.length = cs.map Val.int := by
  simp

@[simp] theorem all_isIntVal_map_int (cs : List Int) : (cs.map Val.int).all isIntVal = true := by
  simp [isIntVal]

/-! ### `strtod`: no NaN without an `n` -/

theorem scaleRound_ne_nan (neg : Bool) (mant base : Nat) (x : Int) :
    decodeF (scaleRound (ratToFloat neg) neg mant base x) ≠ .nan := by
  unfold scaleRound
  repeat' split
  all_goals first
    | with_reducible exact decodeF_ratToFloat_ne_nan _ _ _
    | with_reducible exact decodeF_valToFloat_ne_nan _ _ _
    | with_reducible exact decodeF_infF_ne_nan _

theorem subjectValue_ne_nan (neg : Bool) (cs : List Int) (h : ∀ c ∈ cs, lowerC c ≠ 110) :
    decodeF (subjectValue ratToFloat neg cs) ≠ .nan := by
  unfold subjectValue
  split
  · rename_i c rest
    split
    · exact decodeF_infF_ne_nan _
    · split
      · rename_i hn
        exact absurd (by simpa using hn) (h c (by simp))
      · simp only
        repeat' split
        all_goals first
          | with_reducible exact scaleRound_ne_nan _ _ _ _
          | with_reducible exact decodeF_valToFloat_ne_nan _ _ _
  · exact decodeF_valToFloat_ne_nan _ _ _

/-- `strtod` returns no NaN on input without `n`/`N` (cJSON's `parse_number`
passes only `[0-9+-eE.]`). -/
theorem strtodWith_ne_nan (cs : List Int) (h : ∀ c ∈ cs, lowerC c ≠ 110) :
    decodeF (strtodWith ratToFloat cs).1 ≠ .nan := by
  unfold strtodWith
  simp only
  (repeat' split)
  all_goals first
    | with_reducible exact decodeF_valToFloat_ne_nan _ _ _
    | exact subjectValue_ne_nan _ _ fun c hc =>
        h c (List.mem_of_mem_drop (List.mem_of_mem_drop (List.mem_of_mem_take hc)))

end CIR.Std
