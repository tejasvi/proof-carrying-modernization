/-
StrictTS proof layer: loop theorems.

A `for … of` loop over an array that its body does not modify iterates over the list of the
array's elements at loop entry (`evalForOf_eq_forList`); a loop over a list whose body always
completes normally is a left fold of the body's effect (`forList_fold`). Both are proved once,
by unfolding the interpreter and induction on the remaining length; users never need the
fixpoint-induction principle of the interpreter.
-/
import StrictTS.Proof.Unfold

namespace StrictTS
open JS

variable {TT : TypeTable}

/-- Run a loop body once per element of a list (the meaning of a `for … of` whose array does
not change). Completion handling is the same as in `evalForOf`. -/
def forList (I : Impl) (P : Program TT) {Γ : Ctx} {ρ t : Ty} (body : Block TT (⟨t, false⟩ :: Γ) ρ) :
    List (Val TT t) → Env TT Γ → JS TT (Completion TT ρ × Env TT Γ)
  | [], env => pure (.normal, env)
  | x :: xs, env => do
    let (cb, env1) ← evalB I P body (.cons x env)
    match cb with
    | .normal | .cont 0 => forList I P body xs env1.tail
    | .brk 0 => pure (.normal, env1.tail)
    | .brk (n + 1) => pure (.brk n, env1.tail)
    | .cont (n + 1) => pure (.cont n, env1.tail)
    | other => pure (other, env1.tail)

attribute [ts_sym] forList

/-- The block (run with any value bound to its first variable) leaves the heap cell
`(k, a)` unchanged whenever it holds `c`. -/
def KeepsCell (I : Impl) (P : Program TT) {Γ : Ctx} {ρ : Ty} {s : Slot} (body : Block TT (s :: Γ) ρ)
    (k : HKind) (a : Nat) (c : k.Cell TT) : Prop :=
  ∀ (x : Val TT s.ty) (env : Env TT Γ) (w w' : World TT) r,
    w.heap.get? (k, a) = some c → exec (evalB I P body (.cons x env)) w = some (r, w') →
    w'.heap.get? (k, a) = some c

theorem evalForOf_eq_forList_aux (I : Impl) (P : Program TT) {Γ : Ctx} {ρ t : Ty}
    (body : Block TT (⟨t, false⟩ :: Γ) ρ) (a : Nat) (xs : Array (Val TT t))
    (hk : KeepsCell I P body (.arr t) a xs) :
    ∀ (n i : Nat) (env : Env TT Γ) (w : World TT), xs.size - i = n →
      w.heap.get? (.arr t, a) = some xs →
      exec (evalForOf I P a i body env) w = exec (forList I P body (xs.toList.drop i) env) w := by
  intro n
  induction n with
  | zero =>
    intro i env w hn hw
    have hle : xs.size ≤ i := by omega
    rw [evalForOf.eq_1]
    have hdrop : xs.toList.drop i = [] := List.drop_eq_nil_of_le (by simpa using hle)
    simp [hw, hdrop, forList, Nat.not_lt.mpr hle]
  | succ n ih =>
    intro i env w hn hw
    have hlt : i < xs.size := by omega
    have hdrop : xs.toList.drop i = xs[i] :: xs.toList.drop (i + 1) := by
      rw [List.drop_eq_getElem_cons (by simpa using hlt)]
      simp
    rw [evalForOf.eq_1]
    simp only [exec_bind, exec_readArr, hw, hlt, dite_true, hdrop, forList]
    rcases hb : exec (evalB I P body (.cons xs[i] env)) w with _ | ⟨r, w'⟩
    · rfl
    · have hw' : w'.heap.get? (.arr t, a) = some xs := hk _ _ _ _ _ hw hb
      rcases r with e | ⟨cb, env1⟩
      · rfl
      · simp only
        rcases cb with _ | (_ | m) | (_ | m) | v | p | ex
        · exact ih (i + 1) env1.tail w' (by omega) hw'
        · rfl
        · rfl
        · exact ih (i + 1) env1.tail w' (by omega) hw'
        · rfl
        · rfl
        · rfl
        · rfl

/-- A `for (const x of arr)` loop whose body keeps the array unchanged iterates over the
elements present at loop entry. -/
theorem evalForOf_eq_forList (I : Impl) (P : Program TT) {Γ : Ctx} {ρ t : Ty}
    (body : Block TT (⟨t, false⟩ :: Γ) ρ) (a : Nat) (xs : Array (Val TT t))
    (hk : KeepsCell I P body (.arr t) a xs) (env : Env TT Γ) (w : World TT)
    (hw : w.heap.get? (.arr t, a) = some xs) :
    exec (evalForOf I P a 0 body env) w = exec (forList I P body xs.toList env) w := by
  simpa using evalForOf_eq_forList_aux I P body a xs hk (xs.size - 0) 0 env w rfl hw

/-- A loop over a list whose body always completes normally is a left fold of the body's
effect on the environment and the world. -/
theorem forList_fold (I : Impl) (P : Program TT) {Γ : Ctx} {ρ t : Ty}
    (body : Block TT (⟨t, false⟩ :: Γ) ρ) (F : Val TT t → Env TT Γ × World TT → Env TT Γ × World TT)
    (hbody : ∀ x env w, ∃ env1, exec (evalB I P body (.cons x env)) w = some (.ok (.normal, env1), (F x (env, w)).2)
      ∧ env1.tail = (F x (env, w)).1) :
    ∀ (xs : List (Val TT t)) (env : Env TT Γ) (w : World TT),
      exec (forList I P body xs env) w =
        some (.ok (.normal, (xs.foldl (fun s x => F x s) (env, w)).1), (xs.foldl (fun s x => F x s) (env, w)).2) := by
  intro xs
  induction xs with
  | nil => intro env w; simp [forList]
  | cons x xs ih =>
    intro env w
    obtain ⟨env1, h1, h2⟩ := hbody x env w
    simp only [forList, exec_bind, h1]
    simp only [List.foldl_cons]
    rw [ih, h2]

/-- Loop invariant rule for `forList`: `Inv done env w` describes the state after the
elements `done` (a prefix of the list) have been processed. If the body preserves it and
completes normally, the whole loop completes normally in a state satisfying `Inv xs`. -/
theorem forList_inv (I : Impl) (P : Program TT) {Γ : Ctx} {ρ t : Ty}
    (body : Block TT (⟨t, false⟩ :: Γ) ρ) (Inv : List (Val TT t) → Env TT Γ → World TT → Prop)
    (xs : List (Val TT t))
    (hstep : ∀ done x env w, Inv done env w → ∃ env1 w1,
      exec (evalB I P body (.cons x env)) w = some (.ok (.normal, env1), w1) ∧ Inv (done ++ [x]) env1.tail w1) :
    ∀ (done : List (Val TT t)) (env : Env TT Γ) (w : World TT), Inv done env w →
      ∃ env' w', exec (forList I P body xs env) w = some (.ok (.normal, env'), w') ∧ Inv (done ++ xs) env' w' := by
  induction xs with
  | nil => intro done env w h; exact ⟨env, w, by simp [forList], by simpa using h⟩
  | cons x xs ih =>
    intro done env w h
    obtain ⟨env1, w1, h1, h2⟩ := hstep done x env w h
    obtain ⟨env', w', h3, h4⟩ := ih (done ++ [x]) env1.tail w1 h2
    refine ⟨env', w', ?_, by simpa using h4⟩
    simp only [forList, exec_bind, h1]
    exact h3

/-- Invariant rule for `for (const x of arr)` with an index-based invariant: `Inv i env w` holds
after `i` iterations and implies that the array still holds `xs` (the body may write any
other cell). The step obligation is stated in weakest-precondition form, so `simp [ts_sym]`
computes the body and leaves exactly the invariant to prove. -/
theorem evalForOf_inv (I : Impl) (P : Program TT) {Γ : Ctx} {ρ t : Ty}
    (body : Block TT (⟨t, false⟩ :: Γ) ρ) (a : Nat) (xs : Array (Val TT t))
    (Inv : Nat → Env TT Γ → World TT → Prop)
    (hcell : ∀ i env w, Inv i env w → w.heap.get? (.arr t, a) = some xs)
    (hstep : ∀ i env w (hi : i < xs.size), Inv i env w →
      match exec (evalB I P body (.cons xs[i] env)) w with
      | some (.ok (.normal, env1), w1) => Inv (i + 1) env1.tail w1
      | _ => False) :
    ∀ (n i : Nat) (env : Env TT Γ) (w : World TT), xs.size - i = n → i ≤ xs.size → Inv i env w →
      ∃ env' w', exec (evalForOf I P a i body env) w = some (.ok (.normal, env'), w') ∧ Inv xs.size env' w' := by
  intro n
  induction n with
  | zero =>
    intro i env w hn hle hinv
    have hi : i = xs.size := by omega
    subst hi
    refine ⟨env, w, ?_, hinv⟩
    rw [evalForOf.eq_1]
    simp [hcell _ _ _ hinv]
  | succ n ih =>
    intro i env w hn hle hinv
    have hlt : i < xs.size := by omega
    have hs := hstep i env w hlt hinv
    split at hs
    · next env1 w1 h1 =>
      obtain ⟨env', w', h3, h4⟩ := ih (i + 1) env1.tail w1 (by omega) (by omega) hs
      refine ⟨env', w', ?_, h4⟩
      rw [evalForOf.eq_1]
      simp only [exec_bind, exec_readArr, hcell _ _ _ hinv, hlt, dite_true, h1]
      exact h3
    · exact hs.elim

/-- Total-correctness rule for `while (c) body` / `for (; c; step) body`, with an invariant
`Inv`, a variant `V` (decreasing with every iteration) and an exit condition `Post` (to prove
when the loop condition is false), in weakest-precondition form. -/
theorem evalLoop_inv (I : Impl) (P : Program TT) {Γ : Ctx} {ρ : Ty} (c : Expr TT Γ .bool)
    (body step : Block TT Γ ρ) (Inv Post : Env TT Γ → World TT → Prop) (V : Env TT Γ → World TT → Nat)
    (hstep : ∀ env w, Inv env w →
      match exec (evalE I P c env) w with
      | some (.ok b, w₀) =>
        (b.toBool = false → Post env w₀) ∧
        (b.toBool = true →
          match exec (evalB I P body env) w₀ with
          | some (.ok (.normal, env1), w1) =>
            match exec (evalB I P step env1) w1 with
            | some (.ok (.normal, env2), w2) => Inv env2 w2 ∧ V env2 w2 < V env w
            | _ => False
          | _ => False)
      | _ => False) :
    ∀ (n : Nat) (env : Env TT Γ) (w : World TT), V env w = n → Inv env w →
      ∃ env' w', exec (evalLoop I P c body step env) w = some (.ok (.normal, env'), w') ∧ Post env' w' := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro env w hV hinv
    have hs := hstep env w hinv
    split at hs
    · next b w₀ hc =>
      obtain ⟨hf, ht⟩ := hs
      rw [evalLoop.eq_1]
      cases hb : b.toBool with
      | false =>
        refine ⟨env, w₀, ?_, hf hb⟩
        simp [hc, hb]
      | true =>
        have hs2 := ht hb
        split at hs2
        · next env1 w1 h1 =>
          split at hs2
          · next env2 w2 h2 =>
            obtain ⟨h3, h4⟩ := hs2
            obtain ⟨env', w', h5, h6⟩ := ih (V env2 w2) (by omega) env2 w2 rfl h3
            refine ⟨env', w', ?_, h6⟩
            simp only [exec_bind, exec_catchThrown, hc, hb, h1, h2, ite_true]
            exact h5
          · exact hs2.elim
        · exact hs2.elim
    · exact hs.elim

end StrictTS
