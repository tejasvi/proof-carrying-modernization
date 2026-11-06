/-
StrictTS proof layer: loops that may be left early, in partial correctness.

`evalLoop_partial` (`StrictTS.Proof.Partial`) needs every iteration to end normally. Real loops
leave early: `return` inside a search loop (`isPrime`), `throw`, `break`. `evalLoop_partial_exit`
allows those exits (into states satisfying `Exit`, with the loop's completion) and excludes only
panics; `evalLoop_cases_exit` states it as a case split on the run (it diverges, or it ends with
a completion and state satisfying `Exit`). `ts_auto` uses it for `JS.NoPanic`/`JS.NoFault` goals
with a `while` or counted `for` loop that no summary handles: if no iteration (from every
environment) panics or changes the world, the loop diverges or ends in the same world with a
completion a function body may end with (`Completion.exitOk`). The environments satisfy the
candidates about the slots that one iteration keeps (`Env.slotsOk`: kept values `KeptAt`, safe
naturals `NatAt`, counters running down `IntLeAt`). `evalForOf_partial_exit` /
`evalForOf_cases_exit` are the same for `for … of` over a live array (an iteration may also throw,
e.g. an external call).
-/
import StrictTS.Proof.Partial
import StrictTS.Proof.Summarize

namespace StrictTS
open Lean.Order JS

variable {TT : TypeTable}

/-- The completion of a loop that its body leaves with `cb` (anything but going on). -/
def Completion.loopExit {ρ : Ty} : Completion TT ρ → Completion TT ρ
  | .brk 0 => .normal
  | .brk (n + 1) => .brk n
  | .cont (n + 1) => .cont n
  | c => c

/-- **Partial-correctness rule with exits** for `while (c) body` / `for (; c; step) body`: as
`evalLoop_partial`, but an iteration may also leave the loop (`return`, `throw`, `break`, a
thrown condition), into a state that satisfies `Exit` with the loop's completion; only a panic
is excluded. Every run from an `Inv` state that terminates ends normally with a completion and
state satisfying `Exit`. -/
theorem evalLoop_partial_exit (I : Impl) (P : Program TT) {Γ : Ctx} {ρ : Ty} (c : Expr TT Γ .bool)
    (body step : Block TT Γ ρ) (Inv : Env TT Γ → World TT → Prop)
    (Exit : Completion TT ρ → Env TT Γ → World TT → Prop)
    (hstep : ∀ env w, Inv env w →
      match exec (evalE I P c env) w with
      | some (.ok b, w₀) =>
        (b.toBool = false → Exit .normal env w₀) ∧
        (b.toBool = true →
          match exec (evalB I P body env) w₀ with
          | some (.ok (cb, env1), w1) =>
            (cb.isNext = true →
              match exec (evalB I P step env1) w1 with
              | some (.ok (cs, env2), w2) => (cs = .normal → Inv env2 w2) ∧ (cs ≠ .normal → Exit cs env2 w2)
              | some (.error _, _) => False
              | none => True) ∧
            (cb.isNext = false → Exit cb.loopExit env1 w1)
          | some (.error _, _) => False
          | none => True)
      | some (.error (.thrown ex), w₀) => Exit (.exc ex) env w₀
      | some (.error (.panic _), _) => False
      | none => True) :
    ∀ env w, Inv env w → ∀ r w', exec (evalLoop I P c body step env) w = some (r, w') →
      ∃ cmp env', r = .ok (cmp, env') ∧ Exit cmp env' w' := by
  have key := interp_induct I P
    (fun x => ∀ env w, Inv env w → ∀ r w',
      exec (x.2.2.2.2.2.2.2.2.2.2.2.2.2.1 c body step env) w = some (r, w') →
      ∃ cmp env', r = .ok (cmp, env') ∧ Exit cmp env' w')
    (admissible_proj_loop _ (admissible_loop_pc c body step Inv _)) ?step
  · intro env w hinv r w' hrun
    rw [evalLoop_eq_proj] at hrun
    exact key env w hinv r w' hrun
  case step =>
    intro x hx ih env w hinv r w' hrun
    rw [interpStep_loop] at hrun
    have hE : ∀ {Γ : Ctx} {t : Ty} (e : Expr TT Γ t) (env : Env TT Γ) (w : World TT),
        exec (x.1 e env) w = none ∨ exec (x.1 e env) w = exec (evalE I P e env) w := by
      intro Γ t e env w
      rw [evalE_eq_proj]
      exact exec_le_cases (hx.1 Γ t e env) w
    have hB : ∀ {Γ : Ctx} {ρ : Ty} (b : Block TT Γ ρ) (env : Env TT Γ) (w : World TT),
        exec (x.2.2.2.2.2.2.2.2.1 b env) w = none ∨
          exec (x.2.2.2.2.2.2.2.2.1 b env) w = exec (evalB I P b env) w := by
      intro Γ ρ b env w
      rw [evalB_eq_proj]
      exact exec_le_cases (hx.2.2.2.2.2.2.2.2.1 Γ ρ b env) w
    have hs := hstep env w hinv
    simp only [evalLoopStep, exec_bind, exec_catchThrown] at hrun
    rcases hE c env w with h0 | h0
    · simp [h0] at hrun
    rw [h0] at hrun
    split at hs
    · next b w₀ hc =>
      rw [hc] at hrun
      simp only at hrun
      cases hb : b.toBool
      · simp only [hb, Bool.false_eq_true, ite_false, exec_pure, Option.some.injEq, Prod.mk.injEq] at hrun
        obtain ⟨rfl, rfl⟩ := hrun
        exact ⟨_, env, rfl, hs.1 hb⟩
      · simp only [hb, ite_true, exec_bind] at hrun
        have hs2 := hs.2 hb
        rcases hB body env w₀ with h1 | h1
        · simp [h1] at hrun
        rw [h1] at hrun
        split at hs2
        · next cb env1 w1 hb1 =>
          rw [hb1] at hrun
          simp only at hrun
          -- going on (the step, then the next iteration or an exit), or leaving the loop
          rcases cb with _ | ⟨_ | n⟩ | ⟨_ | n⟩ | v | p | ex <;>
            first
            | (have hs3 := hs2.1 rfl
               simp only [exec_bind] at hrun
               rcases hB step env1 w1 with h2 | h2
               · simp [h2] at hrun
               rw [h2] at hrun
               split at hs3
               · next cs env2 w2 hs1 =>
                 rw [hs1] at hrun
                 rcases cs with _ | _ | _ | _ | _ | _ <;> simp only at hrun
                 · exact ih env2 w2 (hs3.1 rfl) r w' hrun
                 all_goals
                   (simp only [exec_pure, Option.some.injEq, Prod.mk.injEq] at hrun
                    obtain ⟨rfl, rfl⟩ := hrun
                    exact ⟨_, _, rfl, hs3.2 (by intro h; cases h)⟩)
               · exact hs3.elim
               · next hnone => simp [hnone] at hrun)
            | (simp only [exec_pure, Option.some.injEq, Prod.mk.injEq] at hrun
               obtain ⟨rfl, rfl⟩ := hrun
               exact ⟨_, _, rfl, hs2.2 rfl⟩)
        · exact hs2.elim
        · next hnone => simp [hnone] at hrun
    · next ex w₀ hc =>
      rw [hc] at hrun
      simp only [exec_pure, Option.some.injEq, Prod.mk.injEq] at hrun
      obtain ⟨rfl, rfl⟩ := hrun
      exact ⟨_, env, rfl, hs⟩
    · exact hs.elim
    · next hnone => simp [hnone] at hrun


/-- `evalLoop_partial_exit` as a case split on the run: the loop diverges, or it ends normally with
a completion and state satisfying `Exit`. -/
theorem evalLoop_cases_exit (I : Impl) (P : Program TT) {Γ : Ctx} {ρ : Ty} (c : Expr TT Γ .bool)
    (body step : Block TT Γ ρ) (Inv : Env TT Γ → World TT → Prop)
    (Exit : Completion TT ρ → Env TT Γ → World TT → Prop)
    (hstep : ∀ env w, Inv env w →
      match exec (evalE I P c env) w with
      | some (.ok b, w₀) =>
        (b.toBool = false → Exit .normal env w₀) ∧
        (b.toBool = true →
          match exec (evalB I P body env) w₀ with
          | some (.ok (cb, env1), w1) =>
            (cb.isNext = true →
              match exec (evalB I P step env1) w1 with
              | some (.ok (cs, env2), w2) => (cs = .normal → Inv env2 w2) ∧ (cs ≠ .normal → Exit cs env2 w2)
              | some (.error _, _) => False
              | none => True) ∧
            (cb.isNext = false → Exit cb.loopExit env1 w1)
          | some (.error _, _) => False
          | none => True)
      | some (.error (.thrown ex), w₀) => Exit (.exc ex) env w₀
      | some (.error (.panic _), _) => False
      | none => True)
    (env : Env TT Γ) (w : World TT) (hinv : Inv env w) :
    exec (evalLoop I P c body step env) w = none ∨
      ∃ cmp env' w', exec (evalLoop I P c body step env) w = some (.ok (cmp, env'), w') ∧
        Exit cmp env' w' := by
  rcases h : exec (evalLoop I P c body step env) w with _ | ⟨r, w'⟩
  · exact .inl rfl
  · obtain ⟨cmp, env', rfl, hx⟩ := evalLoop_partial_exit I P c body step Inv Exit hstep env w hinv r w' h
    exact .inr ⟨cmp, env', w', rfl, hx⟩

/-- The completion of a `for … of` loop that its body leaves with `cb` (anything but going on). -/
def Completion.forOfExit {ρ : Ty} : Completion TT ρ → Completion TT ρ
  | .brk 0 => .normal
  | .brk (n + 1) => .brk n
  | .cont (n + 1) => .cont n
  | c => c

@[simp] theorem Completion.forOfExit_ret {ρ : Ty} (v : Val TT ρ) : (Completion.ret v).forOfExit = .ret v := rfl
@[simp] theorem Completion.forOfExit_exc {ρ : Ty} (e : ErrVal) :
    (Completion.exc e : Completion TT ρ).forOfExit = .exc e := rfl
@[simp] theorem Completion.forOfExit_retP {ρ : Ty} (p : Nat) :
    (Completion.retP p : Completion TT ρ).forOfExit = .retP p := rfl
@[simp] theorem Completion.forOfExit_brk0 {ρ : Ty} : (Completion.brk 0 : Completion TT ρ).forOfExit = .normal := rfl
@[simp] theorem Completion.forOfExit_brk {ρ : Ty} (n : Nat) :
    (Completion.brk (n + 1) : Completion TT ρ).forOfExit = .brk n := rfl
@[simp] theorem Completion.forOfExit_cont {ρ : Ty} (n : Nat) :
    (Completion.cont (n + 1) : Completion TT ρ).forOfExit = .cont n := rfl

/-- **Partial-correctness rule with exits** for `for (const x of arr)` over a live array: as
`evalForOf_partial`, but an iteration may also leave the loop (`return`, `break`, an exception
thrown by its code, e.g. by an external call), into an outcome satisfying `Exit`; only a panic is
excluded. Every run from an `Inv` state that terminates has an outcome satisfying `Exit`. -/
theorem evalForOf_partial_exit (I : Impl) (P : Program TT) {Γ : Ctx} {ρ t : Ty} (a : Nat)
    (body : Block TT (⟨t, false⟩ :: Γ) ρ) (Inv : Nat → Env TT Γ → World TT → Prop)
    (Exit : Except Exc (Completion TT ρ × Env TT Γ) → World TT → Prop)
    (hstep : ∀ i env w, Inv i env w →
      match w.heap.get? (.arr t, a) with
      | some xs =>
        (xs.size ≤ i → Exit (.ok (.normal, env)) w) ∧
        (∀ h : i < xs.size,
          match exec (evalB I P body (.cons xs[i] env)) w with
          | some (.ok (cb, env1), w1) =>
            (cb.isNext = true → Inv (i + 1) env1.tail w1) ∧
            (cb.isNext = false → Exit (.ok (cb.forOfExit, env1.tail)) w1)
          | some (.error (.thrown e), w1) => Exit (.error (.thrown e)) w1
          | some (.error (.panic _), _) => False
          | none => True)
      | none => False) :
    ∀ i env w, Inv i env w → ∀ r w', exec (evalForOf I P a i body env) w = some (r, w') → Exit r w' := by
  have key := interp_induct I P
    (fun x => ∀ i env w, Inv i env w → ∀ r w',
      exec (x.2.2.2.2.2.2.2.2.2.2.2.1 a i body env) w = some (r, w') → Exit r w')
    (admissible_proj_forOf _ (admissible_forOf_pc a body Inv _)) ?step
  · intro i env w hinv r w' hrun
    rw [evalForOf_eq_proj] at hrun
    exact key i env w hinv r w' hrun
  case step =>
    intro x hx ih i env w hinv r w' hrun
    rw [interpStep_forOf] at hrun
    have hB : ∀ {Γ : Ctx} {ρ : Ty} (b : Block TT Γ ρ) (env : Env TT Γ) (w : World TT),
        exec (x.2.2.2.2.2.2.2.2.1 b env) w = none ∨
          exec (x.2.2.2.2.2.2.2.2.1 b env) w = exec (evalB I P b env) w := by
      intro Γ ρ b env w
      rw [evalB_eq_proj]
      exact exec_le_cases (hx.2.2.2.2.2.2.2.2.1 Γ ρ b env) w
    have hs := hstep i env w hinv
    simp only [evalForOfStep, exec_bind, exec_readArr] at hrun
    split at hs
    · next xs hxs =>
      rw [hxs] at hrun
      simp only at hrun
      by_cases hi : i < xs.size
      · simp only [hi, dite_true, exec_bind] at hrun
        have hs2 := hs.2 hi
        rcases hB body (.cons xs[i] env) w with h1 | h1
        · simp [h1] at hrun
        rw [h1] at hrun
        split at hs2
        · next cb env1 w1 hb1 =>
          rw [hb1] at hrun
          simp only at hrun
          rcases cb with _ | ⟨_ | n⟩ | ⟨_ | n⟩ | v | p | ex <;> simp only at hrun
          · exact ih (i + 1) env1.tail w1 (hs2.1 rfl) r w' hrun
          all_goals first
            | exact ih (i + 1) env1.tail w1 (hs2.1 rfl) r w' hrun
            | (simp only [exec_pure, Option.some.injEq, Prod.mk.injEq] at hrun
               obtain ⟨rfl, rfl⟩ := hrun
               exact hs2.2 rfl)
        · next e w1 hb1 =>
          rw [hb1] at hrun
          simp only [Option.some.injEq, Prod.mk.injEq] at hrun
          obtain ⟨rfl, rfl⟩ := hrun
          exact hs2
        · exact hs2.elim
        · next hnone => simp [hnone] at hrun
      · simp only [hi, dite_false, exec_pure, Option.some.injEq, Prod.mk.injEq] at hrun
        obtain ⟨rfl, rfl⟩ := hrun
        exact hs.1 (by omega)
    · exact hs.elim

/-- `evalForOf_partial_exit` as a case split on the run: the loop diverges, or it ends with an
outcome satisfying `Exit`. -/
theorem evalForOf_cases_exit (I : Impl) (P : Program TT) {Γ : Ctx} {ρ t : Ty} (a : Nat)
    (body : Block TT (⟨t, false⟩ :: Γ) ρ) (Inv : Nat → Env TT Γ → World TT → Prop)
    (Exit : Except Exc (Completion TT ρ × Env TT Γ) → World TT → Prop)
    (hstep : ∀ i env w, Inv i env w →
      match w.heap.get? (.arr t, a) with
      | some xs =>
        (xs.size ≤ i → Exit (.ok (.normal, env)) w) ∧
        (∀ h : i < xs.size,
          match exec (evalB I P body (.cons xs[i] env)) w with
          | some (.ok (cb, env1), w1) =>
            (cb.isNext = true → Inv (i + 1) env1.tail w1) ∧
            (cb.isNext = false → Exit (.ok (cb.forOfExit, env1.tail)) w1)
          | some (.error (.thrown e), w1) => Exit (.error (.thrown e)) w1
          | some (.error (.panic _), _) => False
          | none => True)
      | none => False)
    (i : Nat) (env : Env TT Γ) (w : World TT) (hinv : Inv i env w) :
    exec (evalForOf I P a i body env) w = none ∨
      ∃ r w', exec (evalForOf I P a i body env) w = some (r, w') ∧ Exit r w' := by
  rcases h : exec (evalForOf I P a i body env) w with _ | ⟨r, w'⟩
  · exact .inl rfl
  · exact .inr ⟨r, w', rfl, evalForOf_partial_exit I P a body Inv Exit hstep i env w hinv r w' h⟩

/-- Completions a function body may end with after a loop: `.ret v`; `.normal` if `normalOk`
(not after `while (true)`), `.exc e` if `excOk` (an iteration may throw); never a `break` or
`continue` escape. -/
def Completion.exitOk {ρ : Ty} (normalOk excOk : Bool) : Completion TT ρ → Bool
  | .normal => normalOk
  | .ret _ => true
  | .exc _ => excOk
  | _ => false

@[simp] theorem Completion.exitOk_normal {ρ : Ty} (n e : Bool) :
    (Completion.normal : Completion TT ρ).exitOk n e = n := rfl
@[simp] theorem Completion.exitOk_ret {ρ : Ty} (n e : Bool) (v : Val TT ρ) : (Completion.ret v).exitOk n e = true := rfl
@[simp] theorem Completion.exitOk_exc {ρ : Ty} (n e : Bool) (x : ErrVal) :
    (Completion.exc x : Completion TT ρ).exitOk n e = e := rfl
@[simp] theorem Completion.exitOk_brk {ρ : Ty} (n e : Bool) (k : Nat) :
    (Completion.brk k : Completion TT ρ).exitOk n e = false := rfl
@[simp] theorem Completion.exitOk_cont {ρ : Ty} (n e : Bool) (k : Nat) :
    (Completion.cont k : Completion TT ρ).exitOk n e = false := rfl
@[simp] theorem Completion.exitOk_retP {ρ : Ty} (n e : Bool) (p : Nat) :
    (Completion.retP p : Completion TT ρ).exitOk n e = false := rfl
@[simp] theorem Completion.loopExit_ret {ρ : Ty} (v : Val TT ρ) : (Completion.ret v).loopExit = .ret v := rfl
@[simp] theorem Completion.loopExit_exc {ρ : Ty} (e : ErrVal) :
    (Completion.exc e : Completion TT ρ).loopExit = .exc e := rfl
@[simp] theorem Completion.loopExit_brk0 {ρ : Ty} : (Completion.brk 0 : Completion TT ρ).loopExit = .normal := rfl
@[simp] theorem Completion.isNext_ret {ρ : Ty} (v : Val TT ρ) : (Completion.ret v).isNext = false := rfl
@[simp] theorem Completion.isNext_exc {ρ : Ty} (e : ErrVal) : (Completion.exc e : Completion TT ρ).isNext = false := rfl
@[simp] theorem Completion.isNext_brk {ρ : Ty} (n : Nat) : (Completion.brk n : Completion TT ρ).isNext = false := rfl

/-- Whether the code after a loop runs on its completion (`.normal`): only then does the loop's
final world matter to a function body; `return` and `throw` leave the function. -/
def Completion.isNormal {ρ : Ty} : Completion TT ρ → Bool
  | .normal => true
  | _ => false

@[simp] theorem Completion.isNormal_normal {ρ : Ty} : (Completion.normal : Completion TT ρ).isNormal = true := rfl
@[simp] theorem Completion.isNormal_ret {ρ : Ty} (v : Val TT ρ) : (Completion.ret v).isNormal = false := rfl
@[simp] theorem Completion.isNormal_exc {ρ : Ty} (x : ErrVal) : (Completion.exc x : Completion TT ρ).isNormal = false :=
  rfl
@[simp] theorem Completion.isNormal_brk {ρ : Ty} (k : Nat) : (Completion.brk k : Completion TT ρ).isNormal = false := rfl
@[simp] theorem Completion.isNormal_cont {ρ : Ty} (k : Nat) : (Completion.cont k : Completion TT ρ).isNormal = false :=
  rfl
@[simp] theorem Completion.isNormal_retP {ρ : Ty} (p : Nat) : (Completion.retP p : Completion TT ρ).isNormal = false :=
  rfl

/-- `e1` and `e2` hold the same values in their `const` slots (a loop's iterations keep them). -/
def Env.sameConsts : {Γ : Ctx} → Env TT Γ → Env TT Γ → Prop
  | [], _, _ => True
  | s :: _, .cons v1 r1, .cons v2 r2 => (s.mutable = false → v1 = v2) ∧ Env.sameConsts r1 r2

@[simp] theorem Env.sameConsts_nil (e1 e2 : Env TT []) : Env.sameConsts e1 e2 ↔ True := by
  simp [Env.sameConsts]

@[simp] theorem Env.sameConsts_cons {s : Slot} {Γ : Ctx} (v1 v2 : Val TT s.ty) (r1 r2 : Env TT Γ) :
    Env.sameConsts (.cons v1 r1) (.cons v2 r2) ↔ (s.mutable = false → v1 = v2) ∧ Env.sameConsts r1 r2 :=
  Iff.rfl

/-! Candidate invariants about single slots. `ts_auto`'s fallback proposes some for each loop
(`Env.slotsOk`), checks them by one symbolic iteration and drops the ones that fail,
Houdini-style. The slot's position `p` is an argument only so that a failing candidate names its
slot; both predicates are irreducible, so tactics keep them as they are until a lemma below
applies. -/

/-- Slot `p` keeps the value `v₀` it had at the loop's start. -/
def KeptAt (_p : Nat) {t : Ty} (v v₀ : Val TT t) : Prop := v = v₀

/-- A natural number below `2 ^ 53` (exact as a double); no condition on other types. -/
def Val.isSafeNat : {t : Ty} → Val TT t → Prop
  | .num, .num x => ∃ k : Nat, x = F64.ofNat k ∧ k < 2 ^ 53
  | _, _ => True

/-- Slot `p` holds a natural number below `2 ^ 53` (a counter that stays a valid index). -/
def NatAt (_p : Nat) {t : Ty} (v : Val TT t) : Prop := v.isSafeNat

theorem keptAt_iff (p : Nat) {t : Ty} (v v₀ : Val TT t) : KeptAt p v v₀ ↔ v = v₀ := Iff.rfl

@[simp] theorem keptAt_self (p : Nat) {t : Ty} (v : Val TT t) : KeptAt p v v ↔ True :=
  iff_true_intro rfl

theorem natAt_num_iff (p : Nat) (x : F64) :
    NatAt p (.num x : Val TT .num) ↔ ∃ k : Nat, x = F64.ofNat k ∧ k < 2 ^ 53 := Iff.rfl

theorem natAt_ofNat (p : Nat) {k : Nat} (h : k < 2 ^ 53) : NatAt p (.num (F64.ofNat k) : Val TT .num) :=
  ⟨k, rfl, h⟩

theorem natAt_add_ofNat (p : Nat) {a b : Nat} (h : a + b < 2 ^ 53) :
    NatAt p (.num (F64.ofNat a + F64.ofNat b) : Val TT .num) :=
  ⟨a + b, ofNat_add_ofNat (by omega), h⟩

theorem natAt_sub_ofNat (p : Nat) {a b : Nat} (ha : a < 2 ^ 53) (hb : b ≤ a) :
    NatAt p (.num (F64.ofNat a - F64.ofNat b) : Val TT .num) :=
  ⟨a - b, ofNat_sub_ofNat (by omega) hb, by omega⟩

/-- An integer between `-1` and `b`, with `b < 2 ^ 53` (exact as a double); no condition on other
types. -/
def Val.intLe : {t : Ty} → Val TT t → Int → Prop
  | .num, .num x, b => ∃ z : Int, x = F64.ofInt z ∧ -1 ≤ z ∧ z ≤ b ∧ b < 2 ^ 53
  | _, _, _ => True

/-- Slot `p` holds an integer between `-1` and `b` (a counter running down from `b`, e.g.
`for (let i = xs.length - 1; i >= 0; i--)`). -/
def IntLeAt (_p : Nat) {t : Ty} (v : Val TT t) (b : Int) : Prop := v.intLe b

theorem intLeAt_num_iff (p : Nat) (x : F64) (b : Int) :
    IntLeAt p (.num x : Val TT .num) b ↔ ∃ z : Int, x = F64.ofInt z ∧ -1 ≤ z ∧ z ≤ b ∧ b < 2 ^ 53 := Iff.rfl

theorem intLeAt_ofInt (p : Nat) {z b : Int} (h1 : -1 ≤ z) (h2 : z ≤ b) (h3 : b < 2 ^ 53) :
    IntLeAt p (.num (F64.ofInt z) : Val TT .num) b :=
  ⟨z, rfl, h1, h2, h3⟩

theorem intLeAt_ofInt_sub_ofNat (p : Nat) {z b : Int} {c : Nat} (hc : c ≤ 2 ^ 53) (hz : -2 ^ 53 ≤ z)
    (hz2 : z ≤ 2 ^ 53) (h1 : -1 ≤ z - c) (h2 : z - c ≤ b) (h3 : b < 2 ^ 53) :
    IntLeAt p (.num (F64.ofInt z - F64.ofNat c) : Val TT .num) b := by
  refine ⟨z - c, ?_, h1, h2, h3⟩
  rw [F64.ofNat_eq_ofInt, F64.sub_ofInt (by simp only [F64.Safe]; omega) (by simp only [F64.Safe]; omega)
    (by simp only [F64.Safe]; omega)]

theorem intLeAt_ofNat_sub_ofNat (p : Nat) {a c : Nat} {b : Int} (ha : a ≤ 2 ^ 53) (hc : c ≤ 2 ^ 53)
    (h1 : -1 ≤ (a : Int) - c) (h2 : (a : Int) - c ≤ b) (h3 : b < 2 ^ 53) :
    IntLeAt p (.num (F64.ofNat a - F64.ofNat c) : Val TT .num) b :=
  ⟨(a : Int) - c, ofNat_sub_ofNat_int ha hc, h1, h2, h3⟩

theorem intLeAt_ofNat (p : Nat) {a : Nat} {b : Int} (h2 : (a : Int) ≤ b) (h3 : b < 2 ^ 53) :
    IntLeAt p (.num (F64.ofNat a) : Val TT .num) b :=
  ⟨a, F64.ofNat_eq_ofInt a, by omega, h2, h3⟩

/-- The candidates `ms` hold of `e` (one per slot from position `p` on, a mode and a bound: `1` the
slot is kept, `2` it holds a safe natural, `3` an integer between `-1` and the bound; anything else
or a missing candidate: nothing), and `e`'s `const` slots hold `e₀`'s values. -/
def Env.slotsOk : {Γ : Ctx} → Nat → List (Nat × Int) → Env TT Γ → Env TT Γ → Prop
  | [], _, _, _, _ => True
  | s :: _, p, ms, .cons v r, .cons v₀ r₀ =>
    (s.mutable = false → v = v₀) ∧ ((ms.headD (0, 0)).1 = 1 → KeptAt p v v₀) ∧
      ((ms.headD (0, 0)).1 = 2 → NatAt p v) ∧ ((ms.headD (0, 0)).1 = 3 → IntLeAt p v (ms.headD (0, 0)).2) ∧
      Env.slotsOk (p + 1) ms.tail r r₀

@[simp] theorem Env.slotsOk_nil (p : Nat) (ms : List (Nat × Int)) (e e₀ : Env TT []) :
    Env.slotsOk p ms e e₀ ↔ True := by
  simp [Env.slotsOk]

@[simp] theorem Env.slotsOk_cons {s : Slot} {Γ : Ctx} (p : Nat) (ms : List (Nat × Int)) (v v₀ : Val TT s.ty)
    (r r₀ : Env TT Γ) :
    Env.slotsOk p ms (.cons v r) (.cons v₀ r₀) ↔ (s.mutable = false → v = v₀) ∧
      ((ms.headD (0, 0)).1 = 1 → KeptAt p v v₀) ∧ ((ms.headD (0, 0)).1 = 2 → NatAt p v) ∧
      ((ms.headD (0, 0)).1 = 3 → IntLeAt p v (ms.headD (0, 0)).2) ∧ Env.slotsOk (p + 1) ms.tail r r₀ :=
  Iff.rfl

/-- No candidates: only the `const` slots, which an environment shares with itself. -/
@[simp] theorem Env.slotsOk_nil_refl : {Γ : Ctx} → (p : Nat) → (e : Env TT Γ) → (Env.slotsOk p [] e e ↔ True)
  | [], p, e => by simp
  | _ :: Γ, p, .cons v r => by simp [Env.slotsOk_nil_refl (Γ := Γ) (p + 1) r]

attribute [irreducible] KeptAt NatAt IntLeAt

/-- A world that differs from `w` at most in the content of the cell `K` is `w` with `K`
rewritten (the state of a loop that writes one cell, e.g. a `Set` it fills). -/
@[simp] theorem exists_insert_eq_insert (h : Heap TT) (K : HKey) (c1 : K.1.Cell TT) :
    (∃ c, Std.ExtDHashMap.insert h K c1 = Std.ExtDHashMap.insert h K c) ↔ True :=
  ⟨fun _ => trivial, fun _ => ⟨c1, rfl⟩⟩

end StrictTS
