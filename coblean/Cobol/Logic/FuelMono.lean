/-
# Fuel monotonicity

More fuel never changes a real outcome: if a run with fuel `n` ends with any signal but
`outOfFuel`, a run with any fuel `n' ≥ n` ends with the same signal and state
(`Program.run_mono`). So a theorem proved for one sufficient fuel holds for every larger fuel,
and statements need not match a particular fuel form such as `n + 60`. `tests/FuelMonoUse.lean`
restates `cbcus01c_lists` (fuel `n + 20` for any `n > recs.length`) for every fuel
`F ≥ recs.length + 21`: with `h` the theorem at `n := recs.length + 1`,
`Program.run_mono _ _ (by omega) (by rw [h.1]; decide)` turns the run at `F` into the theorem's.

`ResLe r r'`: `r` ran out of fuel, or `r' = r`. Every construct of the semantics passes
`outOfFuel` through unchanged, which is what makes the relation propagate. The proof covers
every statement (loops, `PERFORM`, `SEARCH`, linked `CALL`), paragraph transitions and `GO TO`.
-/
import Cobol.Sem.Exec

namespace Cobol
namespace Sem

/-- `r'` agrees with `r` unless `r` ran out of fuel. -/
def ResLe (r r' : Res) : Prop := r.1 = .outOfFuel ∨ r' = r

/-- `ResLe` pointwise. -/
def FnLe (f g : State → Res) : Prop := ∀ st, ResLe (f st) (g st)

/-- `ResLe` pointwise, for paragraph runners. -/
def RecLe (rec rec' : Nat → State → Res) : Prop := ∀ k st, ResLe (rec k st) (rec' k st)

theorem ResLe.refl (r : Res) : ResLe r r := Or.inr rfl

theorem FnLe.refl (f : State → Res) : FnLe f f := fun _ => ResLe.refl _

theorem ResLe.real {r r' : Res} (h : ResLe r r') (hr : r.1 ≠ .outOfFuel) : r' = r :=
  h.resolve_left hr

/-- The left side matched on a sub-result that ran out of fuel: it passes `outOfFuel` on. -/
macro "res_oof " h:ident e:term : tactic =>
  `(tactic| (left; generalize $e = r at $h:ident ⊢; obtain ⟨sig, _⟩ := r;
             simp only at $h:ident; subst $h:ident; rfl))

/-- Both sides match on the same sub-result `e`: split on its signal. -/
macro "res_split " e:term : tactic =>
  `(tactic| (generalize $e = r; obtain ⟨sig, _⟩ := r; cases sig))

theorem loopTimes_mono {body body' : State → Res} (hb : FnLe body body') :
    ∀ (k : Nat) (st : State), ResLe (loopTimes body k st) (loopTimes body' k st)
  | 0, st => ResLe.refl _
  | k + 1, st => by
    simp only [loopTimes]
    rcases hb st with h | h
    · res_oof h (body st)
    · rw [h]
      res_split (body st)
      all_goals first | exact ResLe.refl _ | exact loopTimes_mono hb k _

theorem loopUntil_mono (ta : Bool) (cond : State → SemM Bool) {body body' step step' : State → Res}
    (hb : FnLe body body') (hs : FnLe step step') :
    ∀ (n n' : Nat) (st : State), n ≤ n' →
      ResLe (loopUntil ta cond body step n st) (loopUntil ta cond body' step' n' st)
  | 0, _, st, _ => by simp only [loopUntil]; left; rfl
  | n + 1, 0, _, h => absurd h (by omega)
  | n + 1, n' + 1, st, h => by
    have ih : ∀ st, ResLe (loopUntil ta cond body step n st) (loopUntil ta cond body' step' n' st) :=
      fun st => loopUntil_mono ta cond hb hs n n' st (by omega)
    -- after the body (and the test, when it comes after): the step, then the next iteration
    have hstep : ∀ st1, ResLe
        (match step st1 with
          | (.normal, st2) => loopUntil ta cond body step n st2
          | r => r)
        (match step' st1 with
          | (.normal, st2) => loopUntil ta cond body' step' n' st2
          | r => r) := by
      intro st1
      rcases hs st1 with h2 | h2
      · res_oof h2 (step st1)
      · rw [h2]
        res_split (step st1)
        all_goals first | exact ResLe.refl _ | exact ih _
    simp only [loopUntil]
    cases ta
    · simp only [Bool.false_eq_true, ↓reduceIte]
      cases cond st with
      | error f => exact ResLe.refl _
      | ok b =>
        cases b
        · simp only
          rcases hb st with h | h
          · res_oof h (body st)
          · rw [h]
            res_split (body st)
            all_goals first | exact ResLe.refl _ | exact hstep _
        · exact ResLe.refl _
    · simp only [↓reduceIte]
      rcases hb st with h | h
      · res_oof h (body st)
      · rw [h]
        res_split (body st)
        all_goals try exact ResLe.refl _
        all_goals
          simp only
          generalize cond _ = c
          cases c with
          | error f => exact ResLe.refl _
          | ok b => cases b <;> first | exact ResLe.refl _ | exact hstep _
termination_by n => n

theorem performOnce_mono {rec rec' : Nat → State → Res} (hr : RecLe rec rec') (id first : Nat)
    (exit : ExitPt) : FnLe (performOnce rec id first exit) (performOnce rec' id first exit) := by
  intro st
  simp only [performOnce]
  split
  · exact ResLe.refl _
  · rcases hr first _ with h | h
    · res_oof h (rec first _)
    · rw [h]; exact ResLe.refl _

/-- The `USE` declarative of an I/O error runs as an out-of-line `PERFORM`. -/
theorem ioErr_mono (P : Program) {rec rec' : Nat → State → Res} (hr : RecLe rec rec')
    (d : FileDecl) (mode : Option OpenMode) (st : State) (dflt : Res) :
    ResLe (ioErr P rec d mode st dflt) (ioErr P rec' d mode st dflt) := by
  simp only [ioErr]
  split
  · exact ResLe.refl _
  · exact performOnce_mono hr _ _ _ st

theorem ioFinishU_mono (P : Program) {rec rec' : Nat → State → Res} (hr : RecLe rec rec')
    (d : FileDecl) (mode : Option OpenMode) (code : Nat) (nx : IoNext) (st : State) :
    ResLe (ioFinishU P rec d mode code nx st) (ioFinishU P rec' d mode code nx st) := by
  simp only [ioFinishU]
  split
  · exact ioErr_mono P hr d mode st _
  · exact ioErr_mono P hr d mode st _
  · exact ResLe.refl _

theorem searchLoop_mono (over : State → SemM Bool) {whens whens' : (State → Res) → State → Res}
    {atEnd atEnd' bump bump' : State → Res}
    (hw : ∀ k k', FnLe k k' → FnLe (whens k) (whens' k'))
    (ha : FnLe atEnd atEnd') (hb : FnLe bump bump') :
    ∀ (n n' : Nat) (st : State), n ≤ n' →
      ResLe (searchLoop over whens atEnd bump n st) (searchLoop over whens' atEnd' bump' n' st)
  | 0, _, st, _ => by simp only [searchLoop]; left; rfl
  | n + 1, 0, _, h => absurd h (by omega)
  | n + 1, n' + 1, st, h => by
    simp only [searchLoop]
    cases over st with
    | error f => exact ResLe.refl _
    | ok b =>
      cases b
      · simp only [Bool.false_eq_true, ↓reduceIte]
        refine hw _ _ ?_ st
        intro st1
        dsimp only
        rcases hb st1 with h2 | h2
        · res_oof h2 (bump st1)
        · rw [h2]
          res_split (bump st1)
          all_goals first
            | exact ResLe.refl _
            | exact searchLoop_mono over hw ha hb n n' _ (by omega)
      · simp only [↓reduceIte]; exact ha st
termination_by n => n

mutual

theorem execStmt_mono (P : Program) (env : Env) {rec rec' : Nat → State → Res} {fuel fuel' : Nat}
    (hr : RecLe rec rec') (hf : fuel ≤ fuel') :
    ∀ (s : Stmt) (st : State), ResLe (execStmt P env rec fuel s st) (execStmt P env rec' fuel' s st)
  | .perform id first exit, st => by
    simp only [execStmt]; exact performOnce_mono hr id first exit st
  | .performTimes id n first exit, st => by
    simp only [execStmt]
    split
    · exact ResLe.refl _
    · exact loopTimes_mono (performOnce_mono hr id first exit) _ st
  | .performUntil id ta c first exit, st => by
    simp only [execStmt]
    exact loopUntil_mono ta _ (performOnce_mono hr id first exit) (FnLe.refl _) fuel fuel' st hf
  | .performVarying id ta init c step first exit, st => by
    simp only [execStmt]
    rcases execStmts_mono P env hr hf init st with h | h
    · res_oof h (execStmts P env rec fuel init st)
    · rw [h]
      res_split (execStmts P env rec fuel init st)
      all_goals first
        | exact ResLe.refl _
        | exact loopUntil_mono ta _ (performOnce_mono hr id first exit)
            (fun st => execStmts_mono P env hr hf step st) fuel fuel' _ hf
  | .block body, st => by
    simp only [execStmt]; exact execStmts_mono P env hr hf body st
  | .inlineTimes n body, st => by
    simp only [execStmt]
    split
    · exact ResLe.refl _
    · exact loopTimes_mono (fun st => execStmts_mono P env hr hf body st) _ st
  | .inlineUntil ta c body, st => by
    simp only [execStmt]
    exact loopUntil_mono ta _ (fun st => execStmts_mono P env hr hf body st) (FnLe.refl _)
      fuel fuel' st hf
  | .inlineVarying ta init c step body, st => by
    simp only [execStmt]
    rcases execStmts_mono P env hr hf init st with h | h
    · res_oof h (execStmts P env rec fuel init st)
    · rw [h]
      res_split (execStmts P env rec fuel init st)
      all_goals first
        | exact ResLe.refl _
        | exact loopUntil_mono ta _ (fun st => execStmts_mono P env hr hf body st)
            (fun st => execStmts_mono P env hr hf step st) fuel fuel' _ hf
  | .search over conds bodies bump atEnd, st => by
    simp only [execStmt]
    exact searchLoop_mono _ (fun _ _ hk => execWhens_mono P env hr hf conds bodies hk)
      (fun st => execStmts_mono P env hr hf atEnd st) (fun st => execStmts_mono P env hr hf bump st)
      fuel fuel' st hf
  | .callLocal para binds, st => by
    simp only [execStmt]
    split
    · exact ResLe.refl _
    · rcases hr para _ with h | h
      · res_oof h (rec para _)
      · rw [h]; exact ResLe.refl _
  -- the other statements: pure computations, then at most a branch of statements
  | .arith op rcv trap onSize notOnSize, st => by
    simp only [execStmt]
    repeat' (first | exact ResLe.refl _ | exact execStmts_mono P env hr hf onSize _ | exact execStmts_mono P env hr hf notOnSize _ | split)
  | .divRem a b q r trap onSize notOnSize, st => by
    simp only [execStmt]
    repeat' (first | exact ResLe.refl _ | exact execStmts_mono P env hr hf onSize _ | exact execStmts_mono P env hr hf notOnSize _ | split)
  | .ite c t e, st => by
    simp only [execStmt]
    repeat' (first | exact ResLe.refl _ | exact execStmts_mono P env hr hf t _ | exact execStmts_mono P env hr hf e _ | split)
  | .read file recd into atEnd notAtEnd, st => by
    simp only [execStmt]
    repeat' (first | exact ResLe.refl _ | exact execStmts_mono P env hr hf atEnd _ | exact execStmts_mono P env hr hf notAtEnd _ | split)
  | .fread file key into trap exc noExc, st => by
    simp only [execStmt]
    repeat' (first | exact ResLe.refl _ | exact execStmts_mono P env hr hf exc _ | exact execStmts_mono P env hr hf noExc _ | exact ioErr_mono P hr _ _ _ _ | split)
  | .fwrite file recd trap exc noExc, st => by
    simp only [execStmt]
    repeat' (first | exact ResLe.refl _ | exact execStmts_mono P env hr hf exc _ | exact execStmts_mono P env hr hf noExc _ | exact ioErr_mono P hr _ _ _ _ | split)
  | .frewrite file recd trap exc noExc, st => by
    simp only [execStmt]
    repeat' (first | exact ResLe.refl _ | exact execStmts_mono P env hr hf exc _ | exact execStmts_mono P env hr hf noExc _ | exact ioErr_mono P hr _ _ _ _ | split)
  | .fdelete file trap exc noExc, st => by
    simp only [execStmt]
    repeat' (first | exact ResLe.refl _ | exact execStmts_mono P env hr hf exc _ | exact execStmts_mono P env hr hf noExc _ | exact ioErr_mono P hr _ _ _ _ | split)
  | .fstart file op key trap exc noExc, st => by
    simp only [execStmt]
    repeat' (first | exact ResLe.refl _ | exact execStmts_mono P env hr hf exc _ | exact execStmts_mono P env hr hf noExc _ | exact ioErr_mono P hr _ _ _ _ | split)
  | .searchAll i n keys c body atEnd, st => by
    simp only [execStmt]
    repeat' (first | exact ResLe.refl _ | exact execStmts_mono P env hr hf body _ | exact execStmts_mono P env hr hf atEnd _ | split)
  | .unstring src delims into ptr tally trap ovf notOvf, st => by
    simp only [execStmt]
    repeat' (first | exact ResLe.refl _ | exact execStmts_mono P env hr hf ovf _ | exact execStmts_mono P env hr hf notOvf _ | split)
  | .stringInto srcs into ptr trap ovf notOvf, st => by
    simp only [execStmt]
    repeat' (first | exact ResLe.refl _ | exact execStmts_mono P env hr hf ovf _ | exact execStmts_mono P env hr hf notOvf _ | split)
  | .move .., st | .goTo .., st | .goToDep .., st | .exitPerform, st | .exitCycle, st
  | .exitPara, st | .exitSection, st | .nextSentence, st | .cont, st | .stop .., st
  | .setIdx .., st | .setIdxBy .., st | .display .., st | .call .., st | .write .., st
  | .unsupported .., st | .clock .., st | .abend .., st
  | .inspect .., st | .convert .., st | .setAddress .., st | .accept .., st => by
    simp only [execStmt]
    repeat' (first | exact ResLe.refl _ | split)
  | .fopen .., st | .fclose .., st => by
    simp only [execStmt]
    repeat' (first | exact ResLe.refl _ | exact ioFinishU_mono P hr _ _ _ _ _ | split)
  | .fcloseOpt .., st => by
    simp only [execStmt]
    repeat' (first | exact ResLe.refl _ | exact ioFinishU_mono P hr _ _ _ _ _ | split)
  | .fopenRev .., st => by
    simp only [execStmt]
    repeat' (first | exact ResLe.refl _ | exact ioFinishU_mono P hr _ _ _ _ _ | split)

theorem execStmts_mono (P : Program) (env : Env) {rec rec' : Nat → State → Res}
    {fuel fuel' : Nat} (hr : RecLe rec rec') (hf : fuel ≤ fuel') :
    ∀ (ss : List Stmt) (st : State),
      ResLe (execStmts P env rec fuel ss st) (execStmts P env rec' fuel' ss st)
  | [], st => by simp only [execStmts]; exact ResLe.refl _
  | s :: rest, st => by
    simp only [execStmts]
    rcases execStmt_mono P env hr hf s st with h | h
    · res_oof h (execStmt P env rec fuel s st)
    · rw [h]
      res_split (execStmt P env rec fuel s st)
      all_goals first | exact ResLe.refl _ | exact execStmts_mono P env hr hf rest _

theorem execWhens_mono (P : Program) (env : Env) {rec rec' : Nat → State → Res}
    {fuel fuel' : Nat} (hr : RecLe rec rec') (hf : fuel ≤ fuel') :
    ∀ (cs : List Cond) (bs : List Stmt) {k k' : State → Res}, FnLe k k' →
      ∀ st, ResLe (execWhens P env rec fuel cs bs k st) (execWhens P env rec' fuel' cs bs k' st)
  | c :: cs, b :: bs, k, k', hk, st => by
    simp only [execWhens]
    split
    · exact ResLe.refl _
    · split
      · exact execStmt_mono P env hr hf b _
      · exact execWhens_mono P env hr hf cs bs hk _
  | [], _, k, k', hk, st => by simp only [execWhens]; exact hk st
  | _ :: _, [], k, k', hk, st => by simp only [execWhens]; exact hk st

end

theorem execSentences_mono (P : Program) (env : Env) {rec rec' : Nat → State → Res}
    {fuel fuel' : Nat} (hr : RecLe rec rec') (hf : fuel ≤ fuel') :
    ∀ (ss : List (List Stmt)) (st : State),
      ResLe (execSentences P env rec fuel ss st) (execSentences P env rec' fuel' ss st)
  | [], st => by simp only [execSentences]; exact ResLe.refl _
  | s :: ss, st => by
    simp only [execSentences]
    rcases execStmts_mono P env hr hf s st with h | h
    · res_oof h (execStmts P env rec fuel s st)
    · rw [h]
      res_split (execStmts P env rec fuel s st)
      all_goals first | exact ResLe.refl _ | exact execSentences_mono P env hr hf ss _

theorem endOfPara_mono {rec rec' : Nat → State → Res} (hr : RecLe rec rec')
    (slots : List (ExitPt × Nat)) (k : Nat) (st : State) :
    ResLe (endOfPara rec slots k st) (endOfPara rec' slots k st) := by
  simp only [endOfPara]
  repeat' (first | exact ResLe.refl _ | exact hr _ _ | split)

theorem runFrom_mono (P : Program) (env : Env) :
    ∀ (n n' k : Nat) (st : State), n ≤ n' → ResLe (runFrom P env n k st) (runFrom P env n' k st)
  | 0, _, k, st, _ => by simp only [runFrom]; left; rfl
  | n + 1, 0, _, _, h => absurd h (by omega)
  | n + 1, n' + 1, k, st, h => by
    have ih : RecLe (runFrom P env n) (runFrom P env n') :=
      fun k st => runFrom_mono P env n n' k st (by omega)
    simp only [runFrom]
    split
    · exact ResLe.refl _
    · rename_i para _
      rcases execSentences_mono P env ih (by omega : n ≤ n') para.body st with h2 | h2
      · res_oof h2 (execSentences P env (runFrom P env n) n para.body st)
      · rw [h2]
        res_split (execSentences P env (runFrom P env n) n para.body st)
        all_goals first | exact ResLe.refl _ | exact endOfPara_mono ih _ _ _ | exact ih _ _

end Sem

/-- More fuel, same outcome (or the first run ran out of fuel). -/
theorem Program.run_resLe (P : Program) (env : Env) {n n' : Nat} (st : State) (h : n ≤ n') :
    Sem.ResLe (P.run env n st) (P.run env n' st) := by
  simp only [Program.run]
  rcases Sem.runFrom_mono P env n n' 0 st h with h2 | h2
  · res_oof h2 (Sem.runFrom P env n 0 st)
  · rw [h2]; exact Sem.ResLe.refl _

/-- Fuel monotonicity: a run that ends with a real signal (anything but `outOfFuel`) ends with
the same signal and state for every larger fuel. -/
theorem Program.run_mono (P : Program) (env : Env) {n n' : Nat} {st : State} (h : n ≤ n')
    (hr : (P.run env n st).1 ≠ .outOfFuel) : P.run env n' st = P.run env n st :=
  (Program.run_resLe P env st h).real hr

end Cobol
