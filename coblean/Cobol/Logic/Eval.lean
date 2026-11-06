/-
# Symbolic execution

`cobol_sym [h₁, …]` evaluates the interpreter and the data semantics on a concrete program
and symbolic data, using the field-level storage lemmas and the hypotheses `hᵢ` (typically
`decodeNum … (m.read off len) = some x` facts about the input storage).

How it stays cheap:

* the semantics is written with `match` / `if` and no continuation lambdas, and simp
  evaluates `match` / `if` lazily (scrutinee first, then only the selected branch);
* functions that occur partially applied (`runFrom` as the `rec` argument, `execStmts` and
  `performOnce` as loop bodies, loop conditions) are unfolded only through the fully applied
  equations below, never as partial applications;
* the simp set is curated (`simp only`): no default-set arithmetic normalisation;
* structurally recursive parts of the semantics are rewritten with their equation lemmas
  (`cobol_eval_eqns`), never by smart unfolding, which would copy the symbolic state;
* data-dependent branches become value-level `if`s: results of an `IF` whose branches both
  continue normally are merged (`Cobol.Logic.Merge`), a `match` on a result whose signal
  depends on the data is distributed over the `if` (`matchItePre`);
* stores whose value provably fits drop their truncation, impossible size errors disappear
  (`Cobol.Logic.Bounds`);
* a loop whose fuel is symbolic is not unrolled, and simp stops in front of it
  (`unrollLoopUntil`, `stopAtLoop`; see `Cobol.Logic.Loops`).

What remains are goals about scaled-integer arithmetic (`divRound`, `fitNum`, …), closed by
`cobol_grind` (`Cobol.Logic.Equiv`) or `cobol_arith` (`omega`).
-/
import Cobol.Logic.Alnum
import Cobol.Logic.MatchIte
import Cobol.Logic.Ground
import Cobol.Logic.Bounds
import Cobol.Logic.Merge
import Cobol.Logic.Bytes
import Cobol.Logic.MemNorm

namespace Cobol

/-! ## Definitions unfolded by symbolic execution (always fully applied, lazy bodies) -/

attribute [cobol_eval] Program.run Program.initState Program.initMem Program.sectionEnd
  Sem.endOfPara Sem.setAssoc Sem.lift Sem.evalInt
  Sem.move Sem.srcVal Sem.moveInto Sem.numInto Sem.storeMove Sem.badOverlap
  Sem.padRight Sem.padLeft Sem.figBytes Sem.intWidth
  Sem.resolve Sem.refMod Sem.evalSub Sem.numOf Sem.readBytes Sem.writeBytes Sem.idxVal
  Sem.arith Sem.evalOps Sem.catchDiv ArithOp.exprs
  ArithOp.readsReceiver Sem.newValue Sem.storeArith Sem.storeEdited Sem.divRem
  Sem.bin2 Sem.align Sem.quot Sem.bool2 Sem.cmpOp
  Sem.cmpOperand Sem.operandLen Sem.classTest Sem.displayBytes
  Sem.callProg Sem.overflowUndefined NumFmt.fullBinary NumFmt.byteLen Config.binBytes Config.ibm
  Config.space Config.chr Config.zeroChar Config.quote Config.plusChar Config.minusChar
  rescale divRoundZ Sem.rescaleExact Sem.quotExact
  List.isEmpty_nil List.isEmpty_cons Option.isNone_none Option.isNone_some Option.isSome_none Option.isSome_some
  List.lookup_nil List.lookup_cons List.filter_nil List.filter_cons
  List.getElem?_toArray List.getElem?_cons_zero List.getElem?_cons_succ List.getElem?_nil
  Array.getD_eq_getD_getElem?

/-! Files (`Cobol.Sem.File`), clock, abend. -/
attribute [cobol_eval] Sem.fileDecl Sem.fileSt Sem.setFile Sem.clearCur Sem.setStatus Sem.statusBytes Sem.keyOf Sem.keyField
  Sem.keyDecl Sem.canRead Sem.fileOpen Sem.fileClose Sem.fileRead Sem.fileWrite Sem.fileRewrite
  Sem.fileDelete Sem.altClash Sem.ioNext Sem.atEndCond Sem.invalidKeyCond Sem.ioFinish
  Sem.lenFault Config.digitByte List.find?_cons List.find?_nil List.any_cons List.any_nil
  Sem.recLenOk Sem.recordOut Sem.recordIn Sem.setRecLen Sem.fileStart Sem.boundAt Sem.afterBound
  Sem.useProc? Sem.ioErr Sem.ioFinishU
  Sem.fileOpenBasic Sem.fileReadBasic Sem.fileWriteBasic Sem.fileRewriteBasic Sem.fileDeleteBasic
  Sem.fileStartBasic

/-! `INSPECT` (`Cobol.Sem.Inspect`): evaluated on concrete bytes. -/
attribute [cobol_eval] Sem.inspRegion Sem.InspPh.len Sem.inspMatches Sem.putAt Sem.inspExpire
  Sem.inspInit Sem.inspBytes Sem.convByte Sem.inspConvert Sem.unstrPiece Sem.unstring
  Sem.unsignByte Sem.inspView Sem.resignByte Sem.inspUnview
  Sem.strBytes Sem.strPiece Sem.stringInto
  Sem.withIdx Sem.keyVal Sem.searchAllPick

/-- Register the equation lemmas of structurally recursive definitions (one per `match` arm)
in `cobol_eval`, not the definitions themselves: simp unfolds a recursive definition in its
`toUnfold` set by smart unfolding, which walks (and copies) every argument — including the
symbolic state, whose tree size is exponential in the number of merged `IF`s even though its
DAG is linear.  An equation lemma is selected by the constructor of the recursion argument
and instantiated with sharing. -/
elab "cobol_eval_eqns " ids:ident* : command => do
  let some ext ← Lean.Elab.Command.liftCoreM (Lean.Meta.getSimpExtension? `cobol_eval)
    | throwError "cobol_eval simp set missing"
  for id in ids do
    let n ← Lean.Elab.Command.liftCoreM <| Lean.Elab.realizeGlobalConstNoOverloadWithInfo id
    let some eqns ← Lean.Elab.Command.liftTermElabM <| Lean.Meta.getEqnsFor? n
      | throwError "{n}: no equation lemmas"
    for e in eqns do
      Lean.Elab.Command.liftTermElabM <|
        Lean.Meta.addSimpTheorem ext e (post := true) (inv := false) .global (prio := 1000)

cobol_eval_eqns Sem.bytesLt Sem.insertByKey Sem.findKey Sem.firstRec
cobol_eval_eqns Sem.findSub Sem.inspFirst Sem.inspScan Sem.inspPhs Sem.inspTally
cobol_eval_eqns Sem.execWhens Sem.keysInOrder
cobol_eval_eqns Sem.delimAt Sem.nextDelim Sem.skipAll Sem.unstrRun
cobol_eval_eqns Sem.strPut Sem.strRun Sem.copyBytes
cobol_eval_eqns Sem.sysinRead
attribute [cobol_eval] Digits.length_toDigits Int.toNat_natCast List.getD_cons_zero List.getD_cons_succ Sem.alnumAsInt
  List.getD_nil List.set_cons_zero List.set_cons_succ List.set_nil List.eraseIdx_cons_zero
  List.eraseIdx_cons_succ List.eraseIdx_nil
cobol_eval_eqns Sem.execStmt Sem.moveList Sem.subsOff Sem.arithList Sem.evalExprs Sem.evalExpr
  Expr.scale Sem.evalCond Sem.displayAll Sem.resolveAll
/-! De-editing `MOVE` (a numeric-edited sender). -/
cobol_eval_eqns Sem.moveListE Sem.editDigits
attribute [cobol_eval] Sem.deEdit

attribute [cobol_arith] Sem.fitNum Sem.fitDec Sem.fitBin Sem.inBinRange Sem.wrapBin
  truncDigits divRound rescale divRoundZ binHalf binMod

/-! ## Recursive / higher-order functions: fully applied equations only -/

section eqns
variable (P : Program) (env : Env) (rec : Nat → State → Sem.Res) (fuel : Nat) (st : State)

@[cobol_eval] theorem execStmts_nil : Sem.execStmts P env rec fuel [] st = (.normal, st) := by
  rw [Sem.execStmts]
@[cobol_eval] theorem execStmts_cons (s : Stmt) (ss : List Stmt) :
    Sem.execStmts P env rec fuel (s :: ss) st =
      match Sem.execStmt P env rec fuel s st with
      | (.normal, st') => Sem.execStmts P env rec fuel ss st'
      | r => r := by
  rw [Sem.execStmts]; rfl
@[cobol_eval] theorem execSentences_nil : Sem.execSentences P env rec fuel [] st = (.normal, st) := rfl
@[cobol_eval] theorem execSentences_cons (s : List Stmt) (ss : List (List Stmt)) :
    Sem.execSentences P env rec fuel (s :: ss) st =
      match Sem.execStmts P env rec fuel s st with
      | (.normal, st1) | (.nextSentence, st1) => Sem.execSentences P env rec fuel ss st1
      | r => r := rfl
@[cobol_eval] theorem runFrom_zero (k : Nat) : Sem.runFrom P env 0 k st = (.outOfFuel, st) := rfl
@[cobol_eval] theorem runFrom_succ (n k : Nat) :
    Sem.runFrom P env (n + 1) k st =
      match P.paras[k]? with
      | none => (.stop .endOfProgram, st)
      | some para =>
        match Sem.execSentences P env (Sem.runFrom P env n) n para.body st with
        | (.normal, st1) | (.exitPara, st1) => Sem.endOfPara (Sem.runFrom P env n) st1.slots k st1
        | (.exitSection, st1) =>
          Sem.endOfPara (Sem.runFrom P env n) st1.slots (P.sectionEnd k) st1
        | (.goto l, st1) => Sem.runFrom P env n l st1
        | (.exitPerform, st1) | (.exitCycle, st1) | (.nextSentence, st1) =>
          (.fault (.unsupported "EXIT PERFORM outside an inline PERFORM"), st1)
        | r => r := rfl
@[cobol_eval] theorem performOnce_eq (id first : Nat) (exit : ExitPt) :
    Sem.performOnce rec id first exit st =
      if st.active.contains id then (.fault (.unsupported "recursive PERFORM"), st) else
      match rec first { st with slots := Sem.setAssoc st.slots exit (some id),
                                saves := Sem.setAssoc st.saves id (st.slots.lookup exit),
                                active := id :: st.active } with
      | (.ret s, st2) =>
        if s = id then
          (.normal, { st2 with slots := Sem.setAssoc st2.slots exit (st2.saves.lookup id),
                               active := st.active })
        else (.ret s, { st2 with active := st.active })
      | (sig, st2) => (sig, { st2 with active := st.active }) := rfl
@[cobol_eval] theorem condFn_eq (c : Cond) : Sem.condFn P c st = Sem.evalCond P.cfg st c := rfl
@[cobol_eval] theorem noStep_eq : Sem.noStep st = (.normal, st) := rfl
@[cobol_eval] theorem loopUntil_zero (ta : Bool) (cond : State → SemM Bool) (body step : State → Sem.Res) :
    Sem.loopUntil ta cond body step 0 st = (.outOfFuel, st) := by rw [Sem.loopUntil]
/-- One iteration of `PERFORM … UNTIL`.  Not a `cobol_eval` lemma: `unrollLoopUntil` applies it
only when the loop fuel is a numeral, so a loop whose fuel is symbolic (`n + 8`, in theorems
about inputs of any length) stays folded for `Cobol.Logic.Loops`. -/
theorem loopUntil_succ (ta : Bool) (cond : State → SemM Bool) (body step : State → Sem.Res)
    (n : Nat) :
    Sem.loopUntil ta cond body step (n + 1) st =
      if ta then
        match body st with
        | (.normal, st1) | (.exitCycle, st1) =>
          match cond st1 with
          | .error f => (.fault f, st1)
          | .ok true => (.normal, st1)
          | .ok false =>
            match step st1 with
            | (.normal, st2) => Sem.loopUntil ta cond body step n st2
            | r => r
        | (.exitPerform, st1) => (.normal, st1)
        | r => r
      else
        match cond st with
        | .error f => (.fault f, st)
        | .ok true => (.normal, st)
        | .ok false =>
          match body st with
          | (.normal, st1) | (.exitCycle, st1) =>
            match step st1 with
            | (.normal, st2) => Sem.loopUntil ta cond body step n st2
            | r => r
          | (.exitPerform, st1) => (.normal, st1)
          | r => r := by
  rw [Sem.loopUntil]; rfl
/-- One iteration of `PERFORM … UNTIL` with the test before (the usual form), without the
`if testAfter` of `loopUntil_succ`: unrolling a symbolic loop by hand never builds the other
branch. -/
theorem loopUntil_succ_before (cond : State → SemM Bool) (body step : State → Sem.Res) (n : Nat) :
    Sem.loopUntil false cond body step (n + 1) st =
      match cond st with
      | .error f => (.fault f, st)
      | .ok true => (.normal, st)
      | .ok false =>
        match body st with
        | (.normal, st1) | (.exitCycle, st1) =>
          match step st1 with
          | (.normal, st2) => Sem.loopUntil false cond body step n st2
          | r => r
        | (.exitPerform, st1) => (.normal, st1)
        | r => r := by
  rw [loopUntil_succ]; rfl
@[cobol_eval] theorem loopTimes_zero (body : State → Sem.Res) :
    Sem.loopTimes body 0 st = (.normal, st) := rfl
@[cobol_eval] theorem loopTimes_succ (body : State → Sem.Res) (k : Nat) :
    Sem.loopTimes body (k + 1) st =
      match body st with
      | (.normal, st1) | (.exitCycle, st1) => Sem.loopTimes body k st1
      | (.exitPerform, st1) => (.normal, st1)
      | r => r := rfl
end eqns

/-- `SEARCH` loop, one step (the loop is well-founded on the fuel, like `loopUntil`). -/
@[cobol_eval] theorem searchLoop_zero (over : State → SemM Bool)
    (whens : (State → Sem.Res) → State → Sem.Res) (atEnd bump : State → Sem.Res) (st : State) :
    Sem.searchLoop over whens atEnd bump 0 st = (.outOfFuel, st) := by
  rw [Sem.searchLoop]

@[cobol_eval] theorem searchLoop_succ (over : State → SemM Bool)
    (whens : (State → Sem.Res) → State → Sem.Res) (atEnd bump : State → Sem.Res) (n : Nat)
    (st : State) :
    Sem.searchLoop over whens atEnd bump (n + 1) st =
      match over st with
      | .error f => (.fault f, st)
      | .ok b =>
        if b then atEnd st
        else
          whens (fun st1 =>
            match bump st1 with
            | (.normal, st2) => Sem.searchLoop over whens atEnd bump n st2
            | r => r) st := by
  rw [Sem.searchLoop]; rfl

/-- Unroll `PERFORM … UNTIL` one iteration when its fuel is a numeral `k + 1`. -/
simproc_decl unrollLoopUntil (Sem.loopUntil _ _ _ _ _ _) := fun e => do
  let_expr Sem.loopUntil ta cond body step n st := e | return .continue
  let some k ← Lean.Meta.getNatValue? n | return .continue
  if k == 0 then return .continue
  let pf := Lean.mkAppN (Lean.mkConst ``loopUntil_succ) #[st, ta, cond, body, step, Lean.mkNatLit (k - 1)]
  let some (_, _, rhs) := (← Lean.Meta.inferType pf).eq? | return .continue
  let pf ← Lean.Meta.mkExpectedTypeHint pf (← Lean.Meta.mkEq e rhs)
  return .visit { expr := rhs, proof? := some pf }

/-! ## Basic logic used by symbolic execution (a curated set: the default simp set's
arithmetic normalisations interact badly with large symbolic terms) -/

attribute [cobol_eval] Except.pure_eq_ok' Except.throw_eq_error' Except.ok_bind' Except.error_bind'
  Bool.and_true Bool.true_and Bool.and_false Bool.false_and Bool.or_true
  Bool.true_or Bool.or_false Bool.false_or Bool.not_true Bool.not_false Bool.and_self Bool.or_self
  Bool.not_not beq_self_eq_true decide_eq_true_eq decide_true decide_false Bool.false_eq_true
  and_true true_and and_false false_and or_true true_or or_false false_or not_true not_false_eq_true
  eq_self ne_eq Option.some.injEq Prod.mk.injEq List.cons.injEq Except.ok.injEq
  Option.getD_some Option.getD_none Option.map_some Option.map_none
  List.length_cons List.length_nil List.length_map List.length_append
  List.map_cons List.map_nil List.append_nil List.nil_append List.cons_append
  List.replicate_zero List.replicate_succ List.flatten_cons List.flatten_nil Nat.sub_self
  Nat.add_zero Nat.zero_add ite_self Bool.and_eq_true Bool.or_eq_true Bool.not_eq_true'
  bne_iff_ne beq_iff_eq ite_not Bool.decide_eq_true Bool.decide_eq_false
  Int.compare_eq_eq Int.compare_eq_lt Int.compare_eq_gt Int.compare_ne_gt Int.compare_ne_lt
  Int.max_def Int.min_def Nat.max_def Nat.min_def Int.mul_one Int.one_mul Int.zero_mul
  Int.mul_zero Int.add_zero Int.zero_add Int.sub_zero Int.neg_zero Nat.mul_one Nat.one_mul
  Nat.pow_zero Int.pow_zero List.take_succ_cons List.take_zero List.take_nil List.drop_zero
  List.drop_succ_cons List.drop_nil List.length_take List.length_drop List.foldl_cons List.foldl_nil
  List.contains_nil List.contains_cons List.elem_nil List.elem_cons

/-- Association lists with a symbolic tail (the save areas of `PERFORM`s at the head of a loop
over an input of any length): a key just removed is absent. -/
@[cobol_eval] theorem List.lookup_filter_self {κ : Type} [BEq κ] [LawfulBEq κ]
    (l : List (κ × Nat)) (k : κ) : (l.filter (fun p => p.1 != k)).lookup k = none := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    obtain ⟨a, b⟩ := p
    by_cases h : a = k
    · subst h
      simp only [List.filter_cons, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, ih]
    · have h1 : (a != k) = true := by simpa using h
      have h2 : (k == a) = false := by simpa using Ne.symm h
      simp only [List.filter_cons, h1, ↓reduceIte, List.lookup_cons, h2, ih]

@[cobol_eval] theorem List.lookup_filter_ne {κ : Type} [BEq κ] [LawfulBEq κ]
    (l : List (κ × Nat)) (k k' : κ) (h : (k' == k) = false) :
    (l.filter (fun p => p.1 != k)).lookup k' = l.lookup k' := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    obtain ⟨a, b⟩ := p
    by_cases hk : a = k
    · subst hk
      have h2 : (k' == a) = false := h
      simp only [List.filter_cons, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, ih,
        List.lookup_cons, h2]
    · have h1 : (a != k) = true := by simpa using hk
      simp only [List.filter_cons, h1, ↓reduceIte, List.lookup_cons, ih]

attribute [cobol_eval] ExitPt.para.injEq ExitPt.sect.injEq

@[cobol_eval] theorem ExitPt.beq_para (a b : Nat) : (ExitPt.para a == ExitPt.para b) = (a == b) := rfl
@[cobol_eval] theorem ExitPt.beq_sect (a b : Nat) : (ExitPt.sect a == ExitPt.sect b) = (a == b) := rfl
@[cobol_eval] theorem ExitPt.beq_para_sect (a b : Nat) : (ExitPt.para a == ExitPt.sect b) = false := rfl
@[cobol_eval] theorem ExitPt.beq_sect_para (a b : Nat) : (ExitPt.sect a == ExitPt.para b) = false := rfl

@[cobol_eval] theorem Prod.fst_ite' {α β : Type _} (c : Prop) [Decidable c] (a b : α × β) :
    (if c then a else b).1 = if c then a.1 else b.1 := by split <;> rfl
@[cobol_eval] theorem Prod.snd_ite' {α β : Type _} (c : Prop) [Decidable c] (a b : α × β) :
    (if c then a else b).2 = if c then a.2 else b.2 := by split <;> rfl
@[cobol_eval] theorem State.mem_ite (c : Prop) [Decidable c] (a b : State) :
    (if c then a else b).mem = if c then a.mem else b.mem := by split <;> rfl

@[cobol_eval] theorem Mem.read_ite (c : Prop) [Decidable c] (a b : Mem) (off len : Nat) :
    (if c then a else b).read off len = if c then a.read off len else b.read off len := by
  split <;> rfl

@[cobol_eval] theorem decodeNum_ite (cfg : Config) (f : NumFmt) (c : Prop) [Decidable c]
    (a b : List UInt8) :
    decodeNum cfg f (if c then a else b) = if c then decodeNum cfg f a else decodeNum cfg f b := by
  split <;> rfl
@[cobol_eval] theorem Signal.ite_eq (c : Prop) [Decidable c] (a b s : Signal) :
    ((if c then a else b) = s) = (if c then a = s else b = s) := by split <;> rfl
@[cobol_eval] theorem Option.ite_eq {α : Type _} (c : Prop) [Decidable c] (a b s : Option α) :
    ((if c then a else b) = s) = (if c then a = s else b = s) := by split <;> rfl

/-! ## State merging

After an `IF` whose branches both end normally, the two results merge into one result whose
state is an `if`: `(if c then (.normal, s₁) else (.normal, s₂)) = (.normal, if c then s₁ else
s₂)`, and states merge field by field (`mergeCtorIte`, `projIte` in `Cobol.Logic.Merge`).
Execution then continues once, on the merged state (field reads go into the `if`,
`Mem.read_ite`), instead of once per path: a sequence of `IF`s costs polynomial, not
exponential, time.  Values merge the same way (`some`, `.ok`, records of the target model).
Results with different signals (a `GO TO` in one branch) do not merge: the `match` on the
signal is then distributed over the `if` (`matchItePre`). -/

@[cobol_eval] theorem Prod.ite_mk_same_fst {α β : Type _} (c : Prop) [Decidable c] (a : α)
    (b₁ b₂ : β) : (if c then (a, b₁) else (a, b₂)) = (a, if c then b₁ else b₂) := by
  split <;> rfl
@[cobol_eval] theorem Mem.size_ite (c : Prop) [Decidable c] (a b : Mem) :
    (if c then a else b).size = if c then a.size else b.size := by split <;> rfl
/-- Character conversions of merged values go into the `if`, where the literals evaluate. -/
@[cobol_eval] theorem Codepage.cp037Byte_ite (c : Prop) [Decidable c] (a b : Char) :
    Codepage.cp037Byte (if c then a else b) =
      if c then Codepage.cp037Byte a else Codepage.cp037Byte b := by split <;> rfl
@[cobol_eval] theorem Codepage.cp037Char_ite (c : Prop) [Decidable c] (a b : UInt8) :
    Codepage.cp037Char (if c then a else b) =
      if c then Codepage.cp037Char a else Codepage.cp037Char b := by split <;> rfl

@[cobol_eval] theorem ite_ite_same_then {α : Type _} (c : Prop) [Decidable c] (a b d : α) :
    (if c then (if c then a else b) else d) = (if c then a else d) := by split <;> rfl
@[cobol_eval] theorem ite_ite_same_else {α : Type _} (c : Prop) [Decidable c] (a b d : α) :
    (if c then d else (if c then a else b)) = (if c then d else b) := by split <;> rfl

/-! ## Tactics -/

/-- Symbolic execution: one `simp only` pass over the semantics on a concrete program. -/
syntax "cobol_sym" (" [" Lean.Parser.Tactic.simpLemma,* "]")? (Lean.Parser.Tactic.location)? : tactic
macro_rules
  | `(tactic| cobol_sym $[$loc]?) => `(tactic| cobol_sym [] $[$loc]?)
  | `(tactic| cobol_sym [$xs,*] $[$loc]?) =>
    `(tactic| simp (config := { decide := false, maxSteps := 10000000, maxDischargeDepth := 4 }) only
      [cobol_eval, ↓reduceIte, ↓reduceDIte, reduceCtorEq, matchIte, ↓stopAtLoop, ↓matchItePre,
       mergeCtorIte, projIte, normWrite, mergeMemIte,
       unrollLoopUntil,
       reduceFitNumRange, reduceDecodeEncodeRange, reduceIntCmpRange, reduceIntLtRange,
       reduceInt64ToIntOfInt,
       reduceDecodeNum, reduceIntCompare, reduceCp037Char, reduceCp037Byte, reduceCp037CharEq, reduceUInt8Eq, reduceUInt8Range, reduceUInt8ToNatRange, reduceNatCmpRange, reduceEncodeNumBEq,
       Nat.reduceSucc, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, Nat.reduceMod,
       Nat.reducePow, Nat.reduceLT, Nat.reduceGT, Nat.reduceBEq, Nat.reduceBNe, Nat.reduceEqDiff,
       Nat.reduceLeDiff, Nat.reduceSubDiff,
       Int.reduceNeg, Int.reduceAdd, Int.reduceMul, Int.reduceSub, Int.reduceDiv, Int.reduceMod,
       Int.reducePow, Int.reduceLT, Int.reduceLE, Int.reduceGT, Int.reduceGE, Int.reduceEq,
       Int.reduceNe, Int.reduceBEq, Int.reduceBNe, Int.reduceAbs, Int.reduceToNat,
       Int.reduceNatCast, Int.reduceOfNat,
       UInt8.reduceLT, UInt8.reduceLE, UInt8.reduceToNat, UInt8.reduceOfNat, $xs,*] $[$loc]?)

/-- Symbolic execution with path splitting: evaluate, then split on each remaining
data-dependent branch and evaluate every path with its path condition. -/
syntax "cobol_run" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| cobol_run) => `(tactic| cobol_run [])
  | `(tactic| cobol_run [$xs,*]) =>
    `(tactic| (try cobol_sym [$xs,*] at *) <;> (repeat' (split <;> (try cobol_sym [$xs,*] at *))))

/-- Scaled-integer arithmetic: unfold rounding / truncation / fitting (and evaluate the
item formats) everywhere, split every remaining `if`, and run `omega` on each case. -/
syntax "cobol_arith" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| cobol_arith) => `(tactic| cobol_arith [])
  | `(tactic| cobol_arith [$xs,*]) =>
    `(tactic| (try cobol_sym [cobol_arith, NumFmt.Holds, $xs,*] at *) <;>
      (repeat' split) <;> (try cobol_sym [cobol_arith, NumFmt.Holds, $xs,*] at *) <;> omega)

end Cobol
