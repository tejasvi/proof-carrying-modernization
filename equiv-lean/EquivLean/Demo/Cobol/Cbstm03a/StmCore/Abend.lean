/-
# The abend paths of the cross-reference loop

A cross-reference record whose customer (account) is not found: `CBSTM03B`'s keyed `READ`
returns status `23`, `2000-CUSTFILE-GET` (`3000-ACCTFILE-GET`) displays `ERROR READING CUSTFILE`
(`ACCTFILE`) and `RETURN CODE: 23`, and `9999-ABEND-PROGRAM` displays `ABENDING PROGRAM` and
calls `CEE3ABD`: the run ends with `Fault.abend (-1)` (the code the IR passes), after the
statements of the records before it (`stm_run_abort_cust`, `stm_run_abort_acct`).
-/
import EquivLean.Demo.Cobol.Cbstm03a.StmCore.Assembly

open Cobol Cobol.Stm

namespace Cobol.StmCore

/-! ## The failed keyed reads -/

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 50000 in
/-- `2000-CUSTFILE-GET` when no customer has the cross-reference's customer id. -/
stm_summary cust_missing (env : Env) (n : Nat) (mem : Mem) (hm : mem.size = 178495)
    (idx : List (Nat × Int)) (out : List Event) (inp : List (Nat × List (List UInt8))) (clockN : Nat)
    (f1 f2 f3 f4 f6 : FileSt) (cs : List (List UInt8)) (q : Nat) (e : Bool) (cu : Option Nat)
    (cid : Int) (hcid : decodeNum {} { digits := 9 } (mem.read 546 9) = some cid)
    (hk : Sem.findKey { off := 0, len := 9 } (Sem.digitChars {} 9 cid.natAbs) cs = none) :
    Sem.execSentences Stm env (Sem.runFrom Stm env (n + 9)) (n + 9)
      Stm.«2000-CUSTFILE-GET».body
      ⟨mem, idx, [(.para 5, 1)], [], [1], out, inp,
        [(1, f1), (2, f2), (3, f3), (4, f4),
         (5, { mode := some .input, recs := cs, pos := q, eof := e, cur := cu }), (6, f6)], clockN⟩

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 50000 in
/-- `3000-ACCTFILE-GET` when no account has the cross-reference's account id. -/
stm_summary acct_missing (env : Env) (n : Nat) (mem : Mem) (hm : mem.size = 178495)
    (idx : List (Nat × Int)) (out : List Event) (inp : List (Nat × List (List UInt8))) (clockN : Nat)
    (f1 f2 f3 f4 f5 : FileSt) (as : List (List UInt8)) (q : Nat) (e : Bool) (cu : Option Nat)
    (aid : Int) (haid : decodeNum {} { digits := 11 } (mem.read 555 11) = some aid)
    (haidb : aid.natAbs < 100000000000)
    (hk : Sem.findKey { off := 0, len := 11 } (Sem.digitChars {} 11 aid.natAbs) as = none) :
    Sem.execSentences Stm env (Sem.runFrom Stm env (n + 9)) (n + 9)
      Stm.«3000-ACCTFILE-GET».body
      ⟨mem, idx, [(.para 6, 2)], [], [2], out, inp,
        [(1, f1), (2, f2), (3, f3), (4, f4), (5, f5),
         (6, { mode := some .input, recs := as, pos := q, eof := e, cur := cu })], clockN⟩
  using [decodeNum_digitChars11, encodeNum_digits11]

/-- The `DISPLAY`s of a missing customer, newest first: `ABENDING PROGRAM`, `RETURN CODE: 23`,
`ERROR READING CUSTFILE`. -/
def custMsg : List Event :=
  [.display [193, 194, 197, 213, 196, 201, 213, 199, 64, 215, 217, 214, 199, 217, 193, 212],
   .display [217, 197, 227, 228, 217, 213, 64, 195, 214, 196, 197, 122, 64, 242, 243],
   .display [197, 217, 217, 214, 217, 64, 217, 197, 193, 196, 201, 213, 199, 64, 195, 228, 226, 227,
     198, 201, 211, 197]]

/-- The `DISPLAY`s of a missing account (`ERROR READING ACCTFILE`). -/
def acctMsg : List Event :=
  [.display [193, 194, 197, 213, 196, 201, 213, 199, 64, 215, 217, 214, 199, 217, 193, 212],
   .display [217, 197, 227, 228, 217, 213, 64, 195, 214, 196, 197, 122, 64, 242, 243],
   .display [197, 217, 217, 214, 217, 64, 217, 197, 193, 196, 201, 213, 199, 64, 193, 195, 195, 227,
     198, 201, 211, 197]]

/-- A run that ends with the fault `f` in a state satisfying `I`. -/
def FaultAnd (f : Fault) (I : State → Prop) (r : Sem.Res) : Prop := r.1 = .fault f ∧ I r.2

/-- After an abend on the record following `pre`: the messages `msg` after the events of the
records `pre`; `STMT-FILE` and `HTML-FILE` (still open) hold the records of `pre`. -/
def AbortPost (gs : List (List (List UInt8))) (pre custs accts : List (List UInt8))
    (out0 : List Event) (r1 r2 : List (List UInt8)) (msg : List Event) (st : State) : Prop :=
  st.out = msg ++ (pre.flatMap (evsOf gs custs accts)).reverse ++ out0 ∧
  st.files.lookup 1 = some { mode := some .output, recs := r1 ++ pre.flatMap (stmtOf gs custs accts) } ∧
  st.files.lookup 2 = some { mode := some .output, recs := r2 ++ pre.flatMap (htmlOf gs custs accts) }

/-! ## A loop that ends with a fault -/

/-- `PERFORM … UNTIL` (test before) over the items `xs`, then an iteration that ends with the
fault `f`: the loop ends with that fault. -/
theorem loopUntil_list_fault {β : Type} {cond : State → SemM Bool} {body : State → Sem.Res}
    (Inv : List β → State → Prop) (f : Fault) (P : State → Prop)
    (hlast : ∀ st, Inv [] st → cond st = .ok false ∧ (body st).1 = .fault f ∧ P (body st).2)
    (hstep : ∀ x xs st, Inv (x :: xs) st →
      cond st = .ok false ∧ (body st).1 = .normal ∧ Inv xs (body st).2)
    (xs : List β) (n : Nat) (st : State) (hinv : Inv xs st) (hn : xs.length < n) :
    ∃ st', Sem.loopUntil false cond body Sem.noStep n st = (.fault f, st') ∧ P st' := by
  induction xs generalizing n st with
  | nil =>
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp at hn; omega⟩
    obtain ⟨hc, hb, hp⟩ := hlast st hinv
    refine ⟨(body st).2, ?_, hp⟩
    rw [loopUntil_succ_before]
    have eb : body st = (.fault f, (body st).2) := Prod.ext hb rfl
    simp only [hc]
    rw [eb]
  | cons x xs ih =>
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp at hn; omega⟩
    obtain ⟨hc, hb, hi⟩ := hstep x xs st hinv
    obtain ⟨st', h1, h2⟩ := ih m (body st).2 hi (by simp at hn; omega)
    refine ⟨st', ?_, h2⟩
    rw [loopUntil_succ_before]
    have eb : body st = (.normal, (body st).2) := Prod.ext hb rfl
    simp only [hc]
    rw [eb]
    simpa [noStep_eq] using h1

open Lean Meta Elab Tactic in
/-- `cobol_loop_fault Inv f P xs`: apply `loopUntil_list_fault` to the first folded
`Sem.loopUntil false …` of the goal (obligations: `Inv xs st₀`, `xs.length < fuel`, the last
iteration, one iteration). -/
elab "cobol_loop_fault " inv:term:max f:term:max p:term:max xs:term:max : tactic =>
  withMainContext do
    let g ← getMainGoal
    let some loop := (← instantiateMVars (← g.getType)).find? fun t =>
        t.isAppOfArity ``Sem.loopUntil 6 && (t.getArg! 0).isConstOf ``Bool.false
      | throwError "cobol_loop_fault: no folded `Sem.loopUntil false …` in the goal"
    let args := loop.getAppArgs
    let invE ← Term.elabTerm inv none
    let fE ← Term.elabTerm f none
    let pE ← Term.elabTerm p none
    let xsE ← Term.elabTerm xs none
    Term.synthesizeSyntheticMVarsNoPostponing
    let thm ← mkAppOptM ``loopUntil_list_fault #[none, args[1]!, args[2]!, invE, fE, pE]
    let (mvs, _, _) ← forallMetaTelescopeReducing (← inferType thm)
    -- hlast hstep xs n st hinv hn
    unless ← isDefEq mvs[2]! xsE do throwError "cobol_loop_fault: input list has the wrong type"
    unless ← isDefEq mvs[3]! args[4]! do throwError "cobol_loop_fault: fuel"
    unless ← isDefEq mvs[4]! args[5]! do throwError "cobol_loop_fault: state"
    let pf ← instantiateMVars (mkAppN thm mvs)
    let g' ← g.assert `hloop (← inferType pf) pf
    let (_, g'') ← g'.intro1P
    replaceMainGoal [g'']
    let hl := mkIdent `hloop
    let ls := mkIdent `loopState
    let he := mkIdent `hloopEq
    let hp := mkIdent `hloopP
    evalTactic (← `(tactic| obtain ⟨$ls, $he, $hp⟩ := $hl:ident))
    evalTactic (← `(tactic| rw [$he:ident]))
    let main ← getGoals
    setGoals (main ++ [mvs[5]!.mvarId!, mvs[6]!.mvarId!, mvs[0]!.mvarId!, mvs[1]!.mvarId!])

/-! ## The failing iteration -/

section
attribute [local cobol_eval high] xref_found cust_found cust_missing acct_missing

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 50000 in
/-- An iteration on a record `x` whose customer is not found. -/
theorem iter_fail_cust (env : Env) (m : Nat) (gs : List (List (List UInt8)))
    (xrefs custs accts : List (List UInt8))
    (idx : List (Nat × Int)) (inp : List (Nat × List (List UInt8))) (clockN : Nat)
    (out0 : List Event) (r1 r2 : List (List UInt8)) (f3 : FileSt)
    (mem : Mem) (done rest' : List (List UInt8)) (x : List UInt8)
    (hxs : xrefs = done ++ x :: rest') (hxl : x.length = 50)
    (hcid : decodeNum {} { digits := 9 } ((x.drop 16).take 9) = some (xCid x))
    (hkc : Sem.findKey { off := 0, len := 9 } (Sem.digitChars {} 9 (xCid x).natAbs) custs = none)
    (hsz : mem.size = 178495) (heof : mem.read 1429 1 = [213])
    (q5 : Nat) (e5 : Bool) (c5 : Option Nat) (q6 : Nat) (e6 : Bool) (c6 cu4 : Option Nat) :
    FaultAnd (.abend (-1)) (AbortPost gs done custs accts out0 r1 r2 custMsg)
      (Sem.execStmts Stm env (Sem.runFrom Stm env (m + 10)) (m + 10) [Stm.«1000-MAINLINE».s8]
        ⟨mem, idx, [], [], [], (done.flatMap (evsOf gs custs accts)).reverse ++ out0, inp,
          [(1, { mode := some .output, recs := r1 ++ done.flatMap (stmtOf gs custs accts) }),
           (2, { mode := some .output, recs := r2 ++ done.flatMap (htmlOf gs custs accts) }), (3, f3),
           (4, { mode := some .input, recs := xrefs, pos := done.length, eof := false, cur := cu4 }),
           (5, { mode := some .input, recs := custs, pos := q5, eof := e5, cur := c5 }),
           (6, { mode := some .input, recs := accts, pos := q6, eof := e6, cur := c6 })], clockN⟩) := by
  have hy : xrefs[done.length]? = some x := by rw [hxs]; simp
  unfold FaultAnd AbortPost
  stm_auto [custMsg]

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 50000 in
/-- An iteration on a record `x` whose customer is found but whose account is not. -/
theorem iter_fail_acct (env : Env) (m : Nat) (gs : List (List (List UInt8)))
    (xrefs custs accts : List (List UInt8))
    (idx : List (Nat × Int)) (inp : List (Nat × List (List UInt8))) (clockN : Nat)
    (out0 : List Event) (r1 r2 : List (List UInt8)) (f3 : FileSt)
    (mem : Mem) (done rest' : List (List UInt8)) (x : List UInt8)
    (hxs : xrefs = done ++ x :: rest') (hxl : x.length = 50)
    (hcid : decodeNum {} { digits := 9 } ((x.drop 16).take 9) = some (xCid x))
    (haid : decodeNum {} { digits := 11 } ((x.drop 25).take 11) = some (xAid x))
    (i : Nat) (hkc : Sem.findKey { off := 0, len := 9 } (Sem.digitChars {} 9 (xCid x).natAbs) custs = some i)
    (hcl : (custs.getD i []).length = 500)
    (hka : Sem.findKey { off := 0, len := 11 } (Sem.digitChars {} 11 (xAid x).natAbs) accts = none)
    (hsz : mem.size = 178495) (heof : mem.read 1429 1 = [213])
    (q5 : Nat) (e5 : Bool) (c5 : Option Nat) (q6 : Nat) (e6 : Bool) (c6 cu4 : Option Nat) :
    FaultAnd (.abend (-1)) (AbortPost gs done custs accts out0 r1 r2 acctMsg)
      (Sem.execStmts Stm env (Sem.runFrom Stm env (m + 10)) (m + 10) [Stm.«1000-MAINLINE».s8]
        ⟨mem, idx, [], [], [], (done.flatMap (evsOf gs custs accts)).reverse ++ out0, inp,
          [(1, { mode := some .output, recs := r1 ++ done.flatMap (stmtOf gs custs accts) }),
           (2, { mode := some .output, recs := r2 ++ done.flatMap (htmlOf gs custs accts) }), (3, f3),
           (4, { mode := some .input, recs := xrefs, pos := done.length, eof := false, cur := cu4 }),
           (5, { mode := some .input, recs := custs, pos := q5, eof := e5, cur := c5 }),
           (6, { mode := some .input, recs := accts, pos := q6, eof := e6, cur := c6 })], clockN⟩) := by
  have hy : xrefs[done.length]? = some x := by rw [hxs]; simp
  have haidb : (xAid x).natAbs < 100000000000 := (decodeNum_holds _ _ haid).1
  unfold FaultAnd AbortPost
  stm_auto [acctMsg]

end

/-! ## The loop and the whole run -/

theorem map_some_inj {α : Type _} : ∀ a b : List α, a.map some = b.map some → a = b
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | x :: xs, y :: ys, h => by
    simp only [List.map_cons, List.cons.injEq, Option.some.injEq] at h
    rw [h.1, map_some_inj xs ys h.2]

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 50000 in
/-- **The cross-reference loop meets a record it cannot process** (`hfail`: the iteration on it,
after the records `pre`, ends with the fault `f`): the run of `1000-MAINLINE` ends with that
fault. -/
theorem mainline_abort (env : Env) (m : Nat) (gs : List (List (List UInt8))) (m0 : Mem)
    (hS : P4Static (m + 8) gs m0) (xrefs custs accts : List (List UInt8))
    (idx : List (Nat × Int)) (inp : List (Nat × List (List UInt8))) (clockN : Nat)
    (out0 : List Event) (r1 r2 : List (List UInt8)) (f3 : FileSt)
    (pre post : List (List UInt8)) (x : List UInt8) (hxs : xrefs = pre ++ x :: post)
    (hpre : ∀ y ∈ pre, XOk custs accts y) (hlen : pre.length < m + 10)
    (f : Fault) (P : State → Prop)
    (hfail : ∀ (mem : Mem) (q5 : Nat) (e5 : Bool) (c5 : Option Nat) (q6 : Nat) (e6 : Bool)
      (c6 cu4 : Option Nat), mem.size = 178495 → mem.read 1429 1 = [213] →
      FaultAnd f P (Sem.execStmts Stm env (Sem.runFrom Stm env (m + 10)) (m + 10) [Stm.«1000-MAINLINE».s8]
        ⟨mem, idx, [], [], [], (pre.flatMap (evsOf gs custs accts)).reverse ++ out0, inp,
          [(1, { mode := some .output, recs := r1 ++ pre.flatMap (stmtOf gs custs accts) }),
           (2, { mode := some .output, recs := r2 ++ pre.flatMap (htmlOf gs custs accts) }), (3, f3),
           (4, { mode := some .input, recs := xrefs, pos := pre.length, eof := false, cur := cu4 }),
           (5, { mode := some .input, recs := custs, pos := q5, eof := e5, cur := c5 }),
           (6, { mode := some .input, recs := accts, pos := q6, eof := e6, cur := c6 })], clockN⟩))
    (st0 : State)
    (h0 : MInv gs xrefs custs accts m0 idx inp clockN out0 r1 r2 f3 (xrefs.map some ++ [none]) st0) :
    FaultAnd f P (Sem.runFrom Stm env (m + 11) 2 st0) := by
  unfold FaultAnd
  stm_auto
  cobol_loop_fault (fun (ys : List (List UInt8)) st => ∃ dn, pre = dn ++ ys ∧
      MInv gs xrefs custs accts m0 idx inp clockN out0 r1 r2 f3 (ys.map some ++ (x :: post).map some ++ [none])
        st) f P pre
  · stm_auto
    exact hloopP
  · refine ⟨[], by simp, ?_⟩
    rw [show pre.map some ++ (x :: post).map some ++ [none] = xrefs.map some ++ [none] by
      rw [hxs]; simp]
    exact h0
  · exact hlen
  · -- the record that fails
    rintro ⟨mem, idx', slots', saves', active', out', inp', files', clockN'⟩
      ⟨dn, -, done, rest, hxs', hidx, hsl, hsv, hac, hinp, hclk, hout, hsz, -, -, -, q5, e5, c5, q6, e6,
        c6, cu4, hcase⟩
    dsimp only at hidx hsl hsv hac hinp hclk hout hsz hcase
    subst idx' slots' saves' active' inp' clockN' out'
    obtain ⟨hi, heof, hfiles⟩ := hcase.resolve_right (fun ⟨h, _, _, _⟩ => by simp at h)
    subst files'
    have hr : rest = x :: post := by
      apply map_some_inj
      have := List.append_cancel_right hi
      simpa using this.symm
    subst hr
    have hd : done = pre := List.append_cancel_right (hxs'.symm.trans hxs)
    subst hd
    exact ⟨by stm_auto, hfail mem q5 e5 c5 q6 e6 c6 cu4 hsz heof⟩
  · -- a record before it
    rintro y ys ⟨mem, idx', slots', saves', active', out', inp', files', clockN'⟩
      ⟨dn, hdn, done, rest, hxs', hidx, hsl, hsv, hac, hinp, hclk, hout, hsz, htbl, hcr, hc, q5, e5, c5,
        q6, e6, c6, cu4, hcase⟩
    dsimp only at hidx hsl hsv hac hinp hclk hout hsz htbl hcr hc hcase
    subst idx' slots' saves' active' inp' clockN' out'
    obtain ⟨hi, heof, hfiles⟩ := hcase.resolve_right (fun ⟨h, _, _, _⟩ => by simp at h)
    subst files'
    have hr : rest = y :: (ys ++ x :: post) := by
      apply map_some_inj
      have := List.append_cancel_right hi
      simpa using this.symm
    subst hr
    have hy : y ∈ pre := by rw [hdn]; simp
    have hit := iter_some env m gs m0 hS xrefs custs accts idx inp clockN out0 r1 r2 f3 mem done
      (ys ++ x :: post) y hxs' (hpre y hy) hsz htbl hcr hc heof q5 e5 c5 q6 e6 c6 cu4
    refine ⟨by stm_auto, hit.1, dn ++ [y], by rw [hdn]; simp, ?_⟩
    have he : (ys ++ x :: post).map some ++ [none] = ys.map some ++ (x :: post).map some ++ [none] := by
      simp
    rw [← he]
    exact hit.2

/-- A run that ends with a fault is the program's result. -/
theorem run_of_fault {P : Program} {env : Env} {F : Nat} {st : State} {f : Fault}
    (h : (Sem.runFrom P env F 0 st).1 = .fault f) : P.run env F st = Sem.runFrom P env F 0 st := by
  unfold Program.run
  revert h
  cases Sem.runFrom P env F 0 st with
  | mk sig s => cases sig <;> intro h <;> first | rfl | cases h

set_option maxHeartbeats 4000000 in
/-- **`CBSTM03AB` with a customer missing.**  The assumptions of `stm_run` on the address space,
the opens and the transaction file; the cross-reference file is `pre ++ x :: post` with the
records `pre` valid (`XOk`) and `x` of 50 bytes with a numeric customer id that no customer
has: the run ends with `Fault.abend (-1)`, its output being `ERROR READING CUSTFILE`,
`RETURN CODE: 23`, `ABENDING PROGRAM` after the statement events of `pre` and the walk
`DISPLAY`s; `STMT-FILE` and `HTML-FILE` hold the records of `pre`. -/
theorem stm_run_abort_cust (env : Env) (hEnv : env.addrSpace = asp)
    (hOpen : ∀ f md, env.openError f md = none)
    (m0 : Mem) (hm0 : m0.size = 178495) (hpsa : m0.read 175623 4 = [0, 0, 0, 0])
    (trs xrefs custs accts : List (List UInt8))
    (htl : ∀ r ∈ trs, r.length = 350 ∧ AmtOk r) (hne : trs ≠ [])
    (hG : (grp trs).length ≤ 50) (hT : ∀ g ∈ grp trs, g.length ≤ 10)
    (pre post : List (List UInt8)) (x : List UInt8) (hxs : xrefs = pre ++ x :: post)
    (hpre : ∀ y ∈ pre, XOk custs accts y) (hxl : x.length = 50)
    (hcid : decodeNum {} { digits := 9 } ((x.drop 16).take 9) = some (xCid x))
    (hkc : Sem.findKey { off := 0, len := 9 } (Sem.digitChars {} 9 (xCid x).natAbs) custs = none)
    (F : Nat) (hF : trs.length + xrefs.length + 100 ≤ F) :
    FaultAnd (.abend (-1)) (AbortPost (grp trs) pre custs accts walkDisplays [] [] custMsg)
      (Stm.run env F (Stm.initState m0 [(3, trs), (4, xrefs), (5, custs), (6, accts)])) := by
  obtain ⟨m, S2, hrun, hlen, hS4, hMI⟩ :=
    to_mainline env hEnv hOpen m0 hm0 hpsa trs xrefs custs accts htl hne hG hT F hF
  have hpl : pre.length < m + 10 := by
    rw [hxs] at hlen
    simp at hlen
    omega
  have hA := mainline_abort env m (grp trs) S2.mem hS4 xrefs custs accts [] _ 0 walkDisplays [] [] _
    pre post x hxs hpre hpl _ _
    (fun mem q5 e5 c5 q6 e6 c6 cu4 hsz heof => iter_fail_cust env m (grp trs) xrefs custs accts [] _ 0
      walkDisplays [] [] _ mem pre post x hxs hxl hcid hkc hsz heof q5 e5 c5 q6 e6 c6 cu4) S2 hMI
  rw [run_of_fault (by rw [hrun]; exact hA.1), hrun]
  exact hA

set_option maxHeartbeats 4000000 in
/-- **`CBSTM03AB` with an account missing**: as `stm_run_abort_cust`, for a record `x` whose
customer is found (a 500-byte record) but whose numeric account id no account has. -/
theorem stm_run_abort_acct (env : Env) (hEnv : env.addrSpace = asp)
    (hOpen : ∀ f md, env.openError f md = none)
    (m0 : Mem) (hm0 : m0.size = 178495) (hpsa : m0.read 175623 4 = [0, 0, 0, 0])
    (trs xrefs custs accts : List (List UInt8))
    (htl : ∀ r ∈ trs, r.length = 350 ∧ AmtOk r) (hne : trs ≠ [])
    (hG : (grp trs).length ≤ 50) (hT : ∀ g ∈ grp trs, g.length ≤ 10)
    (pre post : List (List UInt8)) (x : List UInt8) (hxs : xrefs = pre ++ x :: post)
    (hpre : ∀ y ∈ pre, XOk custs accts y) (hxl : x.length = 50)
    (hcid : decodeNum {} { digits := 9 } ((x.drop 16).take 9) = some (xCid x))
    (haid : decodeNum {} { digits := 11 } ((x.drop 25).take 11) = some (xAid x))
    (i : Nat) (hkc : Sem.findKey { off := 0, len := 9 } (Sem.digitChars {} 9 (xCid x).natAbs) custs = some i)
    (hcl : (custs.getD i []).length = 500)
    (hka : Sem.findKey { off := 0, len := 11 } (Sem.digitChars {} 11 (xAid x).natAbs) accts = none)
    (F : Nat) (hF : trs.length + xrefs.length + 100 ≤ F) :
    FaultAnd (.abend (-1)) (AbortPost (grp trs) pre custs accts walkDisplays [] [] acctMsg)
      (Stm.run env F (Stm.initState m0 [(3, trs), (4, xrefs), (5, custs), (6, accts)])) := by
  obtain ⟨m, S2, hrun, hlen, hS4, hMI⟩ :=
    to_mainline env hEnv hOpen m0 hm0 hpsa trs xrefs custs accts htl hne hG hT F hF
  have hpl : pre.length < m + 10 := by
    rw [hxs] at hlen
    simp at hlen
    omega
  have hA := mainline_abort env m (grp trs) S2.mem hS4 xrefs custs accts [] _ 0 walkDisplays [] [] _
    pre post x hxs hpre hpl _ _
    (fun mem q5 e5 c5 q6 e6 c6 cu4 hsz heof => iter_fail_acct env m (grp trs) xrefs custs accts [] _ 0
      walkDisplays [] [] _ mem pre post x hxs hxl hcid haid i hkc hcl hka hsz heof q5 e5 c5 q6 e6 c6
      cu4) S2 hMI
  rw [run_of_fault (by rw [hrun]; exact hA.1), hrun]
  exact hA

end Cobol.StmCore
