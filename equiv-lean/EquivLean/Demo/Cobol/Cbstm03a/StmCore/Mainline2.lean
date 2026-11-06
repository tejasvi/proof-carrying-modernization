/-
# Phase 4 of `CBSTM03AB`: the cross-reference loop and the end of `1000-MAINLINE`

`mainline_ok`: from the loop invariant `MInv` at the start of `1000-MAINLINE` (paragraph 2), the
program reads every cross-reference record, writes its statement (`evsOf`, `stmtOf`, `htmlOf`),
closes the six files and ends with `GOBACK` (`MainPost`).  One iteration runs by symbolic
execution with the summaries of the `CBSTM03B` reads, `5000-CREATE-STATEMENT` (`create_rawE`)
and `4000-TRNXFILE-GET` (`perform4_eq`); `p4_gen` then names the storage after `4000` and
states its frame once (`p4_sf`).
-/
import EquivLean.Demo.Cobol.Cbstm03a.StmCore.Mainline

open Cobol Cobol.Stm

namespace Cobol.StmCore

set_option maxHeartbeats 100000000 in
/-- Size and frame of the storage after `PERFORM 4000-TRNXFILE-GET`. -/
theorem p4_sf (env : Env) (m : Nat) (mem : Mem) (hm : mem.size = 178495)
    (idx : List (Nat × Int)) (out : List Event) (inp : List (Nat × List (List UInt8))) (clockN : Nat)
    (r1 r2 : List (List UInt8)) (f3 f4 f5 f6 : FileSt)
    (gs : List (List (List UInt8)))
    (hcr : mem.read 1380 2 = encodeNum {} { digits := 4, signed := true, usage := .binary }
      (gs.length : Int))
    (m0 : Mem) (htbl : mem.read 4365 171258 = m0.read 4365 171258) (hS : P4Static m gs m0)
    (X : List UInt8) (hX : mem.read 530 16 = X) (hXl : X.length = 16)
    (k01 : mem.read 2470 80 = [92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 226, 227, 193, 217, 227, 64, 214, 198, 64, 226, 227, 193, 227, 197, 212, 197, 213, 227, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92])
    (k02 : mem.read 2625 5 = [64, 64, 64, 64, 64])
    (k03 : mem.read 2680 30 = [64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64])
    (k04 : mem.read 2760 30 = [64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64])
    (k05 : mem.read 2870 80 = [96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96])
    (k06 : mem.read 2950 80 = [64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 194, 129, 162, 137, 131, 64, 196, 133, 163, 129, 137, 147, 162, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64])
    (k07 : mem.read 3030 20 = [193, 131, 131, 150, 164, 149, 163, 64, 201, 196, 64, 64, 64, 64, 64, 64, 64, 64, 64, 122])
    (k08 : mem.read 3070 40 = [64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64])
    (k09 : mem.read 3110 20 = [195, 164, 153, 153, 133, 149, 163, 64, 194, 129, 147, 129, 149, 131, 133, 64, 64, 64, 64, 122])
    (k10 : mem.read 3143 47 = [64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64])
    (k11 : mem.read 3190 20 = [198, 201, 195, 214, 64, 226, 131, 150, 153, 133, 64, 64, 64, 64, 64, 64, 64, 64, 64, 122])
    (k12 : mem.read 3230 40 = [64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64])
    (k13 : mem.read 3270 80 = [96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96])
    (k14 : mem.read 3350 80 = [64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 227, 217, 193, 213, 226, 193, 195, 227, 201, 214, 213, 64, 226, 228, 212, 212, 193, 217, 232, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64])
    (k15 : mem.read 3430 80 = [96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96])
    (k16 : mem.read 3510 80 = [227, 153, 129, 149, 64, 201, 196, 64, 64, 64, 64, 64, 64, 64, 64, 64, 227, 153, 129, 149, 64, 196, 133, 163, 129, 137, 147, 162, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 227, 153, 129, 149, 64, 193, 148, 150, 164, 149, 163])
    (k17 : mem.read 3606 1 = [64])
    (k18 : mem.read 3656 1 = [91])
    (k19 : mem.read 3670 67 = [227, 150, 163, 129, 147, 64, 197, 231, 215, 122, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 91])
    (k20 : mem.read 3750 80 = [92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 197, 213, 196, 64, 214, 198, 64, 226, 227, 193, 227, 197, 212, 197, 213, 227, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92])
    (k21 : mem.read 3930 34 = [76, 136, 243, 110, 226, 163, 129, 163, 133, 148, 133, 149, 163, 64, 134, 150, 153, 64, 193, 131, 131, 150, 164, 149, 163, 64, 213, 164, 148, 130, 133, 153, 122, 64])
    (k22 : mem.read 3984 5 = [76, 97, 136, 243, 110])
    (k23 : mem.read 3989 26 = [76, 151, 64, 162, 163, 168, 147, 133, 126, 127, 134, 150, 149, 163, 96, 162, 137, 169, 133, 122, 241, 246, 151, 167, 127, 110])
    (hacc : mem.read 1388 6 =
      encodeNum {} { digits := 11, scale := 2, signed := true, usage := .packed } 0) (fuel : Nat) :
    (p4st env m fuel ⟨mem, idx, [], [], [], out, inp,
          [(1, { mode := some .output, recs := r1 }), (2, { mode := some .output, recs := r2 }),
           (3, f3), (4, f4), (5, f5), (6, f6)], clockN⟩).mem.size = 178495 ∧
    TrnxFrame mem (p4st env m fuel ⟨mem, idx, [], [], [], out, inp,
          [(1, { mode := some .output, recs := r1 }), (2, { mode := some .output, recs := r2 }),
           (3, f3), (4, f4), (5, f5), (6, f6)], clockN⟩).mem :=
  ⟨p4_size env m mem hm idx out inp clockN r1 r2 f3 f4 f5 f6 gs hcr m0 htbl hS X hX hXl k01 k02 k03
    k04 k05 k06 k07 k08 k09 k10 k11 k12 k13 k14 k15 k16 k17 k18 k19 k20 k21 k22 k23 hacc fuel,
   p4_frame env m mem hm idx out inp clockN r1 r2 f3 f4 f5 f6 gs hcr m0 htbl hS X hX hXl k01 k02 k03
    k04 k05 k06 k07 k08 k09 k10 k11 k12 k13 k14 k15 k16 k17 k18 k19 k20 k21 k22 k23 hacc fuel⟩

open Lean Meta Elab Tactic in
/-- `p4_gen`: replace the storage after `PERFORM 4000-TRNXFILE-GET` in the goal, `(p4st …).mem`,
by a variable `PM` (`hPM : (p4st …).mem = PM`), with the hypothesis
`hPM4 : PM.size = 178495 ∧ TrnxFrame mem PM` (`mem`: the storage before), proved in a first goal. -/
elab "p4_gen" : tactic => withMainContext do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  let some e := t.find? (fun e => e.isAppOfArity ``p4st 4)
    | throwError "p4_gen: no `p4st` in the goal"
  let S := e.getAppArgs[3]!
  unless S.isAppOfArity ``State.mk 9 do throwError "p4_gen: the state is not a structure instance"
  let memS := S.getAppArgs[0]!
  let pm ← mkAppM ``State.mem #[e]
  let (fvs, g1) ← g.generalize #[{ expr := pm, xName? := some `PM, hName? := some `hPM }]
  g1.withContext do
    let PM := mkFVar fvs[0]!
    let ty := mkApp2 (mkConst ``And) (← mkEq (← mkAppM ``Mem.size #[PM]) (mkNatLit 178495))
      (← mkAppM ``TrnxFrame #[memS, PM])
    let gP ← mkFreshExprSyntheticOpaqueMVar ty
    let g2 ← g1.assert `hPM4 ty gP
    let (_, g3) ← g2.intro1P
    replaceMainGoal [gP.mvarId!, g3]

/-- A run that ends with `GOBACK` in a state satisfying `I`. -/
def StopAnd (I : State → Prop) (r : Sem.Res) : Prop := r.1 = .stop .goback ∧ I r.2

/-- The end of `1000-MAINLINE`: the events and the records of every cross-reference record, in
order; the six files closed. -/
def MainPost (gs : List (List (List UInt8))) (xrefs custs accts : List (List UInt8))
    (out0 : List Event) (r1 r2 : List (List UInt8)) (f3 : FileSt) (st : State) : Prop :=
  st.out = (xrefs.flatMap (evsOf gs custs accts)).reverse ++ out0 ∧
  ∃ q5 e5 q6 e6, st.files =
    [(1, { mode := none, recs := r1 ++ xrefs.flatMap (stmtOf gs custs accts) }),
     (2, { mode := none, recs := r2 ++ xrefs.flatMap (htmlOf gs custs accts) }),
     (3, { f3 with mode := none, cur := none }),
     (4, { mode := none, recs := xrefs, pos := xrefs.length, eof := true }),
     (5, { mode := none, recs := custs, pos := q5, eof := e5 }),
     (6, { mode := none, recs := accts, pos := q6, eof := e6 })]

attribute [local cobol_eval high] html5100 html5200 xref_found xref_eof cust_found acct_found
  create_rawE

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 50000 in
/-- One iteration of the cross-reference loop (statement 8 of `1000-MAINLINE`) on a valid record
`x'`: the record read through `CBSTM03B`, its customer and account by key,
`5000-CREATE-STATEMENT`, `4000-TRNXFILE-GET`; the invariant holds with `x'` done. -/
theorem iter_some (env : Env) (m : Nat) (gs : List (List (List UInt8))) (m0 : Mem)
    (hS : P4Static (m + 8) gs m0) (xrefs custs accts : List (List UInt8))
    (idx : List (Nat × Int)) (inp : List (Nat × List (List UInt8))) (clockN : Nat)
    (out0 : List Event) (r1 r2 : List (List UInt8)) (f3 : FileSt)
    (mem : Mem) (done rest' : List (List UInt8)) (x' : List UInt8)
    (hxs : xrefs = done ++ x' :: rest') (hxok : XOk custs accts x')
    (hsz : mem.size = 178495) (htbl : mem.read 4365 171258 = m0.read 4365 171258)
    (hcr : mem.read 1380 2 = encodeNum {} { digits := 4, signed := true, usage := .binary }
      (gs.length : Int))
    (hc : ConstsOk mem) (heof : mem.read 1429 1 = [213])
    (q5 : Nat) (e5 : Bool) (c5 : Option Nat) (q6 : Nat) (e6 : Bool) (c6 cu4 : Option Nat) :
    NormalAnd (MInv gs xrefs custs accts m0 idx inp clockN out0 r1 r2 f3 (rest'.map some ++ [none]))
      (Sem.execStmts Stm env (Sem.runFrom Stm env (m + 10)) (m + 10) [Stm.«1000-MAINLINE».s8]
        ⟨mem, idx, [], [], [], (done.flatMap (evsOf gs custs accts)).reverse ++ out0, inp,
          [(1, { mode := some .output, recs := r1 ++ done.flatMap (stmtOf gs custs accts) }),
           (2, { mode := some .output, recs := r2 ++ done.flatMap (htmlOf gs custs accts) }), (3, f3),
           (4, { mode := some .input, recs := xrefs, pos := done.length, eof := false, cur := cu4 }),
           (5, { mode := some .input, recs := custs, pos := q5, eof := e5, cur := c5 }),
           (6, { mode := some .input, recs := accts, pos := q6, eof := e6, cur := c6 })], clockN⟩) := by
  unfold NormalAnd
  obtain ⟨hxl, hcid, haid, hcf, hcl, haf, hal, haid2, hbal, hfico⟩ := hxok
  obtain ⟨i, hki⟩ := Option.isSome_iff_exists.mp hcf
  obtain ⟨j, hkj⟩ := Option.isSome_iff_exists.mp haf
  have hco : custOf custs x' = custs.getD i [] := by simp [custOf, hki]
  have hao : acctOf accts x' = accts.getD j [] := by simp [acctOf, hkj]
  rw [hco] at hcl hfico
  rw [hao] at hal haid2 hbal
  have hy : xrefs[done.length]? = some x' := by rw [hxs]; simp
  have haidb : (xAid x').natAbs < 100000000000 := (decodeNum_holds _ _ haid).1
  have hed : Edit.edit {} [.nine, .nine, .nine, .nine, .nine, .nine, .nine, .nine, .nine, .dot,
      .nine, .nine, .minus] false (aBal (accts.getD j [])) 2 = some (edit9 (aBal (accts.getD j []))) :=
    edit9_eq _
  have hel := length_edit9 (aBal (accts.getD j []))
  clear hcf haf
  simp only [ConstsOk] at hc
  obtain ⟨k01, k02, k03, k04, k05, k06, k07, k08, k09, k10, k11, k12, k13, k14, k15, k16, k17, k18,
    k19, k20, k21, k22, k23⟩ := hc
  stm_auto [hS, List.length_take, List.length_drop, length_ovw,
    perform4_eq (m := m + 8) (gs := gs) (m0 := m0) (hS := hS)]
  p4_gen
  · rw [← hPM]
    refine p4_sf env (m + 8) _ ?_ _ _ _ _ _ _ _ _ _ _ gs ?_ m0 ?_ hS (List.take 16 x') ?_ ?_ ?_ ?_ ?_
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ _
    all_goals stm_auto [List.length_take, length_ovw]
  obtain ⟨hz, F1, F2, F3, F4, F5, F6, F7, F8, F9⟩ := hPM4
  clear hPM
  unfold MInv
  refine ⟨done ++ [x'], rest', by rw [hxs]; simp, rfl, rfl, rfl, rfl, rfl, rfl, ?_, hz, ?_, ?_, ?_,
    i + 1, false, some i, j + 1, false, some j, some done.length, Or.inl ⟨rfl, ?_, ?_⟩⟩
  · -- the events: the statement head, then the transactions
    dsimp only
    simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.reverse_append, evsOf, hco, hao, xCard, List.append_assoc, List.append_cancel_left_eq]
    simp only [headE, fld, stName, stAdd3, stAcctId, stFico]
    text_simp
  · stm_auto [F9, List.length_take, List.length_drop, length_ovw]
  · stm_auto [F1, List.length_take, List.length_drop, length_ovw]
  · simp only [ConstsOk]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_⟩ <;> stm_auto [F3, F4, F5, F6, F7, F8, List.length_take, List.length_drop, length_ovw]
  · stm_auto [F3, List.length_take, List.length_drop, length_ovw]
  · -- the files: both records appended, the three input files one record further
    dsimp only
    simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      stmtOf, htmlOf, hco, hao, xCard, List.append_assoc, List.length_append, List.length_singleton]
    simp only [headS, headH, fld, stName, stAdd3, stAcctId, stFico]
    text_simp

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 50000 in
/-- **Phase 4: `1000-MAINLINE`.** From the loop invariant with every cross-reference record still
to read (`h0`: storage, table `m0` of the groups `gs`, constant texts, the files open), when
every record is valid with its customer and account found (`hx`), the program writes the
statement of each record in turn (`evsOf`, `stmtOf`, `htmlOf`), closes the six files and ends
with `GOBACK`. -/
theorem mainline_ok (env : Env) (m : Nat) (gs : List (List (List UInt8))) (m0 : Mem)
    (hS : P4Static (m + 8) gs m0)
    (xrefs custs accts : List (List UInt8)) (hx : ∀ x ∈ xrefs, XOk custs accts x)
    (hxlen : xrefs.length + 1 < m + 10)
    (idx : List (Nat × Int)) (inp : List (Nat × List (List UInt8))) (clockN : Nat)
    (out0 : List Event) (r1 r2 : List (List UInt8)) (f3 : FileSt) (hf3 : f3.mode = some .input)
    (st0 : State)
    (h0 : MInv gs xrefs custs accts m0 idx inp clockN out0 r1 r2 f3 (xrefs.map some ++ [none]) st0) :
    StopAnd (MainPost gs xrefs custs accts out0 r1 r2 f3) (Sem.runFrom Stm env (m + 11) 2 st0) := by
  unfold StopAnd MainPost
  stm_auto
  cobol_loop (MInv gs xrefs custs accts m0 idx inp clockN out0 r1 r2 f3) (xrefs.map some ++ [none])
  · -- after the loop: the four `CBSTM03B` closes, `CLOSE STMT-FILE HTML-FILE`, `GOBACK`
    obtain ⟨mem, idx', slots', saves', active', out', inp', files', clockN'⟩ := loopState
    obtain ⟨done, rest, hxs, hidx, hsl, hsv, hac, hinp, hclk, hout, hsz, htbl, hcr, hc, q5, e5, c5, q6,
      e6, c6, cu4, hcase⟩ := hloopInv
    dsimp only at hidx hsl hsv hac hinp hclk hout hsz htbl hcr hc hcase
    subst idx' slots' saves' active' inp' clockN' out'
    obtain ⟨-, hr, heof, hfiles⟩ := hcase.resolve_left (fun ⟨h, _, _⟩ => by simp at h)
    subst hr files'
    simp only [List.append_nil] at hxs
    subst hxs
    clear hloopEq h0 hc htbl hcr hx
    stm_auto
    first
      | done
      | exact ⟨q5, e5, q6, e6, rfl, rfl⟩
      | (trace_state; sorry)
  · exact h0
  · simp; omega
  · -- the end of the file was read: `END-OF-FILE = 'Y'`
    rintro ⟨mem, idx', slots', saves', active', out', inp', files', clockN'⟩
      ⟨done, rest, -, -, -, -, -, -, -, -, -, -, -, -, q5, e5, c5, q6, e6, c6, cu4, hcase⟩
    rcases hcase with ⟨hi, -, -⟩ | ⟨-, -, heof, -⟩
    · simp at hi
    · dsimp only at heof
      stm_auto
  · rintro item items' ⟨mem, idx', slots', saves', active', out', inp', files', clockN'⟩
      ⟨done, rest, hxs, hidx, hsl, hsv, hac, hinp, hclk, hout, hsz, htbl, hcr, hc, q5, e5, c5, q6, e6,
        c6, cu4, hcase⟩
    dsimp only at hidx hsl hsv hac hinp hclk hout hsz htbl hcr hc hcase
    subst idx' slots' saves' active' inp' clockN' out'
    obtain ⟨hi, heof, hfiles⟩ := hcase.resolve_right (fun ⟨h, _, _, _⟩ => by simp at h)
    subst files'
    cases item with
    | none =>
      -- the end of the file: `END-OF-FILE := 'Y'`, nothing else
      have hr : rest = [] := by
        cases rest with
        | nil => rfl
        | cons r rs => simp at hi
      subst hr
      have hi' : items' = [] := by simpa using hi
      subst hi'
      simp only [List.append_nil] at hxs
      subst hxs
      have hy : xrefs[xrefs.length]? = none := by simp
      simp only [ConstsOk] at hc
      obtain ⟨k01, k02, k03, k04, k05, k06, k07, k08, k09, k10, k11, k12, k13, k14, k15, k16, k17, k18,
        k19, k20, k21, k22, k23⟩ := hc
      refine ⟨by stm_auto, by stm_auto, ?_⟩
      refine ⟨xrefs, [], by simp, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, q5, e5, c5, q6, e6, c6, cu4,
        Or.inr ⟨rfl, rfl, ?_, ?_⟩⟩
      all_goals try (stm_auto; done)
      simp only [ConstsOk]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
        ?_⟩ <;> stm_auto
    | some x =>
      -- a record: its customer and account, `5000-CREATE-STATEMENT`, `4000-TRNXFILE-GET`
      obtain ⟨x', rest', rfl⟩ : ∃ x' rest', rest = x' :: rest' := by
        cases rest with
        | nil => simp at hi
        | cons r rs => exact ⟨r, rs, rfl⟩
      simp only [List.map_cons, List.cons_append, List.cons.injEq, Option.some.injEq] at hi
      obtain ⟨hxx, hi'⟩ := hi
      subst x hi'
      have hxm : x' ∈ xrefs := by rw [hxs]; simp
      exact ⟨by stm_auto, iter_some env m gs m0 hS xrefs custs accts idx inp clockN out0 r1 r2 f3 mem
        done rest' x' hxs (hx x' hxm) hsz htbl hcr hc heof q5 e5 c5 q6 e6 c6 cu4⟩

end Cobol.StmCore
