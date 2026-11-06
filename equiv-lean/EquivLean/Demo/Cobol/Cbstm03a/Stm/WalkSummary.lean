/-
# Phase 0 of `CBSTM03AB`: the initial `PSA`/`TCB`/`TIOT` walk (`[s0]..[s7], [s13], [s16]`)

Proves the exact execution equation for the first 10 top-level sentences of `Stm.para0.body`:
`[[Stm.para0.s0], [Stm.para0.s1], [Stm.para0.s2], [Stm.para0.s3], [Stm.para0.s4],`
` [Stm.para0.s5], [Stm.para0.s6], [Stm.para0.s7], [Stm.para0.s13], [Stm.para0.s16]]`
(where `s13` is the `PERFORM UNTIL` loop over `TIOT-ENTRY` and `s16` is the post-loop `IF`),
before `[s17, s18]` (`OPEN OUTPUT STMT-FILE HTML-FILE`) and `[s19..s1140]` (`INITIALIZE`), on
the constructed address space `asp` (`Variant B`).

Also proves `execSentences_para0_split`, which splits `Sem.execSentences Stm env rec (fuel + 9) Stm.para0.body st`
directly into `Sem.execSentences Stm env rec (fuel + 9) [[s17, s18], [s19..s1140]] { st with mem := walkMem st.mem, out := walkDisplays ++ st.out }`.
-/
import EquivLean.Demo.Cobol.Cbstm03a.Stm.AddrSpace
import EquivLean.Demo.Cobol.Cbstm03a.Stm.MoveNum
import EquivLean.Demo.Cobol.Cbstm03a.Stm.FlowEqns
import Cobol.Ext.CardDemo

open Cobol Cobol.Stm

namespace Cobol.Stm

cobol_program Stm from "../../../../../examples/cobol/carddemo/cbstm03ab.ir.json"
stm_runFrom_eqns Stm

/-- Length of `(List.range n).map f`, so `normWrite` collapses overwritten `SET ADDRESS OF` writes. -/
theorem length_map_range (n : Nat) (f : Nat → UInt8) :
    ((List.range n).map f).length = n := by
  simp

/-- The 11 `DISPLAY` lines emitted by the 10-sentence walk `[s0]..[s7], [s13], [s16]` on `asp`
(stored in reverse order in `State.out`). -/
def walkDisplays : List Event :=
  [ Event.display [122, 64, 200, 227, 212, 211, 198, 201, 211, 197, 64, 96, 96, 64, 165, 129, 147, 137, 132, 64, 228, 195, 194],
    Event.display [122, 64, 226, 227, 212, 227, 198, 201, 211, 197, 64, 96, 96, 64, 165, 129, 147, 137, 132, 64, 228, 195, 194],
    Event.display [122, 64, 195, 228, 226, 227, 198, 201, 211, 197, 64, 96, 96, 64, 165, 129, 147, 137, 132, 64, 228, 195, 194],
    Event.display [122, 64, 193, 195, 195, 227, 198, 201, 211, 197, 64, 96, 96, 64, 165, 129, 147, 137, 132, 64, 228, 195, 194],
    Event.display [122, 64, 231, 217, 197, 198, 198, 201, 211, 197, 64, 96, 96, 64, 165, 129, 147, 137, 132, 64, 228, 195, 194],
    Event.display [122, 64, 227, 217, 213, 231, 198, 201, 211, 197, 64, 96, 96, 64, 165, 129, 147, 137, 132, 64, 228, 195, 194],
    Event.display [122, 64, 226, 232, 226, 214, 228, 227, 64, 64, 64, 96, 96, 64, 64, 149, 164, 147, 147, 64, 228, 195, 194],
    Event.display [122, 64, 226, 232, 226, 215, 217, 201, 213, 227, 64, 96, 96, 64, 64, 149, 164, 147, 147, 64, 228, 195, 194],
    Event.display [122, 64, 226, 227, 197, 215, 211, 201, 194, 64, 64, 96, 96, 64, 165, 129, 147, 137, 132, 64, 228, 195, 194],
    Event.display [196, 196, 64, 213, 129, 148, 133, 162, 64, 134, 153, 150, 148, 64, 227, 201, 214, 227, 122, 64],
    Event.display [217, 164, 149, 149, 137, 149, 135, 64, 209, 195, 211, 64, 122, 64,
              195, 217, 197, 193, 226, 227, 212, 227, 64, 226, 163, 133, 151, 64,
              226, 227, 197, 215, 240, 244, 240, 64] ]

/-- Memory after the 10-sentence walk (`PSA_BLOCK`, `TCB_BLOCK`, `TIOT_BLOCK`, `TIOT_INDEX`, `TIOT_ENTRY`). -/
def walkMem (m : Mem) : Mem :=
  ((((m.write 175627 (encodeNum {} { digits := 8, signed := true, usage := Usage.binary } 8376)).write
      175639 ((List.range 540).map fun i => asp i)).write
      176179 ((List.range 16).map fun i => asp (4096 + i))).write
      176195 ((List.range 24).map fun i => asp (8192 + i))).write
      176219 ((List.range 24).map fun i => asp (8376 + i))

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 2000000 in
/-- **Walk summary (`para0` sentences `0..9`, i.e. `[[s0]..[s7], [s13], [s16]]`):** starting from any state `st`
with `st.mem.size = 178495` and `PSAPTR = 0` (`st.mem.read 175623 4 = [0, 0, 0, 0]`), executing the first 10
top-level sentences of `para0` (`[s0]..[s7], [s13], [s16]`) under `env.addrSpace = asp` with loop fuel `fuel + 9`
completes normally with `mem = walkMem st.mem` and `out = walkDisplays ++ st.out`. -/
theorem execSentences_walk (env : Env) (hEnv : env.addrSpace = asp)
    (rec : Nat → State → Sem.Res) (fuel : Nat) (st : State)
    (hm : st.mem.size = 178495) (hp : st.mem.read 175623 4 = [0, 0, 0, 0]) :
    Sem.execSentences Stm env rec (fuel + 9)
      [[Stm.para0.s0], [Stm.para0.s1], [Stm.para0.s2], [Stm.para0.s3], [Stm.para0.s4],
       [Stm.para0.s5], [Stm.para0.s6], [Stm.para0.s7], [Stm.para0.s13], [Stm.para0.s16]] st =
      (.normal, { st with mem := walkMem st.mem, out := walkDisplays ++ st.out }) := by
  unfold walkMem walkDisplays
  cobol_auto [hm, hp, hEnv, stm_flow, ↓execStmt_move_num_num, loopUntil_succ_before,
    length_map_range, read_write_map_range, map_range_1, map_range_2, map_range_3, map_range_4, map_range_8,
    reduceAsp]

/-- Generalized `execSentences` append lemma, so `execSentences_walk` splits `Stm.para0.body`
cleanly into the walk prefix followed by `[s17, s18]` (`OPEN`) and `[s19..s1140]` (`INITIALIZE`). -/
theorem execSentences_append (P : Program) (env : Env) (rec : Nat → State → Sem.Res)
    (fuel : Nat) (as bs : List (List Stmt)) (st st1 : State)
    (h : Sem.execSentences P env rec fuel as st = (.normal, st1)) :
    Sem.execSentences P env rec fuel (as ++ bs) st = Sem.execSentences P env rec fuel bs st1 := by
  induction as generalizing st with
  | nil =>
    rw [execSentences_nil] at h
    cases h
    rfl
  | cons a as ih =>
    simp only [List.cons_append, execSentences_cons] at h ⊢
    revert h
    cases Sem.execStmts P env rec fuel a st with
    | mk sig s =>
      cases sig <;> intro h <;> first | exact ih s h | cases h

#print axioms execSentences_walk
#print axioms execSentences_append

end Cobol.Stm
