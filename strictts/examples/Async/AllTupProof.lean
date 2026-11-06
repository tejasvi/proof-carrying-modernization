/-
Whole run of `all_tuple.ts`: `Promise.all` over a tuple of different types (`promAllTup`) and
`Promise.allSettled` over a tuple with a rejection (`promAllSettledTup`), against a then chain.
For every implementation of the host functions, the console output of the run is the one Node
prints: the simp call of `ts_drain`, with `decide` for the string literals the run compares and
builds, executes the module body and every job.
-/
import Async.AllTupEx
import StrictTS.Proof.AsyncRace
import StrictTS.Proof.Tactics
import StrictTS.Str.Lemmas

open StrictTS JS

namespace AllTupEx

theorem program_main : program.main = mainBlock := rfl
theorem program_globals : program.globals = [] := rfl

set_option maxRecDepth 100000 in
theorem output (I : Impl) :
    runOutput I program = some (.ok (), [JSStr.ofString "word b", JSStr.ofString "sync",
      JSStr.ofString "word a", JSStr.ofString "tick 1", JSStr.ofString "count 2",
      JSStr.ofString "tick 2", JSStr.ofString "settled: b rejected", JSStr.ofString "all: 2 a"]) := by
  -- `ts_drain` with `decide`: the narrowing `x.status === "fulfilled"` compares string literals
  simp (config := { decide := true }) [ts_sym, exec_drain_mk_cons, exec_drain_mk_nil, eventLoop_eq,
    exec_eventLoopTail_mk, earliestTimer, runOutput_eq, runProgram, World.init, program_main,
    program_globals, mainBlock, count_call, countDef, word_call, wordDef, fail_call, failDef]

end AllTupEx
