/-
Whole runs of three programs of the differential corpus. For every implementation of the host
functions, the console output of the run (`runOutput`: module body, then the event loop) is
the one Node prints. Each proof is one `ts_drain` call, which executes the module body, every
job of the microtask queue and every timer, then `decide` for the strings the run builds.

* `timers.ts`: `setTimeout` with several delays (`0` is clamped to `1`, as Node does), a timer
  that schedules a microtask, a timer that schedules another timer, `then`, `queueMicrotask`:
  synchronous code first, then the microtasks, then the timers by due time and creation order,
  each followed by the microtasks it schedules.
* `interleave.ts`: three async workers that interleave at the `await` inside their loops, and
  a `main` that awaits them one after the other.
* `all_race.ts`: `Promise.all` and `Promise.race` over async functions that await a different
  number of times (`await null` in a loop), and `Promise.all` of an empty array.
-/
import Async.TimersEx
import Async.InterleaveEx
import Async.AllRaceEx
import StrictTS.Proof.AsyncRace
import StrictTS.Proof.Tactics
import StrictTS.Str.Lemmas

open StrictTS JS

namespace TimersEx

theorem program_main : program.main = mainBlock := rfl
theorem program_globals : program.globals = [] := rfl

theorem output (I : Impl) :
    runOutput I program = some (.ok (), [JSStr.ofString "sync", JSStr.ofString "microtask 1",
      JSStr.ofString "queueMicrotask", JSStr.ofString "timeout 1 (a)",
      JSStr.ofString "microtask inside timer a", JSStr.ofString "timeout 0 (b), same list as 1",
      JSStr.ofString "timeout 100", JSStr.ofString "nested timeout +50 (due 150)",
      JSStr.ofString "timeout 200"]) := by
  ts_drain [runOutput_eq, runProgram, World.init, program_main, program_globals, mainBlock]

end TimersEx

namespace InterleaveEx

theorem program_main : program.main = mainBlock := rfl
theorem program_globals : program.globals = [] := rfl

theorem output (I : Impl) :
    runOutput I program = some (.ok (), [JSStr.ofString "a:1", JSStr.ofString "b:1",
      JSStr.ofString "c:1", JSStr.ofString "all started", JSStr.ofString "sync end",
      JSStr.ofString "a:2", JSStr.ofString "b:2", JSStr.ofString "a:3", JSStr.ofString "a=6",
      JSStr.ofString "b=3 c=1", JSStr.ofString "main finished"]) := by
  ts_drain [runOutput_eq, runProgram, World.init, program_main, program_globals, mainBlock,
    worker_call, main_call, workerDef, mainDef]
  decide

end InterleaveEx

namespace AllRaceEx

theorem program_main : program.main = mainBlock := rfl
theorem program_globals : program.globals = [.arr (.promise .bigint)] := rfl

set_option maxRecDepth 100000 in
theorem output (I : Impl) :
    runOutput I program = some (.ok (), [JSStr.ofString "started", JSStr.ofString "y resolved",
      JSStr.ofString "fast resolved", JSStr.ofString "empty all: true", JSStr.ofString "z resolved",
      JSStr.ofString "x resolved", JSStr.ofString "race: fast", JSStr.ofString "slow resolved",
      JSStr.ofString "all: x,y,z"]) := by
  ts_drain [runOutput_eq, runProgram, World.init, program_main, program_globals, mainBlock,
    delayValue_call, delayValueDef, g_none]
  decide

end AllRaceEx
