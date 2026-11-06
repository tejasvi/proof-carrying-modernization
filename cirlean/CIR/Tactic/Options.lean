import Lean

/-- Debugging: when true, `cir_step` never case-splits on stuck `match`es, so
the first goal where symbolic execution is stuck is left for inspection. -/
register_option cir.nosplit : Bool := {
  defValue := false
  descr := "cir_step: do not split stuck matches (debugging)"
}

/-- Debugging: log the arithmetic facts the lookup simprocs prove by `omega`. -/
register_option cir.traceOmega : Bool := {
  defValue := false
  descr := "log omega calls made by the CIR lookup simprocs"
}

/-- Debugging: log symbolic execution steps slower than 200 ms. -/
register_option cir.traceSteps : Bool := {
  defValue := false
  descr := "log slow cir_step steps"
}

/-- Modular verification: when false, a call of a function with a body is
never inlined; it must be covered by a `@[cir_spec]` theorem (library models
are still used). -/
register_option cir.inline : Bool := {
  defValue := true
  descr := "cir_vcg: inline the bodies of callees without a @[cir_spec] theorem"
}

/-- Debugging: the number of steps `cir_run` takes at most. -/
register_option cir.unroll : Bool := {
  defValue := false
  descr := "cir_vcg: execute loops iteration by iteration instead of stopping at them (cir_eval)"
}

register_option cir.fuel : Nat := {
  defValue := 100000
  descr := "cir_run: maximum number of symbolic execution steps (debugging)"
}

/-- Small memory terms: when true, symbolic execution pushes scope exits into
the writes and drops writes that are dead or overwritten (`normKillRange`,
`collapseUpd`). -/
register_option cir.normMem : Bool := {
  defValue := true
  descr := "cir_run: normalize memory terms (scope exits, dead and overwritten writes)"
}

/-- Loops carry the well-formedness of memory (`LoopFrameW`): each iteration
shows that it keeps the memory well formed, and after the loop (and in its
body) `cirH_wf : σ.mem.WF` holds when the entry memory is well formed. -/
register_option cir.loopWF : Bool := {
  defValue := false
  descr := "cir_loop: carry Mem.WF across loops (LoopFrameW)"
}

/-- `cir_run`: when a goal is stuck, split its latest disjunctive callee
postcondition (`cirH_post…`, e.g. "null or a fresh block", "returns 0 or 1")
and go on in both cases (`cir_split_post_or`). Off by default: it renames the
postcondition's facts that a proof script may refer to. -/
register_option cir.splitOr : Bool := {
  defValue := false
  descr := "cir_run: split the disjunctive callee postcondition of a stuck goal"
}

/-- `cir_run`: the heartbeat budget of one step (0: `maxHeartbeats`). A small
budget leaves a hopeless step's goal open instead of spending minutes on it. -/
register_option cir.stepHeartbeats : Nat := {
  defValue := 0
  descr := "cir_run: heartbeats per symbolic execution step (0: maxHeartbeats)"
}

/-- `cir_call_spec`: when the memory before a call is provably well formed
(`cir_wf_core`), the continuation also gets `cirH_cwfN : cir_memN.WF` for the
memory after it (`holds_call_spec_wf`, from `Returns.wf`): contracts need not
state `m'.WF`. Off by default: one more well-formedness fact in context can
change which one an `‹_›` in an existing proof script picks. -/
register_option cir.callWF : Bool := {
  defValue := false
  descr := "cir_call_spec: add the well-formedness of the memory after a call"
}
