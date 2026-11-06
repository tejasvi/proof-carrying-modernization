/-
StrictTS proof layer: concurrent async code (interleavings and races).

JavaScript runs one job at a time: an async body runs synchronously until its next `await`,
and the microtask loop (`drain`) runs each job to completion before the next. This file turns
that into proof rules.

* **Atomicity.** `execAB_of_noAwait`: an `await`-free part of an async body is one big-step
  evaluation (`evalB`) followed by its continuation, so no other job can interleave with it;
  `runJob_await_of_noAwait`: a resumed task runs the rest of its body that way;
  `exec_drain_run`: the loop runs the first job to completion, then the others.
* **Job specifications.** `JobSpec I P j pre f new`: from every world whose queue-free part
  satisfies `pre`, the job changes that part by `f` and appends `new` to the pending queue: it
  neither reads nor reorders pending jobs. Specifications of concrete jobs are proved by
  symbolic execution (`ts_sym`) on a world with an arbitrary queue.
* **Commutation and composition.** `exec_drain_swap`: two adjacent jobs whose effects commute
  can be swapped without changing the outcome of the loop; `exec_drain_perm`: every order of a
  batch of pairwise independent jobs gives the same outcome; `exec_drain_specs`: a batch of
  jobs that enqueue nothing amounts to the composition of their effects.
* **Running the queue.** `ts_drain`: symbolic execution of the microtask loop on a world whose
  queue is a concrete list, one job after the other until the queue is empty, and of the event
  loop (timers), so that the console output of a whole run (`runOutput`) can be computed.
-/
import StrictTS.Proof.Async

namespace StrictTS
open JS

variable {TT : TypeTable}

/-! ### Atomicity -/

/-- **Atomicity of an `await`-free segment**: an async body without `await` runs as one
big-step evaluation (`evalB`), then its continuation. The CPS executor cannot suspend
inside it, so no other job runs between its statements. -/
theorem execAB_of_noAwait (I : Impl) (P : Program TT) {ρ : Ty} :
    ∀ {Γ : Ctx} (b : Block TT Γ ρ) (env : Env TT Γ) (k : AK TT ρ Γ), b.hasAwait = false →
      execAB I P b env k = (evalB I P b env >>= fun r => applyK I P k r.1 r.2)
  | _, .nil, env, k, _ => by
    rw [execAB.eq_1, evalB.eq_1, pure_bind]
  | _, .seq s rest, env, k, h => by
    simp only [Block.hasAwait, Bool.or_eq_false_iff] at h
    rw [execAB.eq_2, execAS.eq_def]
    simp only [h.1, Bool.false_eq_true, ite_false]
    rw [evalB.eq_2, bind_assoc]
    refine bind_congr fun r => ?_
    obtain ⟨c, env'⟩ := r
    cases c <;> simp [applyK.eq_2, applyK.eq_3, execAB_of_noAwait I P rest env' k h.2]
  | _, .decl s e rest, env, k, h => by
    simp only [Block.hasAwait] at h
    rw [execAB.eq_3, evalB.eq_3, bind_assoc]
    refine bind_congr fun r => ?_
    cases r with
    | error ex => simp
    | ok v =>
      simp only [execAB_of_noAwait I P rest (.cons v env) (.pop k) h, bind_assoc, pure_bind]
      refine bind_congr fun r => ?_
      rw [applyK.eq_4]
  | _, .await _ _ _, _, _, h => by simp [Block.hasAwait] at h

/-- **A resumed task runs to its next `await`**: the job resuming an async body whose
remaining block has no `await` is the big-step evaluation of that block, then the body's
continuation, then settling (or re-suspending) the body's promise. -/
theorem runJob_await_of_noAwait (I : Impl) (P : Program TT) {Γ : Ctx} {ρ : Ty} {s : Slot}
    (rest : Block TT (s :: Γ) ρ) (env : Env TT Γ) (k : AK TT ρ Γ) (p : Nat) (v : Val TT s.ty)
    (h : rest.hasAwait = false) :
    runJob I P (.react (.await (.mk s rest env k) p) (.ok v)) =
      (evalB I P rest (.cons v env) >>= fun r => applyK I P k r.1 r.2.tail >>= handleStep p) := by
  simp only [runJob, resume, execAB_of_noAwait I P rest _ _ h, bind_assoc]
  refine bind_congr fun r => ?_
  rw [applyK.eq_4]

/-- **The loop runs one job at a time**: the first job runs to completion on the world
without it; the loop then continues from the world it leaves. -/
theorem exec_drain_run (I : Impl) (P : Program TT) {w w' : World TT} {j : Job TT}
    {rest : List (Job TT)} (h : w.jobs = j :: rest)
    (hj : exec (runJob I P j) { w with jobs := rest } = some (.ok (), w')) :
    exec (drain I P) w = exec (drain I P) w' := by
  rw [exec_drain_cons I P w j rest h, exec_bind, hj]

/-- A job that fails ends the loop with its error. -/
theorem exec_drain_run_error (I : Impl) (P : Program TT) {w w' : World TT} {j : Job TT}
    {rest : List (Job TT)} {e : Exc} (h : w.jobs = j :: rest)
    (hj : exec (runJob I P j) { w with jobs := rest } = some (.error e, w')) :
    exec (drain I P) w = some (.error e, w') := by
  rw [exec_drain_cons I P w j rest h, exec_bind, hj]

/-! ### Job specifications -/

/-- The world without its microtask queue. -/
abbrev World.noJobs (w : World TT) : World TT := { w with jobs := [] }

@[simp] theorem World.noJobs_withJobs (w : World TT) (q : List (Job TT)) :
    ({ w with jobs := q } : World TT).noJobs = w.noJobs := rfl

/-- Overwriting the queue forgets everything the queue-free part does not record. -/
theorem World.withJobs_eq_of_noJobs {w₁ w₂ : World TT} (h : w₁.noJobs = w₂.noJobs)
    (q : List (Job TT)) : ({ w₁ with jobs := q } : World TT) = { w₂ with jobs := q } := by
  cases w₁; cases w₂
  simp only [World.noJobs, World.mk.injEq] at h ⊢
  simp [h]

/-- `JobSpec I P j pre f new`: from every world `w` whose queue-free part `w₀ = w.noJobs`
satisfies `pre`, the job `j` runs to completion and leaves the world `f w₀` with the queue
`w.jobs ++ new w₀`. The job does not read the pending queue (its effect depends on `w₀`
only) and only appends to it. -/
def JobSpec (I : Impl) (P : Program TT) (j : Job TT) (pre : World TT → Prop)
    (f : World TT → World TT) (new : World TT → List (Job TT)) : Prop :=
  ∀ w : World TT, pre w.noJobs →
    exec (runJob I P j) w = some (.ok (), { f w.noJobs with jobs := w.jobs ++ new w.noJobs })

/-- A specification holds under any stronger precondition. -/
theorem JobSpec.mono {I : Impl} {P : Program TT} {j : Job TT} {pre pre' : World TT → Prop}
    {f : World TT → World TT} {new : World TT → List (Job TT)} (h : JobSpec I P j pre f new)
    (hp : ∀ w, pre' w → pre w) : JobSpec I P j pre' f new :=
  fun w hw => h w (hp _ hw)

/-- One step of the loop with a specified job. -/
theorem exec_drain_spec {I : Impl} {P : Program TT} {j : Job TT} {pre : World TT → Prop}
    {f : World TT → World TT} {new : World TT → List (Job TT)} (hs : JobSpec I P j pre f new)
    (w : World TT) (rest : List (Job TT)) (hp : pre w.noJobs) :
    exec (drain I P) { w with jobs := j :: rest } =
      exec (drain I P) { f w.noJobs with jobs := rest ++ new w.noJobs } :=
  exec_drain_run I P rfl (hs { w with jobs := rest } hp)

/-! ### Commutation -/

/-- **Swapping two adjacent jobs.** If `j₁` and `j₂` commute as transformations of the
queue-free world (`hf`), the loop has the same outcome with `j₁` first or `j₂` first,
provided the two queues they leave behind have the same outcome (`hq`). When neither job
enqueues anything, or both enqueue the same jobs whatever the order, `hq` is `rfl`; when
each enqueues one follow-up job, `hq` is again a swap. -/
theorem exec_drain_swap {I : Impl} {P : Program TT} {j₁ j₂ : Job TT}
    {pre₁ pre₂ : World TT → Prop} {f₁ f₂ : World TT → World TT}
    {new₁ new₂ : World TT → List (Job TT)}
    (h₁ : JobSpec I P j₁ pre₁ f₁ new₁) (h₂ : JobSpec I P j₂ pre₂ f₂ new₂)
    (w : World TT) (rest : List (Job TT))
    (p₁ : pre₁ w.noJobs) (p₂ : pre₂ w.noJobs)
    (p₁₂ : pre₂ (f₁ w.noJobs).noJobs) (p₂₁ : pre₁ (f₂ w.noJobs).noJobs)
    (hf : (f₂ (f₁ w.noJobs).noJobs).noJobs = (f₁ (f₂ w.noJobs).noJobs).noJobs)
    (hq : exec (drain I P) { f₂ (f₁ w.noJobs).noJobs with
              jobs := rest ++ new₁ w.noJobs ++ new₂ (f₁ w.noJobs).noJobs } =
          exec (drain I P) { f₂ (f₁ w.noJobs).noJobs with
              jobs := rest ++ new₂ w.noJobs ++ new₁ (f₂ w.noJobs).noJobs }) :
    exec (drain I P) { w with jobs := j₁ :: j₂ :: rest } =
      exec (drain I P) { w with jobs := j₂ :: j₁ :: rest } := by
  rw [exec_drain_spec h₁ w (j₂ :: rest) p₁, exec_drain_spec h₂ w (j₁ :: rest) p₂]
  have e₁ := exec_drain_spec h₂ (f₁ w.noJobs) (rest ++ new₁ w.noJobs) p₁₂
  have e₂ := exec_drain_spec h₁ (f₂ w.noJobs) (rest ++ new₂ w.noJobs) p₂₁
  simp only at e₁ e₂
  simp only [List.cons_append, e₁, e₂, World.withJobs_eq_of_noJobs hf.symm, List.append_assoc] at hq ⊢
  simpa only [List.append_assoc] using hq

/-- **Order independence for independent jobs.** Let every job `job i` (`i ∈ is`) have a
specification with effect `F i` that enqueues nothing and preserves an invariant `Inv`, and
let these effects commute pairwise on `Inv`. Then the microtask loop has the same outcome for
every order `is'` of these jobs at the head of the queue. -/
theorem exec_drain_perm {I : Impl} {P : Program TT} {ι : Type} {is is' : List ι}
    (hp : is.Perm is') (job : ι → Job TT) (Inv : World TT → Prop) (F : ι → World TT → World TT)
    (hs : ∀ i ∈ is, JobSpec I P (job i) Inv (F i) (fun _ => []))
    (hinv : ∀ i ∈ is, ∀ w, Inv w → Inv (F i w).noJobs)
    (hc : ∀ i₁ ∈ is, ∀ i₂ ∈ is, ∀ w, Inv w →
      (F i₂ (F i₁ w).noJobs).noJobs = (F i₁ (F i₂ w).noJobs).noJobs)
    (w : World TT) (hw : Inv w.noJobs) (rest : List (Job TT)) :
    exec (drain I P) { w with jobs := is.map job ++ rest } =
      exec (drain I P) { w with jobs := is'.map job ++ rest } := by
  induction hp generalizing w with
  | nil => rfl
  | cons x _ ih =>
    simp only [List.map_cons, List.cons_append]
    rw [exec_drain_spec (hs x (List.mem_cons_self ..)) w _ hw,
      exec_drain_spec (hs x (List.mem_cons_self ..)) w _ hw]
    simp only [List.append_nil]
    exact ih (fun i hi => hs i (List.mem_cons_of_mem _ hi))
      (fun i hi => hinv i (List.mem_cons_of_mem _ hi))
      (fun i₁ h₁ i₂ h₂ => hc i₁ (List.mem_cons_of_mem _ h₁) i₂ (List.mem_cons_of_mem _ h₂))
      _ (by simpa using hinv x (List.mem_cons_self ..) _ hw)
  | swap x y l =>
    have hy : y ∈ y :: x :: l := List.mem_cons_self ..
    have hx : x ∈ y :: x :: l := List.mem_cons_of_mem _ (List.mem_cons_self ..)
    simp only [List.map_cons, List.cons_append]
    refine exec_drain_swap (hs y hy) (hs x hx) w (l.map job ++ rest) hw hw
      (hinv y hy _ hw) (hinv x hx _ hw) (hc y hy x hx _ hw) ?_
    simp only [List.append_nil]
  | trans p₁₂ _ ih₁ ih₂ =>
    have m : ∀ i, i ∈ _ → i ∈ _ := fun i hi => (p₁₂.mem_iff).2 hi
    rw [ih₁ hs hinv hc w hw]
    exact ih₂ (fun i hi => hs i (m i hi)) (fun i hi => hinv i (m i hi))
      (fun i₁ h₁ i₂ h₂ => hc i₁ (m i₁ h₁) i₂ (m i₂ h₂)) w hw

/-- `PreChain pre F is w`: running the effects `F i` of the jobs `is` one after the other from
`w`, each job finds its precondition `pre i`. -/
def PreChain {ι : Type} (pre : ι → World TT → Prop) (F : ι → World TT → World TT) :
    List ι → World TT → Prop
  | [], _ => True
  | i :: is, w => pre i w.noJobs ∧ PreChain pre F is (F i w.noJobs)

/-- **A batch of jobs, one task at a time**: jobs with specifications that enqueue nothing run
in queue order, each on the world the previous one leaves, so the loop continues from the
composition of their effects. -/
theorem exec_drain_specs {I : Impl} {P : Program TT} {ι : Type} (job : ι → Job TT)
    (pre : ι → World TT → Prop) (F : ι → World TT → World TT) (is : List ι)
    (hs : ∀ i ∈ is, JobSpec I P (job i) (pre i) (F i) (fun _ => []))
    (w : World TT) (rest : List (Job TT)) (hp : PreChain pre F is w) :
    exec (drain I P) { w with jobs := is.map job ++ rest } =
      exec (drain I P) { is.foldl (fun w i => F i w.noJobs) w with jobs := rest } := by
  induction is generalizing w with
  | nil => rfl
  | cons i is ih =>
    simp only [List.map_cons, List.cons_append, List.foldl_cons]
    rw [exec_drain_spec (hs i (List.mem_cons_self ..)) w _ hp.1, List.append_nil]
    exact ih (fun j hj => hs j (List.mem_cons_of_mem _ hj)) _ hp.2

/-- Writes to different cells commute (the heap is extensional). -/
theorem heap_insert_comm (h : Heap TT) {k k' : HKind} {a a' : Nat} (c : k.Cell TT)
    (c' : k'.Cell TT) (hne : (k, a) ≠ (k', a')) :
    (h.insert (k, a) c).insert (k', a') c' = (h.insert (k', a') c').insert (k, a) c := by
  apply Std.ExtDHashMap.ext_get?
  intro key
  rw [Std.ExtDHashMap.get?_insert, Std.ExtDHashMap.get?_insert, Std.ExtDHashMap.get?_insert,
    Std.ExtDHashMap.get?_insert]
  by_cases h₁ : (k', a') = key <;> by_cases h₂ : (k, a) = key
  · exact absurd (h₂.trans h₁.symm) hne
  all_goals simp_all

/-- Writing back the value a cell holds changes nothing. -/
theorem heap_insert_of_get (h : Heap TT) {k : HKind} {a : Nat} {c : k.Cell TT}
    (hc : h.get? (k, a) = some c) : h.insert (k, a) c = h := by
  apply Std.ExtDHashMap.ext_get?
  intro key
  rw [Std.ExtDHashMap.get?_insert]
  by_cases h₁ : (k, a) = key
  · subst h₁; simp [hc]
  · simp [h₁]

/-! ### Running the queue -/

/- `execAS` runs a statement containing an `await` (inside a loop, `if`, `try`, …) by the CPS
executor and any other statement by `evalS`; symbolic execution decides which by computing
`hasAwait` on the concrete IR. -/
attribute [ts_sym] Stmt.hasAwait Block.hasAwait AltsS.hasAwait

open Lean Meta Simp in
/-- `Vals.toList` of an explicit list of values (the arguments of an array literal such as
`Promise.all([f(), g()])`). The equation lemmas of `Vals.toList` do not fire there: their
index `List.replicate (n + 1) t` does not match the literal indices of generated code. -/
dsimproc [ts_sym] reduceValsToList (Vals.toList _) := fun e => do
  unless e.isAppOfArity ``Vals.toList 4 do return .continue
  let vs ← whnfR e.appArg!
  unless vs.isAppOf ``Vals.cons || vs.isAppOf ``Vals.nil do return .continue
  let r ← withDefault <| whnf e
  if r == e then return .continue
  return .visit r

/-- The loop on an explicit world with an empty queue stops. -/
theorem exec_drain_mk_nil (I : Impl) (P : Program TT) (heap : Heap TT) (next : Nat)
    (out : List JSStr) (timers : List (Nat × Nat × Val TT (.fn .nil .undef))) (clock seqNo : Nat)
    (rand : Nat → F64) (randIdx : Nat) (now : Nat → F64) (nowIdx : Nat)
    (unhandled : List (Nat × ErrVal)) (ext : ExtOracle TT) (extIdx : Nat) :
    exec (drain I P) ⟨heap, next, out, [], timers, clock, seqNo, rand, randIdx, now, nowIdx, unhandled, ext, extIdx⟩ =
      some (.ok (), ⟨heap, next, out, [], timers, clock, seqNo, rand, randIdx, now, nowIdx, unhandled, ext, extIdx⟩) :=
  exec_drain_nil I P _ rfl

/-- The loop on an explicit world with a non-empty queue runs the first job. -/
theorem exec_drain_mk_cons (I : Impl) (P : Program TT) (heap : Heap TT) (next : Nat)
    (out : List JSStr) (j : Job TT) (rest : List (Job TT))
    (timers : List (Nat × Nat × Val TT (.fn .nil .undef))) (clock seqNo : Nat)
    (rand : Nat → F64) (randIdx : Nat) (now : Nat → F64) (nowIdx : Nat)
    (unhandled : List (Nat × ErrVal)) (ext : ExtOracle TT) (extIdx : Nat) :
    exec (drain I P) ⟨heap, next, out, j :: rest, timers, clock, seqNo, rand, randIdx, now, nowIdx, unhandled, ext, extIdx⟩ =
      exec (runJob I P j >>= fun _ => drain I P)
        ⟨heap, next, out, rest, timers, clock, seqNo, rand, randIdx, now, nowIdx, unhandled, ext, extIdx⟩ :=
  exec_drain_cons I P _ j rest rfl

/-- The event loop after its microtask phase: the unhandled-rejection check, then the
earliest timer (whose callback is followed by the whole loop again). -/
def eventLoopTail (I : Impl) (P : Program TT) : JS TT Unit := do
  let w ← get
  match w.unhandled with
  | (_, e) :: _ => throw (.thrown e)
  | [] =>
  match earliestTimer w.timers with
  | none => pure ()
  | some (due, sq, f) => do
    set { w with timers := w.timers.filter (fun x => x.2.1 != sq), clock := max w.clock due }
    let _ ← applyFn I P f .nil
    eventLoop I P

/-- The event loop is the microtask loop followed by `eventLoopTail`. -/
theorem eventLoop_eq (I : Impl) (P : Program TT) :
    eventLoop I P = (drain I P >>= fun _ => eventLoopTail I P) := by
  rw [eventLoop.eq_1]; rfl

/-- `eventLoopTail` on an explicit world: report an unhandled rejection, stop, or run the
earliest timer. -/
theorem exec_eventLoopTail_mk (I : Impl) (P : Program TT) (heap : Heap TT) (next : Nat)
    (out : List JSStr) (jobs : List (Job TT)) (timers : List (Nat × Nat × Val TT (.fn .nil .undef)))
    (clock seqNo : Nat) (rand : Nat → F64) (randIdx : Nat) (now : Nat → F64) (nowIdx : Nat)
    (unhandled : List (Nat × ErrVal)) (ext : ExtOracle TT) (extIdx : Nat) :
    exec (eventLoopTail I P)
        ⟨heap, next, out, jobs, timers, clock, seqNo, rand, randIdx, now, nowIdx, unhandled, ext, extIdx⟩ =
      match unhandled with
      | (_, e) :: _ => some (.error (.thrown e),
          ⟨heap, next, out, jobs, timers, clock, seqNo, rand, randIdx, now, nowIdx, unhandled, ext, extIdx⟩)
      | [] => match earliestTimer timers with
        | none => some (.ok (),
            ⟨heap, next, out, jobs, timers, clock, seqNo, rand, randIdx, now, nowIdx, unhandled, ext, extIdx⟩)
        | some (due, sq, f) => exec (applyFn I P f .nil >>= fun _ => eventLoop I P)
            ⟨heap, next, out, jobs, timers.filter (fun x => x.2.1 != sq), max clock due, seqNo, rand,
              randIdx, now, nowIdx, unhandled, ext, extIdx⟩ := by
  simp only [eventLoopTail, exec_bind, exec_get]
  rcases unhandled with _ | ⟨⟨_, e⟩, _⟩
  · dsimp only
    cases earliestTimer timers with
    | none => rfl
    | some t => obtain ⟨due, sq, f⟩ := t; simp only [exec_bind, exec_set]
  · rfl

/-- A whole run starts from the initial world. -/
theorem runOutput_eq (I : Impl) (P : Program TT) :
    runOutput I P = (exec (runProgram I P) (World.init TT)).map fun (r, w) => (r, w.out) := rfl

/-- `ts_drain [h, …]`: symbolic execution of async code including its microtask loop. It
runs `simp` with the `ts_sym` set and the given facts, and whenever a world
`exec (drain I P) w` has a queue that is a concrete list, it runs the first job and continues,
until the queue is empty; the event loop (`eventLoop`, hence whole runs `runOutput`) continues
with the earliest timer. Fresh addresses are normalised to `w.next + k` (so that distinct
allocations are told apart by `simp`), `Promise.all` over an array literal is unrolled, and
`setTimeout` delays that are integer literals are computed. -/
syntax (name := tsDrain) "ts_drain" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

macro_rules
  | `(tactic| ts_drain) =>
    `(tactic| simp [ts_sym, exec_drain_mk_cons, exec_drain_mk_nil, eventLoop_eq, exec_eventLoopTail_mk,
        earliestTimer, F64.ge, Nat.add_assoc, List.range_succ, and_assoc])
  | `(tactic| ts_drain [$hs,*]) =>
    `(tactic| simp [ts_sym, exec_drain_mk_cons, exec_drain_mk_nil, eventLoop_eq, exec_eventLoopTail_mk,
        earliestTimer, F64.ge, Nat.add_assoc, List.range_succ, and_assoc, $hs,*])

end StrictTS
