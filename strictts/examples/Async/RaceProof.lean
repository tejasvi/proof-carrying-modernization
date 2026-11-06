/-
`examples/Async/race.ts`: a lost update between two concurrent calls of an async increment.

`incRacy` reads the counter, awaits, then writes the value it read plus one. Under
`Promise.all([incRacy(c), incRacy(c)])` both calls read before either writes: each job runs to
completion and the queue is first-in first-out, so the lost update is deterministic and the
counter ends at `x + 1`. `incFixed` reads after its `await`; the two increments then run one
after the other and the counter ends at `x + 1 + 1`. Both statements hold for every double `x`
in the counter and every world whose microtask queue is empty. The corollaries start from
`new Counter()` (`n = 0`): `1` versus `2`; `race_output` states the console output of the whole
program, which is what Node prints (`tests/corpus/async_race_counter.ts` in the differential
corpus).

Each proof is one call of `ts_drain`: it executes the call up to the two suspensions, then the
five jobs of the queue (the two resumptions, the two `Promise.all` slot reactions and the
resumption of `runRacy`/`runFixed`).

The second part reasons one task at a time with the rules of `StrictTS.Proof.AsyncRace`. Each
call queues one resumption job (`incFixed_queues`, `incRacy_queues`); a resumption has a job
specification (`JobSpec`) proved by symbolic execution. Two resumptions on the same counter
commute (`exec_drain_swap`): for `incFixed` both orders add two, for `incRacy` both orders write
the value read plus one, so the update is lost either way. For any number `k` of pending
resumptions (`exec_drain_specs`), `incFixed` adds `k` and `incRacy` leaves the value read plus
one, and every order of the `incFixed` resumptions has the same outcome (`exec_drain_perm`).
-/
import Async.RaceEx
import StrictTS.Proof.AsyncRace
import StrictTS.Proof.Tactics
import StrictTS.Str.Lemmas

open StrictTS JS RaceEx

/-- The racy version loses an update: after `runRacy(c)` and the microtask queue, the counter
holds its initial value plus one, and the promise of `runRacy(c)` is fulfilled. -/
theorem runRacy_lost_update (I : Impl) (w : World TT) (a : Nat) (x : F64) (hj : w.jobs = [])
    (hc : w.heap.get? (.obj "Counter" [.num], a) = some (.cons (some (.num x)) .nil)) :
    ∃ p w₁ w₂, exec (callFun I program runRacyRef (.cons (.obj a) .nil)) w = some (.ok (.promise p), w₁) ∧
      exec (drain I program) w₁ = some (.ok (), w₂) ∧
      w₂.heap.get? (.obj "Counter" [.num], a) = some (.cons (some (.num (x + 1))) .nil) ∧
      ∃ c, w₂.heap.get? (.promise .undef, p) = some c ∧ c.state = .fulfilled .undef := by
  ts_drain [runRacy_call, incRacy_call, runRacyDef, incRacyDef, hj, hc]

/-- The fixed version counts both calls. -/
theorem runFixed_increments_twice (I : Impl) (w : World TT) (a : Nat) (x : F64) (hj : w.jobs = [])
    (hc : w.heap.get? (.obj "Counter" [.num], a) = some (.cons (some (.num x)) .nil)) :
    ∃ p w₁ w₂, exec (callFun I program runFixedRef (.cons (.obj a) .nil)) w = some (.ok (.promise p), w₁) ∧
      exec (drain I program) w₁ = some (.ok (), w₂) ∧
      w₂.heap.get? (.obj "Counter" [.num], a) = some (.cons (some (.num (x + 1 + 1))) .nil) ∧
      ∃ c, w₂.heap.get? (.promise .undef, p) = some c ∧ c.state = .fulfilled .undef := by
  ts_drain [runFixed_call, incFixed_call, runFixedDef, incFixedDef, hj, hc]

/-- `const c = new Counter(); runRacy(c)`: the counter ends at `1`. -/
theorem racy_counter_one (I : Impl) (w : World TT) (hj : w.jobs = []) :
    ∃ a w₁ p w₂ w₃,
      exec (callFun I program Counter_newRef .nil) w = some (.ok (.obj a), w₁) ∧
      exec (callFun I program runRacyRef (.cons (.obj a) .nil)) w₁ = some (.ok (.promise p), w₂) ∧
      exec (drain I program) w₂ = some (.ok (), w₃) ∧
      w₃.heap.get? (.obj "Counter" [.num], a) = some (.cons (some (.num 1)) .nil) := by
  ts_drain [Counter_new_call, runRacy_call, incRacy_call, Counter_newDef, runRacyDef, incRacyDef, hj]

/-- `const c = new Counter(); runFixed(c)`: the counter ends at `2`. -/
theorem fixed_counter_two (I : Impl) (w : World TT) (hj : w.jobs = []) :
    ∃ a w₁ p w₂ w₃,
      exec (callFun I program Counter_newRef .nil) w = some (.ok (.obj a), w₁) ∧
      exec (callFun I program runFixedRef (.cons (.obj a) .nil)) w₁ = some (.ok (.promise p), w₂) ∧
      exec (drain I program) w₂ = some (.ok (), w₃) ∧
      w₃.heap.get? (.obj "Counter" [.num], a) = some (.cons (some (.num 2)) .nil) := by
  ts_drain [Counter_new_call, runFixed_call, incFixed_call, Counter_newDef, runFixedDef, incFixedDef, hj]

theorem RaceEx.program_main : program.main = mainBlock := rfl
theorem RaceEx.program_globals : program.globals = [.obj "Counter", .obj "Counter"] := rfl

/-- **The whole program**: for every implementation of the host functions, running `race.ts`
(module body, then the event loop) prints exactly what Node prints. -/
theorem race_output (I : Impl) :
    runOutput I program = some (.ok (), [JSStr.ofString "racy: 1", JSStr.ofString "fixed: 2"]) := by
  ts_drain [runOutput_eq, runProgram, World.init, program_main, program_globals, mainBlock, g_racy,
    g_fixed, Counter_new_call, runRacy_call, runFixed_call, incRacy_call, incFixed_call, Counter_newDef,
    runRacyDef, runFixedDef, incRacyDef, incFixedDef]
  decide

/-! ### Order independence: the resumptions commute -/

/-- The rest of `incFixed` after its `await`. -/
abbrev incFixedRest : Block TT (⟨.undef, false⟩ :: ([⟨.obj "Counter", false⟩] ++ [])) .undef :=
  .seq (.setField (fs := «Counter».fields) (var! 1) (mem! 0)
    (.prim (.numBin .add) args[.getField (fs := «Counter».fields) (var! 1) (mem! 0), .lit (.num 1)])) .nil

example : incFixedDef.lam = .async [⟨.obj "Counter", false⟩] rfl
    (.await ⟨.undef, false⟩ (.builtin (.promResolve .undef) args[.lit .undef]) incFixedRest) := rfl

/-- The job that resumes `incFixed(c)` after its `await` (`c` at address `a`, the call's
promise `p`). -/
abbrev incFixedJob (a p : Nat) : Job TT :=
  .react (.await (.mk ⟨.undef, false⟩ incFixedRest (.cons (.obj a) .nil) .done) p) (.ok .undef)

/-- A call `incFixed(c)` returns a pending promise `p` and queues `incFixedJob a p`. -/
theorem incFixed_queues (I : Impl) (w : World TT) (a : Nat) :
    ∃ h, exec (callFun I program incFixedRef (.cons (.obj a) .nil)) w =
      some (.ok (.promise w.next),
        { w with heap := h, next := w.next + 2, jobs := w.jobs ++ [incFixedJob a w.next] }) := by
  ts_drain [incFixed_call, incFixedDef, incFixedRest]

/-- The counter at `a` holds a number and the promise `p` exists without reactions. -/
def IncPre (a p : Nat) (w : World TT) : Prop :=
  (∃ x, w.heap.get? (.obj "Counter" [.num], a) = some (.cons (some (.num x)) .nil)) ∧
  ∃ c, w.heap.get? (.promise .undef, p) = some c ∧ c.reactions = []

/-- The number held by the counter at `a`. -/
def counterVal (w : World TT) (a : Nat) : Option F64 :=
  (w.heap.get? (.obj "Counter" [.num], a)).bind fun cell => (cell.get? .here).map Val.toNum

/-- A promise cell after `resolve(undefined)`: fulfilled if it was pending, unchanged otherwise. -/
def settled (c : PromiseCell TT .undef) : PromiseCell TT .undef :=
  match c.state with
  | .pending => { c with state := .fulfilled .undef, reactions := [] }
  | _ => c

/-- Adding one to the counter at `a` and resolving the promise `p`. -/
def incEffect (a p : Nat) (w : World TT) : World TT :=
  match counterVal w a, w.heap.get? (.promise .undef, p) with
  | some x, some c =>
    { w with
      heap := (w.heap.insert (.obj "Counter" [.num], a) (.cons (some (.num (x + 1))) .nil)).insert
        (.promise .undef, p) (settled c) }
  | _, _ => w

/-- The resumption of `incFixed` adds one to the counter and resolves the call's promise (which
has no reactions, so nothing is enqueued). -/
theorem incFixedJob_spec (I : Impl) (a p : Nat) :
    JobSpec I program (incFixedJob a p) (IncPre a p) (incEffect a p) (fun _ => []) := by
  rintro w ⟨⟨x, hx⟩, c, hc, hr⟩
  cases hs : c.state <;>
    simp [ts_sym, incEffect, counterVal, settled, heap_insert_of_get, hx, hc, hs, hr]

/-- The effects of two resumptions on the same counter commute. -/
theorem incEffect_comm (a p₁ p₂ : Nat) (hp : p₁ ≠ p₂) (w : World TT) (x : F64)
    (hx : w.heap.get? (.obj "Counter" [.num], a) = some (.cons (some (.num x)) .nil))
    {c₁ c₂ : PromiseCell TT .undef} (hc₁ : w.heap.get? (.promise .undef, p₁) = some c₁)
    (hc₂ : w.heap.get? (.promise .undef, p₂) = some c₂) :
    (incEffect a p₂ (incEffect a p₁ w).noJobs).noJobs =
      (incEffect a p₁ (incEffect a p₂ w).noJobs).noJobs := by
  have hp' : p₂ ≠ p₁ := Ne.symm hp
  simp only [incEffect, counterVal, OVals.get?, hx, hc₁, hc₂, Option.bind_some, Option.map_some,
    World.noJobs, heap_get_insert_self, heap_get_insert_kind_ne, ne_eq,
    reduceCtorEq, not_false_eq_true, heap_get_insert_addr_ne, hp, hp', World.mk.injEq, and_true]
  -- both orders write the counter twice and each promise once
  conv => lhs; arg 1; rw [heap_insert_comm _ _ _ (by simp)]
  conv => rhs; arg 1; rw [heap_insert_comm _ _ _ (by simp)]
  exact heap_insert_comm _ _ _ (by simpa using hp)

/-- A resumption keeps the facts the other resumptions need. -/
theorem incEffect_pre (a p q : Nat) (w : World TT) (h : IncPre a p w) (hq : IncPre a q w) :
    IncPre a q (incEffect a p w).noJobs := by
  obtain ⟨⟨x, hx⟩, c, hc, hr⟩ := h
  obtain ⟨-, d, hd, hdr⟩ := hq
  by_cases e : p = q
  · subst e
    cases hs : c.state <;> simp [IncPre, incEffect, counterVal, settled, OVals.get?, hx, hc, hs, hr]
  · simp [IncPre, incEffect, counterVal, OVals.get?, hx, hc, hd, hdr, e]

/-- Two resumptions of `incFixed` on the same counter commute: either order adds two. -/
theorem incFixedJob_comm (I : Impl) (a p₁ p₂ : Nat) (hp : p₁ ≠ p₂) (w : World TT)
    (rest : List (Job TT)) (h₁ : IncPre a p₁ w) (h₂ : IncPre a p₂ w) :
    exec (drain I program) { w with jobs := incFixedJob a p₁ :: incFixedJob a p₂ :: rest } =
      exec (drain I program) { w with jobs := incFixedJob a p₂ :: incFixedJob a p₁ :: rest } := by
  obtain ⟨⟨x, hx⟩, c₁, hc₁, -⟩ := id h₁
  obtain ⟨-, c₂, hc₂, -⟩ := id h₂
  exact exec_drain_swap (incFixedJob_spec I a p₁) (incFixedJob_spec I a p₂) w rest h₁ h₂
    (incEffect_pre a p₁ p₂ _ h₁ h₂) (incEffect_pre a p₂ p₁ _ h₂ h₁)
    (incEffect_comm a p₁ p₂ hp _ x hx hc₁ hc₂) rfl

/-- The rest of `incRacy` after its `await` (`v` holds the value read before it). -/
abbrev incRacyRest :
    Block TT (⟨.undef, false⟩ :: ⟨.num, false⟩ :: ([⟨.obj "Counter", false⟩] ++ [])) .undef :=
  .seq (.setField (fs := «Counter».fields) (var! 2) (mem! 0)
    (.prim (.numBin .add) args[var! 1, .lit (.num 1)])) .nil

example : incRacyDef.lam = .async [⟨.obj "Counter", false⟩] rfl
    (.decl ⟨.num, false⟩ (.getField (fs := «Counter».fields) (var! 0) (mem! 0))
      (.await ⟨.undef, false⟩ (.builtin (.promResolve .undef) args[.lit .undef]) incRacyRest)) := rfl

/-- The job that resumes `incRacy(c)` after its `await`; `v` is the value it read. -/
abbrev incRacyJob (a : Nat) (v : F64) (p : Nat) : Job TT :=
  .react (.await (.mk ⟨.undef, false⟩ incRacyRest (.cons (.num v) (.cons (.obj a) .nil)) (.pop .done)) p)
    (.ok .undef)

/-- A call `incRacy(c)` reads the counter (`x`), returns a pending promise `p` and queues
`incRacyJob a x p`. -/
theorem incRacy_queues (I : Impl) (w : World TT) (a : Nat) (x : F64)
    (hc : w.heap.get? (.obj "Counter" [.num], a) = some (.cons (some (.num x)) .nil)) :
    ∃ h, exec (callFun I program incRacyRef (.cons (.obj a) .nil)) w =
      some (.ok (.promise w.next),
        { w with heap := h, next := w.next + 2, jobs := w.jobs ++ [incRacyJob a x w.next] }) := by
  ts_drain [incRacy_call, incRacyDef, incRacyRest, hc]

/-- Writing `v + 1` into the counter at `a` and resolving the promise `p`. -/
def setEffect (a : Nat) (v : F64) (p : Nat) (w : World TT) : World TT :=
  match counterVal w a, w.heap.get? (.promise .undef, p) with
  | some _, some c =>
    { w with
      heap := (w.heap.insert (.obj "Counter" [.num], a) (.cons (some (.num (v + 1))) .nil)).insert
        (.promise .undef, p) (settled c) }
  | _, _ => w

/-- The resumption of `incRacy` writes the value it read plus one, whatever the counter holds. -/
theorem incRacyJob_spec (I : Impl) (a : Nat) (v : F64) (p : Nat) :
    JobSpec I program (incRacyJob a v p) (IncPre a p) (setEffect a v p) (fun _ => []) := by
  rintro w ⟨⟨x, hx⟩, c, hc, hr⟩
  cases hs : c.state <;>
    simp [ts_sym, setEffect, counterVal, settled, heap_insert_of_get, hx, hc, hs, hr]

/-- Both orders of the racy resumptions lose the update: two resumptions that read the same
value `v` commute (each writes `v + 1`). -/
theorem incRacyJob_comm (I : Impl) (a : Nat) (v : F64) (p₁ p₂ : Nat) (hp : p₁ ≠ p₂) (w : World TT)
    (rest : List (Job TT)) (h₁ : IncPre a p₁ w) (h₂ : IncPre a p₂ w) :
    exec (drain I program) { w with jobs := incRacyJob a v p₁ :: incRacyJob a v p₂ :: rest } =
      exec (drain I program) { w with jobs := incRacyJob a v p₂ :: incRacyJob a v p₁ :: rest } := by
  obtain ⟨⟨x, hx⟩, c₁, hc₁, hr₁⟩ := h₁
  obtain ⟨-, c₂, hc₂, hr₂⟩ := h₂
  have hp' : p₂ ≠ p₁ := Ne.symm hp
  refine exec_drain_swap (incRacyJob_spec I a v p₁) (incRacyJob_spec I a v p₂) w rest
    ⟨⟨x, hx⟩, c₁, hc₁, hr₁⟩ ⟨⟨x, hx⟩, c₂, hc₂, hr₂⟩ ?_ ?_ ?_ rfl
  · simp [IncPre, setEffect, counterVal, OVals.get?, hx, hc₁, hc₂, hr₂, hp]
  · simp [IncPre, setEffect, counterVal, OVals.get?, hx, hc₁, hc₂, hr₁, hp']
  · simp only [setEffect, counterVal, OVals.get?, hx, hc₁, hc₂, Option.bind_some, Option.map_some,
      World.noJobs, heap_get_insert_self, heap_get_insert_kind_ne, ne_eq,
      reduceCtorEq, not_false_eq_true, heap_get_insert_addr_ne, hp, hp', World.mk.injEq, and_true]
    conv => lhs; arg 1; rw [heap_insert_comm _ _ _ (by simp)]
    conv => rhs; arg 1; rw [heap_insert_comm _ _ _ (by simp)]
    exact heap_insert_comm _ _ _ (by simpa using hp)

/-! ### Any number of concurrent increments -/

/-- Every promise of `ps` is pending without reactions (nobody awaits the calls yet). -/
def Pending (ps : List Nat) (w : World TT) : Prop :=
  ∀ p ∈ ps, ∃ c, w.heap.get? (.promise .undef, p) = some c ∧ c.state = .pending ∧ c.reactions = []

/-- Running the effects of `incFixed` resumptions for the distinct promises `ps`: each finds its
precondition, and the counter goes from `x` to `x + 1 + ⋯ + 1`, one `+ 1` per resumption. -/
theorem incFixed_fold (a : Nat) : ∀ (ps : List Nat), ps.Nodup → ∀ (w : World TT) (x : F64),
    w.heap.get? (.obj "Counter" [.num], a) = some (.cons (some (.num x)) .nil) → Pending ps w →
    PreChain (fun p => IncPre a p) (fun p => incEffect a p) ps w ∧
    (ps.foldl (fun w p => incEffect a p w.noJobs) w).heap.get? (.obj "Counter" [.num], a) =
      some (.cons (some (.num (ps.foldl (fun y _ => y + 1) x))) .nil)
  | [], _, w, x, hx, _ => ⟨trivial, by simpa using hx⟩
  | p :: ps, hnd, w, x, hx, hp => by
    obtain ⟨c, hc, -, hr⟩ := hp p (List.mem_cons_self ..)
    obtain ⟨hnp, hnd'⟩ := List.nodup_cons.1 hnd
    have hx' : (incEffect a p w.noJobs).heap.get? (.obj "Counter" [.num], a) =
        some (.cons (some (.num (x + 1))) .nil) := by
      simp [incEffect, counterVal, OVals.get?, hx, hc]
    have hp' : Pending ps (incEffect a p w.noJobs) := by
      intro q hq
      have hne : p ≠ q := fun h => hnp (h ▸ hq)
      simpa [incEffect, counterVal, OVals.get?, hx, hc, hne] using hp q (List.mem_cons_of_mem _ hq)
    obtain ⟨hch, hfold⟩ := incFixed_fold a ps hnd' _ (x + 1) hx' hp'
    exact ⟨⟨⟨⟨x, hx⟩, c, hc, hr⟩, hch⟩, hfold⟩

/-- **`k` concurrent fixed increments add `k`**: from any world in which the resumptions of `k`
calls `incFixed(c)` (distinct promises `ps`, nobody awaiting them) are queued, the microtask
loop leaves the counter at `x + 1 + ⋯ + 1` (`k` times). -/
theorem incFixedJobs_add (I : Impl) (a : Nat) (ps : List Nat) (hnd : ps.Nodup) (w : World TT)
    (x : F64) (hx : w.heap.get? (.obj "Counter" [.num], a) = some (.cons (some (.num x)) .nil))
    (hp : Pending ps w) :
    ∃ w', exec (drain I program) { w with jobs := ps.map (incFixedJob a) } = some (.ok (), w') ∧
      w'.heap.get? (.obj "Counter" [.num], a) =
        some (.cons (some (.num (ps.foldl (fun y _ => y + 1) x))) .nil) := by
  obtain ⟨hch, hfold⟩ := incFixed_fold a ps hnd w x hx hp
  have h := exec_drain_specs (I := I) (incFixedJob a) (fun p => IncPre a p) (fun p => incEffect a p)
    ps (fun p _ => incFixedJob_spec I a p) w [] hch
  rw [List.append_nil] at h
  rw [h, exec_drain_nil _ _ _ rfl]
  exact ⟨_, rfl, hfold⟩

/-- Running the effects of `incRacy` resumptions that all read `v`: the counter ends at
`v + 1` (it is unchanged if there is none). -/
theorem incRacy_fold (a : Nat) (v : F64) : ∀ (ps : List Nat), ps.Nodup → ∀ (w : World TT) (x : F64),
    w.heap.get? (.obj "Counter" [.num], a) = some (.cons (some (.num x)) .nil) → Pending ps w →
    PreChain (fun p => IncPre a p) (fun p => setEffect a v p) ps w ∧
    (ps.foldl (fun w p => setEffect a v p w.noJobs) w).heap.get? (.obj "Counter" [.num], a) =
      some (.cons (some (.num (if ps = [] then x else v + 1))) .nil)
  | [], _, w, x, hx, _ => ⟨trivial, by simpa using hx⟩
  | p :: ps, hnd, w, x, hx, hp => by
    obtain ⟨c, hc, -, hr⟩ := hp p (List.mem_cons_self ..)
    obtain ⟨hnp, hnd'⟩ := List.nodup_cons.1 hnd
    have hx' : (setEffect a v p w.noJobs).heap.get? (.obj "Counter" [.num], a) =
        some (.cons (some (.num (v + 1))) .nil) := by
      simp [setEffect, counterVal, OVals.get?, hx, hc]
    have hp' : Pending ps (setEffect a v p w.noJobs) := by
      intro q hq
      have hne : p ≠ q := fun h => hnp (h ▸ hq)
      simpa [setEffect, counterVal, OVals.get?, hx, hc, hne] using hp q (List.mem_cons_of_mem _ hq)
    obtain ⟨hch, hfold⟩ := incRacy_fold a v ps hnd' _ (v + 1) hx' hp'
    refine ⟨⟨⟨⟨x, hx⟩, c, hc, hr⟩, hch⟩, ?_⟩
    simpa using hfold

/-- **The update is lost for any number of racy calls**: if the resumptions of `k ≥ 1` calls
`incRacy(c)` are queued and all of them read `v` (as when every call runs before the first
resumption, `v` being the counter's value then), the loop leaves the counter at `v + 1`. -/
theorem incRacyJobs_lost (I : Impl) (a : Nat) (v : F64) (ps : List Nat) (hnd : ps.Nodup)
    (hne : ps ≠ []) (w : World TT) (x : F64)
    (hx : w.heap.get? (.obj "Counter" [.num], a) = some (.cons (some (.num x)) .nil))
    (hp : Pending ps w) :
    ∃ w', exec (drain I program) { w with jobs := ps.map (incRacyJob a v) } = some (.ok (), w') ∧
      w'.heap.get? (.obj "Counter" [.num], a) = some (.cons (some (.num (v + 1))) .nil) := by
  obtain ⟨hch, hfold⟩ := incRacy_fold a v ps hnd w x hx hp
  have h := exec_drain_specs (I := I) (incRacyJob a v) (fun p => IncPre a p)
    (fun p => setEffect a v p) ps (fun p _ => incRacyJob_spec I a v p) w [] hch
  rw [List.append_nil] at h
  rw [h, exec_drain_nil _ _ _ rfl]
  exact ⟨_, rfl, by simpa [hne] using hfold⟩

/-- **Every order of the fixed increments has the same outcome**: the resumptions of `incFixed`
for the promises `ps` (each existing without reactions; repetitions allowed) can run in any
order `ps'`. -/
theorem incFixedJobs_perm (I : Impl) (a : Nat) (ps ps' : List Nat) (hperm : ps.Perm ps')
    (w : World TT) (hw : ∀ p ∈ ps, IncPre a p w) (rest : List (Job TT)) :
    exec (drain I program) { w with jobs := ps.map (incFixedJob a) ++ rest } =
      exec (drain I program) { w with jobs := ps'.map (incFixedJob a) ++ rest } := by
  refine exec_drain_perm hperm (incFixedJob a) (fun w => ∀ p ∈ ps, IncPre a p w)
    (fun p => incEffect a p) (fun p hp => (incFixedJob_spec I a p).mono fun w h => h p hp)
    (fun p hp w h q hq => incEffect_pre a p q w (h p hp) (h q hq)) ?_ w hw rest
  intro p₁ hp₁ p₂ hp₂ w h
  by_cases e : p₁ = p₂
  · subst e; rfl
  · obtain ⟨⟨x, hx⟩, c₁, hc₁, -⟩ := h p₁ hp₁
    obtain ⟨-, c₂, hc₂, -⟩ := h p₂ hp₂
    exact incEffect_comm a p₁ p₂ e w x hx hc₁ hc₂
