import CIR.Logic.Exec

/-!
  Loop rules.

  Each structured loop (`cir.for`, `cir.while`, `cir.do`) unfolds into one
  non-recursive iteration followed by either an exit or the next iteration:

      loop σ = iter σ >>= fun r => match r with
        | .inl res => pure res     -- the loop ends with `res`
        | .inr σ'  => loop σ'      -- next iteration from `σ'`

  The generic rule `holds_loop` proves total correctness from an invariant
  and a natural-number variant; the iteration itself is executed
  symbolically by `cir_vcg`.
-/

namespace CIR

/-- What happens after one iteration: stop with a result, or iterate again. -/
def loopCont {α : Type} (loop : State → Res α) : Sum α State → Res α
  | .inl a => pure a
  | .inr σ' => loop σ'

/-- What an iteration must establish: the postcondition when the loop stops,
the invariant and a smaller variant when it continues. -/
def loopPost {α : Type} (Q : α → Prop) (Inv : State → Prop) (V : State → Nat) (σ : State) :
    Sum α State → Prop
  | .inl a => Q a
  | .inr σ' => Inv σ' ∧ V σ' < V σ

/-- Generic total-correctness loop rule. -/
theorem holds_loop {α : Type} {iter : State → Res (Sum α State)} {loop : State → Res α}
    (hunfold : ∀ σ, loop σ = iter σ >>= loopCont loop)
    {Q : α → Prop} (Inv : State → Prop) (V : State → Nat)
    (hstep : ∀ σ, Inv σ → (iter σ).holds (loopPost Q Inv V σ)) :
    ∀ σ, Inv σ → (loop σ).holds Q := by
  intro σ
  induction h : V σ using Nat.strongRecOn generalizing σ with
  | ind n ih =>
    intro hinv
    rw [hunfold σ, Res.holds_bind]
    apply Res.holds_mono (hstep σ hinv)
    intro r hr
    match r, hr with
    | .inl a, hr => exact hr
    | .inr σ', ⟨hinv', hlt⟩ => exact ih (V σ') (h ▸ hlt) σ' rfl hinv'

/-! ### `cir.for` -/

/-- One iteration of `cir.for : cond {c} body {b} step {s} [cleanup cl]`. -/
def forIter (ctx : Ctx) (c b s : Region) (cl : Option (CleanupKind × Region)) (σ : State) :
    Res (Sum (Step × State) State) := do
  let (ec, σ) ← evalRegion ctx c [] σ
  match ec with
  | .cond false => do pure (.inl (.next, ← evalIterCleanup ctx cl false σ))
  | .cond true => do
    let (eb, σ) ← evalRegion ctx b [] σ
    match eb with
    | .yield [] => forStepIter ctx s cl σ
    | .cont => forStepIter ctx s cl σ
    | .brk => do pure (.inl (.next, ← evalIterCleanup ctx cl false σ))
    | .goto l => do pure (.inl (.exit (.goto l), ← evalIterCleanup ctx cl false σ))
    | .ret v => do pure (.inl (.exit (.ret v), ← evalIterCleanup ctx cl false σ))
    | .exn x => do pure (.inl (.exit (.exn x), ← evalIterCleanup ctx cl true σ))
    | .halt n => pure (.inl (.exit (.halt n), σ))
    | .longjmp t v => pure (.inl (.exit (.longjmp t v), σ))
    | _ => .ub "abnormal exit from a loop body"
  | .exn x => if cl.isSome then .ub "exception in a loop condition with cleanup" else pure (.inl (.exit (.exn x), σ))
  | .halt n => pure (.inl (.exit (.halt n), σ))
  | .longjmp t v => pure (.inl (.exit (.longjmp t v), σ))
  | _ => .ub "loop condition region did not end with cir.condition"
where
  /-- The step region and per-iteration cleanup at the end of an iteration. -/
  forStepIter (ctx : Ctx) (s : Region) (cl : Option (CleanupKind × Region)) (σ : State) :
      Res (Sum (Step × State) State) := do
    let (es, σ) ← evalRegion ctx s [] σ
    match es with
    | .yield [] => do pure (.inr (← evalIterCleanup ctx cl false σ))
    | .exn x => do pure (.inl (.exit (.exn x), ← evalIterCleanup ctx cl true σ))
    | .halt n => pure (.inl (.exit (.halt n), σ))
    | .longjmp t v => pure (.inl (.exit (.longjmp t v), σ))
    | _ => .ub "abnormal exit from a loop step region"

/-- Bind of a `Res` computation followed by a function of its result is
determined by the computation's outcome. -/
theorem Res.bind_congr_ok {α β : Type} {x : Res α} {f g : α → Res β} (h : ∀ a, x = .ok a → f a = g a) :
    x >>= f = x >>= g := by
  cases x with
  | ok a => exact h a rfl
  | ub m => rfl
  | div => rfl

theorem evalForStep_unfold (ctx : Ctx) (c b s : Region) (cl : Option (CleanupKind × Region))
    (σ : State) :
    evalForStep ctx c b s cl σ = forIter.forStepIter ctx s cl σ >>= loopCont (evalFor ctx c b s cl) := by
  rw [evalForStep.eq_1, forIter.forStepIter]
  simp only [bind_assoc]
  apply Res.bind_congr_ok; rintro ⟨es, σ1⟩ -
  dsimp only
  cases es with
  | yield vs => cases vs <;> simp only [bind_assoc, pure_bind, loopCont] <;> rfl
  | exn x => simp only [bind_assoc, pure_bind, loopCont]
  | halt n => simp only [pure_bind, loopCont]
  | longjmp t v => simp only [pure_bind, loopCont]
  | _ => rfl

theorem evalFor_unfold (ctx : Ctx) (c b s : Region) (cl : Option (CleanupKind × Region)) (σ : State) :
    evalFor ctx c b s cl σ = forIter ctx c b s cl σ >>= loopCont (evalFor ctx c b s cl) := by
  rw [evalFor.eq_1, forIter]
  simp only [loopHead, bind_assoc]
  apply Res.bind_congr_ok; rintro ⟨ec, σ1⟩ -
  dsimp only
  cases ec with
  | cond bv =>
    cases bv with
    | false => simp only [bind_assoc, pure_bind, loopCont]
    | true =>
      simp only [bind_assoc]
      apply Res.bind_congr_ok; rintro ⟨eb, σ2⟩ -
      dsimp only
      cases eb with
      | yield vs =>
        cases vs with
        | nil => exact evalForStep_unfold ctx c b s cl σ2
        | cons _ _ => rfl
      | cont => exact evalForStep_unfold ctx c b s cl σ2
      | brk => simp only [bind_assoc, pure_bind, loopCont]
      | ret v => simp only [bind_assoc, pure_bind, loopCont]
      | exn x => simp only [bind_assoc, pure_bind, loopCont]
      | goto l => simp only [bind_assoc, pure_bind, loopCont]
      | halt n => simp only [pure_bind, loopCont]
      | longjmp t v => simp only [pure_bind, loopCont]
      | cond _ => rfl
  | exn x =>
    dsimp only
    cases cl <;> simp only [Option.isSome_some, Option.isSome_none, Bool.false_eq_true,
      ite_true, ite_false, pure_bind, Res.ub_bind] <;> rfl
  | halt n => simp only [pure_bind, loopCont]
  | longjmp t v => simp only [pure_bind, loopCont]
  | _ => rfl

/-- Total correctness of `cir.for` from an invariant and a variant. -/
theorem holds_for {ctx : Ctx} {c b s : Region} {cl : Option (CleanupKind × Region)}
    {Q : Step × State → Prop} (Inv : State → Prop) (V : State → Nat)
    (hstep : ∀ σ, Inv σ → (forIter ctx c b s cl σ).holds (loopPost Q Inv V σ))
    (σ : State) (h0 : Inv σ) : (evalFor ctx c b s cl σ).holds Q :=
  holds_loop (iter := forIter ctx c b s cl) (loop := evalFor ctx c b s cl) (evalFor_unfold ctx c b s cl)
    Inv V hstep σ h0

/-! ### `cir.while` -/

/-- One iteration of `cir.while {c} do {b} [cleanup cl]`. -/
def whileIter (ctx : Ctx) (c b : Region) (cl : Option (CleanupKind × Region)) (σ : State) :
    Res (Sum (Step × State) State) := do
  let (ec, σ) ← evalRegion ctx c [] σ
  match ec with
  | .cond false => do pure (.inl (.next, ← evalIterCleanup ctx cl false σ))
  | .cond true => do
    let (eb, σ) ← evalRegion ctx b [] σ
    match eb with
    | .yield [] => do pure (.inr (← evalIterCleanup ctx cl false σ))
    | .cont => do pure (.inr (← evalIterCleanup ctx cl false σ))
    | .brk => do pure (.inl (.next, ← evalIterCleanup ctx cl false σ))
    | .goto l => do pure (.inl (.exit (.goto l), ← evalIterCleanup ctx cl false σ))
    | .ret v => do pure (.inl (.exit (.ret v), ← evalIterCleanup ctx cl false σ))
    | .exn x => do pure (.inl (.exit (.exn x), ← evalIterCleanup ctx cl true σ))
    | .halt n => pure (.inl (.exit (.halt n), σ))
    | .longjmp t v => pure (.inl (.exit (.longjmp t v), σ))
    | _ => .ub "abnormal exit from a loop body"
  | .exn x => if cl.isSome then .ub "exception in a loop condition with cleanup" else pure (.inl (.exit (.exn x), σ))
  | .halt n => pure (.inl (.exit (.halt n), σ))
  | .longjmp t v => pure (.inl (.exit (.longjmp t v), σ))
  | _ => .ub "loop condition region did not end with cir.condition"

theorem evalWhile_unfold (ctx : Ctx) (c b : Region) (cl : Option (CleanupKind × Region)) (σ : State) :
    evalWhile ctx c b cl σ = whileIter ctx c b cl σ >>= loopCont (evalWhile ctx c b cl) := by
  rw [evalWhile.eq_1, whileIter]
  simp only [loopHead, bind_assoc]
  apply Res.bind_congr_ok; rintro ⟨ec, σ1⟩ -
  dsimp only
  cases ec with
  | cond bv =>
    cases bv with
    | false => simp only [bind_assoc, pure_bind, loopCont]
    | true =>
      simp only [bind_assoc]
      apply Res.bind_congr_ok; rintro ⟨eb, σ2⟩ -
      dsimp only
      cases eb with
      | yield vs =>
        cases vs with
        | nil => simp only [bind_assoc, pure_bind, loopCont]
        | cons _ _ => rfl
      | cont => simp only [bind_assoc, pure_bind, loopCont]
      | brk => simp only [bind_assoc, pure_bind, loopCont]
      | ret v => simp only [bind_assoc, pure_bind, loopCont]
      | exn x => simp only [bind_assoc, pure_bind, loopCont]
      | goto l => simp only [bind_assoc, pure_bind, loopCont]
      | halt n => simp only [pure_bind, loopCont]
      | longjmp t v => simp only [pure_bind, loopCont]
      | cond _ => rfl
  | exn x =>
    dsimp only
    cases cl <;> simp only [Option.isSome_some, Option.isSome_none, Bool.false_eq_true,
      ite_true, ite_false, pure_bind, Res.ub_bind] <;> rfl
  | halt n => simp only [pure_bind, loopCont]
  | longjmp t v => simp only [pure_bind, loopCont]
  | _ => rfl

theorem holds_while {ctx : Ctx} {c b : Region} {cl : Option (CleanupKind × Region)}
    {Q : Step × State → Prop} (Inv : State → Prop) (V : State → Nat)
    (hstep : ∀ σ, Inv σ → (whileIter ctx c b cl σ).holds (loopPost Q Inv V σ))
    (σ : State) (h0 : Inv σ) : (evalWhile ctx c b cl σ).holds Q :=
  holds_loop (iter := whileIter ctx c b cl) (loop := evalWhile ctx c b cl) (evalWhile_unfold ctx c b cl)
    Inv V hstep σ h0

/-! ### `cir.do` -/

/-- One iteration of `cir.do {b} while {c}`: the body, then the condition. -/
def doIter (ctx : Ctx) (b c : Region) (σ : State) : Res (Sum (Step × State) State) := do
  let (eb, σ) ← evalRegion ctx b [] σ
  match eb with
  | .yield [] => doCondIter ctx c σ
  | .cont => doCondIter ctx c σ
  | .brk => pure (.inl (.next, σ))
  | .goto l => pure (.inl (.exit (.goto l), σ))
  | .ret v => pure (.inl (.exit (.ret v), σ))
  | .exn x => pure (.inl (.exit (.exn x), σ))
  | .halt n => pure (.inl (.exit (.halt n), σ))
  | .longjmp t v => pure (.inl (.exit (.longjmp t v), σ))
  | _ => .ub "abnormal exit from a loop body"
where
  doCondIter (ctx : Ctx) (c : Region) (σ : State) : Res (Sum (Step × State) State) := do
    let (ec, σ) ← evalRegion ctx c [] σ
    match ec with
    | .cond true => pure (.inr σ)
    | .cond false => pure (.inl (.next, σ))
    | .exn x => pure (.inl (.exit (.exn x), σ))
    | .halt n => pure (.inl (.exit (.halt n), σ))
    | .longjmp t v => pure (.inl (.exit (.longjmp t v), σ))
    | _ => .ub "loop condition region did not end with cir.condition"

theorem evalDoCond_unfold (ctx : Ctx) (b c : Region) (σ : State) :
    evalDoCond ctx b c σ = doIter.doCondIter ctx c σ >>= loopCont (evalDo ctx b c) := by
  rw [evalDoCond.eq_1, doIter.doCondIter]
  simp only [bind_assoc]
  apply Res.bind_congr_ok; rintro ⟨ec, σ1⟩ -
  dsimp only
  cases ec with
  | cond bv => cases bv <;> simp only [pure_bind, loopCont]
  | exn x => simp only [pure_bind, loopCont]
  | halt n => simp only [pure_bind, loopCont]
  | longjmp t v => simp only [pure_bind, loopCont]
  | _ => rfl

theorem evalDo_unfold (ctx : Ctx) (b c : Region) (σ : State) :
    evalDo ctx b c σ = doIter ctx b c σ >>= loopCont (evalDo ctx b c) := by
  rw [evalDo.eq_1, doIter]
  simp only [loopHead, bind_assoc]
  apply Res.bind_congr_ok; rintro ⟨eb, σ1⟩ -
  dsimp only
  cases eb with
  | yield vs =>
    cases vs with
    | nil => exact evalDoCond_unfold ctx b c σ1
    | cons _ _ => rfl
  | cont => exact evalDoCond_unfold ctx b c σ1
  | brk => simp only [pure_bind, loopCont]
  | ret v => simp only [pure_bind, loopCont]
  | exn x => simp only [pure_bind, loopCont]
  | goto l => simp only [pure_bind, loopCont]
  | halt n => simp only [pure_bind, loopCont]
  | longjmp t v => simp only [pure_bind, loopCont]
  | cond _ => rfl

theorem holds_do {ctx : Ctx} {b c : Region} {Q : Step × State → Prop}
    (Inv : State → Prop) (V : State → Nat)
    (hstep : ∀ σ, Inv σ → (doIter ctx b c σ).holds (loopPost Q Inv V σ))
    (σ : State) (h0 : Inv σ) : (evalDo ctx b c σ).holds Q :=
  holds_loop (iter := doIter ctx b c) (loop := evalDo ctx b c) (evalDo_unfold ctx b c) Inv V hstep σ h0


/-! Concrete execution (`cir_eval`): one iteration, then the loop again. -/

theorem holds_evalFor_unroll {ctx : Ctx} {c b s : Region} {cl : Option (CleanupKind × Region)}
    {σ : State} {Q : Step × State → Prop}
    (h : (forIter ctx c b s cl σ >>= loopCont (evalFor ctx c b s cl)).holds Q) :
    (evalFor ctx c b s cl σ).holds Q := by
  rw [evalFor_unfold]; exact h

theorem holds_evalWhile_unroll {ctx : Ctx} {c b : Region} {cl : Option (CleanupKind × Region)}
    {σ : State} {Q : Step × State → Prop}
    (h : (whileIter ctx c b cl σ >>= loopCont (evalWhile ctx c b cl)).holds Q) :
    (evalWhile ctx c b cl σ).holds Q := by
  rw [evalWhile_unfold]; exact h

theorem holds_evalDo_unroll {ctx : Ctx} {b c : Region} {σ : State} {Q : Step × State → Prop}
    (h : (doIter ctx b c σ >>= loopCont (evalDo ctx b c)).holds Q) :
    (evalDo ctx b c σ).holds Q := by
  rw [evalDo_unfold]; exact h

/-! ### Loop invariants over local variables -/

/-- The integer held by stack block `b` (0 if it holds something else). It is
unfolded only on explicit states (`State.intAt_mk`), so on the abstract
state of a loop head it stays an opaque name for the variable's value. -/
def State.intAt (σ : State) (b : Nat) : Int :=
  match σ.mem.blocks b with
  | some ⟨_, _, _, .int x⟩ => x
  | _ => 0

theorem State.intAt_mk (m : Mem) (e : VId → Option Val) (n : List (String × Nat)) (b : Nat) :
    (State.mk m e n).intAt b = (match m.blocks b with
      | some ⟨_, _, _, .int x⟩ => x
      | _ => 0) := rfl

/-- The loop-head facts about the frame: the SSA environment and variable
names are those at loop entry `σ₀`, no block disappeared, and every block
older than the loop except the modified ones `mods` is unchanged. -/
def LoopFrame (σ₀ : State) (mods : List Nat) (σ : State) : Prop :=
  σ.env = σ₀.env ∧ σ.names = σ₀.names ∧ σ₀.mem.next ≤ σ.mem.next ∧
  ∀ b, b ∉ mods → b < σ₀.mem.next → σ.mem.blocks b = σ₀.mem.blocks b

/-- `LoopFrame`, and the well-formedness of memory carried across the loop
(`set_option cir.loopWF true`): each iteration then shows that it keeps the
memory well formed (`cir_wf`), and after the loop the memory is well formed
whenever it was at entry. -/
def LoopFrameW (σ₀ : State) (mods : List Nat) (σ : State) : Prop :=
  LoopFrame σ₀ mods σ ∧ (σ₀.mem.WF → σ.mem.WF)

/-- Block `b` is a live stack slot of type `ty` holding an integer of that
type (stores check the range, so this is preserved by every iteration). -/
def IntSlot (σ : State) (b : Nat) (ty : Ty) : Prop :=
  σ.mem.blocks b = some ⟨.stack, true, ty, .int (σ.intAt b)⟩ ∧ fitsTy ty (.int (σ.intAt b)) = true

/-- The loop-head facts about the frame when the invariant describes the
memory itself (a `mem` binder): as `LoopFrame`, but only for the blocks of
the function's own frame (from `lo` on); the caller's blocks, and its heap,
are described by the invariant. -/
def LoopFrameFrom (σ₀ : State) (lo : Nat) (mods : List Nat) (σ : State) : Prop :=
  σ.env = σ₀.env ∧ σ.names = σ₀.names ∧ σ₀.mem.next ≤ σ.mem.next ∧
  ∀ b, b ∉ mods → lo ≤ b → b < σ₀.mem.next → σ.mem.blocks b = σ₀.mem.blocks b

/-- Memory `m'` agrees with `m` on the blocks satisfying `P`. Invariants over
a `mem` binder state their frame this way ("unchanged except the blocks
freed so far"): symbolic execution keeps it folded, since as a rewrite rule
`m'.blocks b = m.blocks b` would be tried, and fail, at every block read. The
facts about the blocks a loop iteration reads are derived from it first. -/
def MemAgree (m' m : Mem) (P : Nat → Prop) : Prop := ∀ b, P b → m'.blocks b = m.blocks b

theorem Mem.WF_upd {bs : Nat → Option MemBlock} {n : Nat} (hwf : Mem.WF ⟨bs, n⟩) {k : Nat}
    (hk : k < n) (v : Option MemBlock) : Mem.WF ⟨upd bs k v, n⟩ := by
  intro b hb
  dsimp only at hb ⊢
  simp only [upd_apply]
  split
  · omega
  · exact hwf b hb

theorem Mem.WF_mono {bs : Nat → Option MemBlock} {n n' : Nat} (hwf : Mem.WF ⟨bs, n⟩) (h : n ≤ n') :
    Mem.WF ⟨bs, n'⟩ := fun b hb => hwf b (Nat.le_trans h hb)

/-- `Mem.WF_mono` with the memory named: its `next` is `m.next` as written
(not a projection `σ.1.next` that `omega` takes for another atom). -/
theorem Mem.WF_mono' {m : Mem} {n' : Nat} (hwf : m.WF) (h : m.next ≤ n') : Mem.WF ⟨m.blocks, n'⟩ :=
  Mem.WF_mono (bs := m.blocks) (n := m.next) hwf h

/-- A memory is well formed when it agrees with a well-formed one from its
own `next` on. -/
theorem Mem.WF_of_frame {m m' : Mem} (hwf : m.WF) (hn : m.next ≤ m'.next)
    (h : ∀ b, m'.next ≤ b → m'.blocks b = m.blocks b) : m'.WF :=
  fun b hb => (h b hb).trans (hwf b (Nat.le_trans hn hb))

theorem Mem.WF_killRange {bs : Nat → Option MemBlock} {n lo hi : Nat} (hwf : Mem.WF ⟨bs, n⟩) :
    Mem.WF ⟨killRange lo hi bs, n⟩ := by
  intro b hb
  have := hwf b hb
  dsimp only at hb this ⊢
  simp [killRange, this]

/-- The pointer to block `bs[k]` of a list of blocks (a linked list's
nodes, in order), `null` past the end. -/
def listPtr (bs : List Nat) (k : Nat) : Ptr :=
  if h : k < bs.length then .loc bs[k] [] else .null

theorem listPtr_of_lt {bs : List Nat} {k : Nat} (h : k < bs.length) : listPtr bs k = .loc bs[k] [] := by
  simp [listPtr, h]

theorem listPtr_of_ge {bs : List Nat} {k : Nat} (h : bs.length ≤ k) : listPtr bs k = .null := by
  simp [listPtr]; omega

/-- The position in `bs` of the block `p` points to (`bs.length` for null):
the variant of a loop over a list of blocks, `bs.length - listIdx bs p`. -/
def listIdx (bs : List Nat) (p : Ptr) : Nat :=
  match p with
  | .loc b _ => bs.idxOf b
  | _ => bs.length

theorem listIdx_listPtr {bs : List Nat} {k : Nat} (hnd : bs.Nodup) (hk : k ≤ bs.length) :
    listIdx bs (listPtr bs k) = k := by
  by_cases h : k < bs.length
  · simp only [listPtr, h, dite_true, listIdx]
    exact List.Nodup.idxOf_getElem hnd k h
  · simp only [listPtr, h, dite_false, listIdx]; omega

theorem listIdx_loc {bs : List Nat} {k : Nat} (hnd : bs.Nodup) (h : k < bs.length) (p : List PathElem) :
    listIdx bs (.loc bs[k] p) = k := List.Nodup.idxOf_getElem hnd k h

/-- `listIdx_loc` for blocks listed as `ts.map f` (the block of item `ts[k]`
of a ghost list, `f ts[k]`). -/
theorem listIdx_loc_map {α : Type} {ts : List α} {f : α → Nat} {k : Nat} (hnd : (ts.map f).Nodup)
    (h : k < ts.length) (p : List PathElem) : listIdx (ts.map f) (.loc (f ts[k]) p) = k := by
  have := listIdx_loc hnd (k := k) (by simpa using h) p
  simpa using this

/-- `listIdx_listPtr` with `listPtr` unfolded (as symbolic execution sees it). -/
theorem listIdx_listPtr' {bs : List Nat} {k : Nat} (hnd : bs.Nodup) (hk : k ≤ bs.length) :
    listIdx bs (if h : k < bs.length then Ptr.loc bs[k] [] else Ptr.null) = k :=
  listIdx_listPtr hnd hk

/-- The pointer held by block `b` (`null` if none). -/
def State.ptrAt (σ : State) (b : Nat) : Ptr :=
  match σ.mem.blocks b with
  | some ⟨_, _, _, .ptr p⟩ => p
  | _ => .null

theorem State.ptrAt_mk (m : Mem) (e : VId → Option Val) (n : List (String × Nat)) (b : Nat) :
    (State.mk m e n).ptrAt b = (match m.blocks b with
      | some ⟨_, _, _, .ptr p⟩ => p
      | _ => .null) := rfl

/-- Block `b` is a live stack slot of type `ty` holding some pointer: the
variable of a loop over a linked structure, named by its value. -/
def PtrValSlot (σ : State) (b : Nat) (ty : Ty) : Prop :=
  σ.mem.blocks b = some ⟨.stack, true, ty, .ptr (σ.ptrAt b)⟩

/-- Block `b` is a live stack slot of type `ty` with some value: a variable
the loop body assigns before reading it (the variable of a range-`for`). -/
def ScratchSlot (σ : State) (b : Nat) (ty : Ty) : Prop :=
  ∃ v, σ.mem.blocks b = some ⟨.stack, true, ty, v⟩

/-! ### Iterator variables

A contiguous iterator object is `Val.agg [.ptr (.loc b path)]` whose last
path step is an element index (`CIR.Std`). An iterator variable of a loop
(the hidden `__begin` of a range-`for`) keeps its container and moves its
index; the invariant names the index. -/

/-- The index of the last step of a path. -/
def lastIndex : List PathElem → Nat
  | [] => 0
  | [e] => e.index
  | _ :: e' :: p => lastIndex (e' :: p)

/-- Move the last step of a path to index `i`. -/
def movePath : List PathElem → Nat → List PathElem
  | [], _ => []
  | [e], i => [e.withIndex i]
  | e :: e' :: p, i => e :: movePath (e' :: p) i

/-- The element index of an iterator value. -/
def iterIdx (v : Val) : Nat :=
  match v with
  | .agg [.ptr (.loc _ p)] => lastIndex p
  | _ => 0

/-- An iterator value moved to element `i` of the same container. -/
def iterMove (v : Val) (i : Nat) : Val :=
  match v with
  | .agg [.ptr (.loc b p)] => .agg [.ptr (.loc b (movePath p i))]
  | _ => v

theorem iterIdx_agg (b : Nat) (p : List PathElem) :
    iterIdx (.agg [.ptr (.loc b p)]) = lastIndex p := rfl

theorem iterMove_agg (b : Nat) (p : List PathElem) (i : Nat) :
    iterMove (.agg [.ptr (.loc b p)]) i = .agg [.ptr (.loc b (movePath p i))] := rfl

/-- The element index of the iterator held by block `b`. Like `intAt`, it is
unfolded only on explicit states. -/
def State.iterAt (σ : State) (b : Nat) : Nat :=
  match σ.mem.blocks b with
  | some blk => iterIdx blk.val
  | none => 0

theorem State.iterAt_mk (m : Mem) (e : VId → Option Val) (n : List (String × Nat)) (b : Nat) :
    (State.mk m e n).iterAt b = (match m.blocks b with
      | some blk => iterIdx blk.val
      | none => 0) := rfl

/-- Block `b` holds the iterator it held at loop entry `σ₀`, moved to element
`σ.iterAt b` of the same container. -/
def IterSlot (σ₀ σ : State) (b : Nat) : Prop :=
  σ.mem.blocks b = (σ₀.mem.blocks b).map fun blk => { blk with val := iterMove blk.val (σ.iterAt b) }

/-- Candidate `k` of a mined loop invariant (the identity, see `cir_houdini`).
Symbolic execution treats `Cand k p` as an atomic goal and only simplifies
inside it, so that a candidate that does not hold is reported by number. -/
def Cand (_k : Nat) (p : Prop) : Prop := p

/-! ### Pointer variables

A pointer variable that walks an array (`while (*p) ++p;`) keeps its array
and moves its element index; the invariant names the index, as for an
iterator. -/

/-- The element index of a pointer value. -/
def ptrIdx (v : Val) : Nat :=
  match v with
  | .ptr (.loc _ p) => lastIndex p
  | _ => 0

/-- A pointer value moved to element `i` of the same array. -/
def ptrMove (v : Val) (i : Nat) : Val :=
  match v with
  | .ptr (.loc b p) => .ptr (.loc b (movePath p i))
  | _ => v

theorem ptrIdx_ptr (b : Nat) (p : List PathElem) : ptrIdx (.ptr (.loc b p)) = lastIndex p := rfl

theorem ptrMove_ptr (b : Nat) (p : List PathElem) (i : Nat) :
    ptrMove (.ptr (.loc b p)) i = .ptr (.loc b (movePath p i)) := rfl

/-- The element index of the pointer held by block `b`. Like `intAt`, it is
unfolded only on explicit states. -/
def State.ptrIdxAt (σ : State) (b : Nat) : Nat :=
  match σ.mem.blocks b with
  | some blk => ptrIdx blk.val
  | none => 0

theorem State.ptrIdxAt_mk (m : Mem) (e : VId → Option Val) (n : List (String × Nat)) (b : Nat) :
    (State.mk m e n).ptrIdxAt b = (match m.blocks b with
      | some blk => ptrIdx blk.val
      | none => 0) := rfl

/-- Block `b` holds the pointer it held at loop entry `σ₀`, moved to element
`σ.ptrIdxAt b` of the same array. -/
def PtrSlot (σ₀ σ : State) (b : Nat) : Prop :=
  σ.mem.blocks b = (σ₀.mem.blocks b).map fun blk => { blk with val := ptrMove blk.val (σ.ptrIdxAt b) }

/-! ### Arrays modified by a loop

A loop that writes the elements of an array (a local array, or a global or
function-local static one) names the array's elements, a `List Val`, by the
array's name. Kind, liveness, type and the number of elements stay those at
loop entry. -/

/-- The elements of the array held by block `b` (`[]` if it holds none). -/
def State.arrVals (σ : State) (b : Nat) : List Val :=
  match σ.mem.blocks b with
  | some blk =>
    match blk.val with
    | .arr xs => xs
    | _ => []
  | none => []

theorem State.arrVals_mk (m : Mem) (e : VId → Option Val) (n : List (String × Nat)) (b : Nat) :
    (State.mk m e n).arrVals b = (match m.blocks b with
      | some blk =>
        match blk.val with
        | .arr xs => xs
        | _ => []
      | none => []) := rfl

/-- Block `b` holds the array of the elements `σ.arrVals b`, as many as at
loop entry `σ₀`; kind, liveness and type are those at loop entry. -/
def ArrSlot (σ₀ σ : State) (b : Nat) : Prop :=
  σ.mem.blocks b = (σ₀.mem.blocks b).map (fun blk => { blk with val := .arr (σ.arrVals b) }) ∧
  (σ.arrVals b).length = (σ₀.arrVals b).length

/-! ### Containers modified through a pointer

A loop that changes a container of the caller (`out.push_back(x)` with
`std::vector<int>& out`) names the container's elements, a `List Int`, by the
name of the pointer variable. The container block is the target of that
pointer at loop entry; every reallocation installs a new generation, so the
generation is existential. -/

/-- The block the pointer held by block `a` points into (0 if none). -/
def State.ptrTarget (σ : State) (a : Nat) : Nat :=
  match σ.mem.blocks a with
  | some blk =>
    match blk.val with
    | .ptr (.loc b _) => b
    | _ => 0
  | none => 0

theorem State.ptrTarget_mk (m : Mem) (e : VId → Option Val) (n : List (String × Nat)) (a : Nat) :
    (State.mk m e n).ptrTarget a = (match m.blocks a with
      | some blk =>
        match blk.val with
        | .ptr (.loc b _) => b
        | _ => 0
      | none => 0) := rfl

/-- The integer of an integer value. -/
def intOf : Val → Option Int
  | .int x => some x
  | _ => none

theorem filterMap_intOf_map_int (xs : List Int) : (xs.map Val.int).filterMap intOf = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [List.filterMap_cons, intOf, ih]

/-- The integers held by the container block `b` (`[]` if it holds none). -/
def State.vecInts (σ : State) (b : Nat) : List Int :=
  match σ.mem.blocks b with
  | some blk =>
    match blk.val with
    | .vec _ xs => xs.filterMap intOf
    | _ => []
  | none => []

theorem State.vecInts_mk (m : Mem) (e : VId → Option Val) (n : List (String × Nat)) (b : Nat) :
    (State.mk m e n).vecInts b = (match m.blocks b with
      | some blk =>
        match blk.val with
        | .vec _ xs => xs.filterMap intOf
        | _ => []
      | none => []) := rfl

/-- Block `b` holds, under some generation, the container of the integers
`σ.vecInts b`; kind, liveness and type are those at loop entry. -/
def VecSlot (σ₀ σ : State) (b : Nat) : Prop :=
  ∃ g, σ.mem.blocks b =
    (σ₀.mem.blocks b).map fun blk => { blk with val := .vec g ((σ.vecInts b).map .int) }

/-! ### Fields of a struct modified through a pointer

A loop that keeps its state in a struct of the caller
(`for (; p->pos < len; p->pos++)` with `parser* p`) names each integer member
it changes by `<pointer variable>_<member index>` (CIR records have no member
names), e.g. `parser_0` for `parser->pos`. -/

/-- The integer in member `k` of the struct held by block `b` (0 if none). -/
def State.fieldInt (σ : State) (b k : Nat) : Int :=
  match σ.mem.blocks b with
  | some blk =>
    match blk.val.get? [.idx k] with
    | some (.int x) => x
    | _ => 0
  | none => 0

theorem State.fieldInt_mk (m : Mem) (e : VId → Option Val) (n : List (String × Nat)) (b k : Nat) :
    (State.mk m e n).fieldInt b k = (match m.blocks b with
      | some blk =>
        match blk.val.get? [.idx k] with
        | some (.int x) => x
        | _ => 0
      | none => 0) := rfl

/-- `v` with the integer members `kvs` (member index, value) replaced. -/
def setFields (v : Val) (kvs : List (Nat × Int)) : Val :=
  kvs.foldl (fun v kx => (v.set? [.idx kx.1] (.int kx.2)).getD v) v

/-- Block `b` holds the struct it held at loop entry with the members `ks`
replaced by their current integers `σ.fieldInt b k`. -/
def FieldsSlot (σ₀ σ : State) (b : Nat) (ks : List Nat) : Prop :=
  σ.mem.blocks b =
    (σ₀.mem.blocks b).map fun blk => { blk with val := setFields blk.val (ks.map fun k => (k, σ.fieldInt b k)) }

end CIR
