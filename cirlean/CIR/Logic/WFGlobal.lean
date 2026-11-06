import Lean
import CIR.Semantics.Eval
import CIR.Logic.WP
import CIR.Std.Models

/-!
  # Memory well-formedness is preserved by every execution

  `Mem.WF m` (no block at or above `m.next`, `CIR/Memory.lean`) holds after
  every successful run of the interpreter from a well-formed memory:
  `evalCall_wf`, the `State`-level versions `evalOps_wf`, …, `evalForStep_wf`
  for the other functions of the mutual block, and `Calls.wf` / `Returns.wf`
  for the program logic (`CIR/Logic/WP.lean`).

  Structure:
  * `cir_split_match` (meta): case split along the decision tree of a `match`
    without its splitter (needed for the 150-alternative `match` of
    `Std.runModel`, whose splitter exceeds the default heartbeat limit);
  * the memory primitives (`Mem.WF_alloc`, `Mem.WF_setBlock`, `Mem.WF_write?`,
    `Mem.WF_free?`, `Mem.WF_endScope`) and `cir_wf_auto`, which takes a `do`
    block apart and records the well-formedness of every intermediate memory;
  * `WF_evalSimple`, `State.WF_bindArgs`, `State.WF_setResults`,
    `Std.WF_runModel` (every library model);
  * the fixpoint induction (`evalOps.fixpoint_induct` and its siblings) with
    partial-correctness motives, admissible since they hold at `Res.div`.
-/

set_option autoImplicit false

/-!
  `cir_split_match h`: for `h : f a₁ … aₙ = rhs` where `f` is defined by a `match`
  (or `h : (match …) = rhs`), case-splits along the decision tree of that
  `match` until it reduces, and replaces `h` by the reduced alternative.
  Unlike `split`, it needs neither the splitter nor the equation lemmas of the
  matcher (for the 150-alternative `match` of `Std.runModel` their generation
  exceeds the default heartbeat limit, and since `runModel` is imported, it
  runs with the command-line options, so `set_option maxHeartbeats` does not
  help): each step finds the free variable on which the matcher is stuck and
  runs `cases` on it.
-/

namespace CIR.SplitDef

open Lean Meta Elab Tactic

/-- The free variable whose constructor form would let the recursor
application `e` (a stuck `whnf` result) reduce. -/
partial def stuckFVar? (e : Expr) : MetaM (Option FVarId) := do
  match e with
  | .mdata _ e => stuckFVar? e
  | .fvar f => return some f
  | .proj _ _ s => stuckFVar? (← whnf s)
  | .app .. =>
    match e.getAppFn with
    | .const fName _ =>
      match (← getEnv).find? fName with
      | some (.recInfo recVal) =>
        let args := e.getAppArgs
        let majorIdx := recVal.getMajorIdx
        if h : majorIdx < args.size then stuckFVar? (← whnf args[majorIdx]) else return none
      | _ => return none
    | _ => return none
  | _ => return none

/-- Split the goal `g` along the matcher of the definition at the head of the
left-hand side of the hypothesis named `hName`. -/
partial def splitDef (g : MVarId) (hName : Name) (fuel : Nat) : MetaM (List MVarId) :=
  g.withContext do
    let some hDecl := (← getLCtx).findFromUserName? hName
      | throwError "cir_split_match: no hypothesis {hName}"
    let hType ← instantiateMVars hDecl.type
    let some (_, lhs, rhs) := hType.eq?
      | throwError "cir_split_match: {hName} is not an equation"
    -- a `match` at the head, or a definition by `match`
    let lhs' ← match ← reduceMatcher? lhs with
      | .notMatcher =>
        let some l ← unfoldDefinition? lhs
          | throwError "cir_split_match: cannot unfold the head of {lhs}"
        pure l.headBeta
      | _ => pure lhs
    match ← reduceMatcher? lhs' with
    | .reduced e =>
      return [← g.replaceLocalDeclDefEq hDecl.fvarId (← mkEq e rhs)]
    | .stuck e' =>
      if fuel = 0 then throwError "cir_split_match: out of fuel"
      let some x ← stuckFVar? e'
        | throwError "cir_split_match: stuck, but not on a free variable:{indentExpr e'}"
      let subgoals ← g.cases x
      let mut res := #[]
      for sg in subgoals do
        res := res ++ (← splitDef sg.mvarId hName (fuel - 1))
      return res.toList
    | _ => throwError "cir_split_match: the unfolding of {lhs} is not a matcher application"

/-- `cir_lhs_head h c` succeeds iff the left-hand side of the equation `h` is
an application of the constant `c` (a cheap guard before trying a lemma). -/
elab "cir_lhs_head " h:ident c:ident : tactic => do
  let g ← getMainGoal
  g.withContext do
    let some d := (← getLCtx).findFromUserName? h.getId
      | throwError "cir_lhs_head: no hypothesis {h.getId}"
    let some (_, lhs, _) := (← instantiateMVars d.type).cleanupAnnotations.eq?
      | throwError "cir_lhs_head: {h.getId} is not an equation"
    let cn ← realizeGlobalConstNoOverloadWithInfo c
    unless lhs.cleanupAnnotations.getAppFn.isConstOf cn do
      throwError "cir_lhs_head: the head is not {cn}"

elab "cir_split_match " h:ident : tactic => do
  let g ← getMainGoal
  let gs ← splitDef g h.getId 64
  replaceMainGoal gs

end CIR.SplitDef

/-!
  Well-formedness of memory (`Mem.WF`: no block at or above `next`) is
  preserved by the memory primitives, the non-recursive state operations and
  `evalSimple`.

  Forward lemmas take the equation of the operation first and the
  well-formedness of the input memory second: `cir_wf_auto` elaborates the
  equation first, which fixes the memory whose well-formedness it then
  proves.
-/

namespace CIR

namespace Mem

/-- A block with contents in a well-formed memory lies below `next`. -/
theorem blocks_lt_next {m : Mem} {b : Nat} {blk : MemBlock} (hwf : m.WF)
    (h : m.blocks b = some blk) : b < m.next := by
  apply Nat.lt_of_not_le
  intro hle
  rw [hwf b hle] at h
  cases h

/-- A live block of a well-formed memory lies below `next`. -/
theorem live?_lt {m : Mem} {b : Nat} {blk : MemBlock} (hwf : m.WF) (h : m.live? b = some blk) :
    b < m.next := by
  unfold live? at h
  split at h
  · exact blocks_lt_next hwf ‹_›
  · cases h

theorem WF_alloc {m : Mem} (hwf : m.WF) (k : BlockKind) (ty : Ty) (v : Val) :
    (m.alloc k ty v).2.WF := by
  intro b hb
  simp only [alloc] at hb ⊢
  have hne : b ≠ m.next := by omega
  simp only [upd, hne, ite_false]
  exact hwf b (by omega)

/-- `Mem.WF_alloc` for the pattern `let (b, m') := m.alloc k ty v`. -/
theorem WF_of_alloc_eq {m m' : Mem} {k : BlockKind} {ty : Ty} {v : Val} {b : Nat}
    (h : m.alloc k ty v = (b, m')) (hwf : m.WF) : m'.WF := by
  have := WF_alloc hwf k ty v
  rw [h] at this
  exact this

theorem WF_setBlock {m : Mem} (hwf : m.WF) {b : Nat} (hb : b < m.next) (blk : MemBlock) :
    (m.setBlock b blk).WF := by
  intro b' hb'
  simp only [setBlock] at hb' ⊢
  have hne : b' ≠ b := by omega
  simp only [upd, hne, ite_false]
  exact hwf b' hb'

theorem WF_write? {m m' : Mem} {p : Ptr} {v : Val} (h : m.write? p v = some m') (hwf : m.WF) :
    m'.WF := by
  cases p with
  | loc b path =>
    cases hl : m.live? b with
    | none => simp [write?, hl] at h
    | some blk =>
      have hset : ∀ blk', (m.setBlock b blk').WF := fun blk' => WF_setBlock hwf (live?_lt hwf hl) blk'
      simp only [write?, hl] at h
      by_cases hro : blk.kind = .readonly
      · by_cases hin : (blk.val.get? path).all (Val.initBy · v) = true
        · simp only [hro, hin, ↓reduceIte] at h
          cases hs : blk.val.set? path v with
          | none => simp [hs] at h
          | some v' => simp only [hs, Option.some.injEq] at h; subst h; exact hset _
        · simp [hro, hin] at h
      · simp only [hro, ↓reduceIte] at h
        cases hs : blk.val.set? path v with
        | none => simp [hs] at h
        | some v' => simp only [hs, Option.some.injEq] at h; subst h; exact hset _
  | _ => simp [write?] at h

theorem WF_free? {m m' : Mem} {b : Nat} (h : m.free? b = some m') (hwf : m.WF) : m'.WF := by
  unfold free? at h
  split at h
  · split at h
    · cases h
      exact WF_setBlock hwf (live?_lt hwf ‹_›) _
    · cases h
  · cases h

theorem WF_endScope {m : Mem} (hwf : m.WF) (lo : Nat) : (m.endScope lo).WF := by
  intro b hb
  simp only [endScope] at hb ⊢
  simp [killRange, hwf b hb]

theorem WF_leaveMem {m : Mem} (hwf : m.WF) (e : Exit) (lo : Nat) : (e.leaveMem m lo).WF := by
  cases e <;> simp only [Exit.leaveMem] <;> first | exact hwf | exact WF_endScope hwf lo

end Mem

/-! ### Results -/

namespace Res

theorem ofOption_eq_ok {α : Type} {msg : String} {o : Option α} {a : α} :
    Res.ofOption msg o = .ok a ↔ o = some a := by
  cases o <;> simp [ofOption]

/-- A successful conditional: one of its branches succeeded. -/
theorem ite_eq_ok {α : Type} {c : Prop} [Decidable c] {x y : Res α} {a : α}
    (h : (if c then x else y) = .ok a) : x = .ok a ∨ y = .ok a := by
  split at h
  · exact .inl h
  · exact .inr h

end Res

/-! ### Typed stores and state operations -/

theorem WF_storeTy {m m' : Mem} {ty : Ty} {p : Ptr} {v : Val} (h : storeTy m ty p v = .ok m')
    (hwf : m.WF) : m'.WF := by
  unfold storeTy at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · cases h
        exact Mem.WF_write? ‹_› hwf

/-- The activation of the union members on a store's path rewrites a block below `next`. -/
theorem WF_unionActivate? {ctx : Ctx} {m : Mem} (hwf : m.WF) (p : Ptr) :
    ((ctx.unionActivate? m p).getD m).WF := by
  cases p with
  | loc b path =>
    simp only [Ctx.unionActivate?]
    cases hb : m.blocks b with
    | none => exact hwf
    | some blk =>
      simp only
      cases ctx.activateVal? blk.ty blk.val path with
      | none => exact hwf
      | some v =>
        exact Mem.WF_setBlock hwf (Mem.blocks_lt_next hwf hb) _
  | _ => exact hwf

theorem WF_ofOption_write? {m m' : Mem} {msg : String} {p : Ptr} {v : Val}
    (h : Res.ofOption msg (m.write? p v) = .ok m') (hwf : m.WF) : m'.WF :=
  Mem.WF_write? (Res.ofOption_eq_ok.mp h) hwf

theorem WF_byteStore {m m' : Mem} {ty : Ty} {b : Nat} {path : List PathElem} {t : Ty} {k : Nat}
    {v : Val} (h : byteStore m ty b path t k v = .ok m') (hwf : m.WF) : m'.WF := by
  unfold byteStore byteStoreOf at h
  repeat' (first | exact WF_ofOption_write? h hwf | (cases h; done) | split at h)

theorem WF_foldlM {α : Type} {f : Mem → α → Res Mem}
    (hf : ∀ (m m' : Mem) (x : α), f m x = .ok m' → m.WF → m'.WF) :
    ∀ (xs : List α) {m m' : Mem}, xs.foldlM f m = .ok m' → m.WF → m'.WF
  | [], m, m', h, hwf => by
    simp only [List.foldlM_nil, Res.pure_eq] at h
    cases h
    exact hwf
  | x :: xs, m, m', h, hwf => by
    simp only [List.foldlM_cons] at h
    obtain ⟨m1, h1, h2⟩ := Res.bind_eq_ok.mp h
    exact WF_foldlM hf xs h2 (hf m m1 x h1 hwf)

theorem WF_scatterAt {ctx : Ctx} : ∀ (fuel : Nat) {m m' : Mem} {b : Nat} {t : Ty} {q : Nat} {v : Val},
    ctx.scatterAt fuel m b t q v = .ok m' → m.WF → m'.WF
  | 0, _, _, _, _, _, _, h, _ => by simp [Ctx.scatterAt] at h
  | fuel + 1, m, m', b, t, q, v, h, hwf => by
    unfold Ctx.scatterAt at h
    repeat' (first
      | exact WF_ofOption_write? h hwf
      | exact WF_storeTy h hwf
      | exact WF_byteStore h hwf
      | (cases h; done)
      | (refine WF_foldlM (fun m₁ m₂ y hy hw => ?_) _ h hwf
         obtain ⟨⟨⟨kd, tj⟩, o⟩, x⟩ := y
         simp only at hy
         split at hy
         · cases hy
           exact hw
         · exact WF_scatterAt fuel hy hw)
      | (refine WF_foldlM (fun m₁ m₂ y hy hw => ?_) _ h hwf
         obtain ⟨x, i⟩ := y
         exact WF_scatterAt fuel hy hw)
      | split at h)

theorem WF_spreadStore {ctx : Ctx} {m m' : Mem} {b : Nat} {path : List PathElem} {t : Ty} {v : Val}
    (h : ctx.spreadStore m b path t v = .ok m') (hwf : m.WF) : m'.WF := by
  unfold Ctx.spreadStore at h
  repeat' (first | exact WF_scatterAt _ h hwf | (cases h; done) | split at h)

theorem WF_typedStore {ctx : Ctx} {m m' : Mem} {ty : Ty} {p : Ptr} {v : Val}
    (h : ctx.typedStore m ty p v = .ok m') (hwf : m.WF) : m'.WF := by
  have hwf' := WF_unionActivate? (ctx := ctx) hwf p
  dsimp only [Ctx.typedStore] at h
  split at h
  · exact WF_byteStore h hwf'
  · exact WF_storeTy h (WF_unionActivate? hwf' _)
  · cases h
  · exact WF_spreadStore h hwf'
  · cases h
  · split at h
    · cases h
    · exact WF_storeTy h hwf'

theorem WF_bfStoreBytes {ctx : Ctx} {b : Nat} {ty : Ty} :
    ∀ {m m' : Mem} {q nb u : Nat}, ctx.bfStoreBytes b ty m q nb u = .ok m' → m.WF → m'.WF
  | _, _, _, 0, _, h, hwf => by
    simp only [Ctx.bfStoreBytes] at h
    cases h
    exact hwf
  | _, _, _, _ + 1, _, h, hwf => by
    simp only [Ctx.bfStoreBytes] at h
    obtain ⟨⟨p, t, k⟩, _, h2⟩ := Res.bind_eq_ok.mp h
    obtain ⟨m1, h3, h4⟩ := Res.bind_eq_ok.mp h2
    exact WF_bfStoreBytes h4 (WF_byteStore h3 hwf)

theorem WF_ofOption_free? {m m' : Mem} {msg : String} {b : Nat}
    (h : Res.ofOption msg (m.free? b) = .ok m') (hwf : m.WF) : m'.WF :=
  Mem.WF_free? (Res.ofOption_eq_ok.mp h) hwf

theorem WF_getD_write? {m : Mem} {p : Ptr} {v : Val} (hwf : m.WF) : ((m.write? p v).getD m).WF := by
  cases h : m.write? p v with
  | none => exact hwf
  | some m' => exact Mem.WF_write? h hwf

theorem WF_writesOn : ∀ (ws : List (Ptr × Val)) {m : Mem}, m.WF → (writesOn m ws).WF
  | [], _, hwf => hwf
  | (_, _) :: ws, _, hwf => WF_writesOn ws (WF_getD_write? hwf)

theorem WF_foldl_forget {ctx : Ctx} :
    ∀ (l : List Val) {m : Mem}, m.WF → (l.foldl (fun m e => writesOn m (forgetWrites ctx m e)) m).WF
  | [], _, hwf => hwf
  | _ :: l, _, hwf => WF_foldl_forget l (WF_writesOn _ hwf)

/-- After a `longjmp`, the objects that became indeterminate keep memory well formed. -/
theorem WF_forgetChanged {ctx : Ctx} {tok : Nat} {m : Mem} (hwf : m.WF) :
    (forgetChanged ctx tok m).WF := by
  unfold forgetChanged
  split
  · exact WF_foldl_forget _ hwf
  · exact hwf

/-- After a destructor, the object made indeterminate again keeps memory well formed. -/
theorem WF_endLifetime {ctx : Ctx} {args : List Val} {m : Mem} (hwf : m.WF) :
    (endLifetime ctx args m).WF := by
  unfold endLifetime
  repeat' split
  all_goals first | exact hwf | exact Mem.WF_setBlock hwf (Mem.blocks_lt_next hwf ‹_›) _

/-- A `setjmp` invocation's record of a store keeps memory well formed. -/
theorem WF_sjMarkOne {b : Nat} {q : List PathElem} {st v : Bool} {m : Mem} {tok : Nat} (hwf : m.WF) :
    (Std.sjMarkOne b q st v m tok).WF := by
  unfold Std.sjMarkOne
  repeat' (first | (dsimp only) | split)
  all_goals first | exact WF_getD_write? hwf | exact hwf

theorem WF_foldl_sjMarkOne {b : Nat} {q : List PathElem} {st v : Bool} :
    ∀ (l : List Nat) {m : Mem}, m.WF → (l.foldl (Std.sjMarkOne b q st v) m).WF
  | [], _, hwf => hwf
  | _ :: l, _, hwf => WF_foldl_sjMarkOne l (WF_sjMarkOne hwf)

/-- The live `setjmp` invocations' records of a store keep memory well formed. -/
theorem WF_sjMarkMem {ctx : Ctx} {m : Mem} {p : Ptr} {st v : Bool} (hwf : m.WF) :
    (Std.sjMarkMem ctx m p st v).WF := by
  unfold Std.sjMarkMem
  split
  · exact WF_foldl_sjMarkOne _ hwf
  · exact hwf

/-- A new `setjmp` invocation in the registry keeps memory well formed. -/
theorem WF_sjRegister {ctx : Ctx} {m : Mem} {tok : Nat} (hwf : m.WF) : (Std.sjRegister ctx m tok).WF := by
  unfold Std.sjRegister
  split
  · exact WF_getD_write? hwf
  · exact hwf

/-- `Op.sjNote` keeps memory well formed. -/
theorem WF_sjNoteMem {ctx : Ctx} {σ : State} {p : VId} {st v : Bool} (hwf : σ.mem.WF) :
    (sjNoteMem ctx σ p st v).WF := by
  unfold sjNoteMem
  split
  · exact WF_sjMarkMem hwf
  · exact hwf

theorem WF_storeMarked {ctx : Ctx} {m m' : Mem} {ty : Ty} {p : Ptr} {v : Val}
    (h : Std.storeMarked ctx m ty p v = .ok m') (hwf : m.WF) : m'.WF := by
  unfold Std.storeMarked at h
  obtain ⟨m1, h1, h2⟩ := Res.bind_eq_ok.mp h
  cases h2
  exact WF_sjMarkMem (WF_typedStore h1 hwf)

theorem WF_writeMarked {ctx : Ctx} {m m' : Mem} {p : Ptr} {v : Val} {msg : String}
    (h : Std.writeMarked ctx m p v msg = .ok m') (hwf : m.WF) : m'.WF := by
  unfold Std.writeMarked at h
  obtain ⟨m1, h1, h2⟩ := Res.bind_eq_ok.mp h
  cases h2
  exact WF_sjMarkMem (WF_ofOption_write? h1 hwf)

theorem WF_sjRegisterR {ctx : Ctx} {m m' : Mem} {tok : Nat} (h : Std.sjRegisterR ctx m tok = .ok m')
    (hwf : m.WF) : m'.WF := by
  unfold Std.sjRegisterR at h
  cases h
  exact WF_sjRegister hwf

namespace State

theorem WF_bindArgs {σ σ' : State} {ps : List VId} {xs : List Val} (h : σ.bindArgs ps xs = .ok σ')
    (hwf : σ.mem.WF) : σ'.mem.WF := by
  induction ps generalizing σ xs with
  | nil =>
    cases xs with
    | nil =>
      simp only [bindArgs] at h
      cases h
      exact hwf
    | cons x xs =>
      simp only [bindArgs] at h
      cases h
      exact Mem.WF_alloc hwf _ _ _
  | cons p ps ih =>
    cases xs with
    | nil =>
      simp only [bindArgs] at h
      cases h
    | cons x xs =>
      simp only [bindArgs] at h
      exact ih h hwf

theorem WF_setResults {σ σ' : State} {r : Option VId} {xs : List Val}
    (h : σ.setResults r xs = .ok σ') (hwf : σ.mem.WF) : σ'.mem.WF := by
  unfold setResults at h
  split at h
  · cases h
    exact hwf
  · cases h
    exact hwf
  · cases h

end State

/-! ### Automation

`cir_wf_auto` proves `Q r` (the well-formedness of the memory of `r`) from
`h : x = .ok r`, where `x` is a computation in `Res` (a `do` block): it takes
the binds apart (`Res.bind_eq_ok`), splits matches and conditionals, and
records the well-formedness of every intermediate memory (`cir_wf_hx`, extensible
by `macro_rules`). The names `h` and `hx` are fixed (hygiene is off). Every
rule body is wrapped in `first | … | fail`, which turns off error recovery, and
a lemma rule first checks the head constant of the equation (`cir_lhs_head`):
a rule that does not apply fails, quickly, instead of being recovered as an
elaboration error with `sorry`. -/

/-- Process an intermediate result `hx : x = .ok a`: record the
well-formedness of the memory it produces, if any. -/
syntax "cir_wf_hx" : tactic
/-- Close a goal `m.WF` from the recorded facts. -/
syntax "cir_wf_close" : tactic
/-- Close the goal from a terminal computation `h : x = .ok r`. -/
syntax "cir_wf_term" : tactic
/-- One step of `cir_wf_auto`. -/
syntax "cir_wf_step" : tactic
/-- Prove the goal from `h : x = .ok r`. -/
syntax "cir_wf_auto" : tactic

-- `macro_rules` are tried from the last one to the first
set_option hygiene false in
macro_rules | `(tactic| cir_wf_hx) => `(tactic| skip)
set_option hygiene false in
macro_rules | `(tactic| cir_wf_hx) => `(tactic| first | (split at hx <;> cir_wf_hx) | fail "wf rule")
set_option hygiene false in
macro_rules | `(tactic| cir_wf_hx) => `(tactic| first | (dsimp only at hx; cir_wf_hx) | fail "wf rule")
set_option hygiene false in
macro_rules | `(tactic| cir_wf_hx) => `(tactic| first | cases hx | fail "wf rule")
set_option hygiene false in
macro_rules | `(tactic| cir_wf_hx) => `(tactic| first | (cir_lhs_head hx storeTy; have := WF_storeTy hx (by cir_wf_close)) | fail "wf rule")
set_option hygiene false in
macro_rules | `(tactic| cir_wf_hx) => `(tactic| first | (cir_lhs_head hx CIR.Ctx.typedStore; have := CIR.WF_typedStore hx (by cir_wf_close)) | fail "wf rule")
set_option hygiene false in
macro_rules | `(tactic| cir_wf_hx) => `(tactic| first | (cir_lhs_head hx CIR.Ctx.bfStoreBytes; have := CIR.WF_bfStoreBytes hx (by cir_wf_close)) | fail "wf rule")
set_option hygiene false in
macro_rules | `(tactic| cir_wf_hx) => `(tactic| first | (cir_lhs_head hx Res.ofOption; have := WF_ofOption_write? hx (by cir_wf_close)) | fail "wf rule")
set_option hygiene false in
macro_rules | `(tactic| cir_wf_hx) => `(tactic| first | (cir_lhs_head hx Res.ofOption; have := WF_ofOption_free? hx (by cir_wf_close)) | fail "wf rule")
set_option hygiene false in
macro_rules | `(tactic| cir_wf_hx) => `(tactic| first | (cir_lhs_head hx State.bindArgs; have := State.WF_bindArgs hx (by cir_wf_close)) | fail "wf rule")
set_option hygiene false in
macro_rules | `(tactic| cir_wf_hx) => `(tactic| first | (cir_lhs_head hx State.setResults; have := State.WF_setResults hx (by cir_wf_close)) | fail "wf rule")

-- declared first, so tried last: only the call of a destructor needs it
macro_rules | `(tactic| cir_wf_close) => `(tactic| first | (refine CIR.WF_endLifetime ?_; cir_wf_close) | fail "wf rule")
macro_rules | `(tactic| cir_wf_close) => `(tactic| first | (dsimp only [State.set, State.withMem]; cir_wf_close) | fail "wf rule")
macro_rules | `(tactic| cir_wf_close) => `(tactic| first | (refine Mem.WF_endScope ?_ _; cir_wf_close) | fail "wf rule")
macro_rules | `(tactic| cir_wf_close) => `(tactic| first | (refine Mem.WF_leaveMem ?_ _ _; cir_wf_close) | fail "wf rule")
macro_rules | `(tactic| cir_wf_close) => `(tactic| first | (refine Mem.WF_setBlock ?_ (Mem.blocks_lt_next ?_ ‹_›) _ <;> cir_wf_close) | fail "wf rule")
macro_rules | `(tactic| cir_wf_close) => `(tactic| first | (refine Mem.WF_of_alloc_eq ‹_› ?_; cir_wf_close) | fail "wf rule")
macro_rules | `(tactic| cir_wf_close) => `(tactic| first | (refine Mem.WF_alloc ?_ _ _ _; cir_wf_close) | fail "wf rule")
-- a memory from a successful write matched in the program (`.unionMember`'s activation)
macro_rules | `(tactic| cir_wf_close) => `(tactic| first | (exact Mem.WF_write? ‹_› (by cir_wf_close)) | fail "wf rule")
macro_rules | `(tactic| cir_wf_close) => `(tactic| first | assumption | fail "wf rule")
macro_rules | `(tactic| cir_wf_close) => `(tactic| first | (refine CIR.WF_forgetChanged ?_; cir_wf_close) | fail "wf rule")
-- (reducible unification: on another memory the rule fails at once instead of unfolding it)
macro_rules | `(tactic| cir_wf_close) => `(tactic| first | ((with_reducible (refine CIR.WF_sjNoteMem ?_)); cir_wf_close) | fail "wf rule")

macro_rules | `(tactic| cir_wf_term) => `(tactic| fail "no terminal rule")
set_option hygiene false in
macro_rules | `(tactic| cir_wf_term) => `(tactic| first | (cir_lhs_head h storeTy; exact WF_storeTy h (by cir_wf_close)) | fail "wf rule")
set_option hygiene false in
macro_rules | `(tactic| cir_wf_term) => `(tactic| first | (cir_lhs_head h CIR.Ctx.typedStore; exact CIR.WF_typedStore h (by cir_wf_close)) | fail "wf rule")
set_option hygiene false in
macro_rules | `(tactic| cir_wf_term) => `(tactic| first | (cir_lhs_head h Res.ofOption; exact WF_ofOption_write? h (by cir_wf_close)) | fail "wf rule")
set_option hygiene false in
macro_rules | `(tactic| cir_wf_term) => `(tactic| first | (cir_lhs_head h Res.ofOption; exact WF_ofOption_free? h (by cir_wf_close)) | fail "wf rule")
-- the library models' stores noted for the live `setjmp` invocations, and a new invocation
set_option hygiene false in
macro_rules | `(tactic| cir_wf_hx) => `(tactic| first | (cir_lhs_head hx Std.storeMarked; have := CIR.WF_storeMarked hx (by cir_wf_close)) | fail "wf rule")
set_option hygiene false in
macro_rules | `(tactic| cir_wf_hx) => `(tactic| first | (cir_lhs_head hx Std.writeMarked; have := CIR.WF_writeMarked hx (by cir_wf_close)) | fail "wf rule")
set_option hygiene false in
macro_rules | `(tactic| cir_wf_hx) => `(tactic| first | (cir_lhs_head hx Std.sjRegisterR; have := CIR.WF_sjRegisterR hx (by cir_wf_close)) | fail "wf rule")
set_option hygiene false in
macro_rules | `(tactic| cir_wf_term) => `(tactic| first | (cir_lhs_head h Std.storeMarked; exact CIR.WF_storeMarked h (by cir_wf_close)) | fail "wf rule")
set_option hygiene false in
macro_rules | `(tactic| cir_wf_term) => `(tactic| first | (cir_lhs_head h Std.writeMarked; exact CIR.WF_writeMarked h (by cir_wf_close)) | fail "wf rule")

set_option hygiene false in
macro_rules | `(tactic| cir_wf_step) => `(tactic| first | (dsimp only at h) | fail "wf rule")
set_option hygiene false in
macro_rules | `(tactic| cir_wf_step) => `(tactic| first | (split at h) | fail "wf rule")
set_option hygiene false in
macro_rules | `(tactic| cir_wf_step) => `(tactic| first | (dsimp only [Mem.alloc] at h) | fail "wf rule")
set_option hygiene false in
macro_rules | `(tactic| cir_wf_step) => `(tactic| first | (cir_lhs_head h ite; rcases Res.ite_eq_ok h with h | h) | fail "wf rule")
set_option hygiene false in
macro_rules | `(tactic| cir_wf_step) => `(tactic| first | (obtain ⟨_, hx, h⟩ := Res.bind_eq_ok.mp h; (try dsimp only at h); cir_wf_hx) | fail "wf rule")
set_option hygiene false in
macro_rules | `(tactic| cir_wf_step) => `(tactic| first | cir_wf_term | fail "wf rule")
set_option hygiene false in
macro_rules | `(tactic| cir_wf_step) => `(tactic| first | (cases h <;> cir_wf_close) | fail "wf rule")

macro_rules | `(tactic| cir_wf_auto) => `(tactic| repeat' cir_wf_step)

/-! ### `evalSimple` -/

theorem WF_vaArgOp {σ σ' : State} {r ap : VId} {ty : Ty} {vp : Bool} (h : vaArgOp σ r ap ty vp = .ok σ')
    (hwf : σ.mem.WF) : σ'.mem.WF := by
  unfold vaArgOp at h
  cir_wf_auto

set_option hygiene false in
macro_rules | `(tactic| cir_wf_term) => `(tactic| first | (cir_lhs_head h CIR.vaArgOp; exact CIR.WF_vaArgOp h (by cir_wf_close)) | fail "wf rule")

theorem WF_evalSimple {ctx : Ctx} {op : Op} {σ σ' : State} (h : evalSimple ctx op σ = .ok σ')
    (hwf : σ.mem.WF) : σ'.mem.WF := by
  unfold evalSimple at h
  split at h
  all_goals cir_wf_auto

end CIR

/-!
  The library models (`Std.runModel`) preserve `Mem.WF`.
-/

namespace CIR

namespace Std

theorem WF_fresh {m : Mem} (hwf : m.WF) : (fresh m).2.WF := by
  intro b hb
  simp only [fresh] at hb ⊢
  exact hwf b (by omega)

theorem WF_writeVal {m m' : Mem} {p : Ptr} {v : Val} (h : writeVal m p v = .ok m') (hwf : m.WF) :
    m'.WF :=
  Mem.WF_write? (Res.ofOption_eq_ok.mp h) hwf

theorem WF_writeVec {m m' : Mem} {p : Ptr} {xs : List Val} (h : writeVec m p xs = .ok m')
    (hwf : m.WF) : m'.WF :=
  WF_writeVal h (WF_fresh hwf)

theorem WF_ensureVec {ctx : Ctx} {m m' : Mem} {p : Ptr} (h : ensureVec ctx m p = .ok m')
    (hwf : m.WF) : m'.WF := by
  unfold ensureVec at h
  split at h <;> (try split at h) <;> first | exact WF_writeVec h hwf | (cases h; exact hwf)

theorem WF_rangeWrite {m m' : Mem} {r : Nat × List PathElem × Option Nat × Nat × Ty}
    {vs : List Val} (h : rangeWrite m r vs = some m') (hwf : m.WF) : m'.WF := by
  unfold rangeWrite at h
  split at h
  · exact Mem.WF_write? h hwf
  · split at h
    · exact Mem.WF_write? h hwf
    · exact Mem.WF_write? h hwf
    · cases h
  · cases h

theorem WF_ofOption_rangeWrite {m m' : Mem} {msg : String}
    {r : Nat × List PathElem × Option Nat × Nat × Ty} {vs : List Val}
    (h : Res.ofOption msg (rangeWrite m r vs) = .ok m') (hwf : m.WF) : m'.WF :=
  WF_rangeWrite (Res.ofOption_eq_ok.mp h) hwf

theorem WF_foldlM {α : Type} {f : Mem → α → Res Mem} {xs : List α} {m m' : Mem}
    (h : xs.foldlM f m = .ok m') (hwf : m.WF)
    (hf : ∀ m a m', f m a = .ok m' → m.WF → m'.WF) : m'.WF := by
  induction xs generalizing m with
  | nil =>
    simp only [List.foldlM_nil] at h
    cases h
    exact hwf
  | cons x xs ih =>
    simp only [List.foldlM_cons] at h
    obtain ⟨m1, h1, h2⟩ := Res.bind_eq_ok.mp h
    exact ih h2 (hf _ _ _ h1 hwf)

set_option hygiene false in
macro_rules | `(tactic| cir_wf_hx) => `(tactic| first | (simp only [bind_pure] at hx; cir_wf_hx) | fail "wf rule")
set_option hygiene false in
macro_rules | `(tactic| cir_wf_hx) => `(tactic| first | (cir_lhs_head hx Std.writeVal; have := WF_writeVal hx (by cir_wf_close)) | fail "wf rule")
set_option hygiene false in
macro_rules | `(tactic| cir_wf_hx) => `(tactic| first | (cir_lhs_head hx Std.writeVec; have := WF_writeVec hx (by cir_wf_close)) | fail "wf rule")
set_option hygiene false in
macro_rules | `(tactic| cir_wf_hx) => `(tactic| first | (cir_lhs_head hx Std.ensureVec; have := WF_ensureVec hx (by cir_wf_close)) | fail "wf rule")
set_option hygiene false in
macro_rules | `(tactic| cir_wf_hx) => `(tactic| first | (cir_lhs_head hx Res.ofOption; have := WF_ofOption_rangeWrite hx (by cir_wf_close)) | fail "wf rule")
set_option hygiene false in
macro_rules | `(tactic| cir_wf_hx) => `(tactic| first | (cir_lhs_head hx List.foldlM; have := WF_foldlM hx (by cir_wf_close) (by intro _ _ _ h _; cir_wf_auto; done)) | fail "wf rule")

theorem WF_storeEnd {ctx : Ctx} {m m' : Mem} {e p : Val} (h : storeEnd ctx m e p = .ok m')
    (hwf : m.WF) : m'.WF := by
  unfold storeEnd at h
  cir_wf_auto

theorem WF_storeGuard {ctx : Ctx} {m m' : Mem} {g : Ptr} {x : Int} {what : String}
    (h : storeGuard ctx m g x what = .ok m') (hwf : m.WF) : m'.WF := by
  unfold storeGuard at h
  cir_wf_auto

theorem WF_setErrno {ctx : Ctx} {m m' : Mem} {e : Int} (h : setErrno ctx m e = .ok m')
    (hwf : m.WF) : m'.WF := by
  unfold setErrno at h
  cir_wf_auto

theorem WF_updErrno {ctx : Ctx} {m m' : Mem} {u : Unit → Option (Option Int)}
    (h : updErrno ctx m u = .ok m') (hwf : m.WF) : m'.WF := by
  unfold updErrno at h
  cir_wf_auto

set_option hygiene false in
macro_rules | `(tactic| cir_wf_hx) => `(tactic| first | (cir_lhs_head hx Std.storeEnd; have := WF_storeEnd hx (by cir_wf_close)) | fail "wf rule")
set_option hygiene false in
macro_rules | `(tactic| cir_wf_hx) => `(tactic| first | (cir_lhs_head hx Std.storeGuard; have := WF_storeGuard hx (by cir_wf_close)) | fail "wf rule")
set_option hygiene false in
macro_rules | `(tactic| cir_wf_hx) => `(tactic| first | (cir_lhs_head hx Std.setErrno; have := WF_setErrno hx (by cir_wf_close)) | fail "wf rule")
set_option hygiene false in
macro_rules | `(tactic| cir_wf_hx) => `(tactic| first | (cir_lhs_head hx Std.updErrno; have := WF_updErrno hx (by cir_wf_close)) | fail "wf rule")

theorem WF_libmRet {ctx : Ctx} {fn : String} {single : Bool} {xs : List Float} {y : Float} {m : Mem}
    {r : Exit × Mem} (h : libmRet ctx fn single xs y m = .ok r) (hwf : m.WF) : r.2.WF := by
  unfold libmRet at h
  cir_wf_auto

theorem WF_setschedparamModel {ctx : Ctx} {m : Mem} {t p : Int} {sp : Ptr} {r : Exit × Mem}
    (h : setschedparamModel ctx m t p sp = .ok r) (hwf : m.WF) : r.2.WF := by
  unfold setschedparamModel at h
  cir_wf_auto

theorem WF_strerrorRModel {ctx : Ctx} {m : Mem} {e : Int} {buf : Ptr} {n : Int} {r : Exit × Mem}
    (h : strerrorRModel ctx m e buf n = .ok r) (hwf : m.WF) : r.2.WF := by
  unfold strerrorRModel at h
  cir_wf_auto

theorem WF_timeModel {ctx : Ctx} {m : Mem} {t : Ptr} {r : Exit × Mem} (h : timeModel ctx m t = .ok r)
    (hwf : m.WF) : r.2.WF := by
  unfold timeModel at h
  cir_wf_auto

theorem WF_ctimeRModel {ctx : Ctx} {m : Mem} {t buf : Ptr} {r : Exit × Mem}
    (h : ctimeRModel ctx m t buf = .ok r) (hwf : m.WF) : r.2.WF := by
  unfold ctimeRModel at h
  cir_wf_auto

theorem WF_sscanfModel {ctx : Ctx} {m : Mem} {s f : Ptr} {rest : List Val} {r : Exit × Mem}
    (h : sscanfModel ctx m s f rest = .ok r) (hwf : m.WF) : r.2.WF := by
  unfold sscanfModel at h
  cir_wf_auto

theorem WF_strtodModel {ctx : Ctx} {single : Bool} {s : Ptr} {rest : List Val} {m : Mem}
    {r : Exit × Mem} (h : strtodModel ctx single s rest m = .ok r) (hwf : m.WF) : r.2.WF := by
  unfold strtodModel at h
  cir_wf_auto

theorem WF_retEilseq {ctx : Ctx} {m : Mem} {r : Exit × Mem} (h : retEilseq ctx m = .ok r)
    (hwf : m.WF) : r.2.WF := by
  unfold retEilseq at h
  cir_wf_auto

theorem WF_perrorModel {ctx : Ctx} {m : Mem} {s : Ptr} {r : Exit × Mem}
    (h : perrorModel ctx m s = .ok r) (hwf : m.WF) : r.2.WF := by
  unfold perrorModel at h
  cir_wf_auto

set_option hygiene false in
macro_rules | `(tactic| cir_wf_term) => `(tactic| first | (cir_lhs_head h Std.libmRet; exact WF_libmRet h (by cir_wf_close)) | fail "wf rule")
set_option hygiene false in
macro_rules | `(tactic| cir_wf_term) => `(tactic| first | (cir_lhs_head h Std.setschedparamModel; exact WF_setschedparamModel h (by cir_wf_close)) | fail "wf rule")
set_option hygiene false in
macro_rules | `(tactic| cir_wf_term) => `(tactic| first | (cir_lhs_head h Std.strerrorRModel; exact WF_strerrorRModel h (by cir_wf_close)) | fail "wf rule")
set_option hygiene false in
macro_rules | `(tactic| cir_wf_term) => `(tactic| first | (cir_lhs_head h Std.timeModel; exact WF_timeModel h (by cir_wf_close)) | fail "wf rule")
set_option hygiene false in
macro_rules | `(tactic| cir_wf_term) => `(tactic| first | (cir_lhs_head h Std.ctimeRModel; exact WF_ctimeRModel h (by cir_wf_close)) | fail "wf rule")
set_option hygiene false in
macro_rules | `(tactic| cir_wf_term) => `(tactic| first | (cir_lhs_head h Std.sscanfModel; exact WF_sscanfModel h (by cir_wf_close)) | fail "wf rule")
set_option hygiene false in
macro_rules | `(tactic| cir_wf_term) => `(tactic| first | (cir_lhs_head h Std.strtodModel; exact WF_strtodModel h (by cir_wf_close)) | fail "wf rule")
set_option hygiene false in
macro_rules | `(tactic| cir_wf_term) => `(tactic| first | (cir_lhs_head h Std.retEilseq; exact WF_retEilseq h (by cir_wf_close)) | fail "wf rule")
set_option hygiene false in
macro_rules | `(tactic| cir_wf_term) => `(tactic| first | (cir_lhs_head h Std.perrorModel; exact WF_perrorModel h (by cir_wf_close)) | fail "wf rule")

theorem WF_freeHeap {m : Mem} {p : Ptr} {r : Exit × Mem} (h : freeHeap m p = .ok r)
    (hwf : m.WF) : r.2.WF := by
  unfold freeHeap at h
  cir_wf_auto

theorem WF_memsetBytes {ctx : Ctx} {m : Mem} {d : Ptr} {c n : Int} {r : Exit × Mem}
    (h : memsetBytes ctx m d c n = .ok r) (hwf : m.WF) : r.2.WF := by
  unfold memsetBytes at h
  cir_wf_auto

theorem WF_memcpyBytes {ctx : Ctx} {m : Mem} {d s : Ptr} {n : Int} {r : Exit × Mem}
    (h : memcpyBytes ctx m d s n = .ok r) (hwf : m.WF) : r.2.WF := by
  unfold memcpyBytes at h
  cir_wf_auto

set_option hygiene false in
macro_rules | `(tactic| cir_wf_term) => `(tactic| first | (cir_lhs_head h Std.memsetBytes; exact WF_memsetBytes h (by cir_wf_close)) | fail "wf rule")
set_option hygiene false in
macro_rules | `(tactic| cir_wf_term) => `(tactic| first | (cir_lhs_head h Std.memcpyBytes; exact WF_memcpyBytes h (by cir_wf_close)) | fail "wf rule")

theorem WF_memsetModel {ctx : Ctx} {m : Mem} {d : Ptr} {c n : Int} {r : Exit × Mem}
    (h : memsetModel ctx m d c n = .ok r) (hwf : m.WF) : r.2.WF := by
  unfold memsetModel at h
  cir_wf_auto

theorem WF_memcpyModel {ctx : Ctx} {m : Mem} {d s : Ptr} {n : Int} {r : Exit × Mem}
    (h : memcpyModel ctx m d s n = .ok r) (hwf : m.WF) : r.2.WF := by
  unfold memcpyModel at h
  cir_wf_auto

theorem WF_memcmpModel {ctx : Ctx} {m : Mem} {a b : Ptr} {n : Int} {r : Exit × Mem}
    (h : memcmpModel ctx m a b n = .ok r) (hwf : m.WF) : r.2.WF := by
  unfold memcmpModel at h
  cir_wf_auto

theorem WF_memchrBytes {ctx : Ctx} {m : Mem} {s : Ptr} {c n : Int} {r : Exit × Mem}
    (h : memchrBytes ctx m s c n = .ok r) (hwf : m.WF) : r.2.WF := by
  unfold memchrBytes at h
  cir_wf_auto

set_option hygiene false in
macro_rules | `(tactic| cir_wf_term) => `(tactic| first | (cir_lhs_head h Std.memchrBytes; exact WF_memchrBytes h (by cir_wf_close)) | fail "wf rule")

theorem WF_memchrModel {ctx : Ctx} {m : Mem} {s : Ptr} {c n : Int} {r : Exit × Mem}
    (h : memchrModel ctx m s c n = .ok r) (hwf : m.WF) : r.2.WF := by
  unfold memchrModel at h
  cir_wf_auto

theorem WF_lrintModel {fn : String} {x : Float} {m : Mem} {r : Exit × Mem}
    (h : lrintModel fn x m = .ok r) (hwf : m.WF) : r.2.WF := by
  unfold lrintModel at h
  cir_wf_auto

theorem WF_crModel {ctx : Ctx} {fn : String} {x : Float} {v : Option Float} {m : Mem} {r : Exit × Mem}
    (h : crModel ctx fn x v m = .ok r) (hwf : m.WF) : r.2.WF := by
  unfold crModel at h
  cir_wf_auto

theorem WF_signalModel {ctx : Ctx} {m : Mem} {sig : Int} {f : Ptr} {r : Exit × Mem}
    (h : signalModel ctx m sig f = .ok r) (hwf : m.WF) : r.2.WF := by
  unfold signalModel at h
  cir_wf_auto

theorem WF_posixMemalignModel {ctx : Ctx} {m : Mem} {mp : Ptr} {a size : Int} {r : Exit × Mem}
    (h : posixMemalignModel ctx m mp a size = .ok r) (hwf : m.WF) : r.2.WF := by
  unfold posixMemalignModel at h
  cir_wf_auto

theorem WF_initListCtor {e : Ty} {this first : Ptr} {n : Int} {m : Mem} {r : Exit × Mem}
    (h : initListCtor e this first n m = .ok r) (hwf : m.WF) : r.2.WF := by
  unfold initListCtor at h
  cir_wf_auto

theorem WF_retVec {m : Mem} {xs : List Val} {r : Exit × Mem} (h : retVec m xs = .ok r)
    (hwf : m.WF) : r.2.WF := by
  unfold retVec retv at h
  cases h
  exact WF_fresh hwf

theorem WF_vecBoolModel {ctx : Ctx} {op : VecBoolOp} {args : List Val} {m : Mem} {r : Exit × Mem}
    (h : vecBoolModel ctx op args m = .ok r) (hwf : m.WF) : r.2.WF := by
  cir_split_match h
  all_goals cir_wf_auto

theorem WF_scanfStdin {ctx : Ctx} {m : Mem} {f : Ptr} {rest : List Val} {r : Exit × Mem}
    (h : scanfStdin ctx m f rest = .ok r) (hwf : m.WF) : r.2.WF := by
  unfold scanfStdin at h
  cir_wf_auto

theorem WF_drand48State {m : Mem} {b0 : Nat} (hwf : m.WF) : (drand48State m b0).2.WF := by
  unfold drand48State
  split
  · exact hwf
  · exact Mem.WF_alloc (Mem.WF_alloc hwf _ _ _) _ _ _

set_option hygiene false in
macro_rules | `(tactic| cir_wf_term) => `(tactic| first | (cir_lhs_head h Std.scanfStdin; exact WF_scanfStdin h (by cir_wf_close)) | fail "wf rule")

theorem WF_libModel {ctx : Ctx} {op : LibOp} {args : List Val} {m : Mem} {r : Exit × Mem}
    (h : libModel ctx op args m = .ok r) (hwf : m.WF) : r.2.WF := by
  -- the memory with the `drand48` state (`cir_wf_close` closes it by assumption)
  have hst := WF_drand48State (m := m) (b0 := ctx.mod.globals.length) hwf
  cir_split_match h
  all_goals cir_wf_auto

theorem WF_longjmpModel {ctx : Ctx} {args : List Val} {m : Mem} {r : Exit × Mem}
    (h : longjmpModel ctx args m = .ok r) (hwf : m.WF) : r.2.WF := by
  cir_split_match h
  all_goals cir_wf_auto

set_option hygiene false in
macro_rules | `(tactic| cir_wf_hx) => `(tactic| first | (cir_lhs_head hx Std.freeHeap; have := WF_freeHeap hx (by cir_wf_close)) | fail "wf rule")
set_option hygiene false in
macro_rules | `(tactic| cir_wf_term) => `(tactic| first | (cir_lhs_head h Std.freeHeap; exact WF_freeHeap h (by cir_wf_close)) | fail "wf rule")
set_option hygiene false in
macro_rules | `(tactic| cir_wf_term) => `(tactic| first | (cir_lhs_head h Std.memsetModel; exact WF_memsetModel h (by cir_wf_close)) | fail "wf rule")
set_option hygiene false in
macro_rules | `(tactic| cir_wf_term) => `(tactic| first | (cir_lhs_head h Std.memcpyModel; exact WF_memcpyModel h (by cir_wf_close)) | fail "wf rule")
set_option hygiene false in
macro_rules | `(tactic| cir_wf_term) => `(tactic| first | (cir_lhs_head h Std.memcmpModel; exact WF_memcmpModel h (by cir_wf_close)) | fail "wf rule")
set_option hygiene false in
macro_rules | `(tactic| cir_wf_term) => `(tactic| first | (cir_lhs_head h Std.memchrModel; exact WF_memchrModel h (by cir_wf_close)) | fail "wf rule")
set_option hygiene false in
macro_rules | `(tactic| cir_wf_term) => `(tactic| first | (cir_lhs_head h Std.lrintModel; exact WF_lrintModel h (by cir_wf_close)) | fail "wf rule")
set_option hygiene false in
macro_rules | `(tactic| cir_wf_term) => `(tactic| first | (cir_lhs_head h Std.crModel; exact WF_crModel h (by cir_wf_close)) | fail "wf rule")
set_option hygiene false in
macro_rules | `(tactic| cir_wf_term) => `(tactic| first | (cir_lhs_head h Std.signalModel; exact WF_signalModel h (by cir_wf_close)) | fail "wf rule")
set_option hygiene false in
macro_rules | `(tactic| cir_wf_term) => `(tactic| first | (cir_lhs_head h Std.posixMemalignModel; exact WF_posixMemalignModel h (by cir_wf_close)) | fail "wf rule")
set_option hygiene false in
macro_rules | `(tactic| cir_wf_term) => `(tactic| first | (cir_lhs_head h Std.initListCtor; exact WF_initListCtor h (by cir_wf_close)) | fail "wf rule")
set_option hygiene false in
macro_rules | `(tactic| cir_wf_term) => `(tactic| first | (cir_lhs_head h Std.retVec; exact WF_retVec h (by cir_wf_close)) | fail "wf rule")
set_option hygiene false in
macro_rules | `(tactic| cir_wf_term) => `(tactic| first | (cir_lhs_head h Std.vecBoolModel; exact WF_vecBoolModel h (by cir_wf_close)) | fail "wf rule")
set_option hygiene false in
macro_rules | `(tactic| cir_wf_term) => `(tactic| first | (cir_lhs_head h Std.libModel; exact WF_libModel h (by cir_wf_close)) | fail "wf rule")
set_option hygiene false in
macro_rules | `(tactic| cir_wf_term) => `(tactic| first | (cir_lhs_head h Std.longjmpModel; exact WF_longjmpModel h (by cir_wf_close)) | fail "wf rule")

/-! #### libevent and POSIX threads -/

theorem WF_allocLib {m : Mem} (hwf : m.WF) (ty : Ty) (v : Val) : (allocLib m ty v).2.WF :=
  Mem.WF_alloc hwf .heap ty v

macro_rules | `(tactic| cir_wf_close) => `(tactic| first | (refine CIR.Std.WF_allocLib ?_ _ _; cir_wf_close) | fail "wf rule")

theorem WF_freeLibObj {m m' : Mem} {tag : String} {p : Ptr} (h : freeLibObj m tag p = .ok m')
    (hwf : m.WF) : m'.WF := by
  unfold freeLibObj at h
  cir_wf_auto

theorem WF_evRemoveFirst {ctx : Ctx} {m m' : Mem} {hp : Ptr} (h : evRemoveFirst ctx m hp = .ok m')
    (hwf : m.WF) : m'.WF := by
  unfold evRemoveFirst at h
  cir_wf_auto

set_option hygiene false in
macro_rules | `(tactic| cir_wf_hx) => `(tactic| first | (cir_lhs_head hx Std.freeLibObj; have := WF_freeLibObj hx (by cir_wf_close)) | fail "wf rule")
set_option hygiene false in
macro_rules | `(tactic| cir_wf_term) => `(tactic| first | (cir_lhs_head h Std.evRemoveFirst; exact WF_evRemoveFirst h (by cir_wf_close)) | fail "wf rule")

theorem WF_evFreeHeaders {ctx : Ctx} {m m' : Mem} {hp : Ptr} (h : evFreeHeaders ctx m hp = .ok m')
    (hwf : m.WF) : m'.WF := by
  unfold evFreeHeaders at h
  cir_wf_auto

set_option hygiene false in
macro_rules | `(tactic| cir_wf_hx) => `(tactic| first | (cir_lhs_head hx Std.evFreeHeaders; have := WF_evFreeHeaders hx (by cir_wf_close)) | fail "wf rule")

theorem WF_evFreeRequest {ctx : Ctx} {m m' : Mem} {req : Ptr} (h : evFreeRequest ctx m req = .ok m')
    (hwf : m.WF) : m'.WF := by
  unfold evFreeRequest at h
  cir_wf_auto

set_option hygiene false in
macro_rules | `(tactic| cir_wf_hx) => `(tactic| first | (cir_lhs_head hx Std.evFreeRequest; have := WF_evFreeRequest hx (by cir_wf_close)) | fail "wf rule")

theorem WF_evAddHeader {ctx : Ctx} {m : Mem} {hp k v : Ptr} {r : Exit × Mem}
    (h : evAddHeader ctx m hp k v = .ok r) (hwf : m.WF) : r.2.WF := by
  unfold evAddHeader at h
  cir_wf_auto

theorem WF_evbufferAdd {ctx : Ctx} {m : Mem} {p d : Ptr} {n : Int} {r : Exit × Mem}
    (h : evbufferAdd ctx m p d n = .ok r) (hwf : m.WF) : r.2.WF := by
  unfold evbufferAdd at h
  cir_wf_auto

theorem WF_evSendReply {ctx : Ctx} {m : Mem} {req reason buf : Ptr} {r : Exit × Mem}
    (h : evSendReply ctx m req reason buf = .ok r) (hwf : m.WF) : r.2.WF := by
  unfold evSendReply at h
  cir_wf_auto

set_option hygiene false in
macro_rules | `(tactic| cir_wf_term) => `(tactic| first | (cir_lhs_head h Std.evAddHeader; exact WF_evAddHeader h (by cir_wf_close)) | fail "wf rule")
set_option hygiene false in
macro_rules | `(tactic| cir_wf_term) => `(tactic| first | (cir_lhs_head h Std.evbufferAdd; exact WF_evbufferAdd h (by cir_wf_close)) | fail "wf rule")
set_option hygiene false in
macro_rules | `(tactic| cir_wf_term) => `(tactic| first | (cir_lhs_head h Std.evSendReply; exact WF_evSendReply h (by cir_wf_close)) | fail "wf rule")

set_option maxHeartbeats 400000 in
/-- Every library model preserves well-formedness. (`cir_split_match` splits the
match of `runModel` without its splitter, whose generation exceeds the default
heartbeat limit; the cases of the 160-odd models together take more than the
default budget too.) -/
theorem WF_runModel {ctx : Ctx} {mdl : Model} {args : List Val} {m : Mem} {r : Exit × Mem}
    (h : runModel ctx mdl args m = .ok r) (hwf : m.WF) : r.2.WF := by
  cir_split_match h
  all_goals cir_wf_auto
  -- `localeconv`: two fresh blocks, at `m.next` and `m.next + 1`
  all_goals
    cases h
    intro b hb
    dsimp only at hb ⊢
    simp only [upd]
    rw [if_neg (by omega), if_neg (by omega)]
    exact hwf b (by omega)

end Std

end CIR

/-!
  Every function of the interpreter preserves `Mem.WF`, by fixpoint
  induction over the mutual `partial_fixpoint` block of `CIR/Semantics/Eval.lean`
  (partial correctness: the motive holds at `Res.div`, so it is admissible).
  The library models enter through the hypothesis `hrm` (`Std.WF_runModel`).
-/

namespace CIR

/-- A partial-correctness predicate on `Res` holds at the bottom `Res.div`, so
it is admissible for the flat order. -/
theorem Res.admissible_imp_ok {α : Type} (H : Prop) (P : α → Prop) :
    Lean.Order.admissible (fun x : Res α => H → ∀ r, x = .ok r → P r) :=
  Lean.Order.admissible_flatOrder (b := (Res.div : Res α)) _ (fun _ r h => by cases h)

/-! ### The motives: every successful run keeps memory well formed -/

namespace WFM

def ops (f : List Op → State → Res (Step × State)) : Prop :=
  ∀ ops σ, σ.mem.WF → ∀ r, f ops σ = .ok r → r.2.mem.WF

def op (f : Op → State → Res (Step × State)) : Prop :=
  ∀ op σ, σ.mem.WF → ∀ r, f op σ = .ok r → r.2.mem.WF

def region (f : Region → List Val → State → Res (Exit × State)) : Prop :=
  ∀ rg args σ, σ.mem.WF → ∀ r, f rg args σ = .ok r → r.2.mem.WF

def block (f : List Block → BlockId → List Val → State → Res (Exit × State)) : Prop :=
  ∀ bs i args σ, σ.mem.WF → ∀ r, f bs i args σ = .ok r → r.2.mem.WF

def loop2 (f : Region → Region → State → Res (Step × State)) : Prop :=
  ∀ b c σ, σ.mem.WF → ∀ r, f b c σ = .ok r → r.2.mem.WF

def loop3 (f : Region → Region → Option (CleanupKind × Region) → State → Res (Step × State)) :
    Prop :=
  ∀ c b cl σ, σ.mem.WF → ∀ r, f c b cl σ = .ok r → r.2.mem.WF

def cleanup (f : Option (CleanupKind × Region) → Bool → State → Res State) : Prop :=
  ∀ cl isEh σ, σ.mem.WF → ∀ r, f cl isEh σ = .ok r → r.mem.WF

def loop4
    (f : Region → Region → Region → Option (CleanupKind × Region) → State → Res (Step × State)) :
    Prop :=
  ∀ c b s cl σ, σ.mem.WF → ∀ r, f c b s cl σ = .ok r → r.2.mem.WF

def call (f : String → List Val → Mem → Res (Exit × Mem)) : Prop :=
  ∀ sym args m, m.WF → ∀ r, f sym args m = .ok r → r.2.WF

open Lean.Order

theorem adm_ops : admissible ops :=
  admissible_pi_apply
    (fun (_ : List Op) (g : State → Res (Step × State)) =>
      ∀ σ : State, σ.mem.WF → ∀ r, g σ = .ok r → r.2.mem.WF) fun _ =>
  admissible_pi_apply
    (fun (σ : State) (x : Res (Step × State)) => σ.mem.WF → ∀ r, x = .ok r → r.2.mem.WF) fun _ =>
  Res.admissible_imp_ok _ _

theorem adm_op : admissible op :=
  admissible_pi_apply
    (fun (_ : Op) (g : State → Res (Step × State)) =>
      ∀ σ : State, σ.mem.WF → ∀ r, g σ = .ok r → r.2.mem.WF) fun _ =>
  admissible_pi_apply
    (fun (σ : State) (x : Res (Step × State)) => σ.mem.WF → ∀ r, x = .ok r → r.2.mem.WF) fun _ =>
  Res.admissible_imp_ok _ _

theorem adm_region : admissible region :=
  admissible_pi_apply
    (fun (_ : Region) (g : List Val → State → Res (Exit × State)) =>
      ∀ (args : List Val) (σ : State), σ.mem.WF → ∀ r, g args σ = .ok r → r.2.mem.WF) fun _ =>
  admissible_pi_apply
    (fun (_ : List Val) (g : State → Res (Exit × State)) =>
      ∀ σ : State, σ.mem.WF → ∀ r, g σ = .ok r → r.2.mem.WF) fun _ =>
  admissible_pi_apply
    (fun (σ : State) (x : Res (Exit × State)) => σ.mem.WF → ∀ r, x = .ok r → r.2.mem.WF) fun _ =>
  Res.admissible_imp_ok _ _

theorem adm_block : admissible block :=
  admissible_pi_apply
    (fun (_ : List Block) (g : BlockId → List Val → State → Res (Exit × State)) =>
      ∀ (i : BlockId) (args : List Val) (σ : State), σ.mem.WF → ∀ r, g i args σ = .ok r → r.2.mem.WF) fun _ =>
  admissible_pi_apply
    (fun (_ : BlockId) (g : List Val → State → Res (Exit × State)) =>
      ∀ (args : List Val) (σ : State), σ.mem.WF → ∀ r, g args σ = .ok r → r.2.mem.WF) fun _ =>
  admissible_pi_apply
    (fun (_ : List Val) (g : State → Res (Exit × State)) =>
      ∀ σ : State, σ.mem.WF → ∀ r, g σ = .ok r → r.2.mem.WF) fun _ =>
  admissible_pi_apply
    (fun (σ : State) (x : Res (Exit × State)) => σ.mem.WF → ∀ r, x = .ok r → r.2.mem.WF) fun _ =>
  Res.admissible_imp_ok _ _

theorem adm_loop2 : admissible loop2 :=
  admissible_pi_apply
    (fun (_ : Region) (g : Region → State → Res (Step × State)) =>
      ∀ (c : Region) (σ : State), σ.mem.WF → ∀ r, g c σ = .ok r → r.2.mem.WF) fun _ =>
  admissible_pi_apply
    (fun (_ : Region) (g : State → Res (Step × State)) =>
      ∀ σ : State, σ.mem.WF → ∀ r, g σ = .ok r → r.2.mem.WF) fun _ =>
  admissible_pi_apply
    (fun (σ : State) (x : Res (Step × State)) => σ.mem.WF → ∀ r, x = .ok r → r.2.mem.WF) fun _ =>
  Res.admissible_imp_ok _ _

theorem adm_loop3 : admissible loop3 :=
  admissible_pi_apply
    (fun (_ : Region) (g : Region → Option (CleanupKind × Region) → State → Res (Step × State)) =>
      ∀ (b : Region) (cl : Option (CleanupKind × Region)) (σ : State), σ.mem.WF → ∀ r, g b cl σ = .ok r → r.2.mem.WF) fun _ =>
  admissible_pi_apply
    (fun (_ : Region) (g : Option (CleanupKind × Region) → State → Res (Step × State)) =>
      ∀ (cl : Option (CleanupKind × Region)) (σ : State), σ.mem.WF → ∀ r, g cl σ = .ok r → r.2.mem.WF) fun _ =>
  admissible_pi_apply
    (fun (_ : Option (CleanupKind × Region)) (g : State → Res (Step × State)) =>
      ∀ σ : State, σ.mem.WF → ∀ r, g σ = .ok r → r.2.mem.WF) fun _ =>
  admissible_pi_apply
    (fun (σ : State) (x : Res (Step × State)) => σ.mem.WF → ∀ r, x = .ok r → r.2.mem.WF) fun _ =>
  Res.admissible_imp_ok _ _

theorem adm_cleanup : admissible cleanup :=
  admissible_pi_apply
    (fun (_ : Option (CleanupKind × Region)) (g : Bool → State → Res State) =>
      ∀ (isEh : Bool) (σ : State), σ.mem.WF → ∀ r, g isEh σ = .ok r → r.mem.WF) fun _ =>
  admissible_pi_apply
    (fun (_ : Bool) (g : State → Res State) =>
      ∀ σ : State, σ.mem.WF → ∀ r, g σ = .ok r → r.mem.WF) fun _ =>
  admissible_pi_apply
    (fun (σ : State) (x : Res State) => σ.mem.WF → ∀ r, x = .ok r → r.mem.WF) fun _ =>
  Res.admissible_imp_ok _ _

theorem adm_loop4 : admissible loop4 :=
  admissible_pi_apply
    (fun (_ : Region)
        (g : Region → Region → Option (CleanupKind × Region) → State → Res (Step × State)) =>
      ∀ (b s : Region) (cl : Option (CleanupKind × Region)) (σ : State), σ.mem.WF → ∀ r, g b s cl σ = .ok r → r.2.mem.WF) fun _ =>
  admissible_pi_apply
    (fun (_ : Region) (g : Region → Option (CleanupKind × Region) → State → Res (Step × State)) =>
      ∀ (s : Region) (cl : Option (CleanupKind × Region)) (σ : State), σ.mem.WF → ∀ r, g s cl σ = .ok r → r.2.mem.WF) fun _ =>
  admissible_pi_apply
    (fun (_ : Region) (g : Option (CleanupKind × Region) → State → Res (Step × State)) =>
      ∀ (cl : Option (CleanupKind × Region)) (σ : State), σ.mem.WF → ∀ r, g cl σ = .ok r → r.2.mem.WF) fun _ =>
  admissible_pi_apply
    (fun (_ : Option (CleanupKind × Region)) (g : State → Res (Step × State)) =>
      ∀ σ : State, σ.mem.WF → ∀ r, g σ = .ok r → r.2.mem.WF) fun _ =>
  admissible_pi_apply
    (fun (σ : State) (x : Res (Step × State)) => σ.mem.WF → ∀ r, x = .ok r → r.2.mem.WF) fun _ =>
  Res.admissible_imp_ok _ _

theorem adm_call : admissible call :=
  admissible_pi_apply
    (fun (_ : String) (g : List Val → Mem → Res (Exit × Mem)) =>
      ∀ (args : List Val) (m : Mem), m.WF → ∀ r, g args m = .ok r → r.2.WF) fun _ =>
  admissible_pi_apply
    (fun (_ : List Val) (g : Mem → Res (Exit × Mem)) =>
      ∀ m : Mem, m.WF → ∀ r, g m = .ok r → r.2.WF) fun _ =>
  admissible_pi_apply
    (fun (m : Mem) (x : Res (Exit × Mem)) => m.WF → ∀ r, x = .ok r → r.2.WF) fun _ =>
  Res.admissible_imp_ok _ _

end WFM

theorem WF_finishRegion {e : Exit} {σ : State} {r : Step × State} (h : finishRegion e σ = .ok r)
    (hwf : σ.mem.WF) : r.2.mem.WF := by
  unfold finishRegion at h
  cir_wf_auto

/-! ### Forward rules for the induction hypotheses (names fixed: `ih_*`, `hrm`) -/

set_option hygiene false in
macro_rules | `(tactic| cir_wf_hx) => `(tactic| first | (cir_lhs_head hx finishRegion; have := WF_finishRegion hx (by cir_wf_close)) | fail "wf rule")
set_option hygiene false in
macro_rules | `(tactic| cir_wf_term) => `(tactic| first | (cir_lhs_head h finishRegion; exact WF_finishRegion h (by cir_wf_close)) | fail "wf rule")

set_option hygiene false in
macro_rules | `(tactic| cir_wf_hx) => `(tactic| first | (cir_lhs_head hx evalSimple; have := WF_evalSimple hx (by cir_wf_close)) | fail "wf rule")
set_option hygiene false in
macro_rules | `(tactic| cir_wf_hx) => `(tactic| first | (cir_lhs_head hx Std.runModel; have := hrm hx (by cir_wf_close)) | fail "wf rule")
set_option hygiene false in
macro_rules | `(tactic| cir_wf_hx) => `(tactic| first | have := ih_ops _ _ (by cir_wf_close) _ hx | fail "wf rule")
set_option hygiene false in
macro_rules | `(tactic| cir_wf_hx) => `(tactic| first | have := ih_op _ _ (by cir_wf_close) _ hx | fail "wf rule")
set_option hygiene false in
macro_rules | `(tactic| cir_wf_hx) => `(tactic| first | have := ih_cases _ _ (by cir_wf_close) _ hx | fail "wf rule")
set_option hygiene false in
macro_rules | `(tactic| cir_wf_hx) => `(tactic| first | have := ih_region _ _ _ (by cir_wf_close) _ hx | fail "wf rule")
set_option hygiene false in
macro_rules | `(tactic| cir_wf_hx) => `(tactic| first | have := ih_block _ _ _ _ (by cir_wf_close) _ hx | fail "wf rule")
set_option hygiene false in
macro_rules | `(tactic| cir_wf_hx) => `(tactic| first | have := ih_do _ _ _ (by cir_wf_close) _ hx | fail "wf rule")
set_option hygiene false in
macro_rules | `(tactic| cir_wf_hx) => `(tactic| first | have := ih_docond _ _ _ (by cir_wf_close) _ hx | fail "wf rule")
set_option hygiene false in
macro_rules | `(tactic| cir_wf_hx) => `(tactic| first | have := ih_while _ _ _ _ (by cir_wf_close) _ hx | fail "wf rule")
set_option hygiene false in
macro_rules | `(tactic| cir_wf_hx) => `(tactic| first | have := ih_cleanup _ _ _ (by cir_wf_close) _ hx | fail "wf rule")
set_option hygiene false in
macro_rules | `(tactic| cir_wf_hx) => `(tactic| first | have := ih_for _ _ _ _ _ (by cir_wf_close) _ hx | fail "wf rule")
set_option hygiene false in
macro_rules | `(tactic| cir_wf_hx) => `(tactic| first | have := ih_forstep _ _ _ _ _ (by cir_wf_close) _ hx | fail "wf rule")
set_option hygiene false in
macro_rules | `(tactic| cir_wf_hx) => `(tactic| first | have := ih_call _ _ _ (by cir_wf_close) _ hx | fail "wf rule")

set_option hygiene false in
macro_rules | `(tactic| cir_wf_term) => `(tactic| first | (cir_lhs_head h Std.runModel; exact hrm h (by cir_wf_close)) | fail "wf rule")
set_option hygiene false in
macro_rules | `(tactic| cir_wf_term) => `(tactic| first | exact ih_ops _ _ (by cir_wf_close) _ h | fail "wf rule")
set_option hygiene false in
macro_rules | `(tactic| cir_wf_term) => `(tactic| first | exact ih_op _ _ (by cir_wf_close) _ h | fail "wf rule")
set_option hygiene false in
macro_rules | `(tactic| cir_wf_term) => `(tactic| first | exact ih_cases _ _ (by cir_wf_close) _ h | fail "wf rule")
set_option hygiene false in
macro_rules | `(tactic| cir_wf_term) => `(tactic| first | exact ih_block _ _ _ _ (by cir_wf_close) _ h | fail "wf rule")
set_option hygiene false in
macro_rules | `(tactic| cir_wf_term) => `(tactic| first | exact ih_do _ _ _ (by cir_wf_close) _ h | fail "wf rule")
set_option hygiene false in
macro_rules | `(tactic| cir_wf_term) => `(tactic| first | exact ih_docond _ _ _ (by cir_wf_close) _ h | fail "wf rule")
set_option hygiene false in
macro_rules | `(tactic| cir_wf_term) => `(tactic| first | exact ih_while _ _ _ _ (by cir_wf_close) _ h | fail "wf rule")
set_option hygiene false in
macro_rules | `(tactic| cir_wf_term) => `(tactic| first | exact ih_for _ _ _ _ _ (by cir_wf_close) _ h | fail "wf rule")
set_option hygiene false in
macro_rules | `(tactic| cir_wf_term) => `(tactic| first | exact ih_forstep _ _ _ _ _ (by cir_wf_close) _ h | fail "wf rule")

/-! ### The induction -/

/-- All functions of the mutual block preserve well-formedness, given that
the library models do. -/
theorem WF_mutual_of
    (hrm : ∀ {ctx : Ctx} {mdl : Model} {args : List Val} {m : Mem} {r : Exit × Mem},
      Std.runModel ctx mdl args m = .ok r → m.WF → r.2.WF) (ctx : Ctx) :
    WFM.ops (evalOps ctx) ∧ WFM.op (evalOp ctx) ∧ WFM.ops (evalCases ctx) ∧
    WFM.region (evalRegion ctx) ∧ WFM.block (evalBlock ctx) ∧ WFM.loop2 (evalDo ctx) ∧
    WFM.loop2 (evalDoCond ctx) ∧ WFM.loop3 (evalWhile ctx) ∧
    WFM.cleanup (evalIterCleanup ctx) ∧ WFM.loop4 (evalFor ctx) ∧ WFM.loop4 (evalForStep ctx) ∧
    WFM.call (evalCall ctx) := by
  refine ⟨
    evalOps.fixpoint_induct ctx WFM.ops WFM.op WFM.ops WFM.region WFM.block WFM.loop2 WFM.loop2
      WFM.loop3 WFM.cleanup WFM.loop4 WFM.loop4 WFM.call WFM.adm_ops WFM.adm_op WFM.adm_ops
      WFM.adm_region WFM.adm_block WFM.adm_loop2 WFM.adm_loop2 WFM.adm_loop3 WFM.adm_cleanup
      WFM.adm_loop4 WFM.adm_loop4 WFM.adm_call ?s1 ?s2 ?s3 ?s4 ?s5 ?s6 ?s7 ?s8 ?s9 ?s10 ?s11 ?s12,
    evalOp.fixpoint_induct ctx WFM.ops WFM.op WFM.ops WFM.region WFM.block WFM.loop2 WFM.loop2
      WFM.loop3 WFM.cleanup WFM.loop4 WFM.loop4 WFM.call WFM.adm_ops WFM.adm_op WFM.adm_ops
      WFM.adm_region WFM.adm_block WFM.adm_loop2 WFM.adm_loop2 WFM.adm_loop3 WFM.adm_cleanup
      WFM.adm_loop4 WFM.adm_loop4 WFM.adm_call ?s1 ?s2 ?s3 ?s4 ?s5 ?s6 ?s7 ?s8 ?s9 ?s10 ?s11 ?s12,
    evalCases.fixpoint_induct ctx WFM.ops WFM.op WFM.ops WFM.region WFM.block WFM.loop2 WFM.loop2
      WFM.loop3 WFM.cleanup WFM.loop4 WFM.loop4 WFM.call WFM.adm_ops WFM.adm_op WFM.adm_ops
      WFM.adm_region WFM.adm_block WFM.adm_loop2 WFM.adm_loop2 WFM.adm_loop3 WFM.adm_cleanup
      WFM.adm_loop4 WFM.adm_loop4 WFM.adm_call ?s1 ?s2 ?s3 ?s4 ?s5 ?s6 ?s7 ?s8 ?s9 ?s10 ?s11 ?s12,
    evalRegion.fixpoint_induct ctx WFM.ops WFM.op WFM.ops WFM.region WFM.block WFM.loop2 WFM.loop2
      WFM.loop3 WFM.cleanup WFM.loop4 WFM.loop4 WFM.call WFM.adm_ops WFM.adm_op WFM.adm_ops
      WFM.adm_region WFM.adm_block WFM.adm_loop2 WFM.adm_loop2 WFM.adm_loop3 WFM.adm_cleanup
      WFM.adm_loop4 WFM.adm_loop4 WFM.adm_call ?s1 ?s2 ?s3 ?s4 ?s5 ?s6 ?s7 ?s8 ?s9 ?s10 ?s11 ?s12,
    evalBlock.fixpoint_induct ctx WFM.ops WFM.op WFM.ops WFM.region WFM.block WFM.loop2 WFM.loop2
      WFM.loop3 WFM.cleanup WFM.loop4 WFM.loop4 WFM.call WFM.adm_ops WFM.adm_op WFM.adm_ops
      WFM.adm_region WFM.adm_block WFM.adm_loop2 WFM.adm_loop2 WFM.adm_loop3 WFM.adm_cleanup
      WFM.adm_loop4 WFM.adm_loop4 WFM.adm_call ?s1 ?s2 ?s3 ?s4 ?s5 ?s6 ?s7 ?s8 ?s9 ?s10 ?s11 ?s12,
    evalDo.fixpoint_induct ctx WFM.ops WFM.op WFM.ops WFM.region WFM.block WFM.loop2 WFM.loop2
      WFM.loop3 WFM.cleanup WFM.loop4 WFM.loop4 WFM.call WFM.adm_ops WFM.adm_op WFM.adm_ops
      WFM.adm_region WFM.adm_block WFM.adm_loop2 WFM.adm_loop2 WFM.adm_loop3 WFM.adm_cleanup
      WFM.adm_loop4 WFM.adm_loop4 WFM.adm_call ?s1 ?s2 ?s3 ?s4 ?s5 ?s6 ?s7 ?s8 ?s9 ?s10 ?s11 ?s12,
    evalDoCond.fixpoint_induct ctx WFM.ops WFM.op WFM.ops WFM.region WFM.block WFM.loop2 WFM.loop2
      WFM.loop3 WFM.cleanup WFM.loop4 WFM.loop4 WFM.call WFM.adm_ops WFM.adm_op WFM.adm_ops
      WFM.adm_region WFM.adm_block WFM.adm_loop2 WFM.adm_loop2 WFM.adm_loop3 WFM.adm_cleanup
      WFM.adm_loop4 WFM.adm_loop4 WFM.adm_call ?s1 ?s2 ?s3 ?s4 ?s5 ?s6 ?s7 ?s8 ?s9 ?s10 ?s11 ?s12,
    evalWhile.fixpoint_induct ctx WFM.ops WFM.op WFM.ops WFM.region WFM.block WFM.loop2 WFM.loop2
      WFM.loop3 WFM.cleanup WFM.loop4 WFM.loop4 WFM.call WFM.adm_ops WFM.adm_op WFM.adm_ops
      WFM.adm_region WFM.adm_block WFM.adm_loop2 WFM.adm_loop2 WFM.adm_loop3 WFM.adm_cleanup
      WFM.adm_loop4 WFM.adm_loop4 WFM.adm_call ?s1 ?s2 ?s3 ?s4 ?s5 ?s6 ?s7 ?s8 ?s9 ?s10 ?s11 ?s12,
    evalIterCleanup.fixpoint_induct ctx WFM.ops WFM.op WFM.ops WFM.region WFM.block WFM.loop2
      WFM.loop2 WFM.loop3 WFM.cleanup WFM.loop4 WFM.loop4 WFM.call WFM.adm_ops WFM.adm_op
      WFM.adm_ops WFM.adm_region WFM.adm_block WFM.adm_loop2 WFM.adm_loop2 WFM.adm_loop3
      WFM.adm_cleanup WFM.adm_loop4 WFM.adm_loop4 WFM.adm_call
      ?s1 ?s2 ?s3 ?s4 ?s5 ?s6 ?s7 ?s8 ?s9 ?s10 ?s11 ?s12,
    evalFor.fixpoint_induct ctx WFM.ops WFM.op WFM.ops WFM.region WFM.block WFM.loop2 WFM.loop2
      WFM.loop3 WFM.cleanup WFM.loop4 WFM.loop4 WFM.call WFM.adm_ops WFM.adm_op WFM.adm_ops
      WFM.adm_region WFM.adm_block WFM.adm_loop2 WFM.adm_loop2 WFM.adm_loop3 WFM.adm_cleanup
      WFM.adm_loop4 WFM.adm_loop4 WFM.adm_call ?s1 ?s2 ?s3 ?s4 ?s5 ?s6 ?s7 ?s8 ?s9 ?s10 ?s11 ?s12,
    evalForStep.fixpoint_induct ctx WFM.ops WFM.op WFM.ops WFM.region WFM.block WFM.loop2 WFM.loop2
      WFM.loop3 WFM.cleanup WFM.loop4 WFM.loop4 WFM.call WFM.adm_ops WFM.adm_op WFM.adm_ops
      WFM.adm_region WFM.adm_block WFM.adm_loop2 WFM.adm_loop2 WFM.adm_loop3 WFM.adm_cleanup
      WFM.adm_loop4 WFM.adm_loop4 WFM.adm_call ?s1 ?s2 ?s3 ?s4 ?s5 ?s6 ?s7 ?s8 ?s9 ?s10 ?s11 ?s12,
    evalCall.fixpoint_induct ctx WFM.ops WFM.op WFM.ops WFM.region WFM.block WFM.loop2 WFM.loop2
      WFM.loop3 WFM.cleanup WFM.loop4 WFM.loop4 WFM.call WFM.adm_ops WFM.adm_op WFM.adm_ops
      WFM.adm_region WFM.adm_block WFM.adm_loop2 WFM.adm_loop2 WFM.adm_loop3 WFM.adm_cleanup
      WFM.adm_loop4 WFM.adm_loop4 WFM.adm_call ?s1 ?s2 ?s3 ?s4 ?s5 ?s6 ?s7 ?s8 ?s9 ?s10 ?s11 ?s12⟩
  case s1 =>
    intro evalOps evalOp ih_ops ih_op ops σ hwf r h
    cir_wf_auto
  case s2 =>
    intro evalOp evalCases evalRegion evalDo evalWhile evalFor evalCall ih_op ih_cases ih_region ih_do
      ih_while ih_for ih_call op σ hwf r h
    dsimp only at h
    cir_split_match h
    all_goals cir_wf_auto
  case s3 =>
    intro evalCases evalRegion ih_cases ih_region ops σ hwf r h
    cir_wf_auto
  case s4 =>
    intro evalBlock ih_block rg args σ hwf r h
    cir_wf_auto
  case s5 =>
    intro evalOps evalBlock ih_ops ih_block bs i args σ hwf r h
    cir_wf_auto
  case s6 =>
    intro evalRegion evalDoCond ih_region ih_docond b c σ hwf r h
    cir_wf_auto
  case s7 =>
    intro evalRegion evalDo ih_region ih_do b c σ hwf r h
    cir_wf_auto
  case s8 =>
    intro evalRegion evalWhile evalIterCleanup ih_region ih_while ih_cleanup c b cl σ hwf r h
    cir_wf_auto
  case s9 =>
    intro evalRegion ih_region cl isEh σ hwf r h
    cir_wf_auto
  case s10 =>
    intro evalRegion evalIterCleanup evalForStep ih_region ih_cleanup ih_forstep c b s cl σ hwf r h
    cir_wf_auto
  case s11 =>
    intro evalRegion evalIterCleanup evalFor ih_region ih_cleanup ih_for c b s cl σ hwf r h
    cir_wf_auto
  case s12 =>
    intro evalRegion ih_region sym args m hwf r h
    cir_wf_auto

end CIR

namespace CIR

/-- Every function of the interpreter keeps memory well formed on every
successful run. -/
theorem WF_mutual (ctx : Ctx) :
    WFM.ops (evalOps ctx) ∧ WFM.op (evalOp ctx) ∧ WFM.ops (evalCases ctx) ∧
    WFM.region (evalRegion ctx) ∧ WFM.block (evalBlock ctx) ∧ WFM.loop2 (evalDo ctx) ∧
    WFM.loop2 (evalDoCond ctx) ∧ WFM.loop3 (evalWhile ctx) ∧
    WFM.cleanup (evalIterCleanup ctx) ∧ WFM.loop4 (evalFor ctx) ∧ WFM.loop4 (evalForStep ctx) ∧
    WFM.call (evalCall ctx) :=
  WF_mutual_of (fun h hwf => Std.WF_runModel h hwf) ctx

theorem evalOps_wf {ctx : Ctx} {ops : List Op} {σ : State} {r : Step × State}
    (hwf : σ.mem.WF) (h : evalOps ctx ops σ = .ok r) : r.2.mem.WF :=
  (WF_mutual ctx).1 ops σ hwf r h

theorem evalOp_wf {ctx : Ctx} {op : Op} {σ : State} {r : Step × State}
    (hwf : σ.mem.WF) (h : evalOp ctx op σ = .ok r) : r.2.mem.WF :=
  (WF_mutual ctx).2.1 op σ hwf r h

theorem evalCases_wf {ctx : Ctx} {ops : List Op} {σ : State} {r : Step × State}
    (hwf : σ.mem.WF) (h : evalCases ctx ops σ = .ok r) : r.2.mem.WF :=
  (WF_mutual ctx).2.2.1 ops σ hwf r h

theorem evalRegion_wf {ctx : Ctx} {rg : Region} {args : List Val} {σ : State} {r : Exit × State}
    (hwf : σ.mem.WF) (h : evalRegion ctx rg args σ = .ok r) : r.2.mem.WF :=
  (WF_mutual ctx).2.2.2.1 rg args σ hwf r h

theorem evalBlock_wf {ctx : Ctx} {bs : List Block} {i : BlockId} {args : List Val} {σ : State}
    {r : Exit × State} (hwf : σ.mem.WF) (h : evalBlock ctx bs i args σ = .ok r) : r.2.mem.WF :=
  (WF_mutual ctx).2.2.2.2.1 bs i args σ hwf r h

theorem evalDo_wf {ctx : Ctx} {b c : Region} {σ : State} {r : Step × State}
    (hwf : σ.mem.WF) (h : evalDo ctx b c σ = .ok r) : r.2.mem.WF :=
  (WF_mutual ctx).2.2.2.2.2.1 b c σ hwf r h

theorem evalDoCond_wf {ctx : Ctx} {b c : Region} {σ : State} {r : Step × State}
    (hwf : σ.mem.WF) (h : evalDoCond ctx b c σ = .ok r) : r.2.mem.WF :=
  (WF_mutual ctx).2.2.2.2.2.2.1 b c σ hwf r h

theorem evalWhile_wf {ctx : Ctx} {c b : Region} {cl : Option (CleanupKind × Region)} {σ : State}
    {r : Step × State} (hwf : σ.mem.WF) (h : evalWhile ctx c b cl σ = .ok r) : r.2.mem.WF :=
  (WF_mutual ctx).2.2.2.2.2.2.2.1 c b cl σ hwf r h

theorem evalIterCleanup_wf {ctx : Ctx} {cl : Option (CleanupKind × Region)} {isEh : Bool}
    {σ : State} {r : State} (hwf : σ.mem.WF) (h : evalIterCleanup ctx cl isEh σ = .ok r) :
    r.mem.WF :=
  (WF_mutual ctx).2.2.2.2.2.2.2.2.1 cl isEh σ hwf r h

theorem evalFor_wf {ctx : Ctx} {c b s : Region} {cl : Option (CleanupKind × Region)} {σ : State}
    {r : Step × State} (hwf : σ.mem.WF) (h : evalFor ctx c b s cl σ = .ok r) : r.2.mem.WF :=
  (WF_mutual ctx).2.2.2.2.2.2.2.2.2.1 c b s cl σ hwf r h

theorem evalForStep_wf {ctx : Ctx} {c b s : Region} {cl : Option (CleanupKind × Region)}
    {σ : State} {r : Step × State} (hwf : σ.mem.WF) (h : evalForStep ctx c b s cl σ = .ok r) :
    r.2.mem.WF :=
  (WF_mutual ctx).2.2.2.2.2.2.2.2.2.2.1 c b s cl σ hwf r h

/-- Every call keeps memory well formed. -/
theorem evalCall_wf {ctx : Ctx} {sym : String} {args : List Val} {m : Mem} {r : Exit × Mem}
    (hwf : m.WF) (h : evalCall ctx sym args m = .ok r) : r.2.WF :=
  (WF_mutual ctx).2.2.2.2.2.2.2.2.2.2.2 sym args m hwf r h

/-- A call from a well-formed memory ends in a well-formed memory. -/
theorem Calls.wf {ctx : Ctx} {sym : String} {args : List Val} {m : Mem}
    {Q : Exit → Mem → Prop} (h : Calls ctx sym args m Q) (hwf : m.WF) :
    Calls ctx sym args m (fun e m' => Q e m' ∧ m'.WF) := by
  unfold Calls at h ⊢
  obtain ⟨r, hr, hq⟩ := Res.holds_ok_iff.mp h
  exact Res.holds_ok_iff.mpr ⟨r, hr, hq, evalCall_wf hwf hr⟩

/-- A function that returns, called from a well-formed memory, returns in a
well-formed memory. -/
theorem Returns.wf {ctx : Ctx} {sym : String} {args : List Val} {m : Mem}
    {post : Option Val → Mem → Prop} (h : Returns ctx sym args m post) (hwf : m.WF) :
    Returns ctx sym args m (fun v m' => post v m' ∧ m'.WF) := by
  unfold Returns Calls at h ⊢
  obtain ⟨⟨e, m'⟩, hr, hq⟩ := Res.holds_ok_iff.mp h
  refine Res.holds_ok_iff.mpr ⟨(e, m'), hr, ?_⟩
  have hw : m'.WF := evalCall_wf hwf hr
  cases e with
  | ret v => exact ⟨hq, hw⟩
  | _ => exact hq.elim


end CIR

namespace CIR

/-- Call rule with memory well-formedness: from a well-formed memory, the
continuation also knows that the memory after the call is well formed
(`Returns.wf`), whatever the callee's postcondition says. -/
theorem holds_call_spec_wf {ctx : Ctx} {sym : String} {args : List Val} {m : Mem}
    {post : Option Val → Mem → Prop} {K : Exit × Mem → Prop}
    (hspec : Returns ctx sym args m post) (hwf : m.WF)
    (hk : ∀ v m', post v m' → m'.WF → K (.ret v, m')) :
    (evalCall ctx sym args m).holds K :=
  holds_call_spec (Returns.wf hspec hwf) fun v m' h => hk v m' h.1 h.2

end CIR
