import CIR.Tactic.VCG
import CIR.Logic.CJTree

/-!
  Frame obligations of loops over the items of a sibling list whose invariant
  states its frame folded (`MemAgree`, see `CIR/Logic/Loops.lean`), as
  `cir_vcg` leaves them:
  * `cir_agree_step hkl hag`: the frame at `k + 1` after an iteration that
    wrote only item `k`'s blocks and stack slots (`MemAgree.cj_step`);
  * `cir_wf`: well-formedness of a memory built by writes below `next` and
    scope exits;
  * `cir_simp_frame`, `cir_simp_frame_at h`: the goal (a hypothesis)
    evaluated through writes, scope exits and the frames of callees (the
    `cirH_…` facts); `cir_refute_mem` uses it on the hypotheses of a path that
    symbolic execution could not refute (a `free` that would find its block
    dead: the lookup through the iteration's writes finds it live).
-/

namespace CIR.Tactic

open Lean Meta Elab Tactic

/-- The simp set of the frame closers: lookups through writes (`upd`) and
scope exits below their range (`killRange_of_lt`), conditions decided by
`cir_disch`. Small on purpose: unfolding every `killRange` duplicates the
memory term at each level, and the full symbolic-execution set exceeds
simp's step limit on the memory of a loop body with a call. -/
def frameLemmas : Array Name := #[``CIR.upd_apply, ``CIR.killRange_of_lt, ``CIR.killRange_of_ge,
  -- (a condition that holds is decided syntactically, `b = b`; trying
  -- `ite_pos'` too would double the discharger's work at every write)
  ``CIR.ite_neg', `reduceIte, ``eq_self_iff_true, ``ite_true, ``ite_false, ``Option.isSome_some,
  ``Option.isSome_none, ``Bool.true_eq_false, ``Bool.false_eq_true, ``implies_true, ``false_implies]

/-- The `cirH_…` facts about memory blocks (`m.blocks b = …`, possibly
quantified: callees' frames, the blocks a loop iteration reads) and the
disequalities among them. -/
def frameHyps (exclude : Name := .anonymous) : TacticM (Array Term) := do
  let lctx := (← (← getMainGoal).getDecl).lctx
  let mut out := #[]
  for d in lctx do
    if d.isImplementationDetail || d.userName.hasMacroScopes || d.userName == exclude then continue
    -- (the latest hypothesis of each name)
    unless (lctx.findFromUserName? d.userName).map (·.fvarId) == some d.fvarId do continue
    unless d.userName.toString.startsWith "cirH_" do continue
    let mut t := d.type.consumeMData
    for _ in [0:8] do
      match t with
      | .forallE _ _ b _ => t := b.consumeMData
      | _ => break
    let isMem := match t.eq? with
      | some (_, lhs, _) => lhs.isApp && lhs.appFn!.isAppOf ``CIR.Mem.blocks
      | none => false
    if isMem || t.isAppOf ``Not || t.isAppOf ``Ne then out := out.push (mkIdent d.userName : Term)
  return out

/-- The discharger of the frame closers: a fact, arithmetic, or a fact under
premises (cheaper than `cir_disch`: the memory of a loop body is a deep term,
and simp tries the conditions of every write at every level). -/
macro "cir_frame_disch" : tactic => `(tactic| first | assumption | omega | cir_hyp_apply)

elab "cir_simp_frame" : tactic => do
  let args ← simpArgs frameLemmas (← frameHyps)
  evalTactic (← `(tactic| simp (config := { maxSteps := 4000000 }) (disch := cir_frame_disch) only [$args,*]))

elab "cir_simp_frame_at " h:ident : tactic => do
  let args ← simpArgs frameLemmas (← frameHyps h.getId)
  evalTactic (← `(tactic| simp (config := { maxSteps := 4000000 }) (disch := cir_frame_disch) only [$args,*] at $h:ident))

/-- Close a goal `False` by evaluating one of the hypotheses about memory
lookups (`upd`, `killRange`) to `False`. -/
elab "cir_refute_mem" : tactic => do
  let g ← getMainGoal
  unless (← whnfR (← instantiateMVars (← g.getType))).isConstOf ``False do
    throwError "cir_refute_mem: the goal is not False"
  let cands ← g.withContext do
    let mut out := #[]
    for d in (← getLCtx) do
      if d.isImplementationDetail then continue
      let ty ← instantiateMVars d.type
      if (ty.find? fun e => e.isConstOf ``CIR.upd || e.isConstOf ``CIR.killRange).isSome then
        out := out.push d.fvarId
    return out
  for fv in cands.reverse do
    let s ← saveState
    try
      -- the hypothesis as a premise of the goal, simplified with the others
      let (_, g') ← g.revert #[fv] (preserveOrder := true)
      replaceMainGoal [g']
      evalTactic (← `(tactic| cir_simp_frame))
      if (← getGoals).isEmpty then return
      s.restore
    catch _ => s.restore
  throwError "cir_refute_mem: no hypothesis evaluates to False"

end CIR.Tactic

namespace CIR

set_option hygiene false in
/-- The frame at `k + 1` after an iteration over item `k` (`MemAgree.cj_step`):
every block written is one of item `k`'s or a stack slot of the function, and
callees changed only their own blocks. -/
macro "cir_agree_step" hkl:term:max hag:term:max : tactic => `(tactic| (
  apply MemAgree.cj_step $hkl $hag
  intro b hb1 hb4
  obtain ⟨cirH_nbi, cirH_nbv, cirH_nbs, cirH_nbc⟩ := CJ.not_mem_blocks hb4
  cir_simp_frame))

/-- Well-formedness of a memory built by writes below `next` and scope exits
(`Mem.WF_upd`, `Mem.WF_killRange`, `Mem.WF_mono`). -/
macro "cir_wf" : tactic => `(tactic| (
  repeat (first
    | refine Mem.WF_upd ?_ (by first | omega | (cir_strip_mdata; omega) | ((try simp only at *); omega)) _
    | refine Mem.WF_killRange ?_)
  first
    | assumption
    | exact Mem.WF_mono' ‹_› (by first | omega | (cir_strip_mdata; omega))
    | exact Mem.WF_mono ‹_› (by first | omega | (cir_strip_mdata; omega))))

end CIR
