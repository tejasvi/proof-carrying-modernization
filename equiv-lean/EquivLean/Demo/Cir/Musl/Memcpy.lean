import EquivLean.Demo.Cir.Musl.MemcpyCex

/-!
# musl `memcpy` where its word paths do not run

musl's generic C `memcpy` first copies single bytes until `s` is 4-aligned (the head loop). If
`d` is then 4-aligned, it copies `n & ~3` bytes as 32-bit words; otherwise, from 32 bytes on, it
copies shifted words. Up to cirlean 28e2380 these word accesses touched one element each. Under
punning2 (cirlean `next`, where this file is checked) musl's word paths are undefined behaviour in
cirlean: GCC defines their `uint32_t` accesses to `char` arrays through `__may_alias__`, cirlean treats
them as type-punned accesses (`MemcpyCex`). So `musl_memcpy_pspec` covers the byte paths only, the runs
without word accesses (`WordFree`): after the head loop's `h` bytes, `n - h < 4` with `d` aligned, or
`n - h < 32` with `d` not aligned. Everything is then copied byte by byte, with `unsigned char` loads
and stores, so the destination gets each source character modulo 256 (`wysf`). Both arrays must be
`char` arrays (`htys`, `htyd`).
-/

open CIR EquivLean.Cir

set_option maxHeartbeats 40000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

namespace EquivLean.Demo.Cir.Musl

open EquivLean.Demo.Cir.Musl.Gen.Memcpy (ctx)

/-- The destination array `zs` after the values `L` were copied to positions `id ..`. -/
def copyList (zs : List Val) (id : Nat) (L : List Val) : List Val :=
  zs.take id ++ L ++ zs.drop (id + L.length)

theorem copyList_nil (zs : List Val) (id : Nat) : copyList zs id [] = zs := by
  simp [copyList]

theorem copyList_length (zs : List Val) (id : Nat) (L : List Val) (h : id + L.length ≤ zs.length) :
    (copyList zs id L).length = zs.length := by
  simp [copyList]; omega

theorem copyList_set (zs : List Val) (id : Nat) (L : List Val) (v : Val) (h : id + L.length < zs.length) :
    (copyList zs id L).set (id + L.length) v = copyList zs id (L ++ [v]) := by
  have hd : zs.drop (id + L.length) = zs[id + L.length] :: zs.drop (id + L.length + 1) :=
    List.drop_eq_getElem_cons h
  have ht : (zs.take id).length = id := by simp; omega
  unfold copyList
  rw [hd, List.append_assoc, List.set_append_right _ _ (by omega), ht, List.set_append_right _ _ (by omega)]
  simp [Nat.add_assoc]

theorem copyList_get_at (zs : List Val) (id : Nat) (L : List Val) (h : id + L.length < zs.length) :
    (copyList zs id L)[id + L.length]? = zs[id + L.length]? := by
  have ht : (zs.take id).length = id := by simp; omega
  unfold copyList
  rw [List.getElem?_append_right (by simp; omega)]
  simp [ht]

/-- The bytes copied after `k` steps: the source values `ysf (is + j)`, `j < k`. -/
def cpy (ysf : Nat → Int) (is k : Nat) : List Val := (List.range k).map fun j => .int (ysf (is + j))

theorem cpy_length (ysf : Nat → Int) (is k : Nat) : (cpy ysf is k).length = k := by simp [cpy]

theorem cpy_succ (ysf : Nat → Int) (is k : Nat) :
    cpy ysf is (k + 1) = cpy ysf is k ++ [.int (ysf (is + k))] := by
  simp [cpy, List.range_succ]

/-- What musl's `unsigned char` load reads from the character `ysf j`: its value modulo 256. -/
def wysf (ysf : Nat → Int) (j : Nat) : Int := wrap false 8 (ysf j)

/-- cirlean's `unsigned char` load (`loadTy`, as the executor unfolds it) of a character
`-128 ≤ x ≤ 255` reads `x` modulo 256, without a case split on the sign of `x`. -/
theorem load_u8 (x : Int) (h1 : -128 ≤ x) (h2 : x ≤ 255) :
    (if inRange false 8 x = true then (Res.ok (Val.int x) : Res Val)
      else if inRange true 8 x = true then Res.ok (Val.int (wrap false 8 x))
      else Res.ub "read of an indeterminate or ill-typed value") = Res.ok (Val.int (wrap false 8 x)) := by
  by_cases h : 0 ≤ x
  · have h3 : inRange false 8 x = true := by rw [inRange_eq_true_iff]; simp only [intMin_u, intMax_u8]; omega
    simp only [h3, ite_true]
    rw [wrap_of_bounds (by decide) (by simp only [intMin_u, intMax_u8]; omega)]
  · have h3 : inRange false 8 x = false := by rw [inRange_eq_false_iff]; simp only [intMin_u, intMax_u8]; omega
    have h4 : inRange true 8 x = true := by rw [inRange_eq_true_iff]; simp only [intMin_s8, intMax_s8]; omega
    simp only [h3, h4, Bool.false_eq_true, ite_false, ite_true]

theorem inRange_wrap_u8 (x : Int) : inRange false 8 (wrap false 8 x) = true := by
  rw [inRange_eq_true_iff]
  simp only [intMin_u, intMax_u8, wrap, Bool.false_and, Bool.false_eq_true, ite_false]
  have : (2 : Int) ^ 8 = 256 := by decide
  rw [this]
  omega

/-- The number of bytes musl's head loop copies: until `s` is 4-aligned in cirlean's pointer
encoding (`(is + h + 1) % 4 = 0`), at most `n`. -/
def hcount (is n : Nat) : Nat := min n ((4 - (is + 1) % 4) % 4)

/-- The runs without musl's word paths: after the head loop, fewer than 4 bytes are left if `d`
is 4-aligned, fewer than 32 otherwise. -/
def WordFree (is id n : Nat) : Prop :=
  if (id + hcount is n + 1) % 4 = 0 then n - hcount is n < 4 else n - hcount is n < 32

theorem hcount_eq {is n k : Nat} (hk : k ≤ n) (hal : ∀ k', k' < k → (is + k' + 1) % 4 ≠ 0)
    (hend : k = n ∨ (is + k + 1) % 4 = 0) : k = hcount is n := by
  unfold hcount
  rcases Nat.lt_or_ge k ((4 - (is + 1) % 4) % 4) with h | h
  · have : (is + k + 1) % 4 ≠ 0 := by omega
    rcases hend with h1 | h1
    · omega
    · exact absurd h1 this
  · rcases Nat.lt_or_ge ((4 - (is + 1) % 4) % 4) k with h2 | h2
    · exact absurd (by omega : (is + (4 - (is + 1) % 4) % 4 + 1) % 4 = 0) (hal _ h2)
    · omega

/-- What a state of `musl_memcpy`'s body keeps fixed: the source block, the caller's other blocks,
the locals `__retval`, `dest`, `src`, `w`, `x` (at `m.next`, `+1`, `+2`, `+6`, `+7`) and the block counter. -/
abbrev MFix (m : Mem) (bs bd is id : Nat) (ks : BlockKind) (tys : Ty) (ys : List Val) (sm : Mem) : Prop :=
  sm.blocks bs = some ⟨ks, true, tys, .arr ys⟩ ∧ m.next + 8 ≤ sm.next ∧
  (∀ b', b' < m.next → b' ≠ bd → sm.blocks b' = m.blocks b') ∧
  sm.blocks m.next = some ⟨.stack, true, Ty.void.ptr, .undef⟩ ∧
  sm.blocks (m.next + 1) = some ⟨.stack, true, Ty.void.ptr, .ptr (.loc bd [.idx id])⟩ ∧
  sm.blocks (m.next + 2) = some ⟨.stack, true, Ty.void.ptr, .ptr (.loc bs [.idx is])⟩ ∧
  sm.blocks (m.next + 6) = some ⟨.stack, true, .int false 32, .undef⟩ ∧
  sm.blocks (m.next + 7) = some ⟨.stack, true, .int false 32, .undef⟩

/-- The head loop's state after `k` bytes: `n - k` left, `d`, `s` at `id + k`, `is + k`, the
destination with `k` bytes copied. -/
abbrev MHead (n bs bd is id : Nat) (kd : BlockKind) (tyd : Ty) (zs : List Val) (ysf : Nat → Int) (m sm : Mem)
    (k : Nat) : Prop :=
  sm.blocks (m.next + 3) = some ⟨.stack, true, .int false 64, .int ((n : Int) - k)⟩ ∧
  sm.blocks (m.next + 4) = some ⟨.stack, true, (Ty.int false 8).ptr, .ptr (.loc bd [.idx (id + k)])⟩ ∧
  sm.blocks (m.next + 5) = some ⟨.stack, true, (Ty.int false 8).ptr, .ptr (.loc bs [.idx (is + k)])⟩ ∧
  sm.blocks bd = some ⟨kd, true, tyd, .arr (copyList zs id (cpy ysf is k))⟩

/-- The bits musl tests on a count below 32 (`n & 16`, ..., `n & 1` on `size_t`). -/
theorem bits_lt32 : ∀ c : Nat, c < 32 →
    bitwise false 64 (fun x1 x2 => x1 &&& x2) (c : Int) 16 = (if 16 ≤ c % 32 then 16 else 0) ∧
    bitwise false 64 (fun x1 x2 => x1 &&& x2) (c : Int) 8 = (if 8 ≤ c % 16 then 8 else 0) ∧
    bitwise false 64 (fun x1 x2 => x1 &&& x2) (c : Int) 4 = (if 4 ≤ c % 8 then 4 else 0) ∧
    bitwise false 64 (fun x1 x2 => x1 &&& x2) (c : Int) 2 = (if 2 ≤ c % 4 then 2 else 0) ∧
    bitwise false 64 (fun x1 x2 => x1 &&& x2) (c : Int) 1 = (if 1 ≤ c % 2 then 1 else 0) := by
  decide

theorem blk_cpy_eq {kd : BlockKind} {tyd : Ty} {zs : List Val} {id : Nat} {w : Nat → Int} {is a b : Nat}
    (h : a = b) :
    (some ⟨kd, true, tyd, .arr (copyList zs id (cpy w is a))⟩ : Option MemBlock) =
      some ⟨kd, true, tyd, .arr (copyList zs id (cpy w is b))⟩ := by
  subst h; rfl

open EquivLean.Cir.Tactic
open Lean Meta Elab Tactic Simp

theorem lt_ne_self {a b : Nat} (h : a < b) : a ≠ b := Nat.ne_of_lt h
theorem self_ne_lt {a b : Nat} (h : a < b) : b ≠ a := (Nat.ne_of_lt h).symm
theorem lt_ne_add {a b c : Nat} (h : a < b) : a ≠ b + c := by omega
theorem add_ne_lt {a b c : Nat} (h : a < b) : b + c ≠ a := by omega

partial def hasKeyUpd (F k : Expr) (fuel : Nat := 4) : Bool :=
  if fuel == 0 then false
  else if F.isAppOfArity ``CIR.upd 6 then
    if (F.getArg! 4).consumeMData == k then true
    else hasKeyUpd (F.getArg! 3) k (fuel - 1)
  else false

def keysNeCaller? (k k1 : Expr) : MetaM (Option Expr) := do
  if let some pf ← CIR.Tactic.keysNe? k k1 then return some pf
  let k := k.consumeMData
  let k1 := k1.consumeMData
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty := (← instantiateMVars d.type).consumeMData
    let some (_, _, a, b) := ty.app4? ``LT.lt | continue
    let a := a.consumeMData
    let b := b.consumeMData
    if k == a && k1 == b then
      return some (mkApp3 (mkConst ``lt_ne_self) a b (mkFVar d.fvarId))
    if k == b && k1 == a then
      return some (mkApp3 (mkConst ``self_ne_lt) a b (mkFVar d.fvarId))
    if k == a && k1.isAppOfArity ``HAdd.hAdd 6 && (k1.getArg! 4).consumeMData == b then
      return some (mkApp4 (mkConst ``lt_ne_add) a b (k1.getArg! 5) (mkFVar d.fvarId))
    if k1 == a && k.isAppOfArity ``HAdd.hAdd 6 && (k.getArg! 4).consumeMData == b then
      return some (mkApp4 (mkConst ``add_ne_lt) a b (k.getArg! 5) (mkFVar d.fvarId))
  return none

partial def dropShadowedCaller? (F k y : Expr) (fuel : Nat := 4) : MetaM (Option (Expr × Expr)) := do
  if fuel == 0 then return none
  let F ← instantiateMVars F
  unless F.isAppOfArity ``CIR.upd 6 do return none
  let G := F.getArg! 3
  let k1 := F.getArg! 4
  let v1 := F.getArg! 5
  if k1.consumeMData == k.consumeMData then
    return some (G, ← mkAppM ``CIR.upd_upd_same #[G, k, v1, y])
  let some hne ← keysNeCaller? k k1 | return none
  let some (G', pG) ← dropShadowedCaller? G k y (fuel - 1) | return none
  let fn := F.getAppFn
  let α := F.getArg! 0
  let β := F.getArg! 1
  let inst := F.getArg! 2
  let mk (f a b : Expr) := mkAppN fn #[α, β, inst, f, a, b]
  let p1 ← mkAppOptM ``CIR.upd_comm #[none, none, none, some G, some k, some k1, some v1, some y, some hne]
  let lam := Lean.mkLambda `g .default (← inferType G) (mk (.bvar 0) k1 v1)
  let p2 ← mkCongrArg lam pG
  let hne' ← mkAppM ``Ne.symm #[hne]
  let p3 ← mkAppOptM ``CIR.upd_comm #[none, none, none, some G', some k1, some k, some y, some v1, some hne']
  let G'' := mk G' k1 v1
  return some (G'', ← mkEqTrans p1 (← mkEqTrans p2 p3))

simproc_decl collapseUpdCaller (upd _ _ _) := fun e => do
  unless e.isAppOfArity ``CIR.upd 6 do return .continue
  unless (e.getArg! 0).isConstOf ``Nat do return .continue
  let F := e.getArg! 3
  let k := (e.getArg! 4).consumeMData
  unless hasKeyUpd F k 4 do return .continue
  let v := e.getArg! 5
  let some (F', pf) ← dropShadowedCaller? F k v 4 | return .continue
  return .done { expr := mkAppN e.getAppFn #[e.getArg! 0, e.getArg! 1, e.getArg! 2, F', e.getArg! 4, v], proof? := some pf }

theorem kr_eq_upd3 (m : Mem) (σ1m : Mem) (bs bd is id k : Nat) (kd : BlockKind) (esd : Bool) (tlend : Nat)
    (zs : List Val) (ysf : Nat → Int)
    (hbd : bd < m.next)
    (hsp : σ1m.blocks (m.next + 5) = some ⟨.stack, true, (Ty.int false 8).ptr, .ptr (.loc bs [.idx (is + k)])⟩)
    (hdp : σ1m.blocks (m.next + 4) = some ⟨.stack, true, (Ty.int false 8).ptr, .ptr (.loc bd [.idx (id + k)])⟩)
    (hbd1 : σ1m.blocks bd = some ⟨kd, true, (Ty.int esd 8).array tlend, .arr (copyList zs id (cpy (wysf ysf) is k))⟩) :
    killRange (m.next + 8) σ1m.next σ1m.blocks =
    upd (upd (upd (killRange (m.next + 8) σ1m.next σ1m.blocks)
      (m.next + 5) (some ⟨.stack, true, (Ty.int false 8).ptr, .ptr (.loc bs [.idx (is + k)])⟩))
      (m.next + 4) (some ⟨.stack, true, (Ty.int false 8).ptr, .ptr (.loc bd [.idx (id + k)])⟩))
      bd (some ⟨kd, true, (Ty.int esd 8).array tlend, .arr (copyList zs id (cpy (wysf ysf) is k))⟩) := by
  funext b
  by_cases h1 : b = bd
  · subst h1; simp (disch := omega) only [upd_apply_same, killRange_of_lt, hbd1]
  · by_cases h2 : b = m.next + 4
    · subst h2; simp (disch := omega) only [upd_apply_ne, upd_apply_same, killRange_of_lt, hdp]
    · by_cases h3 : b = m.next + 5
      · subst h3; simp (disch := omega) only [upd_apply_ne, upd_apply_same, killRange_of_lt, hsp]
      · simp (disch := omega) only [upd_apply_ne]

theorem upd3_congr (kr : Nat → Option MemBlock) (m : Mem) (bs bd is id : Nat) (kd : BlockKind) (esd : Bool) (tlend : Nat)
    (zs : List Val) (ysf : Nat → Int) (k1 k2 : Nat) (h : k1 = k2) :
    upd (upd (upd kr
      (m.next + 5) (some ⟨.stack, true, (Ty.int false 8).ptr, .ptr (.loc bs [.idx (is + k1)])⟩))
      (m.next + 4) (some ⟨.stack, true, (Ty.int false 8).ptr, .ptr (.loc bd [.idx (id + k1)])⟩))
      bd (some ⟨kd, true, (Ty.int esd 8).array tlend, .arr (copyList zs id (cpy (wysf ysf) is k1))⟩) =
    upd (upd (upd kr
      (m.next + 5) (some ⟨.stack, true, (Ty.int false 8).ptr, .ptr (.loc bs [.idx (is + k2)])⟩))
      (m.next + 4) (some ⟨.stack, true, (Ty.int false 8).ptr, .ptr (.loc bd [.idx (id + k2)])⟩))
      bd (some ⟨kd, true, (Ty.int esd 8).array tlend, .arr (copyList zs id (cpy (wysf ysf) is k2))⟩) := by
  subst h; rfl

elab "cir_merge_hk1" : tactic => do
  let [g1, g2] ← getGoals | throwError "cir_merge_hk1: expected 2 goals"
  let (hk1Ty, target) ← g1.withContext do
    let some d := (← getLCtx).findFromUserName? `hk1 | throwError "no hk1"
    return (← instantiateMVars d.type, ← instantiateMVars (← g1.getType))
  let mut gM := g1
  for n in [`cirA_br0, `cirH_br0, `cirA_br1, `cirH_br1, `cirA_br2, `cirH_br2, `cirA_br3, `cirH_br3, `cirA_br4, `cirH_br4] do
    let fv? ← gM.withContext do pure ((← getLCtx).findFromUserName? n |>.map (·.fvarId))
    if let some fv := fv? then gM ← gM.tryClear fv
  let hk1Fv1 ← g1.withContext do pure ((← getLCtx).findFromUserName? `hk1).get!.fvarId
  let hk1Fv2 ← g2.withContext do pure ((← getLCtx).findFromUserName? `hk1).get!.fvarId
  let gBase ← gM.tryClear hk1Fv1
  let fnTy ← gBase.withContext <| mkArrow hk1Ty target
  let mFn ← gBase.withContext <| mkFreshExprSyntheticOpaqueMVar fnTy
  g1.assign (mkApp mFn (mkFVar hk1Fv1))
  g2.assign (mkApp mFn (mkFVar hk1Fv2))
  let (_, gNew) ← mFn.mvarId!.intro `hk1
  replaceMainGoal [gNew]

theorem holds_with_cont {α : Type} {x : Res α} {k : α → Prop} {P : Prop}
    (h : x.holds k) (H : ∀ (K : α → Prop), k = K → x.holds K → P) : P :=
  H k rfl h

theorem holds_evalOp_scope_none_elim {ctx : Ctx} {r : Region} {σ : CIR.State}
    {Q : CIR.Step × CIR.State → Prop} (h : (evalOp ctx (.scope none r) σ).holds Q) :
    (evalRegion ctx r [] σ >>= fun x => match x with
      | (e, σ') => finishRegion e σ').holds Q := by
  unfold evalOp at h
  rw [Res.holds_bind] at h ⊢
  refine Res.holds_mono h (fun ⟨e, σ'⟩ h1 => ?_)
  cases e with
  | yield vs =>
    cases vs with
    | nil => exact h1
    | cons _ _ => exact False.elim h1
  | cond _ => exact h1
  | _ => exact h1

theorem holds_evalOp_ifOp_elim {ctx : Ctx} {c : VId} {tr er : Region} {σ : CIR.State}
    {Q : CIR.Step × CIR.State → Prop} (h : (evalOp ctx (.ifOp c tr er) σ).holds Q) :
    (do
      let b ← σ.getBool c
      let (e, σ') ← evalRegion ctx (if b then tr else er) [] σ
      finishRegion e σ').holds Q := by unfold evalOp at h; exact h

theorem holds_evalRegion_ite_true_elim {ctx : Ctx} {tr er : Region} {args : List Val} {σ : CIR.State}
    {Q : Exit × CIR.State → Prop}
    (h : (evalRegion ctx (if true = true then tr else er) args σ).holds Q) :
    (evalRegion ctx tr args σ).holds Q := h

theorem holds_evalRegion_ite_false_elim {ctx : Ctx} {tr er : Region} {args : List Val} {σ : CIR.State}
    {Q : Exit × CIR.State → Prop}
    (h : (evalRegion ctx (if false = true then tr else er) args σ).holds Q) :
    (evalRegion ctx er args σ).holds Q := h

theorem holds_evalRegion_ite_decide_pos_elim {ctx : Ctx} {p : Prop} {inst : Decidable p} {tr er : Region}
    {args : List Val} {σ : CIR.State} {Q : Exit × CIR.State → Prop}
    (h : (evalRegion ctx (if @decide p inst = true then tr else er) args σ).holds Q) (hp : p) :
    (evalRegion ctx tr args σ).holds Q := by
  rw [decide_eq_true hp] at h; exact h

theorem holds_evalRegion_ite_decide_neg_elim {ctx : Ctx} {p : Prop} {inst : Decidable p} {tr er : Region}
    {args : List Val} {σ : CIR.State} {Q : Exit × CIR.State → Prop}
    (h : (evalRegion ctx (if @decide p inst = true then tr else er) args σ).holds Q) (hp : ¬p) :
    (evalRegion ctx er args σ).holds Q := by
  rw [decide_eq_false hp] at h; exact h

theorem holds_evalRegion_ite_pos_elim {ctx : Ctx} {c : Prop} {inst : Decidable c} {tr er : Region}
    {args : List Val} {σ : CIR.State} {Q : Exit × CIR.State → Prop}
    (h : (evalRegion ctx (@ite _ c inst tr er) args σ).holds Q) (hc : c) :
    (evalRegion ctx tr args σ).holds Q := by
  cases inst with
  | isTrue _ => exact h
  | isFalse hn => exact absurd hc hn

theorem holds_evalRegion_ite_neg_elim {ctx : Ctx} {c : Prop} {inst : Decidable c} {tr er : Region}
    {args : List Val} {σ : CIR.State} {Q : Exit × CIR.State → Prop}
    (h : (evalRegion ctx (@ite _ c inst tr er) args σ).holds Q) (hc : ¬c) :
    (evalRegion ctx er args σ).holds Q := by
  cases inst with
  | isTrue hp => exact absurd hp hc
  | isFalse _ => exact h

theorem holds_finishRegion_endScope_same_elim {bs : Nat → Option MemBlock} {n : Nat}
    {env : VId → Option Val} {names : List (String × Nat)} {Q : CIR.Step × CIR.State → Prop}
    (h : (finishRegion (.yield []) ⟨⟨killRange n n bs, n⟩, env, names⟩).holds Q) :
    Q (CIR.Step.next, ⟨⟨bs, n⟩, env, names⟩) := by
  rw [killRange_self] at h; exact h

theorem holds_finishRegion_yield_nil_elim {σ : CIR.State} {Q : CIR.Step × CIR.State → Prop}
    (h : (finishRegion (.yield []) σ).holds Q) : Q (CIR.Step.next, σ) := h

theorem holds_evalBlock_zero_nil_elim {ctx : Ctx} {ops : List Op}
    {bs : List Block} {σ : CIR.State} {Q : Exit × CIR.State → Prop}
    (h : (evalBlock ctx (.mk [] ops :: bs) 0 [] σ).holds Q) :
    (do
      let (s, σ) ← evalOps ctx ops σ
      match s with
      | .exit (.goto l) =>
        match labelBlock? l (.mk [] ops :: bs) with
        | some j => evalBlock ctx (.mk [] ops :: bs) j [] σ
        | none => pure (.goto l, σ)
      | .exit e => pure (e, σ)
      | .jump j vs => evalBlock ctx (.mk [] ops :: bs) j vs σ
      | .next => .ub "fell off the end of a block").holds Q := by
  rw [evalBlock_zero] at h; exact h

partial def whnfHeadOnly (e : Expr) : MetaM Expr := do
  let e := e.consumeMData
  if e.isHeadBetaTarget then return ← whnfHeadOnly e.headBeta
  match e with
  | .proj _ _ s =>
    let s' ← whnfHeadOnly s
    let e1 := e.updateProj! s'
    if let some e2 ← reduceProj? e1 then return ← whnfHeadOnly e2
    return e1
  | .letE _ _ v b _ => return ← whnfHeadOnly (b.instantiate1 v)
  | .lam n ty b bi =>
    if b.hasLooseBVars then return e
    return .lam n ty (← whnfHeadOnly b) bi
  | .app _ _ =>
    let fn := e.getAppFn.consumeMData
    if let some c := fn.constName? then
      if c == ``CIR.Region.mk || c == ``CIR.Block.mk ||
         c == ``List.cons || c == ``List.nil || c == ``List.append || c == ``HAppend.hAppend ||
         c == ``CIR.upd || c == ``CIR.killRange ||
         c.getPrefix == ``CIR.Op || c.getPrefix == ``CIR.Ty || c.getPrefix == ``CIR.Val || c.getPrefix == ``CIR.Ptr then
        return e
      if c == ``CIR.evalOps && e.getAppNumArgs == 3 then
        let a := e.getAppArgs
        return mkAppN fn #[a[0]!, a[1]!, ← whnfHeadOnly a[2]!]
      if c == ``CIR.evalOp && e.getAppNumArgs == 3 then
        let a := e.getAppArgs
        return mkAppN fn #[a[0]!, a[1]!, ← whnfHeadOnly a[2]!]
      if c == ``CIR.evalRegion && e.getAppNumArgs == 4 then
        let a := e.getAppArgs
        return mkAppN fn #[a[0]!, ← whnfHeadOnly a[1]!, a[2]!, ← whnfHeadOnly a[3]!]
      if c == ``CIR.evalBlock && e.getAppNumArgs == 5 then
        let a := e.getAppArgs
        return mkAppN fn #[a[0]!, a[1]!, a[2]!, a[3]!, ← whnfHeadOnly a[4]!]
      if c == ``ite && e.getAppNumArgs == 5 then
        return e
      let args ← e.getAppArgs.mapM whnfHeadOnly
      let e1 := mkAppN fn args
      if ← Lean.Meta.isMatcher c then
        if let .reduced e2 ← Lean.Meta.reduceMatcher? e1 then
          return ← whnfHeadOnly e2
      if (c == ``Prod.fst || c == ``Prod.snd) && args.size == 3 && args[2]!.isAppOfArity ``Prod.mk 4 then
        return if c == ``Prod.fst then args[2]!.getArg! 2 else args[2]!.getArg! 3
      if (c == ``CIR.State.mem || c == ``CIR.State.env || c == ``CIR.State.names) && args.size == 1 && args[0]!.isAppOfArity ``CIR.State.mk 3 then
        let st := args[0]!
        return if c == ``CIR.State.mem then st.getArg! 0 else if c == ``CIR.State.env then st.getArg! 1 else st.getArg! 2
      if (c == ``CIR.Mem.blocks || c == ``CIR.Mem.next) && args.size == 1 && args[0]!.isAppOfArity ``CIR.Mem.mk 2 then
        let m := args[0]!
        return if c == ``CIR.Mem.blocks then m.getArg! 0 else m.getArg! 1
      if c == ``CIR.Exit.leaveMem && args.size == 3 && !args[0]!.isAppOf ``CIR.Exit.halt &&
          args[1]!.isAppOfArity ``CIR.Mem.mk 2 then
        let m := args[1]!
        let bs := m.getArg! 0
        let hi := m.getArg! 1
        let lo := args[2]!
        return mkApp2 (mkConst ``CIR.Mem.mk) (mkApp3 (mkConst ``CIR.killRange) lo hi bs) hi
      if c == ``CIR.Mem.endScope && args.size == 2 && args[0]!.isAppOfArity ``CIR.Mem.mk 2 then
        let m := args[0]!
        let bs := m.getArg! 0
        let hi := m.getArg! 1
        let lo := args[1]!
        return mkApp2 (mkConst ``CIR.Mem.mk) (mkApp3 (mkConst ``CIR.killRange) lo hi bs) hi
      if c == ``Prod.casesOn || c == ``CIR.Step.casesOn || c == ``CIR.Exit.casesOn then
        let e2 ← whnfCore e1
        if e2 != e1 then return ← whnfHeadOnly e2
      return e1
    return e
  | _ => return e

def hypBetaHeadOnly (h : Name) : TacticM Unit := do
  for g in ← getGoals do
    if ← g.isAssigned then continue
    g.withContext do
      let some d := (← getLCtx).findFromUserName? h | return
      let t ← instantiateMVars d.type
      let mut t' := t.consumeMData
      while t'.isHeadBetaTarget do t' := t'.headBeta.consumeMData
      if t'.isAppOfArity ``CIR.Res.holds 3 then
        let α := t'.getArg! 0
        let x' ← whnfHeadOnly (t'.getArg! 1)
        let k := t'.getArg! 2
        let t'' := mkAppN t'.getAppFn #[α, x', k]
        if t'' != t then
          replaceMainGoal [← g.replaceLocalDeclDefEq d.fvarId t'']
      else if t' != t then
        replaceMainGoal [← g.replaceLocalDeclDefEq d.fvarId t']

def hypHeadSimpFast (h : Name) (names : Array Name) : TacticM Unit := do
  let some (x, k) ← hypHolds? h | throwError "not holds"
  let hI := mkIdent h
  let usesIter := (x.find? fun e => e.isConst && CIR.Tactic.iterConsts.contains e.constName!).isSome
  let names := (if usesIter then names.push `cir_iter else names).push ``collapseUpdCaller
  let g ← getMainGoal
  let hKName ← mkFreshUserName `hK
  let g2 ← g.withContext do
    let d ← hypDecl h
    let t ← whnfR (← instantiateMVars d.type)
    let α := t.getArg! 0
    let hTy ← inferType k
    let pTy ← g.getType
    let body ← withLocalDeclD `K hTy fun kv => do
      let eqTy ← mkEq k kv
      let holdsTy := mkAppN t.getAppFn #[α, x, kv]
      mkForallFVars #[kv] (← mkArrow eqTy (← mkArrow holdsTy pTy))
    let g1 ← mkFreshExprMVar body
    let prf := mkAppN (mkConst ``holds_with_cont) #[α, x, k, pTy, mkFVar d.fvarId, g1]
    g.assign prf
    let g1 ← g1.mvarId!.tryClear d.fvarId
    let (_, g2) ← g1.introN 3 [← mkFreshUserName `K, hKName, h]
    return g2
  replaceMainGoal [g2]
  let fv? := (← hypDecl h).fvarId
  let hyps ← CIR.Tactic.cirHypsExcept (some fv?)
  let args ← CIR.Tactic.simpArgsLazy names hyps
  evalTactic (← `(tactic| simp (disch := cir_disch) only [$args,*] at $hI:ident))
  if (← getGoals).isEmpty then return
  let hKI := mkIdent hKName
  evalTactic (← `(tactic| subst $hKI:ident))
  hypBetaHeadOnly h

def hypStepFast (h : Name) : TacticM Unit := do
  hypBetaHeadOnly h
  let some (x, _) ← hypHolds? h | throwError "not holds"
  let hI := mkIdent h
  let some c := x.getAppFn.constName? | hypStepImpl h; return
  if c == ``CIR.Res.ok then
    evalTactic (← `(tactic| replace $hI:ident := EquivLean.Cir.holds_ok_elim $hI))
    hypBetaHeadOnly h
  else if c == ``Pure.pure then
    evalTactic (← `(tactic| replace $hI:ident := EquivLean.Cir.holds_pure_elim $hI))
    hypBetaHeadOnly h
  else if c == ``CIR.Res.ub then
    evalTactic (← `(tactic| exact EquivLean.Cir.holds_ub_elim $hI))
  else if c == ``CIR.Res.div then
    evalTactic (← `(tactic| exact EquivLean.Cir.holds_div_elim $hI))
  else if c == ``Bind.bind then
    evalTactic (← `(tactic| replace $hI:ident := EquivLean.Cir.holds_bind_elim $hI))
  else if c == ``CIR.evalOps then
    if ← tryTac (evalTactic (← `(tactic| replace $hI:ident := EquivLean.Cir.holds_evalOps_cons_elim $hI))) then
      return
    if ← tryTac (evalTactic (← `(tactic| replace $hI:ident := EquivLean.Cir.holds_evalOps_nil_elim $hI))) then
      hypBetaHeadOnly h; return
    hypHeadSimpFast h CIR.Tactic.execNames
  else if c == ``CIR.evalRegion then
    let r := (x.getArg! 1).consumeMData
    if r.isAppOfArity ``ite 5 then
      let cond := (r.getArg! 1).consumeMData
      if cond.isAppOfArity ``Eq 3 && (cond.getArg! 2).isConstOf ``Bool.true then
        if (cond.getArg! 1).isConstOf ``Bool.true then
          evalTactic (← `(tactic| replace $hI:ident := holds_evalRegion_ite_true_elim $hI))
          return
        if (cond.getArg! 1).isConstOf ``Bool.false then
          evalTactic (← `(tactic| replace $hI:ident := holds_evalRegion_ite_false_elim $hI))
          return
        if (cond.getArg! 1).isAppOfArity ``Decidable.decide 2 then
          let p := (cond.getArg! 1).getArg! 0
          splitOn p
          evalTactic (← `(tactic| case' pos => replace $hI:ident := holds_evalRegion_ite_decide_pos_elim $hI ‹_›))
          evalTactic (← `(tactic| case' neg => replace $hI:ident := holds_evalRegion_ite_decide_neg_elim $hI ‹_›))
          return
      splitOn cond
      evalTactic (← `(tactic| case' pos => replace $hI:ident := holds_evalRegion_ite_pos_elim $hI ‹_›))
      evalTactic (← `(tactic| case' neg => replace $hI:ident := holds_evalRegion_ite_neg_elim $hI ‹_›))
      return
    if ← tryTac (evalTactic (← `(tactic| replace $hI:ident := EquivLean.Cir.holds_evalRegion_cons_elim $hI))) then
      return
    evalTactic (← `(tactic| replace $hI:ident := EquivLean.Cir.holds_evalRegion_nil_elim $hI))
    hypBetaHeadOnly h
  else if c == ``CIR.finishRegion then
    let st := (x.getArg! 1).consumeMData
    if st.isAppOfArity ``CIR.State.mk 3 then
      let m := (st.getArg! 0).consumeMData
      if m.isAppOfArity ``CIR.Mem.mk 2 then
        let kr := (m.getArg! 0).consumeMData
        if kr.isAppOfArity ``CIR.killRange 3 && (kr.getArg! 0).consumeMData == (kr.getArg! 1).consumeMData then
          if ← tryTac (evalTactic (← `(tactic| replace $hI:ident := holds_finishRegion_endScope_same_elim $hI))) then
            hypBetaHeadOnly h; return
    if ← tryTac (evalTactic (← `(tactic| replace $hI:ident := holds_finishRegion_yield_nil_elim $hI))) then
      hypBetaHeadOnly h; return
    hypHeadSimpFast h CIR.Tactic.execNames
  else if c == ``CIR.evalOp then
    if ← tryTac (evalTactic (← `(tactic| replace $hI:ident := holds_evalOp_scope_none_elim $hI))) then
      return
    if ← tryTac (evalTactic (← `(tactic| replace $hI:ident := holds_evalOp_ifOp_elim $hI))) then
      return
    if ← tryTac (hypHeadSimpFast h CIR.Tactic.execNames) then return
    if ← tryTac (hypHeadSimpFast h CIR.Tactic.fallbackNames) then return
    hypStepImpl h
  else if c == ``CIR.evalBlock then
    if ← tryTac (evalTactic (← `(tactic| replace $hI:ident := holds_evalBlock_zero_nil_elim $hI))) then
      return
    if ← tryTac (evalTactic (← `(tactic| replace $hI:ident := EquivLean.Cir.holds_evalBlock_zero_elim $hI))) then
      return
    hypHeadSimpFast h #[``CIR.evalBlock.eq_1, ``List.getElem?_cons_succ, ``List.getElem?_cons_zero]
  else if c == ``ite then
    if ← tryTac (hypHeadSimpFast h CIR.Tactic.execNames) then return
    splitOn (x.getArg! 1)
    evalTactic (← `(tactic| case' pos => replace $hI:ident := EquivLean.Cir.holds_ite_pos_elim $hI ‹_›))
    evalTactic (← `(tactic| case' neg => replace $hI:ident := EquivLean.Cir.holds_ite_neg_elim $hI ‹_›))
    hypBetaHeadOnly h
  else
    hypStepImpl h

elab "cir_hrun_fast " h:ident : tactic => do
  let mut work := (← getGoals)
  let mut done : Array MVarId := #[]
  let mut fuel := (← getOptions).get `cir.fuel (100000 : Nat)
  while !work.isEmpty && fuel > 0 do
    fuel := fuel - 1
    let g := work.head!
    work := work.tail!
    if ← g.isAssigned then continue
    setGoals [g]
    hypBetaHeadOnly h.getId
    let some (x, _) ← hypHolds? h.getId |
      if ← tryTac (hypExists h.getId) then work := (← getGoals) ++ work
      else done := done.push g
      continue
    if x.isAppOf ``CIR.evalFor || x.isAppOf ``CIR.evalWhile || x.isAppOf ``CIR.evalDo ||
        x.isAppOf ``CIR.evalCall then
      done := done.push g; continue
    let s ← saveState
    let ok ← tryCatchRuntimeEx (do
        Lean.Core.withCurrHeartbeats (hypStepFast h.getId)
        pure true)
      fun e => do
        s.restore
        if e.isRuntime then
          logWarning m!"cir_hrun_fast: a step exceeded a resource limit: {e.toMessageData}"
        pure false
    if ok then work := (← getGoals) ++ work
    else done := done.push g
  setGoals (done.toList ++ work)

partial def scopeListLen? (e : Expr) : MetaM (Option Nat) := do
  let e ← whnfD e.consumeMData
  if e.isAppOfArity ``List.nil 1 then return some 0
  if e.isAppOfArity ``List.cons 3 then
    let some n ← scopeListLen? (e.getArg! 2) | return none
    return some (n + 1)
  return none

def isScopeOpsLen (x : Expr) (targetLen : Nat) : MetaM Bool := do
  unless x.isAppOfArity ``CIR.evalOps 3 do return false
  let ops ← whnfD (x.getArg! 1).consumeMData
  unless ops.isAppOfArity ``List.cons 3 do return false
  let hd := (ops.getArg! 1).consumeMData
  unless hd.isAppOf ``CIR.Op.scope do return false
  let some l ← scopeListLen? ops | return false
  return l == targetLen

elab "cir_hrun_to_scope " n:num h:ident : tactic => do
  let targetLen := n.getNat
  let mut work := (← getGoals)
  let mut done : Array MVarId := #[]
  let mut fuel := (← getOptions).get `cir.fuel (100000 : Nat)
  while !work.isEmpty && fuel > 0 do
    fuel := fuel - 1
    let g := work.head!
    work := work.tail!
    if ← g.isAssigned then continue
    setGoals [g]
    hypBetaHeadOnly h.getId
    let some (x, _) ← hypHolds? h.getId |
      if ← tryTac (hypExists h.getId) then work := (← getGoals) ++ work
      else done := done.push g
      continue
    if x.isAppOf ``CIR.evalFor || x.isAppOf ``CIR.evalWhile || x.isAppOf ``CIR.evalDo ||
        x.isAppOf ``CIR.evalCall then
      done := done.push g; continue
    if ← g.withContext (isScopeOpsLen x targetLen) then
      done := done.push g; continue
    let s ← saveState
    let ok ← tryCatchRuntimeEx (do
        Lean.Core.withCurrHeartbeats (hypStepFast h.getId)
        pure true)
      fun e => do
        s.restore
        if e.isRuntime then
          logWarning m!"cir_hrun_to_scope: a step exceeded a resource limit: {e.toMessageData}"
        pure false
    if ok then work := (← getGoals) ++ work
    else done := done.push g
  setGoals (done.toList ++ work)

theorem wrap32_wrap64_tmod4 (a : Int) :
    (wrap false 32 (wrap false 64 a)).tmod 4 = (wrap false 64 a).tmod 4 := by
  unfold wrap
  simp only [Bool.false_and, Bool.false_eq_true, ite_false]
  have h1 : 0 ≤ (a % (2 : Int) ^ 64) % (2 : Int) ^ 32 := Int.emod_nonneg _ (by decide)
  have h2 : 0 ≤ a % (2 : Int) ^ 64 := Int.emod_nonneg _ (by decide)
  rw [Int.tmod_eq_emod_of_nonneg h1, Int.tmod_eq_emod_of_nonneg h2,
    Int.emod_emod_of_dvd _ (by decide : (4 : Int) ∣ 2 ^ 32)]

theorem wrap64_tmod4_range (a : Int) :
    0 ≤ (wrap false 64 a).tmod 4 ∧ (wrap false 64 a).tmod 4 < 4 := by
  unfold wrap
  simp only [Bool.false_and, Bool.false_eq_true, ite_false]
  have h1 : 0 ≤ a % (2 : Int) ^ 64 := Int.emod_nonneg _ (by decide)
  rw [Int.tmod_eq_emod_of_nonneg h1]
  exact ⟨Int.emod_nonneg _ (by decide), Int.emod_lt_of_pos _ (by decide)⟩

set_option maxHeartbeats 2000000000 in
/-- musl's `memcpy` off its word paths (`WordFree`): `n` elements from element `is` of the array
block `bs` to element `id` of the array block `bd`, in another block, where every source element
is a `char` value `ysf j`. If musl returns, it returns `dest`, the destination holds the source
characters modulo 256 from `id` on, and the caller's other blocks are unchanged. -/
theorem musl_memcpy_pspec (ysf : Nat → Int) (ys zs : List Val) (bs bd is id n : Nat) (ks kd : BlockKind)
    (tys tyd : Ty) (m : Mem)
    (hs : m.blocks bs = some ⟨ks, true, tys, .arr ys⟩)
    (hd : m.blocks bd = some ⟨kd, true, tyd, .arr zs⟩)
    (htys : ∃ es tlen, tys = .array (.int es 8) tlen) (htyd : ∃ es tlen, tyd = .array (.int es 8) tlen)
    (hkd : kd ≠ .readonly)
    (hbs : bs < m.next) (hbd : bd < m.next) (hsd : bs ≠ bd)
    (hns : is + n ≤ ys.length) (hnd : id + n ≤ zs.length) (hlend : zs.length < 2 ^ 62)
    (hlens : ys.length < 2 ^ 62)
    (hys : ∀ j, is ≤ j → j < is + n → ys[j]? = some (.int (ysf j)))
    (hyr : ∀ j, is ≤ j → j < is + n → -128 ≤ ysf j ∧ ysf j ≤ 255)
    (_hfree : WordFree is id n) :
    pholds (evalCall ctx "musl_memcpy" [.ptr (.loc bd [.idx id]), .ptr (.loc bs [.idx is]), .int n] m)
      (fun r => r.1 = .ret (some (.ptr (.loc bd [.idx id]))) ∧
        r.2.blocks bd = some ⟨kd, true, tyd, .arr (copyList zs id (cpy (wysf ysf) is n))⟩ ∧
        (∀ b', b' < m.next → b' ≠ bd → r.2.blocks b' = m.blocks b') ∧ m.next ≤ r.2.next) := by
  obtain ⟨ess, tlens, cirH_tys⟩ := htys
  obtain ⟨esd, tlend, cirH_tyd⟩ := htyd
  intro r hr
  have hs0 := holds_of_eq_ok hr
  have cirH_sd : bs ≠ bd := hsd
  have cirH_kd := hkd
  have cirH_t1 : ∀ k : Nat, ((k : Int) + 1).toNat = k + 1 := fun k => by omega
  have cirH_y : ∀ j, is ≤ j → j < is + n → ys[j]? = some (.int (ysf j)) := hys
  have cirH_yg : ∀ (j : Nat) (h : j < ys.length), is ≤ j → j < is + n → ys[j] = .int (ysf j) := fun j h h1 h2 => by
    have := hys j h1 h2; rw [List.getElem?_eq_getElem h] at this; exact Option.some.inj this
  -- the `unsigned char` loads of the source and the stores of their values
  have cirH_ld : ∀ j, is ≤ j → j < is + n →
      (if inRange false 8 (ysf j) = true then (Res.ok (Val.int (ysf j)) : Res Val)
        else if inRange true 8 (ysf j) = true then Res.ok (Val.int (wrap false 8 (ysf j)))
        else Res.ub "read of an indeterminate or ill-typed value") = Res.ok (Val.int (wysf ysf j)) :=
    fun j h1 h2 => load_u8 (ysf j) (hyr j h1 h2).1 (hyr j h1 h2).2
  have cirH_inw : ∀ j, inRange false 8 (wysf ysf j) = true := fun j => inRange_wrap_u8 (ysf j)
  have cirH_cpl : ∀ k, k ≤ n → (copyList zs id (cpy (wysf ysf) is k)).length = zs.length := fun k hk =>
    copyList_length zs id _ (by rw [cpy_length]; omega)
  have cirH_cpg : ∀ (k : Nat) (hk : k < n),
      (copyList zs id (cpy (wysf ysf) is k))[id + k]? = some (zs[id + k]'(by omega)) := by
    intro k hk
    have h1 := copyList_get_at zs id (cpy (wysf ysf) is k) (by rw [cpy_length]; omega)
    rw [cpy_length] at h1
    rw [h1, List.getElem?_eq_getElem]
  have cirH_cps : ∀ (k : Nat), k < n →
      (copyList zs id (cpy (wysf ysf) is k)).set (id + k) (.int (wysf ysf (is + k))) =
        copyList zs id (cpy (wysf ysf) is (k + 1)) := by
    intro k hk
    rw [cpy_succ, ← copyList_set zs id _ _ (by rw [cpy_length]; omega), cpy_length]
  cir_hstep hs0
  cir_hrun_c hs0
  obtain ⟨s0, hs00, hs0⟩ := holds_for_name hs0
  -- the head loop: `for (; (uintptr_t)s % 4 && n; n--) *d++ = *s++;`
  refine (fun hw => ?main1) (holds_for_inv hs0
    (fun σ => σ.env = s0.env ∧ σ.names = s0.names ∧ MFix m bs bd is id ks tys ys σ.mem ∧
      ∃ k, MHead n bs bd is id kd tyd zs (wysf ysf) m σ.mem k ∧ k ≤ n)
    (fun a => a.1 = .next ∧ a.2.env = s0.env ∧ a.2.names = s0.names ∧ MFix m bs bd is id ks tys ys a.2.mem ∧
      ∃ k, MHead n bs bd is id kd tyd zs (wysf ysf) m a.2.mem k ∧ k ≤ n)
    ?init1 ?step1)
  case init1 =>
    subst hs00
    refine ⟨rfl, rfl, ⟨?_, by dsimp only; omega, fun b' hb' hb'' => ?_, ?_, ?_, ?_, ?_, ?_⟩, 0,
      ⟨?_, ?_, ?_, ?_⟩, Nat.zero_le _⟩
    all_goals (simp (disch := omega) only [upd_apply_ne, upd_apply_same, hs, hd, Nat.add_zero, copyList_nil, cpy,
      List.range_zero, List.map_nil]) <;> simp
  case step1 =>
    intro σ ⟨cirH_env, cirH_names, ⟨cirH_bs, cirH_nx, cirH_old, cirH_rv, cirH_de, cirH_sr, cirH_w, cirH_x⟩, k,
      ⟨cirH_n, cirH_dp, cirH_sp, cirH_bd⟩, hkn⟩ r2 hr2
    have hs2 := holds_of_eq_ok hr2
    subst hs00
    dsimp only at cirH_env cirH_names
    unfold forIter at hs2
    by_cases hk : k < n
    · have cirH_nk1 : ((n : Int) - (k : Int) != 0) = true := by simp; omega
      cir_hrun_c hs2
      all_goals (try subst hs2)
      all_goals first
        | -- `s` is 4-aligned: the loop ends
          exact ⟨rfl, rfl, rfl, ⟨cirH_bs, cirH_nx, cirH_old, cirH_rv, cirH_de, cirH_sr, cirH_w, cirH_x⟩, k,
            ⟨cirH_n, cirH_dp, cirH_sp, cirH_bd⟩, hkn⟩
        | -- a byte: `*d++ = *s++; n--`
          refine ⟨rfl, rfl, ⟨?_, ?_, fun b' hb' hb'' => ?_, ?_, ?_, ?_, ?_, ?_⟩, k + 1, ⟨?nslot, ?_, ?_, ?_⟩,
            by omega⟩
          case nslot =>
            rw [show ((n : Int) - ((k + 1 : Nat) : Int)) = (n : Int) - k - 1 by omega]
            simp (disch := omega) only [Mem.endScope, killRange_of_lt, killRange_self, upd_apply_ne, upd_apply_same]
          all_goals first
            | (dsimp only [Mem.endScope]; omega)
            | simp (disch := omega) only [Mem.endScope, killRange_of_lt, killRange_self, upd_apply_ne, upd_apply_same,
                cirH_bs, cirH_old, cirH_rv, cirH_de, cirH_sr, cirH_w, cirH_x, cirH_cps k hk, cirH_tys, cirH_tyd]
    · have cirH_nk0 : ((n : Int) - (k : Int) != 0) = false := by
        have : k = n := by omega
        subst this; simp
      cir_hrun_c hs2
      all_goals (try subst hs2)
      all_goals first
        | exact ⟨rfl, rfl, rfl, ⟨cirH_bs, cirH_nx, cirH_old, cirH_rv, cirH_de, cirH_sr, cirH_w, cirH_x⟩, k,
            ⟨cirH_n, cirH_dp, cirH_sp, cirH_bd⟩, hkn⟩
  case main1 =>
    obtain ⟨⟨st1, σ1⟩, ⟨hst1, cirH_env1, cirH_names1, ⟨cirH_bs1, cirH_nx1, cirH_old1, cirH_rv1, cirH_de1, cirH_sr1,
      cirH_w1, cirH_x1⟩, k, ⟨cirH_n1, cirH_dp1, cirH_sp1, cirH_bd1⟩, hkn⟩, hk1⟩ := hw
    subst hs00
    try dsimp only at hst1 cirH_env1 cirH_names1 cirH_bs1 cirH_nx1 cirH_old1 cirH_rv1 cirH_de1
    try dsimp only at cirH_sr1 cirH_w1 cirH_x1 cirH_n1 cirH_dp1 cirH_sp1 cirH_bd1
    subst hst1
    have hnk : (n : Int) - (k : Int) = ((n - k : Nat) : Int) := by omega
    have cirH_ne16 : ((16 : Int) != 0) = true := by decide
    have cirH_ne8 : ((8 : Int) != 0) = true := by decide
    have cirH_ne4 : ((4 : Int) != 0) = true := by decide
    have cirH_ne2 : ((2 : Int) != 0) = true := by decide
    have cirH_ne1 : ((1 : Int) != 0) = true := by decide
    have cirH_ne0 : ((0 : Int) != 0) = false := by decide
    by_cases cirH_ald : (wrap false 64 (addrOfChar bd (id + k))).tmod 4 = 0
    · -- `d` is 4-aligned
      by_cases hc4 : n - k < 4
      · obtain ⟨hb16, hb8, hb4, hb2, hb1⟩ := bits_lt32 (n - k) (by omega)
        -- fewer than 4 bytes left: `n >= 16`, `n & 8`, `n & 4` fail, the executor splits on `n & 2`, `n & 1`
        have cirH_lt16 : ¬ ((16 : Int) ≤ (n : Int) - (k : Int)) := by omega
        have cirH_bw8 : bitwise false 64 (fun x1 x2 => x1 &&& x2) ((n : Int) - (k : Int)) 8 = 0 := by
          rw [hnk, hb8]; simp only [show ¬ 8 ≤ (n - k) % 16 by omega, ↓reduceIte]
        have cirH_bw4 : bitwise false 64 (fun x1 x2 => x1 &&& x2) ((n : Int) - (k : Int)) 4 = 0 := by
          rw [hnk, hb4]; simp only [show ¬ 4 ≤ (n - k) % 8 by omega, ↓reduceIte]
        have cirH_bw2 : (bitwise false 64 (fun x1 x2 => x1 &&& x2) ((n : Int) - (k : Int)) 2 != 0) =
            decide (2 ≤ (n - k) % 4) := by
          rw [hnk, hb2]; by_cases h : 2 ≤ (n - k) % 4 <;> simp [h]
        have cirH_bw1 : (bitwise false 64 (fun x1 x2 => x1 &&& x2) ((n : Int) - (k : Int)) 1 != 0) =
            decide (1 ≤ (n - k) % 2) := by
          rw [hnk, hb1]; by_cases h : 1 ≤ (n - k) % 2 <;> simp [h]
        cir_hrun_c hk1
        -- `for (; n >= 16; ...)` ends at once
        rw [evalFor_unfold] at hk1
        cir_hrun_c hk1
        all_goals first
          | (exfalso; omega)
          | (subst hk1
             refine ⟨rfl, ?_, fun b' hb' hne => ?_, by dsimp only [Mem.endScope]; omega⟩
             · simp (disch := omega) only [Mem.endScope, killRange_of_lt, killRange_self, upd_apply_ne,
                 upd_apply_same, cirH_bd1, cirH_tyd]
               exact blk_cpy_eq (by omega)
             · simp (disch := omega) only [Mem.endScope, killRange_of_lt, killRange_self, upd_apply_ne, cirH_old1])
      · -- `n - k ≥ 4`: a word copy runs (`n >= 16`, `n & 8`, or `n & 4`), which is UB on a `char` array
        by_cases hc16 : 16 ≤ n - k
        · have cirH_ge16 : (16 : Int) ≤ (n : Int) - (k : Int) := by omega
          cir_hrun_c hk1
          rw [evalFor_unfold] at hk1
          cir_hrun_c hk1
        · have cirH_lt16 : ¬ ((16 : Int) ≤ (n : Int) - (k : Int)) := by omega
          obtain ⟨_, hb8, hb4, _, _⟩ := bits_lt32 (n - k) (by omega)
          by_cases hc8 : 8 ≤ n - k
          · have cirH_bw8 : bitwise false 64 (fun x1 x2 => x1 &&& x2) ((n : Int) - (k : Int)) 8 = 8 := by
              rw [hnk, hb8]; simp only [show 8 ≤ (n - k) % 16 by omega, ↓reduceIte]
            cir_hrun_c hk1
            rw [evalFor_unfold] at hk1
            cir_hrun_c hk1
          · have cirH_bw8 : bitwise false 64 (fun x1 x2 => x1 &&& x2) ((n : Int) - (k : Int)) 8 = 0 := by
              rw [hnk, hb8]; simp only [show ¬ 8 ≤ (n - k) % 16 by omega, ↓reduceIte]
            have cirH_bw4 : bitwise false 64 (fun x1 x2 => x1 &&& x2) ((n : Int) - (k : Int)) 4 = 4 := by
              rw [hnk, hb4]; simp only [show 4 ≤ (n - k) % 8 by omega, ↓reduceIte]
            cir_hrun_c hk1
            rw [evalFor_unfold] at hk1
            cir_hrun_c hk1
    · -- `d` is not 4-aligned
      by_cases hc32 : n - k < 32
      · obtain ⟨hb16, hb8, hb4, hb2, hb1⟩ := bits_lt32 (n - k) hc32
        -- fewer than 32 bytes left: `n >= 32` fails, the executor splits on `n & 16`, ..., `n & 1`
        have cirH_lt32 : ¬ ((32 : Int) ≤ (n : Int) - (k : Int)) := by omega
        have cirH_bw16 : (bitwise false 64 (fun x1 x2 => x1 &&& x2) ((n : Int) - (k : Int)) 16 != 0) =
            decide (16 ≤ (n - k) % 32) := by
          rw [hnk, hb16]; by_cases h : 16 ≤ (n - k) % 32 <;> simp [h]
        have cirH_bw8 : (bitwise false 64 (fun x1 x2 => x1 &&& x2) ((n : Int) - (k : Int)) 8 != 0) =
            decide (8 ≤ (n - k) % 16) := by
          rw [hnk, hb8]; by_cases h : 8 ≤ (n - k) % 16 <;> simp [h]
        have cirH_bw4 : (bitwise false 64 (fun x1 x2 => x1 &&& x2) ((n : Int) - (k : Int)) 4 != 0) =
            decide (4 ≤ (n - k) % 8) := by
          rw [hnk, hb4]; by_cases h : 4 ≤ (n - k) % 8 <;> simp [h]
        have cirH_bw2 : (bitwise false 64 (fun x1 x2 => x1 &&& x2) ((n : Int) - (k : Int)) 2 != 0) =
            decide (2 ≤ (n - k) % 4) := by
          rw [hnk, hb2]; by_cases h : 2 ≤ (n - k) % 4 <;> simp [h]
        have cirH_bw1 : (bitwise false 64 (fun x1 x2 => x1 &&& x2) ((n : Int) - (k : Int)) 1 != 0) =
            decide (1 ≤ (n - k) % 2) := by
          rw [hnk, hb1]; by_cases h : 1 ≤ (n - k) % 2 <;> simp [h]
        cir_hrun_to_scope 9 hk1
        rw [kr_eq_upd3 m σ1.mem bs bd is id k kd esd tlend zs ysf hbd cirH_sp1 cirH_dp1 (cirH_tyd ▸ cirH_bd1)] at hk1
        let k16 : Nat := k + if 16 ≤ (n - k) % 32 then 16 else 0
        have hk16_def : k16 = k + if 16 ≤ (n - k) % 32 then 16 else 0 := rfl
        have hk16_rem : k ≤ k16 ∧ k16 + (n - k) % 16 = n := by rw [hk16_def]; split <;> omega
        cir_hrun_to_scope 8 hk1
        all_goals try rw [upd3_congr _ m bs bd is id kd esd tlend zs ysf k k16 (by rw [hk16_def]; simp [cirH_br0])] at hk1
        all_goals try rw [upd3_congr _ m bs bd is id kd esd tlend zs ysf (k + 16) k16 (by rw [hk16_def]; simp [cirH_br0])] at hk1
        cir_merge_hk1
        let k8 : Nat := k16 + if 8 ≤ (n - k) % 16 then 8 else 0
        have hk8_def : k8 = k16 + if 8 ≤ (n - k) % 16 then 8 else 0 := rfl
        have hk8_rem : k16 ≤ k8 ∧ k8 + (n - k) % 8 = n := by rw [hk8_def]; split <;> omega
        cir_hrun_to_scope 7 hk1
        all_goals try rw [upd3_congr _ m bs bd is id kd esd tlend zs ysf k16 k8 (by rw [hk8_def]; simp [cirH_br0])] at hk1
        all_goals try rw [upd3_congr _ m bs bd is id kd esd tlend zs ysf (k16 + 8) k8 (by rw [hk8_def]; simp [cirH_br0])] at hk1
        cir_merge_hk1
        let k4 : Nat := k8 + if 4 ≤ (n - k) % 8 then 4 else 0
        have hk4_def : k4 = k8 + if 4 ≤ (n - k) % 8 then 4 else 0 := rfl
        have hk4_rem : k8 ≤ k4 ∧ k4 + (n - k) % 4 = n := by rw [hk4_def]; split <;> omega
        cir_hrun_to_scope 6 hk1
        all_goals try rw [upd3_congr _ m bs bd is id kd esd tlend zs ysf k8 k4 (by rw [hk4_def]; simp [cirH_br0])] at hk1
        all_goals try rw [upd3_congr _ m bs bd is id kd esd tlend zs ysf (k8 + 4) k4 (by rw [hk4_def]; simp [cirH_br0])] at hk1
        cir_merge_hk1
        let k2 : Nat := k4 + if 2 ≤ (n - k) % 4 then 2 else 0
        have hk2_def : k2 = k4 + if 2 ≤ (n - k) % 4 then 2 else 0 := rfl
        have hk2_rem : k4 ≤ k2 ∧ k2 + (n - k) % 2 = n := by rw [hk2_def]; split <;> omega
        cir_hrun_to_scope 5 hk1
        all_goals try rw [upd3_congr _ m bs bd is id kd esd tlend zs ysf k4 k2 (by rw [hk2_def]; simp [cirH_br0])] at hk1
        all_goals try rw [upd3_congr _ m bs bd is id kd esd tlend zs ysf (k4 + 2) k2 (by rw [hk2_def]; simp [cirH_br0])] at hk1
        cir_merge_hk1
        cir_hrun_fast hk1
        all_goals first
          | (exfalso; omega)
          | (subst hk1
             refine ⟨rfl, ?_, fun b' hb' hne => ?_, by dsimp only [Mem.endScope]; omega⟩
             · simp (disch := omega) only [Mem.endScope, killRange_of_lt, killRange_self, upd_apply_ne,
                 upd_apply_same, cirH_bd1, cirH_tyd]
               exact blk_cpy_eq (by omega)
             · simp (disch := omega) only [Mem.endScope, killRange_of_lt, killRange_self, upd_apply_ne, cirH_old1])
      · -- `n - k ≥ 32`: `switch ((u32)(uintptr_t)d % 4)` runs `w = *(u32 *)s`, which is UB on a `char` array
        have cirH_ge32 : (32 : Int) ≤ (n : Int) - (k : Int) := by omega
        have hmod := wrap64_tmod4_range (addrOfChar bd (id + k))
        have hcases : (wrap false 64 (addrOfChar bd (id + k))).tmod 4 = 1 ∨
            (wrap false 64 (addrOfChar bd (id + k))).tmod 4 = 2 ∨
            (wrap false 64 (addrOfChar bd (id + k))).tmod 4 = 3 := by omega
        rcases hcases with cirH_sw | cirH_sw | cirH_sw
        all_goals
          have cirH_sw32 := (wrap32_wrap64_tmod4 (addrOfChar bd (id + k))).trans cirH_sw
          cir_hrun_c hk1

end EquivLean.Demo.Cir.Musl
