import CIR
import EquivLean.Bridge.Cir.Tactic

namespace EquivLean.Cir
open CIR

set_option maxHeartbeats 40000000
set_option maxRecDepth 100000

/-! ### Record and Vtable Congruence -/

theorem find?_rec_cons_congr {name : String} (r : RecordDecl) (rs₁ rs₂ : List RecordDecl)
    (h : List.find? (·.name == name) rs₁ = List.find? (·.name == name) rs₂) :
    List.find? (·.name == name) (r :: rs₁) = List.find? (·.name == name) (r :: rs₂) := by
  simp only [List.find?]
  cases (r.name == name) <;> first | exact h | rfl

open Lean Meta Elab Tactic in
elab "cir_prove_record_eq_fast" : tactic => withTheReader Core.Context (fun c => { c with maxRecDepth := 100000 }) do
  evalTactic (← `(tactic| intro $(mkIdent `name):ident))
  let g ← getMainGoal
  let some (_, lhs, rhs) := (← g.withContext do instantiateMVars (← g.getType)).eq?
    | throwError "cir_prove_record_eq_fast: not an equation"
  let ctx1 := lhs.getArg! 0
  let ctx2 := rhs.getArg! 0
  let M1 ← mkAppM ``CIR.Ctx.mod #[ctx1]
  let M2 ← mkAppM ``CIR.Ctx.mod #[ctx2]
  let rs1 ← mkAppM ``CIR.Module.records #[M1]
  let rs2 ← mkAppM ``CIR.Module.records #[M2]
  let some elems1 ← CIR.Tactic.listElems rs1 | throwError "records 1 not a list"
  let some elems2 ← CIR.Tactic.listElems rs2 | throwError "records 2 not a list"
  let names1 ← elems1.mapM fun e => do
    let some k ← CIR.Tactic.strLit? (← mkAppM ``CIR.RecordDecl.name #[e]) | throwError "not str"
    return k
  let names2 ← elems2.mapM fun e => do
    let some k ← CIR.Tactic.strLit? (← mkAppM ``CIR.RecordDecl.name #[e]) | throwError "not str"
    return k
  if names1 == names2 then
    evalTactic (← `(tactic| rfl))
    return
  let s1 : Array String := names1
  let s2 : Array String := names2
  let mut i1 := 0
  let mut i2 := 0
  let mut diffNames : Array String := #[]
  let mut steps : Array Nat := #[]
  while i1 < s1.size || i2 < s2.size do
    if s1.extract i1 s1.size == s2.extract i2 s2.size then
      steps := steps.push 3
      break
    if i1 < s1.size && diffNames.contains s1[i1]! then
      steps := steps.push 1
      i1 := i1 + 1
    else if i2 < s2.size && diffNames.contains s2[i2]! then
      steps := steps.push 2
      i2 := i2 + 1
    else if i1 < s1.size && i2 < s2.size && s1[i1]! == s2[i2]! then
      steps := steps.push 0
      i1 := i1 + 1
      i2 := i2 + 1
    else if i1 < s1.size && (i2 >= s2.size || !(s1.extract i1 s1.size).contains s2[i2]! ||
        ((s2.extract i2 s2.size).findIdx? (· == s1[i1]!)).getD 9999 <
        ((s1.extract i1 s1.size).findIdx? (· == s2[i2]!)).getD 9999) then
      diffNames := diffNames.push s2[i2]!
      steps := steps.push 2
      i2 := i2 + 1
    else
      diffNames := diffNames.push s1[i1]!
      steps := steps.push 1
      i1 := i1 + 1
  let mut mapH : Std.HashMap String Ident := {}
  for k in diffNames do
    if mapH.contains k then continue
    let kLit := Syntax.mkStrLit k
    let hi := mkIdent (Name.mkSimple s!"hrec_{mapH.size}")
    mapH := mapH.insert k hi
    evalTactic (← `(tactic| by_cases $hi:ident : ($kLit == $(mkIdent `name):ident) = true))
    evalTactic (← `(tactic| case' pos => rw [beq_iff_eq] at $hi:ident; subst $hi:ident; rfl))
    evalTactic (← `(tactic| rw [Bool.not_eq_true] at $hi:ident))
  let ctx1I := mkIdent ctx1.constName!
  let ctx2I := mkIdent ctx2.constName!
  let mod1I := mkIdent (Name.str ctx1.constName!.getPrefix "module")
  let mod2I := mkIdent (Name.str ctx2.constName!.getPrefix "module")
  evalTactic (← `(tactic| dsimp only [CIR.Ctx.record?, CIR.Module.findRecord?, CIR.Ctx.ofModule, $ctx1I:ident, $ctx2I:ident, $mod1I:ident, $mod2I:ident]))
  let mut j1 := 0
  let mut j2 := 0
  for st in steps do
    if st == 3 then
      evalTactic (← `(tactic| rfl))
    else if st == 0 then
      evalTactic (← `(tactic| apply find?_rec_cons_congr))
      j1 := j1 + 1
      j2 := j2 + 1
    else if st == 1 then
      let hi := mapH[s1[j1]!]!
      let eS := mkIdent elems1[j1]!.constName!
      evalTactic (← `(tactic| refine (EquivLean.Cir.find?_rec_cons_false $eS:ident _ $hi:ident).trans ?_))
      j1 := j1 + 1
    else if st == 2 then
      let hi := mapH[s2[j2]!]!
      let eS := mkIdent elems2[j2]!.constName!
      evalTactic (← `(tactic| refine Eq.trans ?_ (EquivLean.Cir.find?_rec_cons_false $eS:ident _ $hi:ident).symm))
      j2 := j2 + 1
  evalTactic (← `(tactic| try rfl))

def vtableInit (g : GlobalDecl) : Option (List Const) :=
  match g.init with
  | some (.record cs) => some cs
  | _ => none

def evalVtableElems (ctx : Ctx) : List Const → Nat → Option Val
  | [], _ => none
  | c :: _, 0 => ctx.constVal 32 (.ptr (.int false 8)) c
  | _ :: es, k + 1 => evalVtableElems ctx es k

theorem evalVtableElems_eq (ctx : Ctx) (es : List Const) (k : Nat) :
    (match es[k]? with | some c => ctx.constVal 32 (.ptr (.int false 8)) c | none => none) =
    evalVtableElems ctx es k := by
  induction es generalizing k with
  | nil => rfl
  | cons c es ih => cases k <;> first | rfl | exact ih _

def evalVtableArrays (ctx : Ctx) : List Const → Nat → Nat → Option Val
  | [], _, _ => none
  | .array es :: _, 0, k => evalVtableElems ctx es k
  | _ :: _, 0, _ => none
  | _ :: cs, i + 1, k => evalVtableArrays ctx cs i k

theorem evalVtableArrays_eq (ctx : Ctx) (cs : List Const) (i k : Nat) :
    (match cs[i]? with
     | some (.array es) => match es[k]? with | some c => ctx.constVal 32 (.ptr (.int false 8)) c | none => none
     | _ => none) = evalVtableArrays ctx cs i k := by
  induction cs generalizing i with
  | nil => rfl
  | cons c cs ih =>
    cases i with
    | zero => cases c <;> first | rfl | exact evalVtableElems_eq ctx _ k
    | succ i => cases c <;> exact ih i

def evalVtableAt (ctx : Ctx) (i k : Nat) (o : Option GlobalDecl) : Option Val :=
  match o.bind vtableInit with
  | some cs => evalVtableArrays ctx cs i k
  | none => none

theorem vtableSlot?_eq_evalVtableAt (ctx : Ctx) (vt : String) (i k : Nat) :
    ctx.vtableSlot? vt i k = evalVtableAt ctx i k (ctx.mod.globals.find? (·.sym == vt)) := by
  unfold Ctx.vtableSlot? Module.findGlobal? evalVtableAt vtableInit
  cases ctx.mod.globals.find? (·.sym == vt) with
  | none => rfl
  | some g =>
    dsimp only [Option.bind]
    cases g.init with
    | none => rfl
    | some c => cases c <;> first | rfl | exact evalVtableArrays_eq ctx _ i k

theorem evalVtableElems_nil (ctx₁ ctx₂ : Ctx) (k : Nat) :
    evalVtableElems ctx₁ [] k = evalVtableElems ctx₂ [] k := rfl

theorem evalVtableElems_cons {ctx₁ ctx₂ : Ctx} {c : Const} {es : List Const}
    (hc : ctx₁.constVal 32 (.ptr (.int false 8)) c = ctx₂.constVal 32 (.ptr (.int false 8)) c)
    (hes : ∀ k, evalVtableElems ctx₁ es k = evalVtableElems ctx₂ es k) (k : Nat) :
    evalVtableElems ctx₁ (c :: es) k = evalVtableElems ctx₂ (c :: es) k := by
  cases k with
  | zero => exact hc
  | succ k => exact hes k

theorem evalVtableArrays_nil (ctx₁ ctx₂ : Ctx) (i k : Nat) :
    evalVtableArrays ctx₁ [] i k = evalVtableArrays ctx₂ [] i k := rfl

theorem evalVtableArrays_cons_array {ctx₁ ctx₂ : Ctx} {es : List Const} {cs : List Const}
    (hes : ∀ k, evalVtableElems ctx₁ es k = evalVtableElems ctx₂ es k)
    (hcs : ∀ i k, evalVtableArrays ctx₁ cs i k = evalVtableArrays ctx₂ cs i k) (i k : Nat) :
    evalVtableArrays ctx₁ (.array es :: cs) i k = evalVtableArrays ctx₂ (.array es :: cs) i k := by
  cases i with
  | zero => exact hes k
  | succ i => exact hcs i k

theorem evalVtableArrays_cons_nonarray {ctx₁ ctx₂ : Ctx} {c : Const} {cs : List Const}
    (hc : (match c with | .array _ => false | _ => true) = true)
    (hcs : ∀ i k, evalVtableArrays ctx₁ cs i k = evalVtableArrays ctx₂ cs i k) (i k : Nat) :
    evalVtableArrays ctx₁ (c :: cs) i k = evalVtableArrays ctx₂ (c :: cs) i k := by
  cases i with
  | zero => cases c <;> first | rfl | cases hc
  | succ i => cases c <;> exact hcs i k

theorem evalVtableAt_cons_nonvtable {ctx₁ ctx₂ : Ctx} {vt : String} {i k : Nat}
    {g₁ g₂ : GlobalDecl} {gs₁ gs₂ : List GlobalDecl}
    (hsym : g₁.sym = g₂.sym) (h1 : vtableInit g₁ = none) (h2 : vtableInit g₂ = none)
    (h : evalVtableAt ctx₁ i k (gs₁.find? (·.sym == vt)) = evalVtableAt ctx₂ i k (gs₂.find? (·.sym == vt))) :
    evalVtableAt ctx₁ i k ((g₁ :: gs₁).find? (·.sym == vt)) = evalVtableAt ctx₂ i k ((g₂ :: gs₂).find? (·.sym == vt)) := by
  simp only [List.find?, hsym]
  cases (g₂.sym == vt)
  · exact h
  · unfold evalVtableAt; dsimp only [Option.bind]; rw [h1, h2]

theorem evalVtableAt_cons_vtable {ctx₁ ctx₂ : Ctx} {vt : String} {i k : Nat}
    {g₁ g₂ : GlobalDecl} {gs₁ gs₂ : List GlobalDecl} {cs : List Const}
    (hsym : g₁.sym = g₂.sym) (h1 : vtableInit g₁ = some cs) (h2 : vtableInit g₂ = some cs)
    (hcs : ∀ i k, evalVtableArrays ctx₁ cs i k = evalVtableArrays ctx₂ cs i k)
    (h : evalVtableAt ctx₁ i k (gs₁.find? (·.sym == vt)) = evalVtableAt ctx₂ i k (gs₂.find? (·.sym == vt))) :
    evalVtableAt ctx₁ i k ((g₁ :: gs₁).find? (·.sym == vt)) = evalVtableAt ctx₂ i k ((g₂ :: gs₂).find? (·.sym == vt)) := by
  simp only [List.find?, hsym]
  cases (g₂.sym == vt)
  · exact h
  · unfold evalVtableAt; dsimp only [Option.bind]; rw [h1, h2]; exact hcs i k

theorem evalVtableAt_nil (ctx₁ ctx₂ : Ctx) (i k : Nat) (vt : String) :
    evalVtableAt ctx₁ i k ([].find? (·.sym == vt)) = evalVtableAt ctx₂ i k ([].find? (·.sym == vt)) := rfl

theorem constVal_globalAddr_global {ctx₁ ctx₂ : Ctx} {sym : String} {idx : List Int} {t : Ty}
    {g₁ g₂ : GlobalDecl} {b : Nat}
    (hf₁ : ctx₁.mod.findGlobal? sym = some g₁) (ha₁ : ctx₁.gaddr sym = some b)
    (hf₂ : ctx₂.mod.findGlobal? sym = some g₂) (ha₂ : ctx₂.gaddr sym = some b)
    (hty : g₁.ty = g₂.ty) :
    ctx₁.constVal 32 (.ptr t) (.globalAddr sym idx) = ctx₂.constVal 32 (.ptr t) (.globalAddr sym idx) := by
  simp only [Ctx.constVal, Ctx.symAddr?, hf₁, hf₂, ha₁, ha₂, Option.map, hty]

theorem constVal_globalAddr_func {ctx₁ ctx₂ : Ctx} {sym : String} {idx : List Int} {t : Ty}
    {fd₁ fd₂ : FuncDecl}
    (hg₁ : ctx₁.mod.findGlobal? sym = none) (ha₁ : ctx₁.gaddr sym = none) (hf₁ : ctx₁.mod.findFunc? sym = some fd₁)
    (hg₂ : ctx₂.mod.findGlobal? sym = none) (ha₂ : ctx₂.gaddr sym = none) (hf₂ : ctx₂.mod.findFunc? sym = some fd₂) :
    ctx₁.constVal 32 (.ptr t) (.globalAddr sym idx) = ctx₂.constVal 32 (.ptr t) (.globalAddr sym idx) := by
  simp only [Ctx.constVal, Ctx.symAddr?, hg₁, hg₂, ha₁, ha₂, hf₁, hf₂, Option.map, Option.isSome]

theorem constVal_globalAddr_ext {ctx₁ ctx₂ : Ctx} {sym : String} {idx : List Int} {t : Ty}
    (hg₁ : ctx₁.mod.findGlobal? sym = none) (ha₁ : ctx₁.gaddr sym = none) (hf₁ : ctx₁.mod.findFunc? sym = none)
    (hg₂ : ctx₂.mod.findGlobal? sym = none) (ha₂ : ctx₂.gaddr sym = none) (hf₂ : ctx₂.mod.findFunc? sym = none) :
    ctx₁.constVal 32 (.ptr t) (.globalAddr sym idx) = ctx₂.constVal 32 (.ptr t) (.globalAddr sym idx) := by
  simp only [Ctx.constVal, Ctx.symAddr?, hg₁, hg₂, ha₁, ha₂, hf₁, hf₂, Option.map, Option.isSome]

macro "cir_constVal_eq" : tactic => `(tactic| first
  | exact constVal_globalAddr_func (by cir_lookup) (by cir_lookup) (by cir_lookup) (by cir_lookup) (by cir_lookup) (by cir_lookup)
  | exact constVal_globalAddr_global (by cir_lookup) (by cir_lookup) (by cir_lookup) (by cir_lookup) rfl
  | exact constVal_globalAddr_ext (by cir_lookup) (by cir_lookup) (by cir_lookup) (by cir_lookup) (by cir_lookup) (by cir_lookup)
  | rfl)

macro "cir_prove_vtable_arrays" : tactic => `(tactic| (
  repeat' (first
    | exact evalVtableArrays_nil _ _
    | (intro i k; refine evalVtableArrays_cons_nonarray rfl ?_ i k)
    | (intro i k; refine evalVtableArrays_cons_array ?_ ?_ i k; · repeat' (first
        | exact evalVtableElems_nil _ _
        | (intro k; refine evalVtableElems_cons ?_ ?_ k; · cir_constVal_eq))))))

open Lean Meta Elab Tactic in
elab "cir_prove_vtable_eq" : tactic => withTheReader Core.Context (fun c => { c with maxRecDepth := 100000 }) do
  evalTactic (← `(tactic| funext $(mkIdent `vt):ident $(mkIdent `i):ident $(mkIdent `k):ident))
  evalTactic (← `(tactic| rw [vtableSlot?_eq_evalVtableAt, vtableSlot?_eq_evalVtableAt]))
  let g ← getMainGoal
  let some (_, lhs, rhs) := (← g.withContext do instantiateMVars (← g.getType)).eq?
    | throwError "not eq"
  let ctx1 := lhs.getArg! 0
  let ctx2 := rhs.getArg! 0
  let M1 ← mkAppM ``CIR.Ctx.mod #[ctx1]
  let gs1 ← mkAppM ``CIR.Module.globals #[M1]
  let some elems1 ← CIR.Tactic.listElems gs1 | throwError "gs1 not list"
  let mod1I := mkIdent (Name.str ctx1.constName!.getPrefix "module")
  let mod2I := mkIdent (Name.str ctx2.constName!.getPrefix "module")
  let vtI := mkIdent `vt
  let iI := mkIdent `i
  let kI := mkIdent `k
  let ctx1I := mkIdent ctx1.constName!
  let ctx2I := mkIdent ctx2.constName!
  evalTactic (← `(tactic| change evalVtableAt $ctx1I $iI $kI (List.find? (·.sym == $vtI) (CIR.Module.globals $mod1I)) = evalVtableAt $ctx2I $iI $kI (List.find? (·.sym == $vtI) (CIR.Module.globals $mod2I))))
  evalTactic (← `(tactic| dsimp only [$mod1I:ident, $mod2I:ident]))
  for idx in [0:elems1.size] do
    let e1 := elems1[idx]!
    let vtInit ← whnfD (← mkAppM ``vtableInit #[e1])
    if vtInit.isAppOf ``Option.none then
      evalTactic (← `(tactic| refine evalVtableAt_cons_nonvtable rfl rfl rfl ?_))
    else
      evalTactic (← `(tactic| refine evalVtableAt_cons_vtable rfl rfl rfl (by cir_prove_vtable_arrays) ?_))
  evalTactic (← `(tactic| exact evalVtableAt_nil _ _ _ _ _))

/-! ### Context Primitive Congruence -/

theorem typeAt_congr {ctx₁ ctx₂ : Ctx} (hr : ∀ name, ctx₁.record? name = ctx₂.record? name) :
    ctx₁.typeAt = ctx₂.typeAt := by
  funext ty p
  exact typeAt_eq_of_record_eq hr ty p

theorem sizeAlign_congr {ctx₁ ctx₂ : Ctx}
    (hr : ∀ name, ctx₁.record? name = ctx₂.record? name)
    (hp : ctx₁.mod.ptrBytes = ctx₂.mod.ptrBytes) :
    ctx₁.sizeAlign = ctx₂.sizeAlign := by
  funext d
  induction d with
  | zero => rfl
  | succ d ih =>
    funext ty
    cases ty with
    | float fk => cases fk <;> rfl
    | _ => try simp only [Ctx.sizeAlign, hp, hr, ih]

theorem initVal_congr {ctx₁ ctx₂ : Ctx}
    (hr : ∀ name, ctx₁.record? name = ctx₂.record? name) :
    ctx₁.initVal = ctx₂.initVal := by
  funext d
  induction d with
  | zero => rfl
  | succ d ih =>
    funext ty
    cases ty <;> try simp only [Ctx.initVal, hr, ih]

theorem zeroVal_congr {ctx₁ ctx₂ : Ctx}
    (hr : ∀ name, ctx₁.record? name = ctx₂.record? name) :
    ctx₁.zeroVal = ctx₂.zeroVal := by
  have hi := initVal_congr hr
  funext d
  induction d with
  | zero => rfl
  | succ d ih =>
    funext ty
    cases ty <;> try simp only [Ctx.zeroVal, hr, ih, hi]

theorem punnedMember_congr {ctx₁ ctx₂ : Ctx} (hr : ∀ name, ctx₁.record? name = ctx₂.record? name) :
    ctx₁.punnedMember = ctx₂.punnedMember := by
  funext m ty p; unfold Ctx.punnedMember; rw [typeAt_congr hr]

theorem record?_congr {ctx₁ ctx₂ : Ctx} (hr : ∀ name, ctx₁.record? name = ctx₂.record? name) :
    ctx₁.record? = ctx₂.record? :=
  funext hr

theorem memberOffsets_congr {ctx₁ ctx₂ : Ctx}
    (hr : ∀ name, ctx₁.record? name = ctx₂.record? name)
    (hp : ctx₁.mod.ptrBytes = ctx₂.mod.ptrBytes) :
    ctx₁.memberOffsets = ctx₂.memberOffsets := by
  funext name; unfold Ctx.memberOffsets; rw [hr, sizeAlign_congr hr hp]

theorem isEmptyRecord_congr {ctx₁ ctx₂ : Ctx} (hr : ∀ name, ctx₁.record? name = ctx₂.record? name) :
    ctx₁.isEmptyRecord = ctx₂.isEmptyRecord := by
  funext n; unfold Ctx.isEmptyRecord; rw [hr]

theorem memberAt_congr {ctx₁ ctx₂ : Ctx}
    (hr : ∀ name, ctx₁.record? name = ctx₂.record? name)
    (hp : ctx₁.mod.ptrBytes = ctx₂.mod.ptrBytes) :
    ctx₁.memberAt = ctx₂.memberAt := by
  funext j ms os r
  induction ms generalizing j os with
  | nil => cases os <;> rfl
  | cons hd tl ih =>
    cases os with
    | nil => rfl
    | cons o os =>
      rcases hd with ⟨mk, t⟩
      unfold Ctx.memberAt
      rw [sizeAlign_congr hr hp, ih]

theorem scalarIn_congr {ctx₁ ctx₂ : Ctx}
    (hr : ∀ name, ctx₁.record? name = ctx₂.record? name)
    (hp : ctx₁.mod.ptrBytes = ctx₂.mod.ptrBytes) :
    ctx₁.scalarIn = ctx₂.scalarIn := by
  funext fuel
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
    funext t v path k
    unfold Ctx.scalarIn
    rw [sizeAlign_congr hr hp, record?_congr hr, memberOffsets_congr hr hp, memberAt_congr hr hp, ih]

theorem recordAt_congr {ctx₁ ctx₂ : Ctx}
    (hr : ∀ name, ctx₁.record? name = ctx₂.record? name) :
    ctx₁.recordAt = ctx₂.recordAt := by
  funext fuel
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
    funext t path n
    unfold Ctx.recordAt
    rw [record?_congr hr, ih]

theorem enclosingIn_congr {ctx₁ ctx₂ : Ctx}
    (hr : ∀ name, ctx₁.record? name = ctx₂.record? name) :
    ctx₁.enclosingIn = ctx₂.enclosingIn := by
  suffices h : ∀ rest n t pre cand, ctx₁.enclosingIn n t rest pre cand = ctx₂.enclosingIn n t rest pre cand by
    funext n t rest pre cand; exact h rest n t pre cand
  intro rest; induction rest with
  | nil => intros; rfl
  | cons e rest ih =>
    intro n t pre cand
    cases e <;> cases t <;> simp only [Ctx.enclosingIn, record?_congr hr, ih]

theorem convertPath_congr {ctx₁ ctx₂ : Ctx}
    (hr : ∀ name, ctx₁.record? name = ctx₂.record? name) :
    ctx₁.convertPath = ctx₂.convertPath := by
  funext bty path n; unfold Ctx.convertPath
  rw [typeAt_congr hr, recordAt_congr hr, enclosingIn_congr hr]

theorem convertPtr_congr {ctx₁ ctx₂ : Ctx}
    (hr : ∀ name, ctx₁.record? name = ctx₂.record? name) :
    ctx₁.convertPtr = ctx₂.convertPtr := by
  funext m k x dst; unfold Ctx.convertPtr
  rw [convertPath_congr hr, typeAt_congr hr]

theorem scalarAt_congr {ctx₁ ctx₂ : Ctx}
    (hr : ∀ name, ctx₁.record? name = ctx₂.record? name)
    (hp : ctx₁.mod.ptrBytes = ctx₂.mod.ptrBytes) :
    ctx₁.scalarAt = ctx₂.scalarAt := by
  funext d
  induction d with
  | zero => rfl
  | succ d ih =>
    funext t v o; cases t <;> cases v <;>
      simp only [Ctx.scalarAt, sizeAlign_congr hr hp, record?_congr hr, memberOffsets_congr hr hp, ih]

theorem byteAt_congr {ctx₁ ctx₂ : Ctx}
    (hr : ∀ name, ctx₁.record? name = ctx₂.record? name)
    (hp : ctx₁.mod.ptrBytes = ctx₂.mod.ptrBytes) :
    ctx₁.byteAt = ctx₂.byteAt := by
  funext d
  induction d with
  | zero => rfl
  | succ d ih =>
    funext t v o; cases t <;> cases v <;>
      simp only [Ctx.byteAt, sizeAlign_congr hr hp, record?_congr hr, memberOffsets_congr hr hp, ih]

theorem composeAt_congr {ctx₁ ctx₂ : Ctx}
    (hr : ∀ name, ctx₁.record? name = ctx₂.record? name)
    (hp : ctx₁.mod.ptrBytes = ctx₂.mod.ptrBytes) :
    ctx₁.composeAt = ctx₂.composeAt := by
  funext src sv base t; unfold Ctx.composeAt
  rw [sizeAlign_congr hr hp, byteAt_congr hr hp]

theorem reinterpScalar_congr {ctx₁ ctx₂ : Ctx}
    (hr : ∀ name, ctx₁.record? name = ctx₂.record? name)
    (hp : ctx₁.mod.ptrBytes = ctx₂.mod.ptrBytes) :
    ctx₁.reinterpScalar = ctx₂.reinterpScalar := by
  funext src sv base t; unfold Ctx.reinterpScalar
  rw [scalarAt_congr hr hp, sizeAlign_congr hr hp, composeAt_congr hr hp]

theorem reinterpAt_congr {ctx₁ ctx₂ : Ctx}
    (hr : ∀ name, ctx₁.record? name = ctx₂.record? name)
    (hp : ctx₁.mod.ptrBytes = ctx₂.mod.ptrBytes) :
    ctx₁.reinterpAt = ctx₂.reinterpAt := by
  funext src sv d
  induction d with
  | zero => rfl
  | succ d ih =>
    funext base t; cases t <;>
      simp only [Ctx.reinterpAt, reinterpScalar_congr hr hp, sizeAlign_congr hr hp,
        record?_congr hr, memberOffsets_congr hr hp, ih]

theorem fromActive_congr {ctx₁ ctx₂ : Ctx}
    (hr : ∀ name, ctx₁.record? name = ctx₂.record? name)
    (hp : ctx₁.mod.ptrBytes = ctx₂.mod.ptrBytes) :
    ctx₁.fromActive = ctx₂.fromActive := by
  funext k tk j ms
  induction ms generalizing j with
  | nil => funext vs; simp only [Ctx.fromActive, initVal_congr hr]
  | cons hd tl ih =>
    funext vs; cases vs with
    | nil => simp only [Ctx.fromActive, initVal_congr hr]
    | cons v vs =>
      rcases hd with ⟨mk, t⟩
      unfold Ctx.fromActive
      rw [ih, reinterpAt_congr hr hp]

theorem viewValIn?_congr {ctx₁ ctx₂ : Ctx}
    (hr : ∀ name, ctx₁.record? name = ctx₂.record? name)
    (hp : ctx₁.mod.ptrBytes = ctx₂.mod.ptrBytes) :
    ctx₁.viewValIn? = ctx₂.viewValIn? := by
  suffices h : ∀ p t v, ctx₁.viewValIn? t v p = ctx₂.viewValIn? t v p by
    funext t v p; exact h p t v
  intro p; induction p with
  | nil => intros; rfl
  | cons e p ih =>
    intro t v; cases e <;> cases t <;> cases v <;>
      simp only [Ctx.viewValIn?, record?_congr hr, fromActive_congr hr hp, ih]

theorem activateValIn?_congr {ctx₁ ctx₂ : Ctx}
    (hr : ∀ name, ctx₁.record? name = ctx₂.record? name)
    (hp : ctx₁.mod.ptrBytes = ctx₂.mod.ptrBytes) :
    ctx₁.activateValIn? = ctx₂.activateValIn? := by
  suffices h : ∀ p t v, ctx₁.activateValIn? t v p = ctx₂.activateValIn? t v p by
    funext t v p; exact h p t v
  intro p; induction p with
  | nil => intros; rfl
  | cons e p ih =>
    intro t v; cases e <;> cases t <;> cases v <;>
      simp only [Ctx.activateValIn?, record?_congr hr, fromActive_congr hr hp, ih]

theorem unionOnPath_congr {ctx₁ ctx₂ : Ctx}
    (hr : ∀ name, ctx₁.record? name = ctx₂.record? name) :
    ctx₁.unionOnPath = ctx₂.unionOnPath := by
  funext d
  induction d with
  | zero => rfl
  | succ d ih =>
    funext t p; cases p with
    | nil => rfl
    | cons e p =>
      cases e <;> cases t <;>
        simp only [Ctx.unionOnPath, record?_congr hr, ih]

theorem viewVal?_congr {ctx₁ ctx₂ : Ctx}
    (hr : ∀ name, ctx₁.record? name = ctx₂.record? name)
    (hp : ctx₁.mod.ptrBytes = ctx₂.mod.ptrBytes) :
    ctx₁.viewVal? = ctx₂.viewVal? := by
  funext t v path; unfold Ctx.viewVal?
  rw [unionOnPath_congr hr, viewValIn?_congr hr hp]

theorem activateVal?_congr {ctx₁ ctx₂ : Ctx}
    (hr : ∀ name, ctx₁.record? name = ctx₂.record? name)
    (hp : ctx₁.mod.ptrBytes = ctx₂.mod.ptrBytes) :
    ctx₁.activateVal? = ctx₂.activateVal? := by
  funext t v path; unfold Ctx.activateVal?
  rw [unionOnPath_congr hr, activateValIn?_congr hr hp]

theorem unionView?_congr {ctx₁ ctx₂ : Ctx}
    (hr : ∀ name, ctx₁.record? name = ctx₂.record? name)
    (hp : ctx₁.mod.ptrBytes = ctx₂.mod.ptrBytes) :
    ctx₁.unionView? = ctx₂.unionView? := by
  funext m p; cases p <;> simp only [Ctx.unionView?, viewVal?_congr hr hp]

theorem unionActivate?_congr {ctx₁ ctx₂ : Ctx}
    (hr : ∀ name, ctx₁.record? name = ctx₂.record? name)
    (hp : ctx₁.mod.ptrBytes = ctx₂.mod.ptrBytes) :
    ctx₁.unionActivate? = ctx₂.unionActivate? := by
  funext m p; cases p <;> simp only [Ctx.unionActivate?, activateVal?_congr hr hp]

theorem absPos?_congr {ctx₁ ctx₂ : Ctx}
    (hr : ∀ name, ctx₁.record? name = ctx₂.record? name)
    (hp : ctx₁.mod.ptrBytes = ctx₂.mod.ptrBytes) :
    ctx₁.absPos? = ctx₂.absPos? := by
  suffices h : ∀ path t, ctx₁.absPos? t path = ctx₂.absPos? t path by
    funext t path; exact h path t
  intro path; induction path with
  | nil => intros; rfl
  | cons e rest ih =>
    intro t
    cases e with
    | vel _ _ => cases rest <;> cases t <;> rfl
    | byte k => cases rest <;> cases t <;> rfl
    | idx i =>
      cases t <;> try (cases rest <;> rfl)
      all_goals
        simp only [Ctx.absPos?, sizeAlign_congr hr hp, record?_congr hr, memberOffsets_congr hr hp, ih]

theorem posAligned_congr {ctx₁ ctx₂ : Ctx}
    (hr : ∀ name, ctx₁.record? name = ctx₂.record? name)
    (hp : ctx₁.mod.ptrBytes = ctx₂.mod.ptrBytes) :
    ctx₁.posAligned = ctx₂.posAligned := by
  funext m b path a; unfold Ctx.posAligned; rw [absPos?_congr hr hp]

theorem castAligned_congr {ctx₁ ctx₂ : Ctx}
    (hr : ∀ name, ctx₁.record? name = ctx₂.record? name)
    (hp : ctx₁.mod.ptrBytes = ctx₂.mod.ptrBytes) :
    ctx₁.castAligned = ctx₂.castAligned := by
  funext m b path t; unfold Ctx.castAligned; rw [sizeAlign_congr hr hp, posAligned_congr hr hp]

theorem castCheck_congr {ctx₁ ctx₂ : Ctx}
    (hr : ∀ name, ctx₁.record? name = ctx₂.record? name)
    (hp : ctx₁.mod.ptrBytes = ctx₂.mod.ptrBytes)
    (hcxx : ctx₁.mod.cxx = ctx₂.mod.cxx := by rfl) :
    ctx₁.castCheck = ctx₂.castCheck := by
  funext m k x dst; unfold Ctx.castCheck; rw [castAligned_congr hr hp, hcxx]

theorem gatherAt_congr {ctx₁ ctx₂ : Ctx}
    (hr : ∀ name, ctx₁.record? name = ctx₂.record? name)
    (hp : ctx₁.mod.ptrBytes = ctx₂.mod.ptrBytes) :
    ctx₁.gatherAt = ctx₂.gatherAt := by
  funext fuel
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
    funext m b t q; unfold Ctx.gatherAt
    rw [scalarIn_congr hr hp, record?_congr hr, memberOffsets_congr hr hp, initVal_congr hr, sizeAlign_congr hr hp, ih]

theorem scatterAt_congr {ctx₁ ctx₂ : Ctx}
    (hr : ∀ name, ctx₁.record? name = ctx₂.record? name)
    (hp : ctx₁.mod.ptrBytes = ctx₂.mod.ptrBytes) :
    ctx₁.scatterAt = ctx₂.scatterAt := by
  funext fuel
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
    funext m b t q v; unfold Ctx.scatterAt
    rw [scalarIn_congr hr hp, record?_congr hr, memberOffsets_congr hr hp, sizeAlign_congr hr hp, ih]

theorem spreadLoad_congr {ctx₁ ctx₂ : Ctx}
    (hr : ∀ name, ctx₁.record? name = ctx₂.record? name)
    (hp : ctx₁.mod.ptrBytes = ctx₂.mod.ptrBytes) :
    ctx₁.spreadLoad = ctx₂.spreadLoad := by
  funext m b path t; unfold Ctx.spreadLoad
  rw [absPos?_congr hr hp, gatherAt_congr hr hp]

theorem spreadStore_congr {ctx₁ ctx₂ : Ctx}
    (hr : ∀ name, ctx₁.record? name = ctx₂.record? name)
    (hp : ctx₁.mod.ptrBytes = ctx₂.mod.ptrBytes) :
    ctx₁.spreadStore = ctx₂.spreadStore := by
  funext m b path t v; unfold Ctx.spreadStore
  rw [absPos?_congr hr hp, scatterAt_congr hr hp]

theorem reachIn_congr {ctx₁ ctx₂ : Ctx}
    (hr : ∀ name, ctx₁.record? name = ctx₂.record? name)
    (hp : ctx₁.mod.ptrBytes = ctx₂.mod.ptrBytes) :
    ctx₁.reachIn = ctx₂.reachIn := by
  funext blk ty path
  unfold Ctx.reachIn Ctx.reachTypeNone Ctx.reachNone Ctx.reachSlow Ctx.reachScalarAt Ctx.reachRecordAt
  rw [typeAt_congr hr, isEmptyRecord_congr hr, scalarIn_congr hr hp, recordAt_congr hr]

theorem reach?_congr {ctx₁ ctx₂ : Ctx}
    (hr : ∀ name, ctx₁.record? name = ctx₂.record? name)
    (hp : ctx₁.mod.ptrBytes = ctx₂.mod.ptrBytes) :
    ctx₁.reach? = ctx₂.reach? := by
  funext m ty p; cases p <;> simp only [Ctx.reach?, reachIn_congr hr hp]

theorem typedLoad_congr {ctx₁ ctx₂ : Ctx}
    (hr : ∀ name, ctx₁.record? name = ctx₂.record? name)
    (hp : ctx₁.mod.ptrBytes = ctx₂.mod.ptrBytes := by rfl) :
    ctx₁.typedLoad = ctx₂.typedLoad := by
  funext m ty p; unfold Ctx.typedLoad
  rw [unionView?_congr hr hp, reach?_congr hr hp, spreadLoad_congr hr hp, punnedMember_congr hr]

theorem typedStore_congr {ctx₁ ctx₂ : Ctx}
    (hr : ∀ name, ctx₁.record? name = ctx₂.record? name)
    (hp : ctx₁.mod.ptrBytes = ctx₂.mod.ptrBytes := by rfl) :
    ctx₁.typedStore = ctx₂.typedStore := by
  funext m ty p v; unfold Ctx.typedStore
  rw [unionActivate?_congr hr hp, reach?_congr hr hp, spreadStore_congr hr hp, punnedMember_congr hr]

theorem basePath_congr {ctx₁ ctx₂ : Ctx}
    (hr : ∀ name, ctx₁.record? name = ctx₂.record? name)
    (hp : ctx₁.mod.ptrBytes = ctx₂.mod.ptrBytes) :
    ctx₁.basePath = ctx₂.basePath := by
  have hm := memberOffsets_congr hr hp
  have he := isEmptyRecord_congr hr
  funext fuel
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
    funext d b off
    unfold Ctx.basePath
    rw [hr, hm, he, ih]

theorem vptrPath_congr {ctx₁ ctx₂ : Ctx} (hr : ∀ name, ctx₁.record? name = ctx₂.record? name) :
    ctx₁.vptrPath = ctx₂.vptrPath := by
  funext fuel
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
    funext n; unfold Ctx.vptrPath; rw [hr, ih]

theorem vptrClass?_congr {ctx₁ ctx₂ : Ctx}
    (hr : ∀ name, ctx₁.record? name = ctx₂.record? name) :
    ctx₁.vptrClass? = ctx₂.vptrClass? := by
  funext m p ty; cases p <;> simp only [Ctx.vptrClass?, typeAt_congr hr]

theorem canonByte_congr {ctx₁ ctx₂ : Ctx}
    (hr : ∀ name, ctx₁.record? name = ctx₂.record? name)
    (hp : ctx₁.mod.ptrBytes = ctx₂.mod.ptrBytes) :
    ctx₁.canonByte = ctx₂.canonByte := by
  funext fuel
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
    funext t v path r; unfold Ctx.canonByte
    rw [sizeAlign_congr hr hp, record?_congr hr, memberOffsets_congr hr hp, memberAt_congr hr hp, ih]

theorem vtableStride?_congr {ctx₁ ctx₂ : Ctx}
    (hp : ctx₁.mod.ptrBytes = ctx₂.mod.ptrBytes) :
    ctx₁.vtableStride? = ctx₂.vtableStride? := by
  funext vt i k d; unfold Ctx.vtableStride?; rw [hp]

theorem charStride?_congr {ctx₁ ctx₂ : Ctx}
    (hr : ∀ name, ctx₁.record? name = ctx₂.record? name)
    (hp : ctx₁.mod.ptrBytes = ctx₂.mod.ptrBytes) :
    ctx₁.charStride? = ctx₂.charStride? := by
  funext m p n; unfold Ctx.charStride?
  rw [absPos?_congr hr hp, sizeAlign_congr hr hp, canonByte_congr hr hp, vtableStride?_congr hp]

theorem charDiff?_congr {ctx₁ ctx₂ : Ctx}
    (hr : ∀ name, ctx₁.record? name = ctx₂.record? name)
    (hp : ctx₁.mod.ptrBytes = ctx₂.mod.ptrBytes) :
    ctx₁.charDiff? = ctx₂.charDiff? := by
  funext m p p'; cases p <;> cases p' <;> simp only [Ctx.charDiff?, absPos?_congr hr hp]

theorem sizedAt_congr {ctx₁ ctx₂ : Ctx}
    (hr : ∀ name, ctx₁.record? name = ctx₂.record? name)
    (hp : ctx₁.mod.ptrBytes = ctx₂.mod.ptrBytes) :
    ctx₁.sizedAt = ctx₂.sizedAt := by
  funext fuel
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
    funext t path e; unfold Ctx.sizedAt
    rw [sizeAlign_congr hr hp, record?_congr hr, ih]

theorem elemOf?_congr {ctx₁ ctx₂ : Ctx}
    (hr : ∀ name, ctx₁.record? name = ctx₂.record? name)
    (hp : ctx₁.mod.ptrBytes = ctx₂.mod.ptrBytes) :
    ctx₁.elemOf? = ctx₂.elemOf? := by
  funext bty path; unfold Ctx.elemOf?
  rw [typeAt_congr hr, sizeAlign_congr hr hp]

theorem lens?_congr {ctx₁ ctx₂ : Ctx}
    (hr : ∀ name, ctx₁.record? name = ctx₂.record? name)
    (hp : ctx₁.mod.ptrBytes = ctx₂.mod.ptrBytes) :
    ctx₁.lens? = ctx₂.lens? := by
  funext m e p; cases p <;>
    simp only [Ctx.lens?, elemOf?_congr hr hp, typeAt_congr hr, sizedAt_congr hr hp]

theorem lensStride?_congr {ctx₁ ctx₂ : Ctx}
    (hr : ∀ name, ctx₁.record? name = ctx₂.record? name)
    (hp : ctx₁.mod.ptrBytes = ctx₂.mod.ptrBytes) :
    ctx₁.lensStride? = ctx₂.lensStride? := by
  funext m p n e; unfold Ctx.lensStride?
  rw [vtableStride?_congr hp, lens?_congr hr hp]

theorem lensDiff?_congr {ctx₁ ctx₂ : Ctx}
    (hr : ∀ name, ctx₁.record? name = ctx₂.record? name)
    (hp : ctx₁.mod.ptrBytes = ctx₂.mod.ptrBytes) :
    ctx₁.lensDiff? = ctx₂.lensDiff? := by
  funext m p p' e; unfold Ctx.lensDiff?
  rw [lens?_congr hr hp]

theorem elemTyOf?_congr {ctx₁ ctx₂ : Ctx}
    (hr : ∀ name, ctx₁.record? name = ctx₂.record? name)
    (hp : ctx₁.mod.ptrBytes = ctx₂.mod.ptrBytes) :
    ctx₁.elemTyOf? = ctx₂.elemTyOf? := by
  funext m p; cases p <;> simp only [Ctx.elemTyOf?, typeAt_congr hr, sizeAlign_congr hr hp]

theorem sameUnits_congr {ctx₁ ctx₂ : Ctx}
    (hr : ∀ name, ctx₁.record? name = ctx₂.record? name)
    (hp : ctx₁.mod.ptrBytes = ctx₂.mod.ptrBytes) :
    ctx₁.sameUnits = ctx₂.sameUnits := by
  funext m p elemTy; unfold Ctx.sameUnits; rw [elemTyOf?_congr hr hp, sizeAlign_congr hr hp]

theorem stride?_congr {ctx₁ ctx₂ : Ctx}
    (hr : ∀ name, ctx₁.record? name = ctx₂.record? name)
    (hp : ctx₁.mod.ptrBytes = ctx₂.mod.ptrBytes) :
    ctx₁.stride? = ctx₂.stride? := by
  funext m p n elemTy; unfold Ctx.stride?
  rw [sameUnits_congr hr hp, charStride?_congr hr hp, sizeAlign_congr hr hp, lensStride?_congr hr hp]

theorem diff?_congr {ctx₁ ctx₂ : Ctx}
    (hr : ∀ name, ctx₁.record? name = ctx₂.record? name)
    (hp : ctx₁.mod.ptrBytes = ctx₂.mod.ptrBytes) :
    ctx₁.diff? = ctx₂.diff? := by
  funext m p p' elemTy; unfold Ctx.diff?
  rw [sameUnits_congr hr hp, charDiff?_congr hr hp, sizeAlign_congr hr hp, lensDiff?_congr hr hp]

theorem memberPath_congr {ctx₁ ctx₂ : Ctx}
    (hr : ∀ name, ctx₁.record? name = ctx₂.record? name)
    (hp : ctx₁.mod.ptrBytes = ctx₂.mod.ptrBytes) :
    ctx₁.memberPath = ctx₂.memberPath := by
  funext m b path rt i
  unfold Ctx.memberPath Ctx.memberRelated Ctx.memberOther Ctx.memberSlow Ctx.placeMember
  rw [typeAt_congr hr, convertPath_congr hr, absPos?_congr hr hp, memberOffsets_congr hr hp, canonByte_congr hr hp]

theorem bfPlaced?_congr {ctx₁ ctx₂ : Ctx}
    (hr : ∀ name, ctx₁.record? name = ctx₂.record? name)
    (hp : ctx₁.mod.ptrBytes = ctx₂.mod.ptrBytes) :
    ctx₁.bfPlaced? = ctx₂.bfPlaced? := by
  funext m p st; cases p <;> simp only [Ctx.bfPlaced?, typeAt_congr hr, hr, absPos?_congr hr hp, sizeAlign_congr hr hp]

theorem bfScalarAt_congr {ctx₁ ctx₂ : Ctx}
    (hr : ∀ name, ctx₁.record? name = ctx₂.record? name)
    (hp : ctx₁.mod.ptrBytes = ctx₂.mod.ptrBytes) :
    ctx₁.bfScalarAt = ctx₂.bfScalarAt := by
  funext m b ty q; unfold Ctx.bfScalarAt; rw [scalarIn_congr hr hp]

theorem bfLoadBytes_congr {ctx₁ ctx₂ : Ctx}
    (hr : ∀ name, ctx₁.record? name = ctx₂.record? name)
    (hp : ctx₁.mod.ptrBytes = ctx₂.mod.ptrBytes) :
    ctx₁.bfLoadBytes = ctx₂.bfLoadBytes := by
  funext m b ty q nb
  induction nb generalizing q with
  | zero => rfl
  | succ nb ih => unfold Ctx.bfLoadBytes; rw [bfScalarAt_congr hr hp, ih]

theorem bfLoadBytes0_congr {ctx₁ ctx₂ : Ctx}
    (hr : ∀ name, ctx₁.record? name = ctx₂.record? name)
    (hp : ctx₁.mod.ptrBytes = ctx₂.mod.ptrBytes) :
    ctx₁.bfLoadBytes0 = ctx₂.bfLoadBytes0 := by
  funext m b ty q nb; unfold Ctx.bfLoadBytes0; rw [bfLoadBytes_congr hr hp]

theorem bfStoreBytes_congr {ctx₁ ctx₂ : Ctx}
    (hr : ∀ name, ctx₁.record? name = ctx₂.record? name)
    (hp : ctx₁.mod.ptrBytes = ctx₂.mod.ptrBytes) :
    ctx₁.bfStoreBytes = ctx₂.bfStoreBytes := by
  suffices h : ∀ nb b ty m q u, ctx₁.bfStoreBytes b ty m q nb u = ctx₂.bfStoreBytes b ty m q nb u by
    funext b ty m q nb u; exact h nb b ty m q u
  intro nb; induction nb with
  | zero => intros; rfl
  | succ nb ih =>
    intro b ty m q u; unfold Ctx.bfStoreBytes
    simp only [bfScalarAt_congr hr hp, ih]

theorem endLifetime_congr {ctx₁ ctx₂ : Ctx}
    (hr : ∀ name, ctx₁.record? name = ctx₂.record? name) :
    endLifetime ctx₁ = endLifetime ctx₂ := by
  funext args m; unfold endLifetime; rw [typeAt_congr hr, initVal_congr hr]

theorem loadPtr_congr {ctx₁ ctx₂ : Ctx}
    (hr : ∀ name, ctx₁.record? name = ctx₂.record? name)
    (hv : ctx₁.vtableSlot? = ctx₂.vtableSlot?)
    (hp : ctx₁.mod.ptrBytes = ctx₂.mod.ptrBytes := by rfl) :
    loadPtr ctx₁ = loadPtr ctx₂ := by
  funext m ty p; cases p <;> simp only [loadPtr, hv, typedLoad_congr hr hp]

theorem typedRange?_congr {ctx₁ ctx₂ : Ctx}
    (hr : ∀ name, ctx₁.record? name = ctx₂.record? name)
    (hp : ctx₁.mod.ptrBytes = ctx₂.mod.ptrBytes) :
    Std.typedRange? ctx₁ = Std.typedRange? ctx₂ := by
  funext m p n; unfold Std.typedRange?; rw [typeAt_congr hr, sizeAlign_congr hr hp, hp]

theorem containerAt?_congr {ctx₁ ctx₂ : Ctx}
    (hr : ∀ name, ctx₁.record? name = ctx₂.record? name)
    (hp : ctx₁.mod.ptrBytes = ctx₂.mod.ptrBytes) :
    Std.containerAt? ctx₁ = Std.containerAt? ctx₂ := by
  funext m p; cases p <;> simp only [Std.containerAt?, typeAt_congr hr, sizeAlign_congr hr hp]

theorem isVecObject_congr {ctx₁ ctx₂ : Ctx}
    (hr : ∀ name, ctx₁.record? name = ctx₂.record? name) :
    Std.isVecObject ctx₁ = Std.isVecObject ctx₂ := by
  funext m p; cases p <;> simp only [Std.isVecObject, typeAt_congr hr]

theorem readVec_congr {ctx₁ ctx₂ : Ctx}
    (hr : ∀ name, ctx₁.record? name = ctx₂.record? name)
    (hp : ctx₁.mod.ptrBytes = ctx₂.mod.ptrBytes := by rfl) :
    Std.readVec ctx₁ = Std.readVec ctx₂ := by
  funext m p; unfold Std.readVec; rw [containerAt?_congr hr hp, isVecObject_congr hr]

theorem loadPtrAt_congr {ctx₁ ctx₂ : Ctx}
    (hr : ∀ name, ctx₁.record? name = ctx₂.record? name)
    (hp : ctx₁.mod.ptrBytes = ctx₂.mod.ptrBytes := by rfl) :
    Std.loadPtrAt ctx₁ = Std.loadPtrAt ctx₂ := by
  funext m ty p i; unfold Std.loadPtrAt; rw [typedLoad_congr hr hp]

theorem evAddHeader_congr {ctx₁ ctx₂ : Ctx}
    (hr : ∀ name, ctx₁.record? name = ctx₂.record? name)
    (hp : ctx₁.mod.ptrBytes = ctx₂.mod.ptrBytes := by rfl) :
    Std.evAddHeader ctx₁ = Std.evAddHeader ctx₂ := by
  funext m h k v; unfold Std.evAddHeader
  rw [typeAt_congr hr, zeroVal_congr hr, loadPtrAt_congr hr hp, typedStore_congr hr hp]

theorem evbufferAdd_congr {ctx₁ ctx₂ : Ctx}
    (hr : ∀ name, ctx₁.record? name = ctx₂.record? name)
    (hp : ctx₁.mod.ptrBytes = ctx₂.mod.ptrBytes) :
    Std.evbufferAdd ctx₁ = Std.evbufferAdd ctx₂ := by
  funext m p d n; unfold Std.evbufferAdd; rw [typedRange?_congr hr hp]

theorem evRemoveFirst_congr {ctx₁ ctx₂ : Ctx}
    (hr : ∀ name, ctx₁.record? name = ctx₂.record? name)
    (hp : ctx₁.mod.ptrBytes = ctx₂.mod.ptrBytes := by rfl) :
    Std.evRemoveFirst ctx₁ = Std.evRemoveFirst ctx₂ := by
  funext m h; unfold Std.evRemoveFirst; rw [loadPtrAt_congr hr hp, typedStore_congr hr hp]

theorem evFreeHeaders_congr {ctx₁ ctx₂ : Ctx}
    (hr : ∀ name, ctx₁.record? name = ctx₂.record? name)
    (hp : ctx₁.mod.ptrBytes = ctx₂.mod.ptrBytes := by rfl) :
    Std.evFreeHeaders ctx₁ = Std.evFreeHeaders ctx₂ := by
  funext m h; unfold Std.evFreeHeaders; rw [evRemoveFirst_congr hr hp]

theorem evreqLayout_congr {ctx₁ ctx₂ : Ctx} (hr : ∀ name, ctx₁.record? name = ctx₂.record? name) :
    Std.evreqLayout ctx₁ = Std.evreqLayout ctx₂ := by
  unfold Std.evreqLayout; rw [hr]

theorem evFreeRequest_congr {ctx₁ ctx₂ : Ctx}
    (hr : ∀ name, ctx₁.record? name = ctx₂.record? name)
    (hp : ctx₁.mod.ptrBytes = ctx₂.mod.ptrBytes := by rfl) :
    Std.evFreeRequest ctx₁ = Std.evFreeRequest ctx₂ := by
  funext m req; unfold Std.evFreeRequest; rw [loadPtrAt_congr hr hp, evFreeHeaders_congr hr hp]

theorem evSendReply_congr {ctx₁ ctx₂ : Ctx}
    (hr : ∀ name, ctx₁.record? name = ctx₂.record? name)
    (hp : ctx₁.mod.ptrBytes = ctx₂.mod.ptrBytes := by rfl) :
    Std.evSendReply ctx₁ = Std.evSendReply ctx₂ := by
  funext m req reason buf; unfold Std.evSendReply
  rw [evreqLayout_congr hr, loadPtrAt_congr hr hp, typedLoad_congr hr hp, typedStore_congr hr hp, evFreeRequest_congr hr hp]

/-! ### Operation, Block, Region, and Call Congruence -/

def isGlobalLookupOp : Op → Bool
  | .getGlobal .. | .vtableAddressPoint .. | .vttGlobalAddr ..
  | .const _ _ (.globalAddr ..) | .const _ _ (.vtableAddr ..) | .const _ _ (.array _) | .const _ _ (.record _) => true
  | _ => false

def isNonGlobalConst : Const → Bool
  | .globalAddr .. | .vtableAddr .. | .array _ | .record _ => false
  | _ => true

theorem constVal_non_globalAddr {ctx₁ ctx₂ : Ctx}
    (hr : ∀ name, ctx₁.record? name = ctx₂.record? name)
    (ty : Ty) (c : Const)
    (hc : isNonGlobalConst c = true) :
    ctx₁.constVal 32 ty c = ctx₂.constVal 32 ty c := by
  cases c <;> try (cases hc; done)
  all_goals (cases ty <;> try rfl)
  all_goals (try (rename_i fk; cases fk <;> rfl))
  all_goals (try (rename_i ety _; cases ety <;> rfl))
  all_goals (simp only [Ctx.constVal, zeroVal_congr hr])

def isSimpleNonGlobalCast : CastKind → Bool
  | .intToPtr | .ptrToInt => false
  | _ => true

def isSimpleNonGlobalOp (op : Op) : Bool :=
  match op with
  | .const _ _ (.globalAddr ..) | .const _ _ (.vtableAddr ..) | .const _ _ (.array _) | .const _ _ (.record _) => false
  | .cast _ k _ src _ =>
    isSimpleNonGlobalCast k && (match src with | .array .. => false | _ => true)
  | .cmp _ k _ _ (.ptr _) => (k == .eq || k == .ne)
  | .const .. | .alloca .. | .load .. | .retLoad .. | .store .. | .copy ..
  | .getMember .. | .getElement .. | .ptrStride .. | .ptrDiff .. | .blockAddress ..
  | .baseClassAddr .. | .derivedClassAddr .. | .vtableGetVptr .. | .vtableGetVirtualFnAddr ..
  | .extractMember .. | .binop .. | .fbinop .. | .fmuladd .. | .shift ..
  | .unop .. | .fneg .. | .fmath .. | .isFpClass .. | .bitCount .. | .isConstant ..
  | .getBitfield .. | .setBitfield .. | .bitOp .. | .rotate .. | .copysign .. | .fminmax ..
  | .prefetch .. | .allocaN .. | .stackSave .. | .stackRestore .. | .vaCopy ..
  | .arithOverflow .. | .iabs .. | .atomicFetch .. | .vaStart .. | .vaEnd .. | .vaArg ..
  | .vaBox .. | .vaEndCheck | .fail .. | .fitsCheck ..
  | .unionMember .. | .cmp .. | .select .. => true
  | _ => false

theorem evalSimple_cast_congr {ctx₁ ctx₂ : Ctx}
    (hr : ∀ name, ctx₁.record? name = ctx₂.record? name)
    (hp : ctx₁.mod.ptrBytes = ctx₂.mod.ptrBytes)
    (hcxx : ctx₁.mod.cxx = ctx₂.mod.cxx := by rfl)
    {r : VId} {k : CastKind} {a : VId} {src dst : Ty}
    (hk : isSimpleNonGlobalCast k = true)
    (_hsrc : (match src with | .array .. => false | _ => true) = true)
    (σ : State) :
    evalSimple ctx₁ (.cast r k a src dst) σ = evalSimple ctx₂ (.cast r k a src dst) σ := by
  have hec_k : ∀ m, evalCast ctx₁ m k = evalCast ctx₂ m k := by
    intro m; funext x d
    unfold evalCast
    cases k <;> try (cases hk; done)
    case arrayToPtrDecay =>
      cases x <;> try rfl
      rename_i p; cases p <;> rfl
    case floating =>
      cases x <;> cases d <;> try rfl
      rename_i fk; cases fk <;> rfl
    all_goals (cases x <;> cases d <;> rfl)
  have hvc_k : ∀ m, vecCast ctx₁ m k = vecCast ctx₂ m k := by
    intro m; funext xs se de n; unfold vecCast; rw [hec_k]
  have hvts_k : ∀ m, vecToScalar ctx₁ m k = vecToScalar ctx₂ m k := by
    intro m; funext x xs se de; unfold vecToScalar; rw [hec_k]
  have hsc_k : ∀ m, scalarToVec ctx₁ m k = scalarToVec ctx₂ m k := by
    intro m; funext x se de n; unfold scalarToVec; rw [hec_k]
  have hdo_k : ∀ m, decayOne ctx₁ m k = decayOne ctx₂ m k := by
    intro m; funext x d; unfold decayOne; rw [hec_k]
  have hcv : ∀ m x, castVal ctx₁ m k x src dst = castVal ctx₂ m k x src dst := by
    intro m x; unfold castVal
    rw [hvc_k, hvts_k, hsc_k, hdo_k, hec_k]
  unfold evalSimple
  simp only [sizeAlign_congr hr hp, zeroVal_congr hr, initVal_congr hr,
    convertPtr_congr hr, castCheck_congr hr hp hcxx, hcv]

def isConstIntOrNull : Const → Bool
  | .int _ | .null => true
  | _ => false

theorem evalCmpB_of_int (ctx₁ ctx₂ : Ctx) (m : Mem) (k : CmpKind) (x : Val) (n : Int) :
    ctx₁.evalCmpB m k x (.int n) = ctx₂.evalCmpB m k x (.int n) := by
  unfold Ctx.evalCmpB; cases x <;> rfl

theorem evalCmpB_of_int_or_null (ctx₁ ctx₂ : Ctx) (m : Mem) (k : CmpKind) (x y : Val)
    (hk : (k == .eq || k == .ne) = true)
    (hy : (∃ n, y = .int n) ∨ (∃ b, y = .bool b) ∨ y = .ptr .null) :
    ctx₁.evalCmpB m k x y = ctx₂.evalCmpB m k x y := by
  rcases hy with ⟨n, rfl⟩ | ⟨b, rfl⟩ | rfl
  · exact evalCmpB_of_int ctx₁ ctx₂ m k x n
  · unfold Ctx.evalCmpB; cases x <;> rfl
  · simp only [Bool.or_eq_true, beq_iff_eq] at hk
    unfold Ctx.evalCmpB
    cases x <;> try rfl
    rename_i p
    rcases hk with rfl | rfl <;> cases p <;> rfl

theorem constVal_int_or_null {ctx : Ctx} {ty : Ty} {c : Const} {v : Val}
    (hc : isConstIntOrNull c = true)
    (hv : ctx.constVal 32 ty c = some v) :
    (∃ n, v = .int n) ∨ (∃ b, v = .bool b) ∨ v = .ptr .null := by
  cases c <;> try cases hc
  · cases ty <;> try cases hv
    · simp only [Ctx.constVal] at hv
      split at hv <;> cases hv
      exact Or.inl ⟨_, rfl⟩
    · exact Or.inr (Or.inl ⟨_, rfl⟩)
  · cases ty <;> cases hv
    all_goals exact Or.inr (Or.inr rfl)

theorem evalOp_cmp_of_int_or_null (ctx₁ ctx₂ : Ctx)
    {r_cmp : VId} {k : CmpKind} {r_a r_c : VId} {ty : Ty} {σ : State}
    (hk : (k == .eq || k == .ne) = true)
    (hy : (∃ n, σ.env r_c = some (.int n)) ∨ (∃ b, σ.env r_c = some (.bool b)) ∨ σ.env r_c = some (.ptr .null)) :
    evalOp ctx₁ (.cmp r_cmp k r_a r_c ty) σ = evalOp ctx₂ (.cmp r_cmp k r_a r_c ty) σ := by
  simp only [evalOp, evalSimple, State.get]
  rcases σ.env r_a with _ | va <;> try rfl
  rcases hy with ⟨n, hrc⟩ | ⟨b, hrc⟩ | hrc
  · rw [hrc]
    simp only [Res.ofOption_some, Res.ok_bind, Res.pure_eq, evalCmpB_of_int ctx₁ ctx₂]
  · rw [hrc]
    simp only [Res.ofOption_some, Res.ok_bind, Res.pure_eq,
      evalCmpB_of_int_or_null ctx₁ ctx₂ σ.mem k va (.bool b) hk (Or.inr (Or.inl ⟨b, rfl⟩))]
  · rw [hrc]
    simp only [Res.ofOption_some, Res.ok_bind, Res.pure_eq,
      evalCmpB_of_int_or_null ctx₁ ctx₂ σ.mem k va (.ptr .null) hk (Or.inr (Or.inr rfl))]

theorem evalOps_const_cmp_congr' {ctx₁ ctx₂ : Ctx}
    {r_c r_cmp r_a : VId} {ty ty_cmp : Ty} {c : Const} {k : CmpKind} {ops₁ ops₂ : List Op}
    (hc : isConstIntOrNull c = true)
    (hk : (k == .eq || k == .ne) = true)
    (hops : ∀ σ, evalOps ctx₁ ops₁ σ = evalOps ctx₂ ops₂ σ) (σ : State) :
    evalOps ctx₁ (.const r_c ty c :: .cmp r_cmp k r_a r_c ty_cmp :: ops₁) σ =
    evalOps ctx₂ (.const r_c ty c :: .cmp r_cmp k r_a r_c ty_cmp :: ops₂) σ := by
  have hcv_eq : ctx₁.constVal 32 ty c = ctx₂.constVal 32 ty c := by
    cases c <;> try cases hc
    all_goals (cases ty <;> rfl)
  rw [evalOps.eq_2, evalOps.eq_2]
  simp only [evalOp, evalSimple, hcv_eq]
  rcases hcv : ctx₂.constVal 32 ty c with _ | v
  · rfl
  · simp only [Res.ofOption_some, Res.ok_bind, Res.pure_eq]
    rw [evalOps.eq_2, evalOps.eq_2]
    have hrc : (∃ n, (σ.set r_c v).env r_c = some (.int n)) ∨
        (∃ b, (σ.set r_c v).env r_c = some (.bool b)) ∨
        (σ.set r_c v).env r_c = some (.ptr .null) := by
      rcases constVal_int_or_null hc hcv with ⟨n, rfl⟩ | ⟨b, rfl⟩ | rfl
      · exact Or.inl ⟨n, by simp only [State.set, upd_same]⟩
      · exact Or.inr (Or.inl ⟨b, by simp only [State.set, upd_same]⟩)
      · exact Or.inr (Or.inr (by simp only [State.set, upd_same]))
    rw [evalOp_cmp_of_int_or_null ctx₁ ctx₂ hk hrc]
    congr 1; funext ⟨s, σ'⟩; cases s <;> first | exact hops σ' | rfl

def isSimpleNonCmpOp (op : Op) : Bool :=
  match op with
  | .cmp .. => false
  | op => isSimpleNonGlobalOp op

theorem evalSimple_noncmp_congr {ctx₁ ctx₂ : Ctx}
    (hr : ∀ name, ctx₁.record? name = ctx₂.record? name)
    (hp : ctx₁.mod.ptrBytes = ctx₂.mod.ptrBytes)
    (hv : ctx₁.vtableSlot? = ctx₂.vtableSlot?)
    (hcxx : ctx₁.mod.cxx = ctx₂.mod.cxx := by rfl)
    {op : Op} (hop : isSimpleNonCmpOp op = true) (σ : State) :
    evalSimple ctx₁ op σ = evalSimple ctx₂ op σ := by
  cases op <;> try (cases hop; done)
  case const r ty c =>
    have hc : isNonGlobalConst c = true := by
      cases c <;> first | rfl | (cases hop; done)
    simp only [evalSimple, constVal_non_globalAddr hr ty c hc]
  case cast r k a src dst =>
    simp only [isSimpleNonCmpOp, isSimpleNonGlobalOp, Bool.and_eq_true] at hop
    exact evalSimple_cast_congr hr hp hcxx hop.1 hop.2 σ
  all_goals
    try simp only [evalSimple, initVal_congr hr, zeroVal_congr hr, sizeAlign_congr hr hp,
      loadPtr_congr hr hv hp, typedLoad_congr hr hp, typedStore_congr hr hp, record?_congr hr,
      memberPath_congr hr hp, fromActive_congr hr hp,
      stride?_congr hr hp, diff?_congr hr hp, basePath_congr hr hp, vptrPath_congr hr,
      vptrClass?_congr hr, bfPlaced?_congr hr hp, bfLoadBytes_congr hr hp,
      bfLoadBytes0_congr hr hp, bfStoreBytes_congr hr hp, unionView?_congr hr hp,
      posAligned_congr hr hp, hcxx]

theorem evalOp_simple_congr {ctx₁ ctx₂ : Ctx}
    (hr : ∀ name, ctx₁.record? name = ctx₂.record? name)
    (hp : ctx₁.mod.ptrBytes = ctx₂.mod.ptrBytes)
    (hv : ctx₁.vtableSlot? = ctx₂.vtableSlot?)
    (hcxx : ctx₁.mod.cxx = ctx₂.mod.cxx := by rfl)
    {op : Op} (hop : isSimpleNonCmpOp op = true) (σ : State) :
    evalOp ctx₁ op σ = evalOp ctx₂ op σ := by
  cases op <;> try (cases hop; done)
  all_goals simp only [evalOp, evalSimple_noncmp_congr hr hp hv hcxx hop]

def isCtxFreeTerminatorOp : Op → Bool
  | .yield .. | .condition .. | .brk | .cont | .goto .. | .indirectGoto .. | .label ..
  | .asmBarrier | .asmTied .. | .ret .. | .br .. | .brcond .. | .throw .. | .resume ..
  | .trap | .unreachable | .ehTerminate .. | .case .. | .unknown .. => true
  | _ => false

theorem evalOp_terminator_congr {ctx₁ ctx₂ : Ctx}
    {op : Op} (hop : isCtxFreeTerminatorOp op = true) (σ : State) :
    evalOp ctx₁ op σ = evalOp ctx₂ op σ := by
  cases op <;> try (cases hop; done)
  case ret r => cases r <;> simp only [evalOp]
  case throw obj _ ti => cases obj <;> cases ti <;> simp only [evalOp]
  all_goals simp only [evalOp]

theorem evalOp_getGlobal_congr {ctx₁ ctx₂ : Ctx} {r : VId} {sym : String} {ty : Ty} {b : Nat}
    (ha₁ : ctx₁.gaddr sym = some b) (ha₂ : ctx₂.gaddr sym = some b) (σ : State) :
    evalOp ctx₁ (.getGlobal r sym ty) σ = evalOp ctx₂ (.getGlobal r sym ty) σ := by
  simp only [evalOp, evalSimple, Ctx.symAddr?, ha₁, ha₂]

theorem evalOp_getGlobal_fn_congr {ctx₁ ctx₂ : Ctx} {r : VId} {sym : String} {ty : Ty} {fd₁ fd₂ : FuncDecl}
    (ha₁ : ctx₁.gaddr sym = none) (hf₁ : ctx₁.mod.findFunc? sym = some fd₁)
    (ha₂ : ctx₂.gaddr sym = none) (hf₂ : ctx₂.mod.findFunc? sym = some fd₂) (σ : State) :
    evalOp ctx₁ (.getGlobal r sym ty) σ = evalOp ctx₂ (.getGlobal r sym ty) σ := by
  simp only [evalOp, evalSimple, Ctx.symAddr?, ha₁, ha₂, hf₁, hf₂, List.isEmpty, Option.isSome, Bool.true_and]

theorem evalOp_scope_congr {ctx₁ ctx₂ : Ctx} {res : Option VId} {b₁ b₂ : Region}
    (hb : ∀ σ, evalRegion ctx₁ b₁ [] σ = evalRegion ctx₂ b₂ [] σ) (σ : State) :
    evalOp ctx₁ (.scope res b₁) σ = evalOp ctx₂ (.scope res b₂) σ := by
  simp only [evalOp, hb]

theorem evalOp_ifOp_congr {ctx₁ ctx₂ : Ctx} {c : VId} {t₁ t₂ el₁ el₂ : Region}
    (ht : ∀ σ, evalRegion ctx₁ t₁ [] σ = evalRegion ctx₂ t₂ [] σ)
    (hel : ∀ σ, evalRegion ctx₁ el₁ [] σ = evalRegion ctx₂ el₂ [] σ) (σ : State) :
    evalOp ctx₁ (.ifOp c t₁ el₁) σ = evalOp ctx₂ (.ifOp c t₂ el₂) σ := by
  simp only [evalOp]
  congr 1; funext b; cases b <;> simp only [Bool.false_eq_true, ↓reduceIte, hel, ht]

theorem callsDestructor_single_call {ctx₁ ctx₂ : Ctx} {loc₁ loc₂ : Loc} {res : Option VId}
    {s : String} {args : List VId} {argTys : List Ty} {retTy : Ty} {nt : Bool} {ops : List Op}
    {fd₁ fd₂ : FuncDecl}
    (hf₁ : ctx₁.mod.findFunc? s = some fd₁) (hs₁ : fd₁.special = .dtor)
    (hf₂ : ctx₂.mod.findFunc? s = some fd₂) (hs₂ : fd₂.special = .dtor) :
    callsDestructor ctx₁ (.mk [.mk [] (.call loc₁ res (.direct s) args argTys retTy nt :: ops)]) =
    callsDestructor ctx₂ (.mk [.mk [] (.call loc₂ res (.direct s) args argTys retTy nt :: ops)]) := by
  simp only [callsDestructor, List.any_cons, hf₁, hf₂, Option.any, hs₁, hs₂, beq_self_eq_true, Bool.true_or]

theorem evalOp_cleanupScope_congr {ctx₁ ctx₂ : Ctx} {k : CleanupKind} {b₁ b₂ cl₁ cl₂ : Region}
    (hb : ∀ σ, evalRegion ctx₁ b₁ [] σ = evalRegion ctx₂ b₂ [] σ)
    (hcl : ∀ σ, evalRegion ctx₁ cl₁ [] σ = evalRegion ctx₂ cl₂ [] σ)
    (hcd : callsDestructor ctx₁ cl₁ = callsDestructor ctx₂ cl₂) (σ : State) :
    evalOp ctx₁ (.cleanupScope k b₁ cl₁) σ = evalOp ctx₂ (.cleanupScope k b₂ cl₂) σ := by
  simp only [evalOp, hb, hcd]
  congr 1; funext ⟨e, σ1⟩
  cases e <;> try rfl
  all_goals (try dsimp only; split <;> first | rw [hcl] | rfl)

theorem evalOp_call_direct_congr {ctx₁ ctx₂ : Ctx}
    {loc₁ loc₂ : Loc} {res : Option VId} {sym : String} {args : List VId} {argTys : List Ty} {retTy : Ty} {nothrow : Bool}
    (hcall : ∀ vs m, evalCall ctx₁ sym vs m = evalCall ctx₂ sym vs m) (σ : State) :
    evalOp ctx₁ (.call loc₁ res (.direct sym) args argTys retTy nothrow) σ =
    evalOp ctx₂ (.call loc₂ res (.direct sym) args argTys retTy nothrow) σ := by
  simp only [evalOp, adjustThis, Res.pure_eq, Res.ok_bind]
  congr 1; funext vs; rw [hcall]

theorem evalOps_nil_congr (ctx₁ ctx₂ : Ctx) (σ : State) :
    evalOps ctx₁ [] σ = evalOps ctx₂ [] σ := by
  rw [evalOps.eq_1, evalOps.eq_1]

theorem evalOps_cons_congr {ctx₁ ctx₂ : Ctx} {op₁ op₂ : Op} {ops₁ ops₂ : List Op}
    (hop : ∀ σ, evalOp ctx₁ op₁ σ = evalOp ctx₂ op₂ σ)
    (hops : ∀ σ, evalOps ctx₁ ops₁ σ = evalOps ctx₂ ops₂ σ) (σ : State) :
    evalOps ctx₁ (op₁ :: ops₁) σ = evalOps ctx₂ (op₂ :: ops₂) σ := by
  rw [evalOps.eq_2, evalOps.eq_2, hop]
  congr 1; funext ⟨s, σ'⟩; cases s <;> first | exact hops σ' | rfl

theorem evalBlock_single_congr {ctx₁ ctx₂ : Ctx} {params : List VId} {ops₁ ops₂ : List Op}
    (hl₁ : blockNoLabel [.mk params ops₁] = true)
    (hl₂ : blockNoLabel [.mk params ops₂] = true)
    (hmj : (ops₁.any opMayJump) = false)
    (hops : ∀ σ, evalOps ctx₁ ops₁ σ = evalOps ctx₂ ops₂ σ)
    (args : List Val) (σ : State) :
    evalBlock ctx₁ [.mk params ops₁] 0 args σ = evalBlock ctx₂ [.mk params ops₂] 0 args σ := by
  rw [evalBlock_zero, evalBlock_zero]
  congr 1; funext σ₁
  have hnj : ∀ j vs σ', evalOps ctx₁ ops₁ σ₁ ≠ .ok (.jump j vs, σ') := by
    intro j vs σ' hok
    have h1 : (evalOps ctx₁ ops₁ σ₁).holds (fun _ => True) := by rw [hok]; trivial
    have h2 := evalOps_not_jump hmj h1
    rw [hok] at h2
    exact h2.1 j vs rfl
  rw [hops σ₁] at hnj ⊢
  apply Res.bind_congr_ok
  rintro ⟨s, σ₂⟩ hok
  cases s with
  | exit e =>
    cases e <;> try rfl
    dsimp only
    rw [labelBlock?_of_noLabel hl₁, labelBlock?_of_noLabel hl₂]
  | jump j vs => exact False.elim (hnj j vs σ₂ hok)
  | next => rfl

theorem evalRegion_single_congr {ctx₁ ctx₂ : Ctx} {params : List VId} {ops₁ ops₂ : List Op}
    (hl₁ : blockNoLabel [.mk params ops₁] = true)
    (hl₂ : blockNoLabel [.mk params ops₂] = true)
    (hmj : (ops₁.any opMayJump) = false)
    (hops : ∀ σ, evalOps ctx₁ ops₁ σ = evalOps ctx₂ ops₂ σ)
    (args : List Val) (σ : State) :
    evalRegion ctx₁ (.mk [.mk params ops₁]) args σ = evalRegion ctx₂ (.mk [.mk params ops₂]) args σ := by
  rw [evalRegion.eq_2, evalRegion.eq_2, evalBlock_single_congr hl₁ hl₂ hmj hops]

theorem evalRegion_nil_congr (ctx₁ ctx₂ : Ctx) (args : List Val) (σ : State) :
    evalRegion ctx₁ (.mk []) args σ = evalRegion ctx₂ (.mk []) args σ := by
  rw [evalRegion.eq_1, evalRegion.eq_1]

/-! ### `dropEnv` and `cerr` Line-Number Congruence -/

def dropEnv (r : Res (Step × State)) : Res (Step × Mem) :=
  r >>= fun (s, σ') => .ok (s, σ'.mem)

theorem evalRegion_congr_of_dropEnv {ctx₁ ctx₂ : Ctx} {ops₁ ops₂ : List Op}
    (hl₁ : blockNoLabel [.mk [] ops₁] = true)
    (hl₂ : blockNoLabel [.mk [] ops₂] = true)
    (hmj₁ : (ops₁.any opMayJump) = false)
    (hmj₂ : (ops₂.any opMayJump) = false)
    (h : ∀ σ, dropEnv (evalOps ctx₁ ops₁ σ) = dropEnv (evalOps ctx₂ ops₂ σ))
    (σ : State) :
    evalRegion ctx₁ (.mk [.mk [] ops₁]) [] σ = evalRegion ctx₂ (.mk [.mk [] ops₂]) [] σ := by
  have conv : ∀ (ctx : Ctx) (ops : List Op),
      blockNoLabel [.mk [] ops] = true → (ops.any opMayJump) = false →
      evalRegion ctx (.mk [.mk [] ops]) [] σ =
      (dropEnv (evalOps ctx ops σ) >>= fun (s, m') =>
        match s with
        | .exit e => pure (e, { mem := e.leaveMem m' σ.mem.next, env := σ.env, names := σ.names })
        | _ => .ub "fell off the end of a block") := by
    intro ctx ops hl hmj
    rw [evalRegion.eq_2, evalBlock_zero]
    simp only [State.bindArgs, Res.ok_bind, dropEnv, bind_assoc]
    have hnj : ∀ j vs σ', evalOps ctx ops σ ≠ .ok (.jump j vs, σ') := by
      intro j vs σ' hok
      have h1 : (evalOps ctx ops σ).holds (fun _ => True) := by rw [hok]; trivial
      have h2 := evalOps_not_jump hmj h1
      rw [hok] at h2
      exact h2.1 j vs rfl
    apply Res.bind_congr_ok
    rintro ⟨s, σ'⟩ hok
    cases s with
    | exit e =>
      cases e <;> try rfl
      simp only [Res.ok_bind, Res.pure_eq, labelBlock?_of_noLabel hl]
    | jump j vs => exact False.elim (hnj j vs σ' hok)
    | next => rfl
  rw [conv ctx₁ ops₁ hl₁ hmj₁, conv ctx₂ ops₂ hl₂ hmj₂, h σ]

theorem dropEnv_cons_congr {ctx₁ ctx₂ : Ctx} {op₁ op₂ : Op} {ops₁ ops₂ : List Op}
    (hop : ∀ σ, evalOp ctx₁ op₁ σ = evalOp ctx₂ op₂ σ)
    (hops : ∀ σ, dropEnv (evalOps ctx₁ ops₁ σ) = dropEnv (evalOps ctx₂ ops₂ σ)) (σ : State) :
    dropEnv (evalOps ctx₁ (op₁ :: ops₁) σ) = dropEnv (evalOps ctx₂ (op₂ :: ops₂) σ) := by
  simp only [dropEnv, evalOps.eq_2, bind_assoc, hop]
  congr 1; funext ⟨s, σ'⟩
  cases s <;> first | exact hops σ' | rfl

theorem runModel_ostreamOut0 (ctx : Ctx) (os : Ptr) (v : Val) (m : Mem) :
    Std.runModel ctx (.ostreamOut 0) [.ptr os, v] m =
      if (match os with | .loc b _ => (m.live? b).isSome | _ => false) = true then
        .ok (.ret (some (.ptr os)), m)
      else .ub "operator<<: the stream is not an object" := by
  cases os <;> first | rfl | (dsimp only [Std.runModel]; cases (m.live? _).isSome <;> rfl)

theorem dropEnv_cerrLineTail_congr {ctx₁ ctx₂ : Ctx}
    {fd_i1 fd_i2 fd_c1 fd_c2 : FuncDecl}
    (hfi1 : ctx₁.mod.findFunc? "_ZNSolsEi" = some fd_i1) (hmi1 : fd_i1.model = some (.ostreamOut 0))
    (hfi2 : ctx₂.mod.findFunc? "_ZNSolsEi" = some fd_i2) (hmi2 : fd_i2.model = some (.ostreamOut 0))
    (hfc1 : ctx₁.mod.findFunc? "_ZStlsISt11char_traitsIcEERSt13basic_ostreamIcT_ES5_c" = some fd_c1) (hmc1 : fd_c1.model = some (.ostreamOut 0))
    (hfc2 : ctx₂.mod.findFunc? "_ZStlsISt11char_traitsIcEERSt13basic_ostreamIcT_ES5_c" = some fd_c2) (hmc2 : fd_c2.model = some (.ostreamOut 0))
    (loc₁ loc₂ : Loc) (r_line r_os r_out1 r_nl r_out2 : VId)
    (hne1 : r_os ≠ r_line) (hne2 : r_out1 ≠ r_nl)
    (L₁ L₂ : Int) (hL₁ : inRange true 32 L₁ = true) (hL₂ : inRange true 32 L₂ = true)
    (σ : State) :
    dropEnv (evalOps ctx₁
      [.const r_line (.int true 32) (.int L₁),
       .call loc₁ (some r_out1) (.direct "_ZNSolsEi") [r_os, r_line] [(.ptr (.record "std::basic_ostream<char, std::char_traits<char>>")), (.int true 32)] (.ptr (.record "std::basic_ostream<char, std::char_traits<char>>")) false,
       .const r_nl (.int true 8) (.int 10),
       .call loc₁ (some r_out2) (.direct "_ZStlsISt11char_traitsIcEERSt13basic_ostreamIcT_ES5_c") [r_out1, r_nl] [(.ptr (.record "std::basic_ostream<char, std::char_traits<char>>")), (.int true 8)] (.ptr (.record "std::basic_ostream<char, std::char_traits<char>>")) false] σ) =
    dropEnv (evalOps ctx₂
      [.const r_line (.int true 32) (.int L₂),
       .call loc₂ (some r_out1) (.direct "_ZNSolsEi") [r_os, r_line] [(.ptr (.record "std::basic_ostream<char, std::char_traits<char>>")), (.int true 32)] (.ptr (.record "std::basic_ostream<char, std::char_traits<char>>")) false,
       .const r_nl (.int true 8) (.int 10),
       .call loc₂ (some r_out2) (.direct "_ZStlsISt11char_traitsIcEERSt13basic_ostreamIcT_ES5_c") [r_out1, r_nl] [(.ptr (.record "std::basic_ostream<char, std::char_traits<char>>")), (.int true 8)] (.ptr (.record "std::basic_ostream<char, std::char_traits<char>>")) false] σ) := by
  have eval4 : ∀ (ctx : Ctx) (fd_i fd_c : FuncDecl) (loc : Loc) (L : Int),
      ctx.mod.findFunc? "_ZNSolsEi" = some fd_i → fd_i.model = some (.ostreamOut 0) →
      ctx.mod.findFunc? "_ZStlsISt11char_traitsIcEERSt13basic_ostreamIcT_ES5_c" = some fd_c → fd_c.model = some (.ostreamOut 0) →
      inRange true 32 L = true →
      dropEnv (evalOps ctx
        [.const r_line (.int true 32) (.int L),
         .call loc (some r_out1) (.direct "_ZNSolsEi") [r_os, r_line] [(.ptr (.record "std::basic_ostream<char, std::char_traits<char>>")), (.int true 32)] (.ptr (.record "std::basic_ostream<char, std::char_traits<char>>")) false,
         .const r_nl (.int true 8) (.int 10),
         .call loc (some r_out2) (.direct "_ZStlsISt11char_traitsIcEERSt13basic_ostreamIcT_ES5_c") [r_out1, r_nl] [(.ptr (.record "std::basic_ostream<char, std::char_traits<char>>")), (.int true 8)] (.ptr (.record "std::basic_ostream<char, std::char_traits<char>>")) false] σ) =
      match σ.env r_os with
      | some (.ptr os) =>
        if (match os with | .loc b _ => (σ.mem.live? b).isSome | _ => false) = true then
          .ok (.exit (.yield []), σ.mem)
        else .ub "operator<<: the stream is not an object"
      | some _ => .ub "library model called with unexpected arguments"
      | none => .ub "use of undefined SSA value" := by
    intro ctx fd_i fd_c loc L hfi hmi hfc hmc hL
    have h10 : inRange true 8 10 = true := by decide
    simp only [dropEnv, evalOps.eq_2, evalOp, evalSimple, Ctx.constVal, hL, h10, ↓reduceIte,
      Res.ofOption_some, Res.ok_bind, Res.pure_eq, bind_assoc, List.mapM, List.mapM.loop,
      State.get, State.set, upd_ne _ _ _ _ hne1, upd_same]
    rcases hros : σ.env r_os with _ | vos
    · rfl
    · simp only [Res.ofOption_some, Res.ok_bind, List.reverse, List.reverseAux,
        adjustThis, evalCall_model hfi hmi]
      cases vos <;> try rfl
      rename_i pos
      rw [runModel_ostreamOut0]
      cases pos <;> try rfl
      rename_i b path
      by_cases hlive : (σ.mem.live? b).isSome = true
      · simp only [hlive, ↓reduceIte, Res.ofOption_some, Res.ok_bind, Option.toList,
          State.setResults, State.withMem, State.set_env, State.set_mem, upd_ne _ _ _ _ hne2, upd_same,
          evalCall_model hfc hmc, runModel_ostreamOut0, evalOps.eq_1]
      · simp only [hlive, Bool.false_eq_true, ↓reduceIte, Res.ub_bind]
  rw [eval4 ctx₁ fd_i1 fd_c1 loc₁ L₁ hfi1 hmi1 hfc1 hmc1 hL₁,
      eval4 ctx₂ fd_i2 fd_c2 loc₂ L₂ hfi2 hmi2 hfc2 hmc2 hL₂]

/-! ### Library Model Call Congruence -/

theorem evalCall_model_congr {ctx₁ ctx₂ : Ctx}
    {sym : String} {fd₁ fd₂ : FuncDecl} {mdl : Model}
    (hf₁ : ctx₁.mod.findFunc? sym = some fd₁) (hm₁ : fd₁.model = some mdl)
    (hf₂ : ctx₂.mod.findFunc? sym = some fd₂) (hm₂ : fd₂.model = some mdl)
    (hmdl : ∀ vs m, Std.runModel ctx₁ mdl vs m = Std.runModel ctx₂ mdl vs m)
    (vs : List Val) (m : Mem) :
    evalCall ctx₁ sym vs m = evalCall ctx₂ sym vs m := by
  rw [evalCall_model hf₁ hm₁, evalCall_model hf₂ hm₂, hmdl]

theorem evalCall_ext_congr {ctx₁ ctx₂ : Ctx} {sym : String} {fd₁ fd₂ : FuncDecl}
    (hf₁ : ctx₁.mod.findFunc? sym = some fd₁) (hm₁ : fd₁.model = none) (hb₁ : fd₁.body = none)
    (hf₂ : ctx₂.mod.findFunc? sym = some fd₂) (hm₂ : fd₂.model = none) (hb₂ : fd₂.body = none)
    (vs : List Val) (m : Mem) :
    evalCall ctx₁ sym vs m = evalCall ctx₂ sym vs m := by
  rw [evalCall.eq_1, evalCall.eq_1, hf₁, hf₂]; dsimp only; rw [hm₁, hm₂, hb₁, hb₂]

theorem evalCall_body_congr {ctx₁ ctx₂ : Ctx} {sym : String} {fd₁ fd₂ : FuncDecl} {body₁ body₂ : Region}
    (hf₁ : ctx₁.mod.findFunc? sym = some fd₁) (hm₁ : fd₁.model = none) (hb₁ : fd₁.body = some body₁)
    (hf₂ : ctx₂.mod.findFunc? sym = some fd₂) (hm₂ : fd₂.model = none) (hb₂ : fd₂.body = some body₂)
    (hnt : fd₁.nothrow = fd₂.nothrow)
    (hs₁ : fd₁.special ≠ .dtor := by decide) (hs₂ : fd₂.special ≠ .dtor := by decide)
    (hbody : ∀ args σ, evalRegion ctx₁ body₁ args σ = evalRegion ctx₂ body₂ args σ)
    (vs : List Val) (m : Mem) :
    evalCall ctx₁ sym vs m = evalCall ctx₂ sym vs m := by
  rw [evalCall_body hf₁ hm₁ hb₁ hs₁, evalCall_body hf₂ hm₂ hb₂ hs₂]
  congr 1
  · exact hbody vs _
  · funext ⟨e, σ⟩; cases e <;> simp only [hnt]

theorem runModel_evhttpAddHeader_congr {ctx₁ ctx₂ : Ctx}
    (hr : ∀ name, ctx₁.record? name = ctx₂.record? name)
    (hp : ctx₁.mod.ptrBytes = ctx₂.mod.ptrBytes := by rfl)
    (vs : List Val) (m : Mem) :
    Std.runModel ctx₁ .evhttpAddHeader vs m = Std.runModel ctx₂ .evhttpAddHeader vs m := by
  rcases vs with _ | ⟨v0, vs⟩; · rfl
  cases v0 <;> try rfl
  rcases vs with _ | ⟨v1, vs⟩; · rfl
  cases v1 <;> try rfl
  rcases vs with _ | ⟨v2, vs⟩; · rfl
  cases v2 <;> try rfl
  rcases vs with _ | ⟨_, _⟩ <;> try rfl
  dsimp only [Std.runModel]; rw [evAddHeader_congr hr hp]

theorem runModel_evbufferAdd_congr {ctx₁ ctx₂ : Ctx}
    (hr : ∀ name, ctx₁.record? name = ctx₂.record? name)
    (hp : ctx₁.mod.ptrBytes = ctx₂.mod.ptrBytes)
    (vs : List Val) (m : Mem) :
    Std.runModel ctx₁ .evbufferAdd vs m = Std.runModel ctx₂ .evbufferAdd vs m := by
  rcases vs with _ | ⟨v0, vs⟩; · rfl
  cases v0 <;> try rfl
  rcases vs with _ | ⟨v1, vs⟩; · rfl
  cases v1 <;> try rfl
  rcases vs with _ | ⟨v2, vs⟩; · rfl
  cases v2 <;> try rfl
  rcases vs with _ | ⟨_, _⟩ <;> try rfl
  dsimp only [Std.runModel]; rw [evbufferAdd_congr hr hp]

theorem runModel_evhttpSendReply_congr {ctx₁ ctx₂ : Ctx}
    (hr : ∀ name, ctx₁.record? name = ctx₂.record? name)
    (hp : ctx₁.mod.ptrBytes = ctx₂.mod.ptrBytes := by rfl)
    (vs : List Val) (m : Mem) :
    Std.runModel ctx₁ .evhttpSendReply vs m = Std.runModel ctx₂ .evhttpSendReply vs m := by
  rcases vs with _ | ⟨v0, vs⟩; · rfl
  cases v0 <;> try rfl
  rcases vs with _ | ⟨v1, vs⟩; · rfl
  cases v1 <;> try rfl
  rcases vs with _ | ⟨v2, vs⟩; · rfl
  cases v2 <;> try rfl
  rcases vs with _ | ⟨v3, vs⟩; · rfl
  cases v3 <;> try rfl
  rcases vs with _ | ⟨_, _⟩ <;> try rfl
  dsimp only [Std.runModel]; rw [evSendReply_congr hr hp]

theorem runModel_evbufferNew_congr (ctx₁ ctx₂ : Ctx) (vs : List Val) (m : Mem) :
    Std.runModel ctx₁ .evbufferNew vs m = Std.runModel ctx₂ .evbufferNew vs m := by
  rcases vs with _ | ⟨_, _⟩ <;> rfl

theorem runModel_evbufferFree_congr (ctx₁ ctx₂ : Ctx) (vs : List Val) (m : Mem) :
    Std.runModel ctx₁ .evbufferFree vs m = Std.runModel ctx₂ .evbufferFree vs m := by
  rcases vs with _ | ⟨v0, vs⟩; · rfl
  cases v0 <;> try rfl
  rcases vs with _ | ⟨_, _⟩ <;> rfl

theorem runModel_ostreamOut_congr (ctx₁ ctx₂ : Ctx) (chk : Nat)
    (hchk : chk ≠ 2 := by decide) (vs : List Val) (m : Mem) :
    Std.runModel ctx₁ (.ostreamOut chk) vs m = Std.runModel ctx₂ (.ostreamOut chk) vs m := by
  rcases vs with _ | ⟨v0, rest⟩; · rfl
  cases v0 <;> try rfl
  rename_i pos
  cases pos <;> try rfl
  cases chk with
  | zero => rfl
  | succ n =>
    cases n with
    | zero =>
      rcases rest with _ | ⟨v1, rest2⟩; · rfl
      cases v1 <;> try rfl
      cases rest2 <;> rfl
    | succ n =>
      cases n with
      | zero => exact False.elim (hchk rfl)
      | succ _ => rfl

theorem runModel_eventBaseLoopbreak_congr (ctx₁ ctx₂ : Ctx) (vs : List Val) (m : Mem) :
    Std.runModel ctx₁ .eventBaseLoopbreak vs m = Std.runModel ctx₂ .eventBaseLoopbreak vs m := by
  rcases vs with _ | ⟨v0, vs⟩; · rfl
  cases v0 <;> try rfl
  rename_i p
  rcases vs with _ | ⟨_, _⟩ <;> try (cases p <;> rfl)

theorem runModel_pthreadSelf_congr (ctx₁ ctx₂ : Ctx) (vs : List Val) (m : Mem) :
    Std.runModel ctx₁ .pthreadSelf vs m = Std.runModel ctx₂ .pthreadSelf vs m := by
  rcases vs with _ | ⟨_, _⟩ <;> rfl

theorem runModel_pthreadEqual_congr (ctx₁ ctx₂ : Ctx) (vs : List Val) (m : Mem) :
    Std.runModel ctx₁ .pthreadEqual vs m = Std.runModel ctx₂ .pthreadEqual vs m := by
  rcases vs with _ | ⟨v0, vs⟩; · rfl
  cases v0 <;> try rfl
  rcases vs with _ | ⟨v1, vs⟩; · rfl
  cases v1 <;> try rfl
  rcases vs with _ | ⟨_, _⟩ <;> rfl

theorem runModel_operatorDelete_congr (ctx₁ ctx₂ : Ctx) (vs : List Val) (m : Mem) :
    Std.runModel ctx₁ .operatorDelete vs m = Std.runModel ctx₂ .operatorDelete vs m := by
  rcases vs with _ | ⟨v0, vs⟩; · rfl
  cases v0 <;> try rfl
  rcases vs with _ | ⟨v1, vs⟩; · rfl
  cases v1 <;> try rfl
  rcases vs with _ | ⟨v2, vs⟩; · rfl
  cases v2 <;> try rfl
  rcases vs with _ | ⟨_, _⟩ <;> rfl

theorem runModel_strDtor_congr {ctx₁ ctx₂ : Ctx}
    (hr : ∀ name, ctx₁.record? name = ctx₂.record? name)
    (hp : ctx₁.mod.ptrBytes = ctx₂.mod.ptrBytes := by rfl)
    (vs : List Val) (m : Mem) :
    Std.runModel ctx₁ .strDtor vs m = Std.runModel ctx₂ .strDtor vs m := by
  rcases vs with _ | ⟨v0, vs⟩; · rfl
  cases v0 <;> try rfl
  rcases vs with _ | ⟨_, _⟩ <;> try rfl
  dsimp only [Std.runModel]; rw [readVec_congr hr hp]

theorem runModel_uptrCtorPtr_congr (ctx₁ ctx₂ : Ctx) (e : Ty) (vs : List Val) (m : Mem) :
    Std.runModel ctx₁ (.uptrCtorPtr e) vs m = Std.runModel ctx₂ (.uptrCtorPtr e) vs m := by
  rcases vs with _ | ⟨v0, vs⟩; · rfl
  cases v0 <;> try rfl
  rcases vs with _ | ⟨v1, vs⟩; · rfl
  cases v1 <;> try rfl
  rcases vs with _ | ⟨_, _⟩ <;> rfl

theorem runModel_uptrDtor_congr (ctx₁ ctx₂ : Ctx) (e : Ty) (vs : List Val) (m : Mem) :
    Std.runModel ctx₁ (.uptrDtor e) vs m = Std.runModel ctx₂ (.uptrDtor e) vs m := by
  rcases vs with _ | ⟨v0, vs⟩; · rfl
  cases v0 <;> try rfl
  rcases vs with _ | ⟨_, _⟩ <;> rfl

theorem runModel_uptrGet_congr (ctx₁ ctx₂ : Ctx) (e : Ty) (vs : List Val) (m : Mem) :
    Std.runModel ctx₁ (.uptrGet e) vs m = Std.runModel ctx₂ (.uptrGet e) vs m := by
  rcases vs with _ | ⟨v0, vs⟩; · rfl
  cases v0 <;> try rfl
  rcases vs with _ | ⟨_, _⟩ <;> rfl

theorem runModel_uptrDeref_congr (ctx₁ ctx₂ : Ctx) (e : Ty) (vs : List Val) (m : Mem) :
    Std.runModel ctx₁ (.uptrDeref e) vs m = Std.runModel ctx₂ (.uptrDeref e) vs m := by
  rcases vs with _ | ⟨v0, vs⟩; · rfl
  cases v0 <;> try rfl
  rcases vs with _ | ⟨_, _⟩ <;> rfl

theorem runModel_uptrBool_congr (ctx₁ ctx₂ : Ctx) (e : Ty) (vs : List Val) (m : Mem) :
    Std.runModel ctx₁ (.uptrBool e) vs m = Std.runModel ctx₂ (.uptrBool e) vs m := by
  rcases vs with _ | ⟨v0, vs⟩; · rfl
  cases v0 <;> try rfl
  rcases vs with _ | ⟨_, _⟩ <;> rfl

theorem runModel_uptrRelease_congr (ctx₁ ctx₂ : Ctx) (e : Ty) (vs : List Val) (m : Mem) :
    Std.runModel ctx₁ (.uptrRelease e) vs m = Std.runModel ctx₂ (.uptrRelease e) vs m := by
  rcases vs with _ | ⟨v0, vs⟩; · rfl
  cases v0 <;> try rfl
  rcases vs with _ | ⟨_, _⟩ <;> rfl

theorem runModel_uptrReset_congr (ctx₁ ctx₂ : Ctx) (e : Ty) (vs : List Val) (m : Mem) :
    Std.runModel ctx₁ (.uptrReset e) vs m = Std.runModel ctx₂ (.uptrReset e) vs m := by
  rcases vs with _ | ⟨v0, vs⟩; · rfl
  cases v0 <;> try rfl
  rcases vs with _ | ⟨v1, vs⟩; · rfl
  cases v1 <;> try rfl
  rcases vs with _ | ⟨_, _⟩ <;> rfl

theorem runModel_stdMove_congr (ctx₁ ctx₂ : Ctx) (e : Ty) (vs : List Val) (m : Mem) :
    Std.runModel ctx₁ (.stdMove e) vs m = Std.runModel ctx₂ (.stdMove e) vs m := by
  rcases vs with _ | ⟨v0, vs⟩; · rfl
  cases v0 <;> try rfl
  rcases vs with _ | ⟨_, _⟩ <;> rfl

/-! ### Dead-Code Loop Elimination and Virtual Call Congruence -/

def isSimpleAnyOp : Op → Bool
  | .const .. | .alloca .. | .load .. | .retLoad .. | .store .. | .copy .. | .getMember .. | .getElement ..
  | .ptrStride .. | .ptrDiff .. | .getGlobal .. | .blockAddress .. | .baseClassAddr .. | .derivedClassAddr ..
  | .vtableAddressPoint .. | .vtableGetVptr .. | .vtableGetVirtualFnAddr ..
  | .extractMember .. | .binop .. | .fbinop .. | .fmuladd .. | .shift .. | .unop .. | .fneg ..
  | .fmath .. | .isFpClass .. | .bitCount .. | .isConstant .. | .getBitfield .. | .setBitfield ..
  | .bitOp .. | .rotate .. | .copysign .. | .fminmax .. | .prefetch .. | .allocaN .. | .stackSave ..
  | .stackRestore .. | .vaCopy ..
  | .arithOverflow .. | .iabs .. | .atomicFetch .. | .atomicXchg .. | .atomicCmpXchg .. | .vaStart ..
  | .vaEnd .. | .vaArg .. | .vaBox .. | .vaEndCheck | .fail .. | .fitsCheck .. | .unionMember ..
  | .cmp .. | .cast .. | .select .. | .allocException .. | .beginCatch .. | .endCatch ..
  | .initCatchParam .. | .assume .. => true
  | _ => false

theorem evalOp_eq_simple_any {ctx : Ctx} {op : Op} (h : isSimpleAnyOp op = true) (σ : State) :
    evalOp ctx op σ = (evalSimple ctx op σ >>= fun σ' => pure (.next, σ')) := by
  cases op <;> first | (cases h; done) | simp only [evalOp]

theorem evalCall_ext_eq {ctx : Ctx} {sym : String} {fd : FuncDecl}
    (hf : ctx.mod.findFunc? sym = some fd) (hm : fd.model = none) (hb : fd.body = none)
    (vs : List Val) (m : Mem) :
    evalCall ctx sym vs m = .ub ("call to an external function without a model: " ++ sym) := by
  rw [evalCall.eq_1, hf]; dsimp only; rw [hm, hb]

theorem not_ok_bind {α β : Type} {r : Res α} {f : α → Res β}
    (h : ∀ a, ∀ b, f a ≠ .ok b) (b : β) :
    (r >>= f) ≠ .ok b := by
  cases r with
  | ok a => exact h a b
  | ub _ => intro hc; cases hc
  | div => intro hc; cases hc

theorem evalOps_call_ext_dead {ctx₁ ctx₂ : Ctx} {fd₁ fd₂ : FuncDecl}
    {loc₁ loc₂ : Loc} {res : Option VId} {sym : String}
    {args : List VId} {argTys : List Ty} {retTy : Ty} {nothrow : Bool}
    {ops₁ ops₂ : List Op}
    (hf₁ : ctx₁.mod.findFunc? sym = some fd₁) (hm₁ : fd₁.model = none) (hb₁ : fd₁.body = none)
    (hf₂ : ctx₂.mod.findFunc? sym = some fd₂) (hm₂ : fd₂.model = none) (hb₂ : fd₂.body = none)
    (σ : State) :
    evalOps ctx₁ (.call loc₁ res (.direct sym) args argTys retTy nothrow :: ops₁) σ =
    evalOps ctx₂ (.call loc₂ res (.direct sym) args argTys retTy nothrow :: ops₂) σ := by
  rw [evalOps.eq_2, evalOps.eq_2]
  simp only [evalOp, adjustThis, evalCall_ext_eq hf₁ hm₁ hb₁, evalCall_ext_eq hf₂ hm₂ hb₂,
    Res.pure_eq, Res.ok_bind, Res.ub_bind, bind_assoc]

theorem evalOps_call_ext_not_ok {ctx : Ctx} {fd : FuncDecl}
    {loc : Loc} {res : Option VId} {sym : String}
    {args : List VId} {argTys : List Ty} {retTy : Ty} {nothrow : Bool}
    {ops : List Op}
    (hf : ctx.mod.findFunc? sym = some fd) (hm : fd.model = none) (hb : fd.body = none)
    (σ : State) (x : Step × State) :
    evalOps ctx (.call loc res (.direct sym) args argTys retTy nothrow :: ops) σ ≠ .ok x := by
  rw [evalOps.eq_2]
  simp only [evalOp, adjustThis, evalCall_ext_eq hf hm hb,
    Res.pure_eq, Res.ok_bind, Res.ub_bind, bind_assoc]
  exact not_ok_bind (fun _ _ hc => by cases hc) x

theorem evalOps_simple_not_ok {ctx : Ctx} {op : Op} {ops : List Op}
    (hs : isSimpleAnyOp op = true)
    (hops : ∀ σ x, evalOps ctx ops σ ≠ .ok x) (σ : State) (x : Step × State) :
    evalOps ctx (op :: ops) σ ≠ .ok x := by
  rw [evalOps.eq_2, evalOp_eq_simple_any hs]
  simp only [bind_assoc, Res.ok_bind, Res.pure_eq]
  exact not_ok_bind (fun σ' b => hops σ' b) x

theorem evalRegion_single_not_ok {ctx : Ctx} {ops : List Op}
    (hops : ∀ σ x, evalOps ctx ops σ ≠ .ok x) (σ : State) (x : Exit × State) :
    evalRegion ctx (.mk [.mk [] ops]) [] σ ≠ .ok x := by
  rw [evalRegion.eq_2, evalBlock_zero]
  simp only [State.bindArgs, Res.ok_bind, bind_assoc]
  exact fun hc => by
    cases h : evalOps ctx ops σ with
    | ok a => exact hops σ a h
    | ub _ => rw [h] at hc; cases hc
    | div => rw [h] at hc; cases hc

theorem evalOps_scope_not_ok {ctx : Ctx} {res : Option VId} {body : Region} {ops : List Op}
    (hb : ∀ σ x, evalRegion ctx body [] σ ≠ .ok x) (σ : State) (x : Step × State) :
    evalOps ctx (.scope res body :: ops) σ ≠ .ok x := by
  rw [evalOps.eq_2]
  simp only [evalOp, bind_assoc]
  exact fun hc => by
    cases h : evalRegion ctx body [] σ with
    | ok a => exact hb σ a h
    | ub _ => rw [h] at hc; cases hc
    | div => rw [h] at hc; cases hc

theorem evalOp_whileOp_dead_congr {ctx₁ ctx₂ : Ctx} {loc₁ loc₂ : Loc} {c₁ c₂ b₁ b₂ : Region}
    (hc : ∀ σ, evalRegion ctx₁ c₁ [] σ = evalRegion ctx₂ c₂ [] σ)
    (hb : ∀ σ, evalRegion ctx₁ b₁ [] σ = evalRegion ctx₂ b₂ [] σ)
    (hdead : ∀ σ x, evalRegion ctx₂ b₂ [] σ ≠ .ok x) (σ : State) :
    evalOp ctx₁ (.whileOp loc₁ c₁ b₁ none) σ = evalOp ctx₂ (.whileOp loc₂ c₂ b₂ none) σ := by
  simp only [evalOp]
  rw [evalWhile.eq_1, evalWhile.eq_1, hc]
  apply Res.bind_congr_ok; rintro ⟨ec, σ1⟩ _
  cases ec with
  | cond bv =>
    cases bv
    · simp only [evalIterCleanup.eq_1, Res.ok_bind, Res.pure_eq]
    · simp only [hb σ1]
      apply Res.bind_congr_ok; rintro x hx
      exact False.elim (hdead σ1 x hx)
  | _ => rfl

theorem holds_evalWhile_dead_elim {ctx : Ctx} {c b : Region} {cl : Option (CleanupKind × Region)}
    {σ : State} {K : Step × State → Prop}
    (hdead : ∀ σ₁ x, evalRegion ctx b [] σ₁ ≠ .ok x)
    (h : (evalWhile ctx c b cl σ).holds K) :
    (evalRegion ctx c [] σ).holds (fun p => p.1 ≠ .cond true) := by
  rw [evalWhile.eq_1, loopHead] at h
  have h1 := holds_bind_elim h
  apply Res.holds_mono h1
  rintro ⟨ec, σ₁⟩ h2 hc
  subst hc
  dsimp only at h2
  have h3 := holds_bind_elim h2
  cases hok : evalRegion ctx b [] σ₁ with
  | ok x => exact hdead σ₁ x hok
  | ub _ => rw [hok] at h3; exact h3
  | div => rw [hok] at h3; exact h3

macro "cir_prove_dead" : tactic => `(tactic| (
  repeat' first
    | (intro σ x; refine evalRegion_single_not_ok ?_ σ x)
    | (intro σ x; refine evalOps_scope_not_ok ?_ σ x)
    | (intro σ x; refine evalOps_simple_not_ok rfl ?_ σ x)
    | (intro σ x; refine evalOps_call_ext_not_ok ?_ rfl rfl σ x; cir_lookup)))

def vcall5 (ctx : Ctx) (clsName : String) (b : Nat) (path : List PathElem) (sym : String) (m : Mem) :
    Res (Exit × Mem) :=
  adjustThisIndirect ctx sym [(.ptr (.record clsName))] [.ptr (.loc b path)] >>= fun vs =>
    evalCall ctx sym vs m

theorem evalOps_virtual_call5_congr {ctx₁ ctx₂ : Ctx}
    (hr : ∀ name, ctx₁.record? name = ctx₂.record? name)
    (hv : ctx₁.vtableSlot? = ctx₂.vtableSlot?)
    (hp : ctx₁.mod.ptrBytes = ctx₂.mod.ptrBytes := by rfl)
    {r_vp r_this r_vptr r_fnaddr r_fn : VId} {clsName : String} {slot : Nat} {fnTy : Ty}
    {loc₁ loc₂ : Loc} {res : Option VId} {retTy : Ty} {nothrow : Bool}
    {ops₁ ops₂ : List Op}
    (hne1 : r_this ≠ r_vp) (hne2 : r_this ≠ r_vptr) (hne3 : r_this ≠ r_fnaddr) (hne4 : r_this ≠ r_fn)
    (hvc : ∀ vt i k sym b path m,
      ctx₂.vtableSlot? vt i k = some (.ptr (.fn sym)) →
      vcall5 ctx₁ clsName b path sym m = vcall5 ctx₂ clsName b path sym m)
    (hops : ∀ σ, evalOps ctx₁ ops₁ σ = evalOps ctx₂ ops₂ σ)
    (σ : State) :
    evalOps ctx₁
      (.vtableGetVptr r_vp r_this (.record clsName) ::
       .load r_vptr r_vp .vptr ::
       .vtableGetVirtualFnAddr r_fnaddr r_vptr slot ::
       .load r_fn r_fnaddr (.ptr fnTy) ::
       .call loc₁ res (.indirect r_fn) [r_this] [(.ptr (.record clsName))] retTy nothrow ::
       ops₁) σ =
    evalOps ctx₂
      (.vtableGetVptr r_vp r_this (.record clsName) ::
       .load r_vptr r_vp .vptr ::
       .vtableGetVirtualFnAddr r_fnaddr r_vptr slot ::
       .load r_fn r_fnaddr (.ptr fnTy) ::
       .call loc₂ res (.indirect r_fn) [r_this] [(.ptr (.record clsName))] retTy nothrow ::
       ops₂) σ := by
  rw [evalOps.eq_2, evalOps.eq_2]
  simp only [evalOp, evalSimple, State.getPtr, State.get, vptrClass?_congr hr, vptrPath_congr hr]
  rcases hthis : σ.env r_this with _ | v_th <;> try rfl
  simp only [Res.ofOption_some, Res.ok_bind, Res.pure_eq]
  cases v_th <;> try rfl
  rename_i p
  cases p <;> try rfl
  rename_i b path
  rcases hcls : ctx₂.vptrClass? σ.mem (.loc b path) (.record clsName) with _ | cls' <;>
    simp only [hcls, Res.ofOption_none, Res.ofOption_some, Res.ub_bind, Res.ok_bind] <;> try rfl
  rcases hvp : ctx₂.vptrPath 16 cls' with _ | vp <;>
    simp only [hvp, Res.ofOption_none, Res.ofOption_some, Res.ub_bind, Res.ok_bind] <;> try rfl
  rw [evalOps.eq_2, evalOps.eq_2]
  simp only [evalOp, evalSimple, State.getPtr, State.get, State.set, upd_same,
    Res.ofOption_some, Res.ok_bind, Res.pure_eq, loadPtr_congr hr hv hp]
  rcases hld : ctx₂.typedLoad σ.mem .vptr (.loc b (path ++ List.map PathElem.idx vp)) with v_vptr | msg <;>
    simp only [loadPtr, hld, Res.ok_bind, Res.ub_bind] <;> try rfl
  rw [evalOps.eq_2, evalOps.eq_2]
  simp only [evalOp, evalSimple, State.getPtr, State.get, State.set, upd_same,
    Res.ofOption_some, Res.ok_bind, Res.pure_eq]
  cases v_vptr <;> try rfl
  rename_i p_vptr
  cases p_vptr <;> try rfl
  rename_i vt i k
  simp only [Res.ok_bind]
  rw [evalOps.eq_2, evalOps.eq_2]
  simp only [evalOp, evalSimple, State.getPtr, State.get, State.set, upd_same,
    Res.ofOption_some, Res.ok_bind, Res.pure_eq, loadPtr, hv]
  rcases hslot : ctx₂.vtableSlot? vt i (k + slot) with _ | v_fn <;>
    simp only [Res.ofOption_none, Res.ofOption_some, Res.ub_bind, Res.ok_bind, vtableRead] <;> try rfl
  rw [evalOps.eq_2, evalOps.eq_2]
  have hget_this :
      upd (upd (upd (upd σ.env r_vp (some (Val.ptr (Ptr.loc b (path ++ List.map PathElem.idx vp)))))
        r_vptr (some (Val.ptr (Ptr.vtable vt i k))))
        r_fnaddr (some (Val.ptr (Ptr.vtable vt i (k + slot)))))
        r_fn (some v_fn) r_this = some (.ptr (.loc b path)) := by
    rw [upd_ne _ _ _ _ hne4, upd_ne _ _ _ _ hne3, upd_ne _ _ _ _ hne2, upd_ne _ _ _ _ hne1, hthis]
  simp only [evalOp, List.mapM, List.mapM.loop, State.get, hget_this, upd_same,
    Res.ofOption_some, Res.ok_bind, Res.pure_eq, List.reverse, List.reverseAux]
  cases v_fn <;> try rfl
  rename_i p_fn
  cases p_fn <;> try rfl
  rename_i sym_fn
  simp only [adjustThis, ← bind_assoc]
  rw [show (adjustThisIndirect ctx₁ sym_fn [(.ptr (.record clsName))] [.ptr (.loc b path)] >>= fun x => evalCall ctx₁ sym_fn x σ.mem) = vcall5 ctx₁ clsName b path sym_fn σ.mem from rfl,
      show (adjustThisIndirect ctx₂ sym_fn [(.ptr (.record clsName))] [.ptr (.loc b path)] >>= fun x => evalCall ctx₂ sym_fn x σ.mem) = vcall5 ctx₂ clsName b path sym_fn σ.mem from rfl,
      hvc vt i (k + slot) sym_fn b path σ.mem hslot]
  congr 1; funext ⟨s, σ_next⟩
  cases s <;> first | exact hops σ_next | rfl

theorem vcall5_unsupported_layout {ctx₁ ctx₂ : Ctx}
    (hr : ∀ name, ctx₁.record? name = ctx₂.record? name)
    (hp : ctx₁.mod.ptrBytes = ctx₂.mod.ptrBytes)
    {clsName sym d : String} {fd₁ fd₂ : FuncDecl}
    (hf₁ : ctx₁.mod.findFunc? sym = some fd₁) (hd₁ : fd₁.params.head? = some (.ptr (.record d)))
    (hf₂ : ctx₂.mod.findFunc? sym = some fd₂) (hd₂ : fd₂.params.head? = some (.ptr (.record d)))
    (hne : (clsName == d) = false)
    (hbp : ctx₂.basePath 16 d clsName 0 = none)
    (hth : isThunk sym = false := by rfl)
    (b : Nat) (path : List PathElem) (m : Mem) :
    vcall5 ctx₁ clsName b path sym m = vcall5 ctx₂ clsName b path sym m := by
  unfold vcall5 adjustThisIndirect
  simp only [hf₁, hf₂, Option.bind, hd₁, hd₂, hne, hth, Bool.false_eq_true, ↓reduceIte, basePath_congr hr hp, hbp, Res.ub_bind]

theorem vcall5_of_evalCall_congr {ctx₁ ctx₂ : Ctx}
    (hr : ∀ name, ctx₁.record? name = ctx₂.record? name)
    (hp : ctx₁.mod.ptrBytes = ctx₂.mod.ptrBytes)
    {clsName sym : String} {fd₁ fd₂ : FuncDecl}
    (hf₁ : ctx₁.mod.findFunc? sym = some fd₁)
    (hf₂ : ctx₂.mod.findFunc? sym = some fd₂)
    (hpar : fd₁.params.head? = fd₂.params.head?)
    (hcall : ∀ vs m, evalCall ctx₁ sym vs m = evalCall ctx₂ sym vs m)
    (b : Nat) (path : List PathElem) (m : Mem) :
    vcall5 ctx₁ clsName b path sym m = vcall5 ctx₂ clsName b path sym m := by
  unfold vcall5 adjustThisIndirect
  simp only [hf₁, hf₂, Option.bind, hpar, basePath_congr hr hp]
  congr 1; funext vs; exact hcall vs m

theorem vcall5_ext_congr {ctx₁ ctx₂ : Ctx}
    {clsName sym : String} {fd₁ fd₂ : FuncDecl}
    (hf₁ : ctx₁.mod.findFunc? sym = some fd₁) (hm₁ : fd₁.model = none) (hb₁ : fd₁.body = none) (hp₁ : fd₁.params = [])
    (hf₂ : ctx₂.mod.findFunc? sym = some fd₂) (hm₂ : fd₂.model = none) (hb₂ : fd₂.body = none) (hp₂ : fd₂.params = [])
    (b : Nat) (path : List PathElem) (m : Mem) :
    vcall5 ctx₁ clsName b path sym m = vcall5 ctx₂ clsName b path sym m := by
  unfold vcall5 adjustThisIndirect
  simp only [hf₁, hf₂, Option.bind, hp₁, hp₂, List.head?, Res.ok_bind,
    evalCall_ext_eq hf₁ hm₁ hb₁, evalCall_ext_eq hf₂ hm₂ hb₂]

theorem equiv_obsEq_of_eq {m : Mem} {r₁ r₂ : Res (Exit × Mem)} (h : r₁ = r₂) :
    Equiv (ObsEq m) r₁ r₂ := by
  rw [h]
  refine ⟨?_, ?_⟩
  · rw [sim_res_res]; intro os hs; exact Res.holds_mono hs (fun _ ho => ho ▸ ⟨rfl, fun _ _ => rfl⟩)
  · rw [obsEq_flip, sim_res_res]; intro os hs; exact Res.holds_mono hs (fun _ ho => ho ▸ ⟨rfl, fun _ _ => rfl⟩)

/-! ### `IsLocEnv`: Congruence Without `vtableSlot?` -/

def IsLocPtr : Option Val → Bool
  | some (.ptr (.loc _ _)) => true
  | _ => false

def IsLocEnv (rs : List VId) (σ : State) : Prop :=
  ∀ r, r ∈ rs → IsLocPtr (σ.env r) = true

theorem isLocEnv_nil (σ : State) : IsLocEnv [] σ := by
  intro r hr; cases hr

theorem isLocEnv_set_loc {rs : List VId} {σ : State} {r b : Nat} {path : List PathElem}
    (h : IsLocEnv rs σ) :
    IsLocEnv (r :: rs) (σ.set r (.ptr (.loc b path))) := by
  intro x hx
  by_cases hxr : x = r
  · subst hxr; simp only [State.set, upd_same, IsLocPtr]
  · rw [List.mem_cons, or_iff_right hxr] at hx
    simp only [State.set, upd_ne _ _ _ _ hxr]
    exact h x hx

theorem isLocEnv_set_other {rs : List VId} {σ : State} {r : VId} {v : Val}
    (h : IsLocEnv rs σ) (hn : decide (r ∈ rs) = false) :
    IsLocEnv rs (σ.set r v) := by
  intro x hx
  have hne : x ≠ r := by
    intro heq; subst heq
    rw [decide_eq_false_iff_not] at hn
    exact hn hx
  simp only [State.set, upd_ne _ _ _ _ hne]
  exact h x hx

theorem isLocEnv_withMem {rs : List VId} {σ : State} {m : Mem} (h : IsLocEnv rs σ) :
    IsLocEnv rs (σ.withMem m) := h

theorem isLocEnv_bindArgs {rs : List VId} {params : List VId} {args : List Val} {σ σ' : State}
    (h : IsLocEnv rs σ) (hd : (params.any (fun p => decide (p ∈ rs))) = false)
    (hb : σ.bindArgs params args = .ok σ') :
    IsLocEnv rs σ' := by
  induction params generalizing args σ with
  | nil =>
    cases args <;> cases hb <;> exact h
  | cons p ps ih =>
    cases args with
    | nil => cases hb
    | cons v vs =>
      simp only [List.any_cons, Bool.or_eq_false_iff] at hd
      exact ih (isLocEnv_set_other h hd.1) hd.2 hb

theorem evalRegion_env {ctx : Ctx} {r : Region} {args : List Val} {σ : State} {e : Exit} {σ' : State}
    (h : evalRegion ctx r args σ = .ok (e, σ')) : σ'.env = σ.env := by
  cases r with
  | mk bs =>
    cases bs with
    | nil => rw [evalRegion.eq_1] at h; cases h; rfl
    | cons b bs =>
      rw [evalRegion.eq_2] at h
      rcases h1 : evalBlock ctx (b :: bs) 0 args σ with ⟨e0, σ0⟩ | _ | _ <;>
        rw [h1] at h <;> cases h <;> rfl

theorem evalOp_load_congr_of_loc {ctx₁ ctx₂ : Ctx}
    (hr : ∀ name, ctx₁.record? name = ctx₂.record? name)
    (hp : ctx₁.mod.ptrBytes = ctx₂.mod.ptrBytes := by rfl)
    {rs : List VId} {r a : VId} {ty : Ty} {σ : State}
    (hloc : IsLocEnv rs σ) (ha : decide (a ∈ rs) = true) :
    evalOp ctx₁ (.load r a ty) σ = evalOp ctx₂ (.load r a ty) σ := by
  have hpa := hloc a (of_decide_eq_true ha)
  simp only [evalOp, evalSimple, State.getPtr, State.get]
  rcases h : σ.env a with _ | v <;> rw [h] at hpa <;> try cases hpa
  cases v <;> try cases hpa
  rename_i p
  cases p <;> try cases hpa
  simp only [Res.ofOption_some, Res.ok_bind, Res.pure_eq, loadPtr, typedLoad_congr hr hp]

def isSimpleNonLoadOp (op : Op) : Bool :=
  match op with
  | .load .. | .retLoad .. => false
  | op => isSimpleNonCmpOp op

theorem evalSimple_nonload_congr {ctx₁ ctx₂ : Ctx}
    (hr : ∀ name, ctx₁.record? name = ctx₂.record? name)
    (hp : ctx₁.mod.ptrBytes = ctx₂.mod.ptrBytes)
    (hcxx : ctx₁.mod.cxx = ctx₂.mod.cxx := by rfl)
    {op : Op} (hop : isSimpleNonLoadOp op = true) (σ : State) :
    evalSimple ctx₁ op σ = evalSimple ctx₂ op σ := by
  cases op <;> try (cases hop; done)
  case const r ty c =>
    have hc : isNonGlobalConst c = true := by
      cases c <;> first | rfl | (cases hop; done)
    simp only [evalSimple, constVal_non_globalAddr hr ty c hc]
  case cast r k a src dst =>
    simp only [isSimpleNonLoadOp, isSimpleNonCmpOp, isSimpleNonGlobalOp, Bool.and_eq_true] at hop
    exact evalSimple_cast_congr hr hp hcxx hop.1 hop.2 σ
  all_goals
    try simp only [evalSimple, initVal_congr hr, zeroVal_congr hr, sizeAlign_congr hr hp,
      typedLoad_congr hr hp, typedStore_congr hr hp, record?_congr hr,
      memberPath_congr hr hp, fromActive_congr hr hp,
      stride?_congr hr hp, diff?_congr hr hp, basePath_congr hr hp, vptrPath_congr hr,
      vptrClass?_congr hr, bfPlaced?_congr hr hp, bfLoadBytes_congr hr hp,
      bfLoadBytes0_congr hr hp, bfStoreBytes_congr hr hp, unionView?_congr hr hp,
      posAligned_congr hr hp, hcxx]

theorem evalOp_simple_nonload_congr {ctx₁ ctx₂ : Ctx}
    (hr : ∀ name, ctx₁.record? name = ctx₂.record? name)
    (hp : ctx₁.mod.ptrBytes = ctx₂.mod.ptrBytes)
    (hcxx : ctx₁.mod.cxx = ctx₂.mod.cxx := by rfl)
    {op : Op} (hop : isSimpleNonLoadOp op = true) (σ : State) :
    evalOp ctx₁ op σ = evalOp ctx₂ op σ := by
  cases op <;> try (cases hop; done)
  all_goals simp only [evalOp, evalSimple_nonload_congr hr hp hcxx hop]

theorem ok_bind_eq_ok {α β : Type} {x : Res α} {f : α → Res β} {b : β}
    (h : (x >>= f) = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | ok a => exact ⟨a, rfl, h⟩
  | ub _ => cases h
  | div => cases h

theorem isLocEnv_setResults {rs : List VId} {res : Option VId} {vs : List Val} {σ σ' : State}
    (h : IsLocEnv rs σ)
    (hn : (match res with | none => true | some r => !decide (r ∈ rs)) = true)
    (hs : σ.setResults res vs = .ok σ') :
    IsLocEnv rs σ' := by
  cases res with
  | none =>
    cases vs <;> cases hs; exact h
  | some r =>
    cases vs with
    | nil => cases hs
    | cons v rest =>
      cases rest with
      | nil =>
        cases hs
        simp only [Bool.not_eq_true'] at hn
        exact isLocEnv_set_other h hn
      | cons _ _ => cases hs

theorem evalOp_pres_alloca {ctx : Ctx} {rs : List VId} {r : VId} {ty : Ty} {name : String} {σ σ' : State}
    (h : IsLocEnv rs σ) (hok : evalOp ctx (.alloca r ty name) σ = .ok (.next, σ')) :
    IsLocEnv (r :: rs) σ' := by
  simp only [evalOp, evalSimple, Res.ok_bind, Res.pure_eq] at hok
  cases hok
  exact isLocEnv_set_loc h

theorem evalOp_pres_getMember {ctx : Ctx} {rs : List VId} {r base : VId} {i : Nat} {rt ft : Ty} {σ σ' : State}
    (h : IsLocEnv rs σ) (hok : evalOp ctx (.getMember r base i rt ft) σ = .ok (.next, σ')) :
    IsLocEnv (r :: rs) σ' := by
  simp only [evalOp, evalSimple] at hok
  obtain ⟨σ1, h1, h2⟩ := ok_bind_eq_ok hok
  cases h2
  obtain ⟨p, _, hp⟩ := ok_bind_eq_ok h1
  cases p <;> cases hp
  exact isLocEnv_set_loc h

theorem evalOp_pres_getElement {ctx : Ctx} {rs : List VId} {r base idx : VId} {it et : Ty} {σ σ' : State}
    (h : IsLocEnv rs σ) (hok : evalOp ctx (.getElement r base idx it et) σ = .ok (.next, σ')) :
    IsLocEnv (r :: rs) σ' := by
  simp only [evalOp, evalSimple] at hok
  obtain ⟨σ1, h1, h2⟩ := ok_bind_eq_ok hok
  cases h2
  obtain ⟨p, _, h1⟩ := ok_bind_eq_ok h1
  obtain ⟨iv, _, h1⟩ := ok_bind_eq_ok h1
  rcases p with _ | ⟨b, path⟩ | _ | _ | _ | _ <;> try cases h1
  rcases hmv : σ.mem.read? (.loc b path) with _ | mv <;> rw [hmv] at h1 <;> try cases h1
  cases mv <;> try cases h1
  dsimp only at h1
  split at h1 <;> cases h1
  exact isLocEnv_set_loc h

theorem evalOp_pres_store {ctx : Ctx} {rs : List VId} {v a : VId} {ty : Ty} {σ σ' : State}
    (h : IsLocEnv rs σ) (hok : evalOp ctx (.store v a ty) σ = .ok (.next, σ')) :
    IsLocEnv rs σ' := by
  simp only [evalOp, evalSimple] at hok
  obtain ⟨σ1, h1, h2⟩ := ok_bind_eq_ok hok; cases h2
  obtain ⟨_, _, h1⟩ := ok_bind_eq_ok h1
  obtain ⟨_, _, h1⟩ := ok_bind_eq_ok h1
  obtain ⟨_, _, h1⟩ := ok_bind_eq_ok h1
  obtain ⟨_, _, h1⟩ := ok_bind_eq_ok h1
  cases h1; exact h

theorem evalOp_pres_copy {ctx : Ctx} {rs : List VId} {src dst : VId} {ty : Ty} {σ σ' : State}
    (h : IsLocEnv rs σ) (hok : evalOp ctx (.copy src dst ty) σ = .ok (.next, σ')) :
    IsLocEnv rs σ' := by
  simp only [evalOp, evalSimple] at hok
  obtain ⟨σ1, h1, h2⟩ := ok_bind_eq_ok hok; cases h2
  obtain ⟨_, _, h1⟩ := ok_bind_eq_ok h1
  obtain ⟨_, _, h1⟩ := ok_bind_eq_ok h1
  obtain ⟨_, _, h1⟩ := ok_bind_eq_ok h1
  obtain ⟨_, _, h1⟩ := ok_bind_eq_ok h1
  obtain ⟨_, _, h1⟩ := ok_bind_eq_ok h1
  cases h1; exact h

theorem evalOp_pres_scope {ctx : Ctx} {rs : List VId} {res : Option VId} {body : Region} {σ σ' : State}
    (h : IsLocEnv rs σ)
    (hn : (match res with | none => true | some r => !decide (r ∈ rs)) = true)
    (hok : evalOp ctx (.scope res body) σ = .ok (.next, σ')) :
    IsLocEnv rs σ' := by
  simp only [evalOp] at hok
  obtain ⟨⟨e, σ1⟩, he, hok⟩ := ok_bind_eq_ok hok
  have henv : IsLocEnv rs σ1 := by
    intro x hx; rw [evalRegion_env he]; exact h x hx
  cases e with
  | yield vs =>
    obtain ⟨σ2, hs, h2⟩ := ok_bind_eq_ok hok
    cases h2
    exact isLocEnv_setResults henv hn hs
  | _ => cases hok

theorem evalOp_pres_ifOp {ctx : Ctx} {rs : List VId} {c : VId} {t el : Region} {σ σ' : State}
    (h : IsLocEnv rs σ) (hok : evalOp ctx (.ifOp c t el) σ = .ok (.next, σ')) :
    IsLocEnv rs σ' := by
  simp only [evalOp] at hok
  obtain ⟨b, _, hok⟩ := ok_bind_eq_ok hok
  obtain ⟨⟨e, σ1⟩, he, hok⟩ := ok_bind_eq_ok hok
  have henv : IsLocEnv rs σ1 := by
    intro x hx; rw [evalRegion_env he]; exact h x hx
  cases e with
  | yield vs => cases vs <;> cases hok; exact henv
  | _ => cases hok

theorem evalOp_pres_whileOp {ctx : Ctx} {rs : List VId} {loc : Loc} {c b : Region} {σ σ' : State}
    (hdead : ∀ σ₁ x, evalRegion ctx b [] σ₁ ≠ .ok x)
    (h : IsLocEnv rs σ) (hok : evalOp ctx (.whileOp loc c b none) σ = .ok (.next, σ')) :
    IsLocEnv rs σ' := by
  simp only [evalOp] at hok
  rw [evalWhile.eq_1, loopHead] at hok
  obtain ⟨⟨ec, σ1⟩, hec, hok⟩ := ok_bind_eq_ok hok
  have henv : IsLocEnv rs σ1 := by
    intro x hx; rw [evalRegion_env hec]; exact h x hx
  cases ec with
  | cond bv =>
    cases bv
    · simp only [evalIterCleanup.eq_1, Res.ok_bind, Res.pure_eq] at hok
      cases hok; exact henv
    · obtain ⟨x, hx, _⟩ := ok_bind_eq_ok hok
      exact False.elim (hdead σ1 x hx)
  | _ => cases hok

theorem evalOp_pres_call_direct {ctx : Ctx} {rs : List VId}
    {loc : Loc} {res : Option VId} {sym : String} {args : List VId} {argTys : List Ty} {retTy : Ty} {nt : Bool}
    {σ σ' : State}
    (h : IsLocEnv rs σ)
    (hn : (match res with | none => true | some r => !decide (r ∈ rs)) = true)
    (hok : evalOp ctx (.call loc res (.direct sym) args argTys retTy nt) σ = .ok (.next, σ')) :
    IsLocEnv rs σ' := by
  simp only [evalOp, adjustThis, Res.pure_eq, Res.ok_bind] at hok
  obtain ⟨vs, _, hok⟩ := ok_bind_eq_ok hok
  obtain ⟨⟨e, m'⟩, _, hok⟩ := ok_bind_eq_ok hok
  cases e with
  | ret v =>
    obtain ⟨σ2, hs, h2⟩ := ok_bind_eq_ok hok
    cases h2
    exact isLocEnv_setResults (isLocEnv_withMem h) hn hs
  | _ => cases hok

def singleWriteReg? : Op → Option VId
  | .const r .. | .load r .. | .getGlobal r .. | .cmp r .. | .unop r .. | .binop r .. | .cast r .. => some r
  | _ => none

theorem evalOp_pres_singleWrite {ctx : Ctx} {rs : List VId} {op : Op} {r : VId} {σ σ' : State}
    (hsw : singleWriteReg? op = some r)
    (hn : decide (r ∈ rs) = false)
    (h : IsLocEnv rs σ)
    (hok : evalOp ctx op σ = .ok (.next, σ')) :
    IsLocEnv rs σ' := by
  cases op <;> try (cases hsw; done)
  case const r' ty c =>
    cases hsw; simp only [evalOp, evalSimple] at hok
    obtain ⟨σ1, h1, h2⟩ := ok_bind_eq_ok hok; cases h2
    obtain ⟨v, _, h1⟩ := ok_bind_eq_ok h1; cases h1
    exact isLocEnv_set_other h hn
  case load r' a ty =>
    cases hsw; simp only [evalOp, evalSimple] at hok
    obtain ⟨σ1, h1, h2⟩ := ok_bind_eq_ok hok; cases h2
    obtain ⟨p, _, h1⟩ := ok_bind_eq_ok h1
    obtain ⟨v, _, h1⟩ := ok_bind_eq_ok h1; cases h1
    exact isLocEnv_set_other h hn
  case getGlobal r' sym ty =>
    cases hsw; simp only [evalOp, evalSimple] at hok
    obtain ⟨σ1, h1, h2⟩ := ok_bind_eq_ok hok; cases h2
    obtain ⟨p, _, h1⟩ := ok_bind_eq_ok h1; cases h1
    exact isLocEnv_set_other h hn
  case cmp r' k a b ty =>
    cases hsw; simp only [evalOp, evalSimple] at hok
    obtain ⟨σ1, h1, h2⟩ := ok_bind_eq_ok hok; cases h2
    obtain ⟨x, _, h1⟩ := ok_bind_eq_ok h1
    obtain ⟨y, _, h1⟩ := ok_bind_eq_ok h1
    obtain ⟨c, _, h1⟩ := ok_bind_eq_ok h1; cases h1
    exact isLocEnv_set_other h hn
  case unop r' k nsw a ty =>
    cases hsw; simp only [evalOp, evalSimple] at hok
    obtain ⟨σ1, h1, h2⟩ := ok_bind_eq_ok hok; cases h2
    cases ty <;> try cases h1
    · obtain ⟨x, _, h1⟩ := ok_bind_eq_ok h1
      obtain ⟨z, _, h1⟩ := ok_bind_eq_ok h1; cases h1
      exact isLocEnv_set_other h hn
    · cases k <;> try cases h1
      obtain ⟨x, _, h1⟩ := ok_bind_eq_ok h1; cases h1
      exact isLocEnv_set_other h hn
    · rename_i ety n
      cases ety <;> try cases h1
      obtain ⟨v, _, h1⟩ := ok_bind_eq_ok h1
      cases v <;> try cases h1
      obtain ⟨zs, _, h1⟩ := ok_bind_eq_ok h1; cases h1
      exact isLocEnv_set_other h hn
  case binop r' k nsw nuw a b ty =>
    cases hsw; simp only [evalOp, evalSimple] at hok
    obtain ⟨σ1, h1, h2⟩ := ok_bind_eq_ok hok; cases h2
    cases ty <;> try cases h1
    · obtain ⟨x, _, h1⟩ := ok_bind_eq_ok h1
      obtain ⟨y, _, h1⟩ := ok_bind_eq_ok h1
      obtain ⟨z, _, h1⟩ := ok_bind_eq_ok h1; cases h1
      exact isLocEnv_set_other h hn
    · obtain ⟨x, _, h1⟩ := ok_bind_eq_ok h1
      obtain ⟨y, _, h1⟩ := ok_bind_eq_ok h1
      cases k <;> cases h1 <;> exact isLocEnv_set_other h hn
    · rename_i ety n
      cases ety <;> try cases h1
      obtain ⟨x, _, h1⟩ := ok_bind_eq_ok h1
      obtain ⟨y, _, h1⟩ := ok_bind_eq_ok h1
      obtain ⟨zs, _, h1⟩ := ok_bind_eq_ok h1; cases h1
      exact isLocEnv_set_other h hn
  case cast r' k a s d =>
    cases hsw; simp only [evalOp, evalSimple] at hok
    obtain ⟨σ1, h1, h2⟩ := ok_bind_eq_ok hok; cases h2
    obtain ⟨x, -, h1⟩ := ok_bind_eq_ok h1
    have close_cast : ∀ (σ2 : State) (x2 : Val), IsLocEnv rs σ2 →
        (pure (σ2, x2) >>= fun __x : State × Val =>
          let x := ctx.convertPtr __x.1.mem k __x.2 d
          ctx.castCheck __x.1.mem k x d >>= fun _ =>
            castVal ctx __x.1.mem k x s d >>= fun v => pure (__x.1.set r v)) = Res.ok σ' →
        IsLocEnv rs σ' := by
      intro σ2 x2 h2loc hc
      simp only [Res.pure_eq, Res.ok_bind] at hc
      obtain ⟨_, _, hc⟩ := ok_bind_eq_ok hc
      obtain ⟨v, _, hc⟩ := ok_bind_eq_ok hc; cases hc
      exact isLocEnv_set_other h2loc hn
    cases k <;> try exact close_cast _ _ h h1
    cases x <;> try exact close_cast _ _ h h1
    rename_i p; cases p <;> try exact close_cast _ _ h h1
    rename_i b path; cases path <;> try exact close_cast _ _ h h1
    cases d <;> try exact close_cast _ _ h h1
    dsimp only at h1
    rcases hblk : σ.mem.blocks b with _ | ⟨bk, al, bty, bval⟩ <;> rw [hblk] at h1 <;> try exact close_cast _ _ h h1
    cases bk <;> try exact close_cast _ _ h h1
    cases al <;> try exact close_cast _ _ h h1
    cases bty <;> try exact close_cast _ _ h h1
    rename_i ety n
    cases ety <;> try exact close_cast _ _ h h1
    rename_i tag
    cases bval <;> try exact close_cast _ _ h h1
    dsimp only at h1
    rcases hhk : heapKind? tag with _ | zero <;> rw [hhk] at h1 <;> try exact close_cast _ _ h h1
    rcases hsa : ctx.sizeAlign 32 _ with _ | ⟨sz, _⟩ <;> rw [hsa] at h1 <;> try exact close_cast _ _ h h1
    dsimp only at h1
    split at h1 <;> exact close_cast _ _ (isLocEnv_withMem h) h1

theorem evalOps_cons_loc_congr {ctx₁ ctx₂ : Ctx} {rs rs' : List VId}
    {op₁ op₂ : Op} {ops₁ ops₂ : List Op}
    (hop : ∀ σ, IsLocEnv rs σ → evalOp ctx₁ op₁ σ = evalOp ctx₂ op₂ σ)
    (hpres : ∀ σ σ', IsLocEnv rs σ → evalOp ctx₂ op₂ σ = .ok (.next, σ') → IsLocEnv rs' σ')
    (hops : ∀ σ, IsLocEnv rs' σ → evalOps ctx₁ ops₁ σ = evalOps ctx₂ ops₂ σ)
    (σ : State) (hloc : IsLocEnv rs σ) :
    evalOps ctx₁ (op₁ :: ops₁) σ = evalOps ctx₂ (op₂ :: ops₂) σ := by
  rw [evalOps.eq_2, evalOps.eq_2, hop σ hloc]
  apply Res.bind_congr_ok
  rintro ⟨s, σ'⟩ hok
  cases s with
  | next => exact hops σ' (hpres σ σ' hloc hok)
  | exit _ => rfl
  | jump _ _ => rfl

theorem evalRegion_single_loc_congr {ctx₁ ctx₂ : Ctx} {rs : List VId} {params : List VId} {ops₁ ops₂ : List Op}
    (hl₁ : blockNoLabel [.mk params ops₁] = true)
    (hl₂ : blockNoLabel [.mk params ops₂] = true)
    (hmj : (ops₁.any opMayJump) = false)
    (hd : (params.any (fun p => decide (p ∈ rs))) = false)
    (hops : ∀ σ, IsLocEnv rs σ → evalOps ctx₁ ops₁ σ = evalOps ctx₂ ops₂ σ)
    (args : List Val) (σ : State) (hloc : IsLocEnv rs σ) :
    evalRegion ctx₁ (.mk [.mk params ops₁]) args σ = evalRegion ctx₂ (.mk [.mk params ops₂]) args σ := by
  rw [evalRegion.eq_2, evalRegion.eq_2, evalBlock_zero, evalBlock_zero]
  congr 1
  apply Res.bind_congr_ok
  intro σ₁ hb
  have hloc₁ := isLocEnv_bindArgs hloc hd hb
  have hnj : ∀ j vs σ', evalOps ctx₁ ops₁ σ₁ ≠ .ok (.jump j vs, σ') := by
    intro j vs σ' hok
    have h1 : (evalOps ctx₁ ops₁ σ₁).holds (fun _ => True) := by rw [hok]; trivial
    have h2 := evalOps_not_jump hmj h1
    rw [hok] at h2
    exact h2.1 j vs rfl
  rw [hops σ₁ hloc₁] at hnj ⊢
  apply Res.bind_congr_ok
  rintro ⟨s, σ₂⟩ hok
  cases s with
  | exit e =>
    cases e <;> try rfl
    dsimp only
    rw [labelBlock?_of_noLabel hl₁, labelBlock?_of_noLabel hl₂]
  | jump j vs => exact False.elim (hnj j vs σ₂ hok)
  | next => rfl

theorem evalOp_scope_loc_congr {ctx₁ ctx₂ : Ctx} {rs : List VId} {res : Option VId} {b₁ b₂ : Region}
    (hb : ∀ σ, IsLocEnv rs σ → evalRegion ctx₁ b₁ [] σ = evalRegion ctx₂ b₂ [] σ)
    (σ : State) (hloc : IsLocEnv rs σ) :
    evalOp ctx₁ (.scope res b₁) σ = evalOp ctx₂ (.scope res b₂) σ := by
  simp only [evalOp, hb σ hloc]

theorem evalOp_ifOp_loc_congr {ctx₁ ctx₂ : Ctx} {rs : List VId} {c : VId} {t₁ t₂ el₁ el₂ : Region}
    (ht : ∀ σ, IsLocEnv rs σ → evalRegion ctx₁ t₁ [] σ = evalRegion ctx₂ t₂ [] σ)
    (hel : ∀ σ, IsLocEnv rs σ → evalRegion ctx₁ el₁ [] σ = evalRegion ctx₂ el₂ [] σ)
    (σ : State) (hloc : IsLocEnv rs σ) :
    evalOp ctx₁ (.ifOp c t₁ el₁) σ = evalOp ctx₂ (.ifOp c t₂ el₂) σ := by
  simp only [evalOp]
  congr 1; funext b; cases b <;> simp only [Bool.false_eq_true, ↓reduceIte, hel σ hloc, ht σ hloc]

theorem evalOp_whileOp_dead_loc_congr {ctx₁ ctx₂ : Ctx} {rs : List VId} {loc₁ loc₂ : Loc} {c₁ c₂ b₁ b₂ : Region}
    (hc : ∀ σ, IsLocEnv rs σ → evalRegion ctx₁ c₁ [] σ = evalRegion ctx₂ c₂ [] σ)
    (hb : ∀ σ, IsLocEnv rs σ → evalRegion ctx₁ b₁ [] σ = evalRegion ctx₂ b₂ [] σ)
    (hdead : ∀ σ x, evalRegion ctx₂ b₂ [] σ ≠ .ok x)
    (σ : State) (hloc : IsLocEnv rs σ) :
    evalOp ctx₁ (.whileOp loc₁ c₁ b₁ none) σ = evalOp ctx₂ (.whileOp loc₂ c₂ b₂ none) σ := by
  simp only [evalOp]
  rw [evalWhile.eq_1, evalWhile.eq_1, loopHead, hc σ hloc]
  apply Res.bind_congr_ok; rintro ⟨ec, σ1⟩ hec
  have hloc1 : IsLocEnv rs σ1 := by
    intro x hx; rw [evalRegion_env hec]; exact hloc x hx
  cases ec with
  | cond bv =>
    cases bv
    · simp only [evalIterCleanup.eq_1, Res.ok_bind, Res.pure_eq]
    · simp only [hb σ1 hloc1]
      apply Res.bind_congr_ok; rintro x hx
      exact False.elim (hdead σ1 x hx)
  | _ => rfl

theorem evalCall_body_loc_congr {ctx₁ ctx₂ : Ctx} {sym : String} {fd₁ fd₂ : FuncDecl} {body₁ body₂ : Region}
    (hf₁ : ctx₁.mod.findFunc? sym = some fd₁) (hm₁ : fd₁.model = none) (hb₁ : fd₁.body = some body₁)
    (hf₂ : ctx₂.mod.findFunc? sym = some fd₂) (hm₂ : fd₂.model = none) (hb₂ : fd₂.body = some body₂)
    (hnt : fd₁.nothrow = fd₂.nothrow)
    (hs₁ : fd₁.special ≠ .dtor := by decide) (hs₂ : fd₂.special ≠ .dtor := by decide)
    (hbody : ∀ args σ, IsLocEnv [] σ → evalRegion ctx₁ body₁ args σ = evalRegion ctx₂ body₂ args σ)
    (vs : List Val) (m : Mem) :
    evalCall ctx₁ sym vs m = evalCall ctx₂ sym vs m := by
  rw [evalCall_body hf₁ hm₁ hb₁ hs₁, evalCall_body hf₂ hm₂ hb₂ hs₂]
  congr 1
  · exact hbody vs _ (isLocEnv_nil _)
  · funext ⟨e, σ⟩; cases e <;> simp only [hnt]

def blocksNoLabel (bs : List Block) : Bool :=
  bs.all fun b => match b with | .mk _ (.label _ :: _) => false | _ => true

theorem labelBlock?_of_blocksNoLabel {l : String} {bs : List Block}
    (h : blocksNoLabel bs = true) : labelBlock? l bs = none := by
  unfold labelBlock?
  rw [List.findIdx?_eq_none_iff]
  intro b hb
  unfold blocksNoLabel at h
  rw [List.all_eq_true] at h
  have hb' := h b hb
  cases b with
  | mk ps ops =>
    cases ops with
    | nil => rfl
    | cons op ops => cases op <;> first | rfl | cases hb'

theorem evalRegion_two_first_nojump {ctx₁ ctx₂ : Ctx} {rs : List VId}
    {ops₁ ops₂ : List Op} {b₁ b₂ : Block}
    (hl₁ : blocksNoLabel [.mk [] ops₁, b₁] = true)
    (hl₂ : blocksNoLabel [.mk [] ops₂, b₂] = true)
    (hmj : (ops₁.any opMayJump) = false)
    (hops : ∀ σ, IsLocEnv rs σ → evalOps ctx₁ ops₁ σ = evalOps ctx₂ ops₂ σ)
    (σ : State) (hloc : IsLocEnv rs σ) :
    evalRegion ctx₁ (.mk [.mk [] ops₁, b₁]) [] σ = evalRegion ctx₂ (.mk [.mk [] ops₂, b₂]) [] σ := by
  rw [evalRegion.eq_2, evalRegion.eq_2, evalBlock.eq_1, evalBlock.eq_1]
  simp only [List.getElem?_cons_zero, State.bindArgs, Res.ok_bind]
  congr 1
  have hnj : ∀ j vs σ', evalOps ctx₁ ops₁ σ ≠ .ok (.jump j vs, σ') := by
    intro j vs σ' hok
    have h1 : (evalOps ctx₁ ops₁ σ).holds (fun _ => True) := by rw [hok]; trivial
    have h2 := evalOps_not_jump hmj h1
    rw [hok] at h2
    exact h2.1 j vs rfl
  rw [hops σ hloc] at hnj ⊢
  apply Res.bind_congr_ok
  rintro ⟨s, σ₂⟩ hok
  cases s with
  | exit e =>
    cases e <;> try rfl
    dsimp only
    rw [labelBlock?_of_blocksNoLabel hl₁, labelBlock?_of_blocksNoLabel hl₂]
  | jump j vs => exact False.elim (hnj j vs σ₂ hok)
  | next => rfl

theorem evalOp_tryOp_all_congr {ctx₁ ctx₂ : Ctx} {rs : List VId}
    {body₁ body₂ : Region} {r_eh : VId}
    (hb : ∀ σ, IsLocEnv rs σ → evalRegion ctx₁ body₁ [] σ = evalRegion ctx₂ body₂ [] σ)
    (σ : State) (hloc : IsLocEnv rs σ) :
    evalOp ctx₁ (.tryOp body₁ [(.all, .mk [.mk [r_eh] [.ehTerminate r_eh]])] none) σ =
    evalOp ctx₂ (.tryOp body₂ [(.all, .mk [.mk [r_eh] [.ehTerminate r_eh]])] none) σ := by
  simp only [evalOp, hb σ hloc]
  congr 1; funext ⟨e, σ1⟩
  cases e <;> try rfl
  simp only [findHandler, Res.ok_bind, evalRegion.eq_2, evalBlock_zero,
    State.bindArgs, State.set, evalOps.eq_2, evalOp, Res.ub_bind]

theorem evalOp_pres_tryOp_all {ctx : Ctx} {rs : List VId}
    {body : Region} {r_eh : VId} {σ σ' : State}
    (h : IsLocEnv rs σ)
    (hok : evalOp ctx (.tryOp body [(.all, .mk [.mk [r_eh] [.ehTerminate r_eh]])] none) σ = .ok (.next, σ')) :
    IsLocEnv rs σ' := by
  simp only [evalOp] at hok
  obtain ⟨⟨e, σ1⟩, he, hok⟩ := ok_bind_eq_ok hok
  have henv : IsLocEnv rs σ1 := by
    intro x hx; rw [evalRegion_env he]; exact h x hx
  cases e with
  | yield vs => cases vs <;> cases hok; exact henv
  | exn x =>
    simp only [findHandler, Res.ok_bind, evalRegion.eq_2, evalBlock_zero,
      State.bindArgs, State.set, evalOps.eq_2, evalOp, Res.ub_bind] at hok
    cases hok
  | _ => cases hok

theorem evalRegion_single_whileOp_dead_loc_congr {ctx₁ ctx₂ : Ctx} {rs : List VId}
    {loc₁ loc₂ : Loc} {c₁ c₂ b₁ b₂ : Region}
    (hc : ∀ σ, IsLocEnv rs σ → evalRegion ctx₁ c₁ [] σ = evalRegion ctx₂ c₂ [] σ)
    (hb : ∀ σ, IsLocEnv rs σ → evalRegion ctx₁ b₁ [] σ = evalRegion ctx₂ b₂ [] σ)
    (hdead : ∀ σ x, evalRegion ctx₂ b₂ [] σ ≠ .ok x)
    (σ : State) (hloc : IsLocEnv rs σ) :
    evalRegion ctx₁ (.mk [.mk [] [.whileOp loc₁ c₁ b₁ none]]) [] σ =
    evalRegion ctx₂ (.mk [.mk [] [.whileOp loc₂ c₂ b₂ none]]) [] σ := by
  have h1 : ∀ (ctx : Ctx) (loc : Loc) (c b : Region),
      evalBlock ctx [.mk [] [.whileOp loc c b none]] 0 [] σ =
      (evalOp ctx (.whileOp loc c b none) σ >>= fun (s, σ') =>
        match s with
        | .next => .ok (.yield [], σ')
        | .exit (.goto l) => .ok (.goto l, σ')
        | .exit e => .ok (e, σ')
        | .jump j vs => evalBlock ctx [.mk [] [.whileOp loc c b none]] j vs σ') := by
    intro ctx loc c b
    rw [evalBlock_zero]
    simp only [State.bindArgs, Res.ok_bind, evalOps.eq_2, evalOps.eq_1, bind_assoc]
    apply Res.bind_congr_ok
    rintro ⟨s, σ'⟩ _
    cases s with
    | next => rfl
    | exit e => cases e <;> rfl
    | jump j vs => rfl
  rw [evalRegion.eq_2, evalRegion.eq_2, h1, h1, evalOp_whileOp_dead_loc_congr hc hb hdead σ hloc]
  congr 1
  apply Res.bind_congr_ok
  rintro ⟨s, σ'⟩ hok
  cases s with
  | next => rfl
  | exit e => cases e <;> rfl
  | jump j vs =>
    exfalso
    simp only [evalOp] at hok
    rw [evalWhile.eq_1, loopHead] at hok
    obtain ⟨⟨ec, σ1⟩, _, hok⟩ := ok_bind_eq_ok hok
    cases ec with
    | cond bv =>
      cases bv
      · simp only [evalIterCleanup.eq_1, Res.ok_bind, Res.pure_eq] at hok; cases hok
      · obtain ⟨x, hx, _⟩ := ok_bind_eq_ok hok
        exact hdead σ1 x hx
    | exn _ => cases hok
    | halt _ => cases hok
    | longjmp _ _ => cases hok
    | _ => cases hok

theorem evalCall_body_loc_congr' {ctx₁ ctx₂ : Ctx} {sym : String} {fd₁ fd₂ : FuncDecl} {body₁ body₂ : Region}
    (hf₁ : ctx₁.mod.findFunc? sym = some fd₁) (hm₁ : fd₁.model = none) (hb₁ : fd₁.body = some body₁)
    (hf₂ : ctx₂.mod.findFunc? sym = some fd₂) (hm₂ : fd₂.model = none) (hb₂ : fd₂.body = some body₂)
    (hnt : fd₁.nothrow = fd₂.nothrow)
    (hs₁ : fd₁.special ≠ .dtor := by decide) (hs₂ : fd₂.special ≠ .dtor := by decide)
    (hbody : ∀ args σ, IsLocEnv [] σ → evalRegion ctx₁ body₁ args σ = evalRegion ctx₂ body₂ args σ) :
    ∀ vs m, evalCall ctx₁ sym vs m = evalCall ctx₂ sym vs m :=
  evalCall_body_loc_congr hf₁ hm₁ hb₁ hf₂ hm₂ hb₂ hnt hs₁ hs₂ hbody

theorem evalOp_scope_if_false (ctx : Ctx) (r_tmp r_var : VId) (t : Region) (σ : State) (b : Nat)
    (henv : σ.env r_var = some (.ptr (.loc b [])))
    (hblk : σ.mem.blocks b = some ⟨.stack, true, .bool, .bool false⟩) :
    evalOp ctx (.scope none (.mk [.mk [] [.load r_tmp r_var .bool, .ifOp r_tmp t (.mk [])]])) σ =
    .ok (.next, { σ with mem := σ.mem.endScope σ.mem.next }) := by
  simp only [evalOp, evalRegion.eq_2, evalBlock_zero, State.bindArgs, Res.ok_bind]
  rw [evalOps.eq_2]
  simp only [evalOp, evalSimple, State.getPtr, State.get, henv, Res.ofOption_some, Res.ok_bind, Res.pure_eq,
    loadPtr, Ctx.typedLoad, Ctx.unionView?, Ctx.viewVal?, Ctx.unionOnPath, Option.getD,
    Ctx.reach?, Ctx.reachIn, Ctx.reachTypeNone, Ctx.reachNone, splitByte, Ctx.typeAt,
    Mem.live?, hblk, splitLast, Option.map, reduceCtorEq, beq_self_eq_true,
    Ctx.punnedMember, Ty.atPath, Ty.isScalar, Ty.accessCompatible, Ty.isChar, Ty.hasBytes,
    Bool.and_true, Bool.and_false, Bool.true_or, Bool.or_true, Bool.not_true, Bool.not_false,
    loadTy, Mem.read?, Val.get?, Mem.punnedAccess, fitsTy, Bool.false_eq_true, ↓reduceIte, State.set]
  rw [evalOps.eq_2]
  simp only [evalOp, State.getBool, State.get, upd_same, Res.ofOption_some, Res.ok_bind, Res.pure_eq,
    Bool.false_eq_true, ↓reduceIte, evalRegion.eq_1, finishRegion]
  rw [evalOps.eq_1]
  simp only [Res.ok_bind, Exit.leaveMem, State.setResults]

theorem evalOps_breakLoop_false_prefix {ctx₁ ctx₂ : Ctx}
    {ty_this : Ty} {t₁ t₂ : Region} {rest₁ rest₂ : List Op}
    (hrest : ∀ σ, IsLocEnv [3, 2] σ → evalOps ctx₁ rest₁ σ = evalOps ctx₂ rest₂ σ)
    (x0 : Ptr) (m : Mem) :
    evalOps ctx₁
      (.alloca 2 (.ptr ty_this) "this" ::
       .alloca 3 .bool "error" ::
       .store 0 2 (.ptr ty_this) ::
       .store 1 3 .bool ::
       .load 4 2 (.ptr ty_this) ::
       .scope none (.mk [.mk [] [.load 5 3 .bool, .ifOp 5 t₁ (.mk [])]]) ::
       rest₁)
      { mem := m, env := upd (upd (fun _ => none) 0 (some (.ptr x0))) 1 (some (.bool false)), names := [] } =
    evalOps ctx₂
      (.alloca 2 (.ptr ty_this) "this" ::
       .alloca 3 .bool "error" ::
       .store 0 2 (.ptr ty_this) ::
       .store 1 3 .bool ::
       .load 4 2 (.ptr ty_this) ::
       .scope none (.mk [.mk [] [.load 5 3 .bool, .ifOp 5 t₂ (.mk [])]]) ::
       rest₂)
      { mem := m, env := upd (upd (fun _ => none) 0 (some (.ptr x0))) 1 (some (.bool false)), names := [] } := by
  have step5 : ∀ (ctx : Ctx) (t : Region) (rest : List Op),
      evalOps ctx
        (.alloca 2 (.ptr ty_this) "this" ::
         .alloca 3 .bool "error" ::
         .store 0 2 (.ptr ty_this) ::
         .store 1 3 .bool ::
         .load 4 2 (.ptr ty_this) ::
         .scope none (.mk [.mk [] [.load 5 3 .bool, .ifOp 5 t (.mk [])]]) ::
         rest)
        { mem := m, env := upd (upd (fun _ => none) 0 (some (.ptr x0))) 1 (some (.bool false)), names := [] } =
      evalOps ctx rest
        { mem :=
            Mem.endScope
              { blocks :=
                  upd
                    (upd
                      (upd
                        (upd m.blocks m.next
                          (some { kind := .stack, alive := true, ty := .ptr ty_this, val := .undef }))
                        (m.next + 1)
                        (some { kind := .stack, alive := true, ty := .bool, val := .undef }))
                      m.next
                      (some { kind := .stack, alive := true, ty := .ptr ty_this, val := .ptr x0 }))
                    (m.next + 1)
                    (some { kind := .stack, alive := true, ty := .bool, val := .bool false }),
                next := m.next + 2 } (m.next + 2),
          env :=
            upd
              (upd
                (upd
                  (upd (upd (fun _ => none) 0 (some (.ptr x0))) 1 (some (.bool false)))
                  2 (some (.ptr (.loc m.next []))))
                3 (some (.ptr (.loc (m.next + 1) []))))
              4 (some (.ptr x0)),
          names := [("error", m.next + 1), ("this", m.next)] } := by
    intro ctx t rest
    have h10 : (0 : VId) ≠ 1 := by decide
    have h20 : (0 : VId) ≠ 2 := by decide
    have h30 : (0 : VId) ≠ 3 := by decide
    have h21 : (1 : VId) ≠ 2 := by decide
    have h31 : (1 : VId) ≠ 3 := by decide
    have h23 : (2 : VId) ≠ 3 := by decide
    have h34 : (3 : VId) ≠ 4 := by decide
    have hne : m.next ≠ m.next + 1 := by omega
    rw [evalOps.eq_2]
    simp only [evalOp, evalSimple, Ctx.initVal, Mem.alloc, State.withMem, State.set, Res.ok_bind, Res.pure_eq]
    rw [evalOps.eq_2]
    simp only [evalOp, evalSimple, Ctx.initVal, Mem.alloc, State.withMem, State.set, Res.ok_bind, Res.pure_eq]
    rw [evalOps.eq_2]
    simp only [evalOp, evalSimple, State.get, State.getPtr,
      upd_ne _ _ _ _ h30, upd_ne _ _ _ _ h20, upd_ne _ _ _ _ h10,
      upd_ne _ _ _ _ h23, upd_same, Res.ofOption_some, Res.ok_bind, Res.pure_eq,
      missingAggCheck, Ctx.typedStore, Ctx.unionActivate?, Ctx.activateVal?, Ctx.unionOnPath, Option.getD,
      Ctx.reach?, Ctx.reachIn, Ctx.reachTypeNone, Ctx.reachNone, splitByte, Ctx.typeAt, beq_self_eq_true,
      Mem.live?, upd_ne _ _ _ _ hne,
      splitLast, Option.map, Ctx.punnedMember, Ty.atPath, Ty.isScalar, Ty.accessCompatible, Ty.isChar, Ty.hasBytes,
      Bool.and_true, Bool.and_false, Bool.true_or, Bool.or_true, Bool.not_true, Bool.not_false,
      storeTy, Mem.write?, Val.set?, Mem.punnedAccess, fitsTy,
      reduceCtorEq, Mem.setBlock, Bool.false_eq_true, ↓reduceIte, State.withMem]
    rw [evalOps.eq_2]
    simp only [evalOp, evalSimple, State.get, State.getPtr,
      upd_ne _ _ _ _ h31, upd_ne _ _ _ _ h21, upd_same,
      Res.ofOption_some, Res.ok_bind, Res.pure_eq,
      missingAggCheck, Ctx.typedStore, Ctx.unionActivate?, Ctx.activateVal?, Ctx.unionOnPath, Option.getD,
      Ctx.reach?, Ctx.reachIn, Ctx.reachTypeNone, Ctx.reachNone, splitByte, Ctx.typeAt, beq_self_eq_true,
      Mem.live?, upd_ne _ _ _ _ (Ne.symm hne),
      splitLast, Option.map, Ctx.punnedMember, Ty.atPath, Ty.isScalar, Ty.accessCompatible, Ty.isChar, Ty.hasBytes,
      Bool.and_true, Bool.and_false, Bool.true_or, Bool.or_true, Bool.not_true, Bool.not_false,
      storeTy, Mem.write?, Val.set?, Mem.punnedAccess, fitsTy,
      reduceCtorEq, Mem.setBlock, Bool.false_eq_true, ↓reduceIte, State.withMem]
    rw [evalOps.eq_2]
    simp only [evalOp, evalSimple, State.get, State.getPtr,
      upd_ne _ _ _ _ h23, upd_same, Res.ofOption_some, Res.ok_bind, Res.pure_eq,
      loadPtr, Ctx.typedLoad, Ctx.unionView?, Ctx.viewVal?, Ctx.unionOnPath, Option.getD,
      Ctx.reach?, Ctx.reachIn, Ctx.reachTypeNone, Ctx.reachNone, splitByte, Ctx.typeAt, reduceCtorEq, beq_self_eq_true,
      Mem.live?, upd_ne _ _ _ _ hne,
      splitLast, Option.map, Ctx.punnedMember, Ty.atPath, Ty.isScalar, Ty.accessCompatible, Ty.isChar, Ty.hasBytes,
      Bool.and_true, Bool.and_false, Bool.true_or, Bool.or_true, Bool.not_true, Bool.not_false,
      loadTy, Mem.read?, Val.get?, Mem.punnedAccess, fitsTy,
      Bool.false_eq_true, ↓reduceIte, State.set]
    rw [evalOps.eq_2, evalOp_scope_if_false ctx 5 3 t _ (m.next + 1)
      (by simp only [upd_ne _ _ _ _ h34, upd_same])
      (by simp only [upd_same])]
    rfl
  rw [step5 ctx₁ t₁ rest₁, step5 ctx₂ t₂ rest₂]
  apply hrest
  intro r hr
  rcases List.mem_cons.mp hr with rfl | hr
  · simp only [upd_ne _ _ _ _ (by decide : (3 : VId) ≠ 4), upd_same, IsLocPtr]
  · rcases List.mem_cons.mp hr with rfl | hr
    · simp only [upd_ne _ _ _ _ (by decide : (2 : VId) ≠ 4),
        upd_ne _ _ _ _ (by decide : (2 : VId) ≠ 3), upd_same, IsLocPtr]
    · cases hr

theorem evalCall_breakLoop_false_congr {ctx₁ ctx₂ : Ctx} {sym : String} {fd₁ fd₂ : FuncDecl}
    {ty_this : Ty} {t₁ t₂ : Region} {rest₁ rest₂ : List Op}
    (hf₁ : ctx₁.mod.findFunc? sym = some fd₁) (hm₁ : fd₁.model = none)
    (hb₁ : fd₁.body = some (.mk [.mk [0, 1]
      (.alloca 2 (.ptr ty_this) "this" :: .alloca 3 .bool "error" ::
       .store 0 2 (.ptr ty_this) :: .store 1 3 .bool :: .load 4 2 (.ptr ty_this) ::
       .scope none (.mk [.mk [] [.load 5 3 .bool, .ifOp 5 t₁ (.mk [])]]) :: rest₁)]))
    (hf₂ : ctx₂.mod.findFunc? sym = some fd₂) (hm₂ : fd₂.model = none)
    (hb₂ : fd₂.body = some (.mk [.mk [0, 1]
      (.alloca 2 (.ptr ty_this) "this" :: .alloca 3 .bool "error" ::
       .store 0 2 (.ptr ty_this) :: .store 1 3 .bool :: .load 4 2 (.ptr ty_this) ::
       .scope none (.mk [.mk [] [.load 5 3 .bool, .ifOp 5 t₂ (.mk [])]]) :: rest₂)]))
    (hnt : fd₁.nothrow = fd₂.nothrow)
    (hmj : (rest₂.any opMayJump) = false)
    (hrest : ∀ σ, IsLocEnv [3, 2] σ → evalOps ctx₁ rest₁ σ = evalOps ctx₂ rest₂ σ)
    (x0 : Ptr) (m : Mem)
    (hs₁ : fd₁.special ≠ .dtor := by decide) (hs₂ : fd₂.special ≠ .dtor := by decide) :
    evalCall ctx₁ sym [.ptr x0, .bool false] m = evalCall ctx₂ sym [.ptr x0, .bool false] m := by
  rw [evalCall_body hf₁ hm₁ hb₁ hs₁, evalCall_body hf₂ hm₂ hb₂ hs₂]
  congr 1
  · rw [evalRegion.eq_2, evalRegion.eq_2, evalBlock_zero, evalBlock_zero]
    simp only [State.bindArgs, State.set, Res.ok_bind]
    congr 1
    have hmj_all : ((.alloca 2 (.ptr ty_this) "this" :: .alloca 3 .bool "error" ::
       .store 0 2 (.ptr ty_this) :: .store 1 3 .bool :: .load 4 2 (.ptr ty_this) ::
       .scope none (.mk [.mk [] [.load 5 3 .bool, .ifOp 5 t₂ (.mk [])]]) :: rest₂).any opMayJump) = false := by
      simp only [List.any_cons, opMayJump, Bool.false_or, hmj]
    rw [evalOps_breakLoop_false_prefix hrest x0 m]
    apply Res.bind_congr_ok
    rintro ⟨s, σ₂⟩ hok
    cases s with
    | exit e => cases e <;> rfl
    | jump j vs =>
      have h1 : (evalOps ctx₂
        (.alloca 2 (.ptr ty_this) "this" :: .alloca 3 .bool "error" ::
         .store 0 2 (.ptr ty_this) :: .store 1 3 .bool :: .load 4 2 (.ptr ty_this) ::
         .scope none (.mk [.mk [] [.load 5 3 .bool, .ifOp 5 t₂ (.mk [])]]) :: rest₂)
        { mem := m, env := upd (upd (fun _ => none) 0 (some (.ptr x0))) 1 (some (.bool false)), names := [] }).holds (fun _ => True) := by
        rw [hok]; trivial
      have h2 := evalOps_not_jump hmj_all h1
      rw [hok] at h2
      exact False.elim (h2.1 j vs rfl)
    | next => rfl
  · funext ⟨e, σ⟩; cases e <;> simp only [hnt]

theorem loadTy_int_is_int {m : Mem} {s : Bool} {w : Nat} {p : Ptr} {v : Val}
    (h : loadTy m (.int s w) p = .ok v) : ∃ n, v = .int n := by
  unfold loadTy at h
  split at h; · cases h
  rcases h1 : m.read? p with _ | vr <;> rw [h1] at h
  · cases h
  · dsimp only [Ty.isScalar, ↓reduceIte] at h
    cases vr <;> try (dsimp only [fitsTy, Bool.false_eq_true, ↓reduceIte] at h; cases h)
    rename_i n
    by_cases hr : inRange s w n = true
    · simp only [fitsTy, hr, ↓reduceIte] at h; cases h; exact ⟨_, rfl⟩
    · simp only [fitsTy, hr, Bool.false_eq_true, ↓reduceIte] at h
      split at h <;> cases h; exact ⟨_, rfl⟩

theorem byteLoad_int_is_int {m : Mem} {s : Bool} {w : Nat} {b : Nat} {path : List PathElem} {t : Ty} {k : Nat} {v : Val}
    (h : byteLoad m (.int s w) b path t k = .ok v) : ∃ n, v = .int n := by
  unfold byteLoad byteLoadOf at h
  rcases w with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ <;> try cases h
  rcases h1 : m.read? (.loc b path) with _ | vr <;> rw [h1] at h
  · cases h
  · dsimp only at h
    rcases h2 : byteOf t vr k with _ | c <;> rw [h2] at h <;> cases h
    exact ⟨_, rfl⟩

theorem reachScalar_not_spread {ty : Ty} {k0 : Nat} {x : List PathElem × Ty × Nat} {p' : List PathElem} {t' : Ty} :
    reachScalar ty k0 x ≠ .spread p' t' := by
  rcases x with ⟨path, t, k⟩
  unfold reachScalar
  repeat (first | (intro h; cases h) | split)

theorem reachIn_int_not_spread {ctx : Ctx} {blk : MemBlock} {s : Bool} {w : Nat} {path : List PathElem} {p' : List PathElem} {t' : Ty} :
    ctx.reachIn blk (.int s w) path ≠ some (.spread p' t') := by
  unfold Ctx.reachIn
  split; · intro h; cases h
  unfold Ctx.reachSlow
  split; · intro h; cases h
  rcases ctx.typeAt blk.ty (splitByte path).1 with _ | t
  · simp [Ty.isAggregate]
  · simp only [Ty.isScalar, ↓reduceIte]
    unfold Ctx.reachScalarAt
    split <;> try (intro h; cases h)
    rcases (if blk.alive then blk.val.get? (splitByte path).1 else none) with _ | v
    · intro h; cases h
    · dsimp only
      split
      · rcases ctx.scalarIn 32 t v (splitByte path).1 (splitByte path).2 with _ | sc
        · intro h; cases h
        · dsimp only [Option.elim]
          intro h
          exact reachScalar_not_spread (Option.some.inj h)
      · intro h; cases h

theorem typedLoad_int_is_int {ctx : Ctx} {m : Mem} {s : Bool} {w : Nat} {p : Ptr} {v : Val}
    (h : ctx.typedLoad m (.int s w) p = .ok v) : ∃ n, v = .int n := by
  unfold Ctx.typedLoad at h
  dsimp only at h
  rcases hr : ctx.reach? ((ctx.unionView? m p).getD m) (.int s w) p with _ | ⟨b, r⟩ <;> rw [hr] at h
  · dsimp only at h
    split at h; · cases h
    exact loadTy_int_is_int h
  · cases r with
    | byte path t k => exact byteLoad_int_is_int h
    | obj path => exact loadTy_int_is_int h
    | punned => cases h
    | external => cases h
    | spread path t =>
      exfalso
      cases p <;> try cases hr
      rename_i bp pathp
      simp only [Ctx.reach?] at hr
      rcases hblk : ((ctx.unionView? m (.loc bp pathp)).getD m).blocks bp with _ | blk <;> rw [hblk] at hr
      · cases hr
      · simp only [Option.map] at hr
        rcases hri : ctx.reachIn blk (.int s w) pathp with _ | r' <;> rw [hri] at hr <;> cases hr
        exact reachIn_int_not_spread hri

theorem evalOps_const_int_cmp_loc_congr {ctx₁ ctx₂ : Ctx} {rs : List VId}
    {r_c r_cmp r_a : VId} {s : Bool} {w : Nat} {n : Int} {k : CmpKind} {ty_cmp : Ty}
    {ops₁ ops₂ : List Op}
    (hnc : decide (r_c ∈ rs) = false)
    (hncmp : decide (r_cmp ∈ rs) = false)
    (hops : ∀ σ, IsLocEnv rs σ → evalOps ctx₁ ops₁ σ = evalOps ctx₂ ops₂ σ)
    (σ : State) (hloc : IsLocEnv rs σ) :
    evalOps ctx₁ (.const r_c (.int s w) (.int n) :: .cmp r_cmp k r_a r_c ty_cmp :: ops₁) σ =
    evalOps ctx₂ (.const r_c (.int s w) (.int n) :: .cmp r_cmp k r_a r_c ty_cmp :: ops₂) σ := by
  rw [evalOps.eq_2, evalOps.eq_2]
  simp only [evalOp, evalSimple, Ctx.constVal]
  split
  · simp only [Res.ofOption_some, Res.ok_bind, Res.pure_eq]
    rw [evalOps.eq_2, evalOps.eq_2]
    have hcmp : evalOp ctx₁ (.cmp r_cmp k r_a r_c ty_cmp) (σ.set r_c (.int n)) =
                evalOp ctx₂ (.cmp r_cmp k r_a r_c ty_cmp) (σ.set r_c (.int n)) := by
      simp only [evalOp, evalSimple, State.get]
      rcases (σ.set r_c (.int n)).env r_a with _ | va <;> try rfl
      have hrc : (σ.set r_c (.int n)).env r_c = some (.int n) := by simp only [State.set, upd_same]
      rw [hrc]
      simp only [Res.ofOption_some, Res.ok_bind, Res.pure_eq, evalCmpB_of_int ctx₁ ctx₂]
    rw [hcmp]
    apply Res.bind_congr_ok
    rintro ⟨st, σ'⟩ hok
    cases st with
    | next =>
      have hloc1 := isLocEnv_set_other (v := .int n) hloc hnc
      have hloc2 := evalOp_pres_singleWrite (ctx := ctx₂) rfl hncmp hloc1 hok
      exact hops σ' hloc2
    | exit _ => rfl
    | jump _ _ => rfl
  · rfl

theorem evalOps_load_int_cmp_loc_congr {ctx₁ ctx₂ : Ctx}
    (hr : ∀ name, ctx₁.record? name = ctx₂.record? name)
    (hp : ctx₁.mod.ptrBytes = ctx₂.mod.ptrBytes := by rfl)
    {rs : List VId} {r_b r_ptr r_cmp r_a : VId} {s : Bool} {w : Nat} {k : CmpKind} {ty_cmp : Ty}
    {ops₁ ops₂ : List Op}
    (hptr : decide (r_ptr ∈ rs) = true)
    (hnb : decide (r_b ∈ rs) = false)
    (hncmp : decide (r_cmp ∈ rs) = false)
    (hops : ∀ σ, IsLocEnv rs σ → evalOps ctx₁ ops₁ σ = evalOps ctx₂ ops₂ σ)
    (σ : State) (hloc : IsLocEnv rs σ) :
    evalOps ctx₁ (.load r_b r_ptr (.int s w) :: .cmp r_cmp k r_a r_b ty_cmp :: ops₁) σ =
    evalOps ctx₂ (.load r_b r_ptr (.int s w) :: .cmp r_cmp k r_a r_b ty_cmp :: ops₂) σ := by
  rw [evalOps.eq_2, evalOps.eq_2, evalOp_load_congr_of_loc hr hp hloc hptr]
  apply Res.bind_congr_ok
  rintro ⟨st1, σ1⟩ hok1
  cases st1 with
  | exit _ => rfl
  | jump _ _ => rfl
  | next =>
    dsimp only
    have hloc1 := evalOp_pres_singleWrite (ctx := ctx₂) rfl hnb hloc hok1
    have hint : ∃ n, σ1.env r_b = some (.int n) := by
      have hlp := hloc r_ptr (of_decide_eq_true hptr)
      simp only [evalOp, evalSimple, State.getPtr, State.get] at hok1
      rcases h : σ.env r_ptr with _ | vp <;> rw [h] at hlp <;> try cases hlp
      cases vp <;> try cases hlp
      rename_i p
      cases p <;> try cases hlp
      simp only [h, Res.ofOption_some, Res.ok_bind, Res.pure_eq, loadPtr] at hok1
      obtain ⟨σ0, h0, h2⟩ := ok_bind_eq_ok hok1; cases h2
      obtain ⟨v, hv, h0⟩ := ok_bind_eq_ok h0; cases h0
      obtain ⟨n, rfl⟩ := typedLoad_int_is_int hv
      exact ⟨n, by simp only [State.set, upd_same]⟩
    obtain ⟨n, hrb⟩ := hint
    rw [evalOps.eq_2, evalOps.eq_2]
    have hcmp : evalOp ctx₁ (.cmp r_cmp k r_a r_b ty_cmp) σ1 =
                evalOp ctx₂ (.cmp r_cmp k r_a r_b ty_cmp) σ1 := by
      simp only [evalOp, evalSimple, State.get]
      rcases σ1.env r_a with _ | va <;> try rfl
      rw [hrb]
      simp only [Res.ofOption_some, Res.ok_bind, Res.pure_eq, evalCmpB_of_int ctx₁ ctx₂]
    rw [hcmp]
    apply Res.bind_congr_ok
    rintro ⟨st2, σ2⟩ hok2
    cases st2 with
    | next => exact hops σ2 (evalOp_pres_singleWrite (ctx := ctx₂) rfl hncmp hloc1 hok2)
    | exit _ => rfl
    | jump _ _ => rfl

macro "cir_loc_call" : tactic => `(tactic| first
  | (intro vs m; exact evalCall_model_congr (by cir_lookup) rfl (by cir_lookup) rfl (runModel_pthreadSelf_congr _ _) vs m)
  | (intro vs m; exact evalCall_model_congr (by cir_lookup) rfl (by cir_lookup) rfl (runModel_pthreadEqual_congr _ _) vs m)
  | (intro vs m; exact evalCall_model_congr (by cir_lookup) rfl (by cir_lookup) rfl (runModel_eventBaseLoopbreak_congr _ _) vs m)
  | refine evalCall_body_loc_congr' (by cir_lookup) rfl rfl (by cir_lookup) rfl rfl rfl (by decide) (by decide) ?_)

macro "cir_loc_congr" hr:term:max : tactic => `(tactic| (
  repeat' first
    | (intro σ _; exact evalOps_nil_congr _ _ σ)
    | (intro σ _; exact evalRegion_nil_congr _ _ _ σ)
    | (intro σ hloc; refine evalRegion_single_whileOp_dead_loc_congr ?_ ?_ ?_ σ hloc)
    | (intro σ hloc; refine evalRegion_single_loc_congr rfl rfl rfl rfl ?_ _ σ hloc)
    | (intro args σ hloc; refine evalRegion_single_loc_congr rfl rfl rfl rfl ?_ args σ hloc)
    | (intro σ hloc; refine evalRegion_two_first_nojump rfl rfl rfl ?_ σ hloc)
    | (intro σ _; exact evalOps_call_ext_dead (by cir_lookup) rfl rfl (by cir_lookup) rfl rfl σ)
    | (intro σ x; refine evalRegion_single_not_ok ?_ σ x)
    | (intro σ x; refine evalOps_scope_not_ok ?_ σ x)
    | (intro σ x; refine evalOps_simple_not_ok rfl ?_ σ x)
    | (intro σ x; exact evalOps_call_ext_not_ok (by cir_lookup) rfl rfl σ x)
    | (intro σ hloc; refine evalOps_const_int_cmp_loc_congr rfl rfl ?_ σ hloc)
    | (intro σ hloc; refine evalOps_load_int_cmp_loc_congr $hr rfl rfl rfl ?_ σ hloc)
    | (intro σ hloc; refine evalOps_cons_loc_congr
        (fun σ _ => evalOp_simple_nonload_congr $hr rfl rfl σ)
        (fun _ _ h hok => evalOp_pres_alloca h hok) ?_ σ hloc)
    | (intro σ hloc; refine evalOps_cons_loc_congr
        (fun σ _ => evalOp_simple_nonload_congr $hr rfl rfl σ)
        (fun _ _ h hok => evalOp_pres_getMember h hok) ?_ σ hloc)
    | (intro σ hloc; refine evalOps_cons_loc_congr
        (fun σ _ => evalOp_simple_nonload_congr $hr rfl rfl σ)
        (fun _ _ h hok => evalOp_pres_getElement h hok) ?_ σ hloc)
    | (intro σ hloc; refine evalOps_cons_loc_congr
        (fun σ _ => evalOp_simple_nonload_congr $hr rfl rfl σ)
        (fun _ _ h hok => evalOp_pres_store h hok) ?_ σ hloc)
    | (intro σ hloc; refine evalOps_cons_loc_congr
        (fun σ _ => evalOp_simple_nonload_congr $hr rfl rfl σ)
        (fun _ _ h hok => evalOp_pres_copy h hok) ?_ σ hloc)
    | (intro σ hloc; refine evalOps_cons_loc_congr
        (fun σ h => evalOp_load_congr_of_loc $hr h rfl)
        (fun _ _ h hok => evalOp_pres_singleWrite rfl rfl h hok) ?_ σ hloc)
    | (intro σ hloc; refine evalOps_cons_loc_congr
        (fun σ _ => evalOp_simple_nonload_congr $hr rfl rfl σ)
        (fun _ _ h hok => evalOp_pres_singleWrite rfl rfl h hok) ?_ σ hloc)
    | (intro σ hloc; refine evalOps_cons_loc_congr
        (fun σ _ => evalOp_getGlobal_fn_congr rfl (by cir_lookup) rfl (by cir_lookup) σ)
        (fun _ _ h hok => evalOp_pres_singleWrite rfl rfl h hok) ?_ σ hloc)
    | (intro σ _; refine evalOps_cons_congr
        (fun σ => evalOp_terminator_congr rfl σ)
        (fun σ => evalOps_nil_congr _ _ σ) σ)
    | (intro σ hloc; refine evalOps_cons_loc_congr
        (fun σ h => evalOp_scope_loc_congr ?_ σ h)
        (fun _ _ h hok => evalOp_pres_scope h rfl hok) ?_ σ hloc)
    | (intro σ hloc; refine evalOps_cons_loc_congr
        (fun σ h => evalOp_ifOp_loc_congr ?_ ?_ σ h)
        (fun _ _ h hok => evalOp_pres_ifOp h hok) ?_ σ hloc)
    | (intro σ hloc; refine evalOps_cons_loc_congr
        (fun σ h => evalOp_tryOp_all_congr ?_ σ h)
        (fun _ _ h hok => evalOp_pres_tryOp_all h hok) ?_ σ hloc)
    | (intro σ hloc; refine evalOps_cons_loc_congr
        (fun σ _ => evalOp_call_direct_congr ?_ σ)
        (fun _ _ h hok => evalOp_pres_call_direct h rfl hok) ?_ σ hloc)
    | cir_loc_call))

/-! ### `spClosed`: Fixpoint Induction Congruence for `TEvhttpServer::complete` -/

def RelEq {α : Type} (x y : Res α) : Prop :=
  x = .div ∨ x = y

theorem relEq_refl {α : Type} (x : Res α) : RelEq x x :=
  Or.inr rfl

theorem relEq_of_eq {α : Type} {x y : Res α} (h : x = y) : RelEq x y :=
  Or.inr h

theorem relEq_antisymm {α : Type} {x y : Res α} (h1 : RelEq x y) (h2 : RelEq y x) : x = y := by
  rcases h1 with rfl | h1
  · rcases h2 with rfl | h2
    · rfl
    · exact h2.symm
  · exact h1

theorem relEq_bind {α β : Type} {x₁ x₂ : Res α} {f₁ f₂ : α → Res β}
    (hx : RelEq x₁ x₂) (hf : ∀ a, x₂ = .ok a → RelEq (f₁ a) (f₂ a)) :
    RelEq (x₁ >>= f₁) (x₂ >>= f₂) := by
  rcases hx with rfl | rfl
  · exact Or.inl rfl
  · cases x₁ with
    | ok a => exact hf a rfl
    | ub _ => exact Or.inr rfl
    | div => exact Or.inl rfl

theorem relEq_bind_same {α β : Type} (x : Res α) {f₁ f₂ : α → Res β}
    (hf : ∀ a, x = .ok a → RelEq (f₁ a) (f₂ a)) :
    RelEq (x >>= f₁) (x >>= f₂) :=
  relEq_bind (relEq_refl x) hf

theorem admissible_relEq {α : Type} (H : Prop) (y : Res α) :
    Lean.Order.admissible (fun x : Res α => H → RelEq x y) :=
  Lean.Order.admissible_flatOrder (b := (Res.div : Res α)) _ (fun _ => Or.inl rfl)

def isSpCls (clsName : String) : Bool :=
  clsName == "std::_Sp_counted_base<__gnu_cxx::_S_atomic>" ||
  clsName == "std::_Sp_counted_ptr<apache::thrift::TConfiguration *, __gnu_cxx::_S_atomic>" ||
  clsName == "std::_Sp_counted_ptr<apache::thrift::transport::TMemoryBuffer *, __gnu_cxx::_S_atomic>" ||
  clsName == "apache::thrift::transport::TMemoryBuffer"

inductive VCallState where
  | s0 | s1 | s2 | s3 | s4 | s5 (r_c : VId)

mutual
def spOkOp (goodSym : String → Bool) : Op → Bool
  | .getGlobal _ sym _ => sym == "__libc_single_threaded"
  | .call _ _ (.direct sym) _ _ _ _ => goodSym sym
  | .call .. => false
  | .scope _ r => spOkRegion goodSym r
  | .cleanupScope _ b c => spOkRegion goodSym b && spOkRegion goodSym c
  | .ifOp _ t e | .ternary _ _ t e => spOkRegion goodSym t && spOkRegion goodSym e
  | .tryOp b [(.all, hreg)] none => spOkRegion goodSym b && spOkRegion goodSym hreg
  | .tryOp .. | .forOp .. | .whileOp .. | .doWhileOp .. | .switch .. | .setjmp .. | .setjmpRun .. | .libc .. | .vtableAddressPoint .. => false
  | op => isSimpleNonCmpOp op || isCtxFreeTerminatorOp op

def spOkOps (goodSym : String → Bool) : VCallState → VId → VId → List Op → Bool
  | .s0, _, _, [] => true
  | .s0, _, _, .vtableGetVptr r_vp r_this (.record clsName) :: ops =>
      isSpCls clsName && decide (r_this ≠ r_vp) && spOkOps goodSym .s1 r_this r_vp ops
  | .s0, _, _, .const r_c ty c :: (.cmp r_cmp k r_a r_c' ty_cmp :: ops) =>
      isConstIntOrNull c && spOkOps goodSym (.s5 r_c) 0 0 (.cmp r_cmp k r_a r_c' ty_cmp :: ops)
  | .s5 r_c, _, _, .cmp _ k _ r_c' _ :: ops =>
      decide (r_c = r_c') && (k == .eq || k == .ne) && spOkOps goodSym .s0 0 0 ops
  | .s1, r_this, r_vp, .load r_vptr r_vp' .vptr :: ops =>
      decide (r_vp = r_vp') && decide (r_this ≠ r_vptr) && spOkOps goodSym .s2 r_this r_vptr ops
  | .s2, r_this, r_vptr, .vtableGetVirtualFnAddr r_fnaddr r_vptr' _ :: ops =>
      decide (r_vptr = r_vptr') && decide (r_this ≠ r_fnaddr) && spOkOps goodSym .s3 r_this r_fnaddr ops
  | .s3, r_this, r_fnaddr, .load r_fn r_fnaddr' (.ptr _) :: ops =>
      decide (r_fnaddr = r_fnaddr') && decide (r_this ≠ r_fn) && spOkOps goodSym .s4 r_this r_fn ops
  | .s4, r_this, r_fn, .call _ _ (.indirect r_fn') [r_this'] [.ptr (.record clsName)] _ _ :: ops =>
      decide (r_this = r_this') && decide (r_fn = r_fn') && isSpCls clsName && spOkOps goodSym .s0 0 0 ops
  | .s0, _, _, op :: ops =>
      spOkOp goodSym op && spOkOps goodSym .s0 0 0 ops
  | _, _, _, _ => false

def spOkBlocks (goodSym : String → Bool) : List Block → Bool
  | [] => true
  | .mk _ ops :: bs => spOkOps goodSym .s0 0 0 ops && spOkBlocks goodSym bs

def spOkRegion (goodSym : String → Bool) : Region → Bool
  | .mk bs => spOkBlocks goodSym bs
end

def vcallInv (ctx : Ctx) : VCallState → VId → VId → State → Prop
  | .s0, _, _, _ => True
  | .s1, r_this, _, σ => ∃ b path, σ.env r_this = some (.ptr (.loc b path))
  | .s2, r_this, _, σ => ∃ b path, σ.env r_this = some (.ptr (.loc b path))
  | .s3, r_this, r_addr, σ =>
      (∃ b path, σ.env r_this = some (.ptr (.loc b path))) ∧
      (∃ vt i k, σ.env r_addr = some (.ptr (.vtable vt i k)))
  | .s4, r_this, r_fn, σ =>
      (∃ b path, σ.env r_this = some (.ptr (.loc b path))) ∧
      (∃ vt i k v_fn, ctx.vtableSlot? vt i k = some v_fn ∧ σ.env r_fn = some v_fn)
  | .s5 r_c, _, _, σ => (∃ n, σ.env r_c = some (.int n)) ∨ (∃ b, σ.env r_c = some (.bool b)) ∨ σ.env r_c = some (.ptr .null)

theorem spOkOps_zero_cons {goodSym : String → Bool} {r1 r2 : VId} {op : Op} {ops : List Op}
    (h : spOkOps goodSym .s0 r1 r2 (op :: ops) = true) :
    (∃ r_vp r_this clsName, op = .vtableGetVptr r_vp r_this (.record clsName) ∧
      isSpCls clsName = true ∧ r_this ≠ r_vp ∧ spOkOps goodSym .s1 r_this r_vp ops = true) ∨
    (∃ r_c ty c, op = .const r_c ty c ∧ isConstIntOrNull c = true ∧
      spOkOps goodSym (.s5 r_c) 0 0 ops = true) ∨
    (spOkOp goodSym op = true ∧ spOkOps goodSym .s0 0 0 ops = true) := by
  unfold spOkOps at h
  cases op with
  | vtableGetVptr r_vp r_this ty =>
    cases ty with
    | record clsName =>
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      exact Or.inl ⟨_, _, _, rfl, h.1.1, h.1.2, h.2⟩
    | _ =>
      simp only [Bool.and_eq_true] at h
      exact Or.inr (Or.inr h)
  | const r_c ty c =>
    cases ops with
    | nil =>
      simp only [Bool.and_eq_true] at h
      exact Or.inr (Or.inr h)
    | cons op2 rest =>
      cases op2 with
      | cmp r_cmp k r_a r_c' ty_cmp =>
        simp only [Bool.and_eq_true] at h
        exact Or.inr (Or.inl ⟨r_c, ty, c, rfl, h.1, h.2⟩)
      | _ =>
        simp only [Bool.and_eq_true] at h
        exact Or.inr (Or.inr h)
  | _ =>
    simp only [Bool.and_eq_true] at h
    exact Or.inr (Or.inr h)

theorem spOkOps_s5_cons {goodSym : String → Bool} {r_c r1 r2 : VId} {op : Op} {ops : List Op}
    (h : spOkOps goodSym (.s5 r_c) r1 r2 (op :: ops) = true) :
    ∃ r_cmp k r_a ty, op = .cmp r_cmp k r_a r_c ty ∧ (k == .eq || k == .ne) = true ∧
      spOkOps goodSym .s0 0 0 ops = true := by
  cases op <;> try cases h
  rename_i r_cmp k r_a r_c' ty
  simp only [spOkOps, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨r_cmp, k, r_a, ty, h.1.1 ▸ rfl, h.1.2, h.2⟩

theorem spOkOps_s1_cons {goodSym : String → Bool} {r_this r_vp : VId} {op : Op} {ops : List Op}
    (h : spOkOps goodSym .s1 r_this r_vp (op :: ops) = true) :
    ∃ r_vptr, op = .load r_vptr r_vp .vptr ∧ r_this ≠ r_vptr ∧ spOkOps goodSym .s2 r_this r_vptr ops = true := by
  cases op <;> try cases h
  rename_i r_vptr r_vp' ty
  cases ty <;> try cases h
  simp only [spOkOps, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨r_vptr, h.1.1 ▸ rfl, h.1.2, h.2⟩

theorem spOkOps_s2_cons {goodSym : String → Bool} {r_this r_vptr : VId} {op : Op} {ops : List Op}
    (h : spOkOps goodSym .s2 r_this r_vptr (op :: ops) = true) :
    ∃ r_fnaddr slot, op = .vtableGetVirtualFnAddr r_fnaddr r_vptr slot ∧ r_this ≠ r_fnaddr ∧
      spOkOps goodSym .s3 r_this r_fnaddr ops = true := by
  cases op <;> try cases h
  rename_i r_fnaddr r_vptr' slot
  simp only [spOkOps, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨r_fnaddr, slot, h.1.1 ▸ rfl, h.1.2, h.2⟩

theorem spOkOps_s3_cons {goodSym : String → Bool} {r_this r_fnaddr : VId} {op : Op} {ops : List Op}
    (h : spOkOps goodSym .s3 r_this r_fnaddr (op :: ops) = true) :
    ∃ r_fn fnTy, op = .load r_fn r_fnaddr (.ptr fnTy) ∧ r_this ≠ r_fn ∧
      spOkOps goodSym .s4 r_this r_fn ops = true := by
  cases op <;> try cases h
  rename_i r_fn r_fnaddr' ty
  cases ty <;> try cases h
  rename_i fnTy
  simp only [spOkOps, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨r_fn, fnTy, h.1.1 ▸ rfl, h.1.2, h.2⟩

theorem spOkOps_s4_cons {goodSym : String → Bool} {r_this r_fn : VId} {op : Op} {ops : List Op}
    (h : spOkOps goodSym .s4 r_this r_fn (op :: ops) = true) :
    ∃ loc res clsName retTy nt,
      op = .call loc res (.indirect r_fn) [r_this] [.ptr (.record clsName)] retTy nt ∧
      isSpCls clsName = true ∧ spOkOps goodSym .s0 0 0 ops = true := by
  cases op <;> try cases h
  rename_i loc res callee args argTys retTy nt
  cases callee <;> try cases h
  rcases args with _ | ⟨r_this', _ | _⟩ <;> try cases h
  rcases argTys with _ | ⟨aty, restT⟩ <;> try cases h
  cases aty <;> try cases h
  rename_i pty
  cases pty <;> try cases h
  cases restT <;> try cases h
  simp only [spOkOps, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨loc, res, _, retTy, nt, by rw [h.1.1.1, h.1.1.2], h.1.2, h.2⟩

theorem spOkBlocks_getElem {goodSym : String → Bool} {bs : List Block} {i : Nat} {params : List VId} {ops : List Op}
    (hbs : spOkBlocks goodSym bs = true) (hi : bs[i]? = some (.mk params ops)) :
    spOkOps goodSym .s0 0 0 ops = true := by
  induction bs generalizing i with
  | nil => cases hi
  | cons b bs ih =>
    cases b with
    | mk ps ops' =>
      simp only [spOkBlocks, Bool.and_eq_true] at hbs
      cases i with
      | zero => cases hi; exact hbs.1
      | succ i => exact ih hbs.2 hi

def opCallsDtor (ctx : Ctx) (op : Op) : Bool :=
  match op with
  | .call _ _ (.direct s) _ _ _ _ => (ctx.mod.findFunc? s).any (·.special == .dtor)
  | _ => false

theorem callsDestructor_eq_of_spOkOps {ctx₁ ctx₂ : Ctx} {goodSym : String → Bool}
    (hf : ∀ sym, goodSym sym = true → (ctx₁.mod.findFunc? sym).any (·.special == .dtor) = (ctx₂.mod.findFunc? sym).any (·.special == .dtor)) :
    ∀ st r1 r2 ops, spOkOps goodSym st r1 r2 ops = true →
      ops.any (opCallsDtor ctx₁) = ops.any (opCallsDtor ctx₂) := by
  intro st r1 r2 ops
  induction ops generalizing st r1 r2 with
  | nil => intros; rfl
  | cons op ops ih =>
    intro h
    cases st with
    | s0 =>
      rcases spOkOps_zero_cons h with ⟨r_vp, r_this, clsName, rfl, _, _, h2⟩ | ⟨r_c, ty, c, rfl, _, h2⟩ | ⟨h1, h2⟩
      · simp only [List.any_cons, opCallsDtor, Bool.false_or]
        exact ih .s1 r_this r_vp h2
      · simp only [List.any_cons, opCallsDtor, Bool.false_or]
        exact ih (.s5 r_c) 0 0 h2
      · simp only [List.any_cons, ih .s0 0 0 h2]
        cases op <;> try rfl
        rename_i loc res callee args argTys retTy nt
        cases callee with
        | direct s =>
          simp only [spOkOp] at h1
          simp only [opCallsDtor, hf s h1]
        | indirect _ => cases h1
    | s5 r_c =>
      rcases spOkOps_s5_cons h with ⟨_, _, _, _, rfl, _, h2⟩
      simp only [List.any_cons, opCallsDtor, Bool.false_or]
      exact ih .s0 0 0 h2
    | s1 =>
      rcases spOkOps_s1_cons h with ⟨r_vptr, rfl, _, h2⟩
      simp only [List.any_cons, opCallsDtor, Bool.false_or]
      exact ih .s2 r1 r_vptr h2
    | s2 =>
      rcases spOkOps_s2_cons h with ⟨r_fnaddr, _, rfl, _, h2⟩
      simp only [List.any_cons, opCallsDtor, Bool.false_or]
      exact ih .s3 r1 r_fnaddr h2
    | s3 =>
      rcases spOkOps_s3_cons h with ⟨r_fn, _, rfl, _, h2⟩
      simp only [List.any_cons, opCallsDtor, Bool.false_or]
      exact ih .s4 r1 r_fn h2
    | s4 =>
      rcases spOkOps_s4_cons h with ⟨_, _, _, _, _, rfl, _, h2⟩
      simp only [List.any_cons, opCallsDtor, Bool.false_or]
      exact ih .s0 0 0 h2

theorem callsDestructor_eq_of_spOkRegion {ctx₁ ctx₂ : Ctx} {goodSym : String → Bool}
    (hf : ∀ sym, goodSym sym = true → (ctx₁.mod.findFunc? sym).any (·.special == .dtor) = (ctx₂.mod.findFunc? sym).any (·.special == .dtor))
    {cl : Region} (hcl : spOkRegion goodSym cl = true) :
    callsDestructor ctx₁ cl = callsDestructor ctx₂ cl := by
  cases cl with
  | mk bs =>
    simp only [spOkRegion] at hcl
    change (bs.any fun (.mk _ ops) => ops.any (opCallsDtor ctx₁)) =
           (bs.any fun (.mk _ ops) => ops.any (opCallsDtor ctx₂))
    induction bs with
    | nil => rfl
    | cons b bs ih =>
      cases b with
      | mk ps ops =>
        simp only [spOkBlocks, Bool.and_eq_true] at hcl
        simp only [List.any_cons, callsDestructor_eq_of_spOkOps hf .s0 0 0 ops hcl.1, ih hcl.2]

theorem vcallInv_step_s0_s1 {ctx : Ctx} {r_vp r_this : VId} {clsName : String} {σ σ' : State}
    (hne : r_this ≠ r_vp)
    (hok : evalOp ctx (.vtableGetVptr r_vp r_this (.record clsName)) σ = .ok (.next, σ')) :
    vcallInv ctx .s1 r_this r_vp σ' := by
  simp only [evalOp, evalSimple] at hok
  obtain ⟨σ1, h1, h2⟩ := ok_bind_eq_ok hok; cases h2
  obtain ⟨p, hp, h1⟩ := ok_bind_eq_ok h1
  cases p <;> try cases h1
  rename_i b path
  rcases hcls : ctx.vptrClass? σ.mem (.loc b path) (.record clsName) with _ | n <;>
    rw [hcls] at h1 <;> try cases h1
  obtain ⟨vp, -, h1⟩ := ok_bind_eq_ok h1; cases h1
  simp only [State.getPtr, State.get] at hp
  rcases hth : σ.env r_this with _ | v <;> rw [hth] at hp <;> try cases hp
  cases v <;> try cases hp
  exact ⟨b, path, by simp only [State.set, upd_ne _ _ _ _ hne, hth]⟩

theorem vcallInv_step_s0_s5 {ctx : Ctx} {r_c : VId} {ty : Ty} {c : Const} {σ σ' : State}
    (hc : isConstIntOrNull c = true)
    (hok : evalOp ctx (.const r_c ty c) σ = .ok (.next, σ')) :
    vcallInv ctx (.s5 r_c) 0 0 σ' := by
  simp only [evalOp, evalSimple] at hok
  obtain ⟨σ1, h1, h2⟩ := ok_bind_eq_ok hok; cases h2
  obtain ⟨v, hv, h1⟩ := ok_bind_eq_ok h1; cases h1
  rcases hcv : ctx.constVal 32 ty c with _ | v' <;> rw [hcv] at hv <;> cases hv
  rcases constVal_int_or_null hc hcv with ⟨n, rfl⟩ | ⟨b, rfl⟩ | rfl
  · exact Or.inl ⟨n, by simp only [State.set, upd_same]⟩
  · exact Or.inr (Or.inl ⟨b, by simp only [State.set, upd_same]⟩)
  · exact Or.inr (Or.inr (by simp only [State.set, upd_same]))

theorem vcallInv_step_s1_s2 {ctx : Ctx} {r_this r_vp r_vptr : VId} {σ σ' : State}
    (hinv : vcallInv ctx .s1 r_this r_vp σ)
    (hne : r_this ≠ r_vptr)
    (hok : evalOp ctx (.load r_vptr r_vp .vptr) σ = .ok (.next, σ')) :
    vcallInv ctx .s2 r_this r_vptr σ' := by
  rcases hinv with ⟨b, path, hth⟩
  simp only [evalOp, evalSimple] at hok
  obtain ⟨σ1, h1, h2⟩ := ok_bind_eq_ok hok; cases h2
  obtain ⟨p, -, h1⟩ := ok_bind_eq_ok h1
  obtain ⟨v, -, h1⟩ := ok_bind_eq_ok h1; cases h1
  exact ⟨b, path, by simp only [State.set, upd_ne _ _ _ _ hne, hth]⟩

theorem vcallInv_step_s2_s3 {ctx : Ctx} {r_this r_vptr r_fnaddr : VId} {slot : Nat} {σ σ' : State}
    (hinv : vcallInv ctx .s2 r_this r_vptr σ)
    (hne : r_this ≠ r_fnaddr)
    (hok : evalOp ctx (.vtableGetVirtualFnAddr r_fnaddr r_vptr slot) σ = .ok (.next, σ')) :
    vcallInv ctx .s3 r_this r_fnaddr σ' := by
  rcases hinv with ⟨b, path, hth⟩
  simp only [evalOp, evalSimple] at hok
  rcases ok_bind_eq_ok hok with ⟨σ1, h1, h2⟩; clear hok; cases h2
  rcases ok_bind_eq_ok h1 with ⟨p, -, h3⟩; clear h1
  cases p <;> cases h3
  rename_i vt i k
  exact ⟨⟨b, path, by simp only [State.set, upd_ne _ _ _ _ hne, hth]⟩,
         ⟨vt, i, k + slot, by simp only [State.set, upd_same]⟩⟩

theorem vcallInv_step_s3_s4 {ctx : Ctx} {r_this r_fnaddr r_fn : VId} {fnTy : Ty} {σ σ' : State}
    (hinv : vcallInv ctx .s3 r_this r_fnaddr σ)
    (hne : r_this ≠ r_fn)
    (hok : evalOp ctx (.load r_fn r_fnaddr (.ptr fnTy)) σ = .ok (.next, σ')) :
    vcallInv ctx .s4 r_this r_fn σ' := by
  rcases hinv with ⟨⟨b, path, hth⟩, ⟨vt, i, k, hvt⟩⟩
  simp only [evalOp, evalSimple, State.getPtr, State.get, hvt, Res.ofOption_some, Res.ok_bind, Res.pure_eq, loadPtr, vtableRead] at hok
  obtain ⟨σ1, h1, h2⟩ := ok_bind_eq_ok hok; cases h2
  obtain ⟨v_fn, hslot, h1⟩ := ok_bind_eq_ok h1; cases h1
  rcases hs : ctx.vtableSlot? vt i k with _ | v <;> rw [hs] at hslot <;> cases hslot
  exact ⟨⟨b, path, by simp only [State.set, upd_ne _ _ _ _ hne, hth]⟩,
         ⟨vt, i, k, v_fn, hs, by simp only [State.set, upd_same]⟩⟩

theorem admissible_and' {α : Type} [Lean.Order.CCPO α] {P Q : α → Prop}
    (hP : Lean.Order.admissible P) (hQ : Lean.Order.admissible Q) :
    Lean.Order.admissible (fun x => P x ∧ Q x) :=
  fun c hc h => ⟨hP c hc (fun x hx => (h x hx).1), hQ c hc (fun x hx => (h x hx).2)⟩

namespace SpM
open Lean.Order

def ops (ctx₂ : Ctx) (goodSym : String → Bool) (f : List Op → State → Res (Step × State)) : Prop :=
  ∀ ops σ, (∃ st r1 r2, spOkOps goodSym st r1 r2 ops = true ∧ vcallInv ctx₂ st r1 r2 σ) →
    RelEq (f ops σ) (evalOps ctx₂ ops σ)

def op1 (ctx₂ : Ctx) (goodSym : String → Bool) (f : Op → State → Res (Step × State)) : Prop :=
  ∀ op σ, spOkOp goodSym op = true → RelEq (f op σ) (evalOp ctx₂ op σ)

def op2 (ctx₂ : Ctx) (f : Op → State → Res (Step × State)) : Prop :=
  ∀ op σ, (∃ loc res r_fn r_this clsName retTy nt,
    op = .call loc res (.indirect r_fn) [r_this] [.ptr (.record clsName)] retTy nt ∧
    isSpCls clsName = true ∧ vcallInv ctx₂ .s4 r_this r_fn σ) →
    RelEq (f op σ) (evalOp ctx₂ op σ)

def op3 (ctx₂ : Ctx) (f : Op → State → Res (Step × State)) : Prop :=
  ∀ op σ, (∃ r_cmp k r_a r_c ty,
    op = .cmp r_cmp k r_a r_c ty ∧ (k == .eq || k == .ne) = true ∧
    vcallInv ctx₂ (.s5 r_c) 0 0 σ) →
    RelEq (f op σ) (evalOp ctx₂ op σ)

def op (ctx₂ : Ctx) (goodSym : String → Bool) (f : Op → State → Res (Step × State)) : Prop :=
  op1 ctx₂ goodSym f ∧ op2 ctx₂ f ∧ op3 ctx₂ f

def region (ctx₂ : Ctx) (goodSym : String → Bool) (f : Region → List Val → State → Res (Exit × State)) : Prop :=
  ∀ r args σ, spOkRegion goodSym r = true → RelEq (f r args σ) (evalRegion ctx₂ r args σ)

def block (ctx₂ : Ctx) (goodSym : String → Bool) (f : List Block → BlockId → List Val → State → Res (Exit × State)) : Prop :=
  ∀ bs i args σ, spOkBlocks goodSym bs = true → RelEq (f bs i args σ) (evalBlock ctx₂ bs i args σ)

def call (ctx₂ : Ctx) (goodSym : String → Bool) (f : String → List Val → Mem → Res (Exit × Mem)) : Prop :=
  ∀ sym args m, goodSym sym = true → RelEq (f sym args m) (evalCall ctx₂ sym args m)

def triv {α : Type} (_ : α) : Prop := True

theorem adm_triv {α : Type} [CCPO α] : admissible (@triv α) :=
  fun _ _ _ => trivial

theorem adm_ops (ctx₂ : Ctx) (goodSym : String → Bool) : admissible (ops ctx₂ goodSym) := by
  unfold ops
  refine admissible_pi_apply _ fun _ =>
    admissible_pi_apply _ fun _ =>
    admissible_relEq _ _

theorem adm_op (ctx₂ : Ctx) (goodSym : String → Bool) : admissible (op ctx₂ goodSym) := by
  unfold op op1 op2 op3
  refine admissible_and'
    (admissible_pi_apply _ fun _ => admissible_pi_apply _ fun _ => admissible_relEq _ _)
    (admissible_and'
      (admissible_pi_apply _ fun _ => admissible_pi_apply _ fun _ => admissible_relEq _ _)
      (admissible_pi_apply _ fun _ => admissible_pi_apply _ fun _ => admissible_relEq _ _))

theorem adm_region (ctx₂ : Ctx) (goodSym : String → Bool) : admissible (region ctx₂ goodSym) := by
  unfold region
  refine admissible_pi_apply _ fun _ =>
    admissible_pi_apply _ fun _ =>
    admissible_pi_apply _ fun _ =>
    admissible_relEq _ _

theorem adm_block (ctx₂ : Ctx) (goodSym : String → Bool) : admissible (block ctx₂ goodSym) := by
  unfold block
  refine admissible_pi_apply _ fun _ =>
    admissible_pi_apply _ fun _ =>
    admissible_pi_apply _ fun _ =>
    admissible_pi_apply _ fun _ =>
    admissible_relEq _ _

theorem adm_call (ctx₂ : Ctx) (goodSym : String → Bool) : admissible (call ctx₂ goodSym) := by
  unfold call
  refine admissible_pi_apply _ fun _ =>
    admissible_pi_apply _ fun _ =>
    admissible_pi_apply _ fun _ =>
    admissible_relEq _ _

end SpM

def SpFuncSpec (ctx₁ ctx₂ : Ctx) (goodSym : String → Bool) (sym : String) : Prop :=
  ∃ fd₁ fd₂,
    ctx₁.mod.findFunc? sym = some fd₁ ∧
    ctx₂.mod.findFunc? sym = some fd₂ ∧
    fd₁.params = fd₂.params ∧
    fd₁.nothrow = fd₂.nothrow ∧
    fd₁.special = fd₂.special ∧
    ((fd₁.model = some .pureVirtual ∧ fd₂.model = some .pureVirtual) ∨
     (fd₁.model = some .operatorDelete ∧ fd₂.model = some .operatorDelete) ∨
     (fd₁.model = none ∧ fd₂.model = none ∧
      ∃ b₁ b₂, fd₁.body = some b₁ ∧ fd₂.body = some b₂ ∧
        spOkRegion goodSym b₁ = true ∧ spOkRegion goodSym b₂ = true ∧
        ∀ ctx args σ, evalRegion ctx b₁ args σ = evalRegion ctx b₂ args σ))

def SpVcallSpec (ctx₁ ctx₂ : Ctx) (goodSym : String → Bool) (clsName sym : String) : Prop :=
  goodSym sym = true ∨
  (∃ fd₁ fd₂ d,
    ctx₁.mod.findFunc? sym = some fd₁ ∧ fd₁.params.head? = some (.ptr (.record d)) ∧
    ctx₂.mod.findFunc? sym = some fd₂ ∧ fd₂.params.head? = some (.ptr (.record d)) ∧
    (clsName == d) = false ∧ ctx₂.basePath 16 d clsName 0 = none ∧ isThunk sym = false)

theorem evalCall_relEq_of_spClosed {ctx₁ ctx₂ : Ctx} {goodSym : String → Bool}
    (hr : ∀ name, ctx₁.record? name = ctx₂.record? name)
    (hp : ctx₁.mod.ptrBytes = ctx₂.mod.ptrBytes)
    (hv : ctx₁.vtableSlot? = ctx₂.vtableSlot?)
    (hg : ctx₁.symAddr? "__libc_single_threaded" [] = ctx₂.symAddr? "__libc_single_threaded" [])
    (hfuncs : ∀ sym, goodSym sym = true → SpFuncSpec ctx₁ ctx₂ goodSym sym)
    (hvcall : ∀ clsName vt i k sym, isSpCls clsName = true →
      ctx₂.vtableSlot? vt i k = some (.ptr (.fn sym)) → SpVcallSpec ctx₁ ctx₂ goodSym clsName sym)
    (hcxx : ctx₁.mod.cxx = ctx₂.mod.cxx := by rfl) :
    SpM.call ctx₂ goodSym (evalCall ctx₁) := by
  have hdtor : ∀ sym, goodSym sym = true →
      (ctx₁.mod.findFunc? sym).any (·.special == .dtor) = (ctx₂.mod.findFunc? sym).any (·.special == .dtor) := by
    intro sym hs
    obtain ⟨fd₁, fd₂, hf1, hf2, _, _, hsp, _⟩ := hfuncs sym hs
    rw [hf1, hf2]; simp only [Option.any, hsp]
  refine evalCall.fixpoint_induct ctx₁
    (SpM.ops ctx₂ goodSym) (SpM.op ctx₂ goodSym) SpM.triv
    (SpM.region ctx₂ goodSym) (SpM.block ctx₂ goodSym) SpM.triv SpM.triv
    SpM.triv SpM.triv SpM.triv SpM.triv (SpM.call ctx₂ goodSym)
    (SpM.adm_ops ctx₂ goodSym) (SpM.adm_op ctx₂ goodSym) SpM.adm_triv
    (SpM.adm_region ctx₂ goodSym) (SpM.adm_block ctx₂ goodSym) SpM.adm_triv SpM.adm_triv
    SpM.adm_triv SpM.adm_triv SpM.adm_triv SpM.adm_triv (SpM.adm_call ctx₂ goodSym)
    ?s1 ?s2 (fun _ _ _ _ => trivial) ?s4 ?s5
    (fun _ _ _ _ => trivial) (fun _ _ _ _ => trivial) (fun _ _ _ _ _ _ => trivial)
    (fun _ _ => trivial) (fun _ _ _ _ _ _ => trivial) (fun _ _ _ _ _ _ => trivial) ?s12
  case s1 =>
    intro evalOps_1 evalOp_1 ih_ops ⟨ih_op1, ih_op2, ih_op3⟩ ops σ ⟨st, r1, r2, hok_ops, hinv⟩
    cases ops with
    | nil => rw [evalOps.eq_1]; exact relEq_refl _
    | cons op rest =>
      rw [evalOps.eq_2]
      cases st with
      | s0 =>
        rcases spOkOps_zero_cons hok_ops with ⟨r_vp, r_this, clsName, rfl, _, hne, hrest⟩ | ⟨r_c, ty, c, rfl, hc, hrest⟩ | ⟨hop, hrest⟩
        · refine relEq_bind (ih_op1 _ σ rfl) ?_
          rintro ⟨s, σ'⟩ hok
          cases s with
          | next => exact ih_ops rest σ' ⟨.s1, r_this, r_vp, hrest, vcallInv_step_s0_s1 hne hok⟩
          | exit _ => exact relEq_refl _
          | jump _ _ => exact relEq_refl _
        · have hop : spOkOp goodSym (.const r_c ty c) = true := by
            cases c <;> first | rfl | cases hc
          refine relEq_bind (ih_op1 _ σ hop) ?_
          rintro ⟨s, σ'⟩ hok
          cases s with
          | next => exact ih_ops rest σ' ⟨.s5 r_c, 0, 0, hrest, vcallInv_step_s0_s5 hc hok⟩
          | exit _ => exact relEq_refl _
          | jump _ _ => exact relEq_refl _
        · refine relEq_bind (ih_op1 op σ hop) ?_
          rintro ⟨s, σ'⟩ _
          cases s with
          | next => exact ih_ops rest σ' ⟨.s0, 0, 0, hrest, trivial⟩
          | exit _ => exact relEq_refl _
          | jump _ _ => exact relEq_refl _
      | s5 r_c =>
        rcases spOkOps_s5_cons hok_ops with ⟨r_cmp, k, r_a, ty, rfl, hk, hrest⟩
        refine relEq_bind (ih_op3 _ σ ⟨r_cmp, k, r_a, r_c, ty, rfl, hk, hinv⟩) ?_
        rintro ⟨s, σ'⟩ _
        cases s with
        | next => exact ih_ops rest σ' ⟨.s0, 0, 0, hrest, trivial⟩
        | exit _ => exact relEq_refl _
        | jump _ _ => exact relEq_refl _
      | s1 =>
        rcases spOkOps_s1_cons hok_ops with ⟨r_vptr, rfl, hne, hrest⟩
        refine relEq_bind (ih_op1 _ σ rfl) ?_
        rintro ⟨s, σ'⟩ hok
        cases s with
        | next => exact ih_ops rest σ' ⟨.s2, r1, r_vptr, hrest, vcallInv_step_s1_s2 hinv hne hok⟩
        | exit _ => exact relEq_refl _
        | jump _ _ => exact relEq_refl _
      | s2 =>
        rcases spOkOps_s2_cons hok_ops with ⟨r_fnaddr, slot, rfl, hne, hrest⟩
        refine relEq_bind (ih_op1 _ σ rfl) ?_
        rintro ⟨s, σ'⟩ hok
        cases s with
        | next => exact ih_ops rest σ' ⟨.s3, r1, r_fnaddr, hrest, vcallInv_step_s2_s3 hinv hne hok⟩
        | exit _ => exact relEq_refl _
        | jump _ _ => exact relEq_refl _
      | s3 =>
        rcases spOkOps_s3_cons hok_ops with ⟨r_fn, fnTy, rfl, hne, hrest⟩
        refine relEq_bind (ih_op1 _ σ rfl) ?_
        rintro ⟨s, σ'⟩ hok
        cases s with
        | next => exact ih_ops rest σ' ⟨.s4, r1, r_fn, hrest, vcallInv_step_s3_s4 hinv hne hok⟩
        | exit _ => exact relEq_refl _
        | jump _ _ => exact relEq_refl _
      | s4 =>
        rcases spOkOps_s4_cons hok_ops with ⟨loc, res, clsName, retTy, nt, rfl, hcls, hrest⟩
        refine relEq_bind (ih_op2 _ σ ⟨loc, res, r2, r1, clsName, retTy, nt, rfl, hcls, hinv⟩) ?_
        rintro ⟨s, σ'⟩ _
        cases s with
        | next => exact ih_ops rest σ' ⟨.s0, 0, 0, hrest, trivial⟩
        | exit _ => exact relEq_refl _
        | jump _ _ => exact relEq_refl _
  case s4 =>
    intro evalBlock_1 ih_block r args σ hok_reg
    cases r with
    | mk bs =>
      cases bs with
      | nil => rw [evalRegion.eq_1]; exact relEq_refl _
      | cons b bs =>
        rw [evalRegion.eq_2]
        exact relEq_bind (ih_block (b :: bs) 0 args σ hok_reg) (fun _ _ => relEq_refl _)
  case s5 =>
    intro evalOps_1 evalBlock_1 ih_ops ih_block bs i args σ hok_bs
    dsimp only
    rw [evalBlock.eq_1]
    rcases hi : bs[i]? with _ | ⟨params, ops⟩
    · exact relEq_refl _
    · dsimp only
      have hops := spOkBlocks_getElem hok_bs hi
      refine relEq_bind_same (σ.bindArgs params args) ?_
      intro σ1 _
      refine relEq_bind (ih_ops ops σ1 ⟨.s0, 0, 0, hops, trivial⟩) ?_
      rintro ⟨s, σ2⟩ -
      cases s with
      | next => exact relEq_refl _
      | jump j vs => exact ih_block bs j vs σ2 hok_bs
      | exit e =>
        cases e <;> try exact relEq_refl _
        rename_i l
        dsimp only
        cases labelBlock? l bs with
        | none => exact relEq_refl _
        | some j => exact ih_block bs j [] σ2 hok_bs
  case s12 =>
    intro evalRegion_1 ih_region sym args m hgood
    dsimp only
    rw [evalCall.eq_1]
    obtain ⟨fd₁, fd₂, hf1, hf2, _, hnt, hsp, hspec⟩ := hfuncs sym hgood
    rw [hf1, hf2]; dsimp only
    rcases hspec with ⟨hm1, hm2⟩ | ⟨hm1, hm2⟩ | ⟨hm1, hm2, b₁, b₂, hb1, hb2, hok1, _, hbeq⟩
    · rw [hm1, hm2]; exact relEq_refl _
    · rw [hm1, hm2]; exact relEq_of_eq (runModel_operatorDelete_congr ctx₁ ctx₂ args m)
    · rw [hm1, hm2, hb1, hb2]; dsimp only
      rw [← hbeq ctx₂ args ⟨m, fun _ => none, []⟩, hnt, hsp, endLifetime_congr hr]
      exact relEq_bind (ih_region b₁ args ⟨m, fun _ => none, []⟩ hok1) (fun _ _ => relEq_refl _)
  case s2 =>
    intro evalOp_1 evalCases_1 evalRegion_1 evalDo_1 evalWhile_1 evalFor_1 evalCall_1
      _ _ ih_region _ _ _ ih_call
    refine ⟨?_, ?_, ?_⟩
    · intro op σ hop
      dsimp only
      by_cases hng : isSimpleNonCmpOp op = true
      · have hs : isSimpleAnyOp op = true := by
          cases op <;> first | rfl | (cases hng; done)
        rw [evalOp_eq_simple_any hs, ← evalSimple_noncmp_congr hr hp hv hcxx hng]
        cases op <;> first | exact relEq_refl _ | (cases hng; done)
      · by_cases htm : isCtxFreeTerminatorOp op = true
        · cases op <;> try (cases htm; done)
          case ret r => cases r <;> simp only [evalOp] <;> exact relEq_refl _
          case throw obj _ ti => cases obj <;> cases ti <;> simp only [evalOp] <;> exact relEq_refl _
          all_goals (simp only [evalOp]; exact relEq_refl _)
        · cases op with
          | getGlobal r sym ty =>
            simp only [spOkOp, beq_iff_eq] at hop
            subst hop
            simp only [evalOp, evalSimple, hg]
            exact relEq_refl _
          | call loc res callee args argTys retTy nt =>
            cases callee with
            | direct sym =>
              simp only [spOkOp] at hop
              simp only [evalOp, adjustThis, Res.pure_eq, Res.ok_bind]
              refine relEq_bind_same (args.mapM σ.get) ?_
              intro vs _
              exact relEq_bind (ih_call sym vs σ.mem hop) (fun _ _ => relEq_refl _)
            | indirect _ => cases hop
          | scope res body =>
            simp only [spOkOp] at hop
            simp only [evalOp]
            exact relEq_bind (ih_region body [] σ hop) (fun _ _ => relEq_refl _)
          | cleanupScope k body cl =>
            simp only [spOkOp, Bool.and_eq_true] at hop
            simp only [evalOp, callsDestructor_eq_of_spOkRegion hdtor hop.2]
            refine relEq_bind (ih_region body [] σ hop.1) ?_
            rintro ⟨e, σ1⟩ _
            cases e <;> try exact relEq_refl _
            all_goals
              dsimp only
              split
              · exact relEq_bind (ih_region cl [] σ1 hop.2) (fun _ _ => relEq_refl _)
              · exact relEq_refl _
          | ifOp c t el =>
            simp only [spOkOp, Bool.and_eq_true] at hop
            simp only [evalOp]
            refine relEq_bind_same (σ.getBool c) ?_
            intro b _
            cases b
            · exact relEq_bind (ih_region el [] σ hop.2) (fun _ _ => relEq_refl _)
            · exact relEq_bind (ih_region t [] σ hop.1) (fun _ _ => relEq_refl _)
          | ternary res c t el =>
            simp only [spOkOp, Bool.and_eq_true] at hop
            simp only [evalOp]
            refine relEq_bind_same (σ.getBool c) ?_
            intro b _
            cases b
            · exact relEq_bind (ih_region el [] σ hop.2) (fun _ _ => relEq_refl _)
            · exact relEq_bind (ih_region t [] σ hop.1) (fun _ _ => relEq_refl _)
          | tryOp body hs unw =>
            rcases hs with _ | ⟨⟨ck, hreg⟩, rest⟩ <;> try cases hop
            cases ck <;> try cases hop
            cases rest <;> try cases hop
            cases unw <;> try cases hop
            simp only [spOkOp, Bool.and_eq_true] at hop
            simp only [evalOp]
            refine relEq_bind (ih_region body [] σ hop.1) ?_
            rintro ⟨e, σ1⟩ _
            cases e <;> try exact relEq_refl _
            simp only [findHandler, Res.ok_bind]
            exact relEq_bind (ih_region hreg _ σ1 hop.2) (fun _ _ => relEq_refl _)
          | _ =>
            first
              | (cases hop; done)
              | (simp only [spOkOp, Bool.or_eq_true] at hop
                 rcases hop with h | h
                 · exact False.elim (hng h)
                 · exact False.elim (htm h))
    · rintro op σ ⟨loc, res, r_fn, r_this, clsName, retTy, nt, rfl, hcls, ⟨⟨b, path, hth⟩, ⟨vt, i, k, v_fn, hslot, hfn⟩⟩⟩
      dsimp only
      simp only [evalOp, List.mapM, List.mapM.loop, State.get, hth, hfn,
        Res.ofOption_some, Res.ok_bind, Res.pure_eq, List.reverse, List.reverseAux]
      cases v_fn <;> try exact relEq_refl _
      rename_i p_fn
      cases p_fn <;> try exact relEq_refl _
      rename_i sym_fn
      simp only [adjustThis]
      rcases hvcall clsName vt i k sym_fn hcls hslot with hgood | ⟨fd₁, fd₂, d, hf₁, hd₁, hf₂, hd₂, hne_d, hbp, hthk⟩
      · obtain ⟨fd₁, fd₂, hf1, hf2, hpar, _⟩ := hfuncs sym_fn hgood
        have hadj : adjustThisIndirect ctx₁ sym_fn [(.ptr (.record clsName))] [.ptr (.loc b path)] =
                    adjustThisIndirect ctx₂ sym_fn [(.ptr (.record clsName))] [.ptr (.loc b path)] := by
          unfold adjustThisIndirect
          rw [hf1, hf2]; dsimp only [Option.bind]; rw [hpar, basePath_congr hr hp]
        rw [hadj]
        refine relEq_bind_same _ ?_
        intro vs _
        exact relEq_bind (ih_call sym_fn vs σ.mem hgood) (fun _ _ => relEq_refl _)
      · unfold adjustThisIndirect
        simp only [hf₁, hf₂, Option.bind, hd₁, hd₂, hne_d, hthk, Bool.false_eq_true, ↓reduceIte,
          basePath_congr hr hp, hbp, Res.ub_bind]
        exact relEq_refl _
    · rintro op σ ⟨r_cmp, k, r_a, r_c, ty, rfl, hk, hinv⟩
      dsimp only
      rw [← evalOp_eq_simple_any (h := rfl), evalOp_cmp_of_int_or_null ctx₁ ctx₂ hk hinv]
      exact relEq_refl _

def NotSpDerived (ctx : Ctx) (d : String) : Bool :=
  !("std::_Sp_counted_base<__gnu_cxx::_S_atomic>" == d) &&
  (ctx.basePath 16 d "std::_Sp_counted_base<__gnu_cxx::_S_atomic>" 0).isNone &&
  !("std::_Sp_counted_ptr<apache::thrift::TConfiguration *, __gnu_cxx::_S_atomic>" == d) &&
  (ctx.basePath 16 d "std::_Sp_counted_ptr<apache::thrift::TConfiguration *, __gnu_cxx::_S_atomic>" 0).isNone &&
  !("std::_Sp_counted_ptr<apache::thrift::transport::TMemoryBuffer *, __gnu_cxx::_S_atomic>" == d) &&
  (ctx.basePath 16 d "std::_Sp_counted_ptr<apache::thrift::transport::TMemoryBuffer *, __gnu_cxx::_S_atomic>" 0).isNone &&
  !("apache::thrift::transport::TMemoryBuffer" == d) &&
  (ctx.basePath 16 d "apache::thrift::transport::TMemoryBuffer" 0).isNone

theorem notSpDerived_elim {ctx : Ctx} {clsName d : String}
    (hcls : isSpCls clsName = true) (hnd : NotSpDerived ctx d = true) :
    (clsName == d) = false ∧ ctx.basePath 16 d clsName 0 = none := by
  simp only [NotSpDerived, Bool.and_eq_true, Bool.not_eq_true', Option.isNone_iff_eq_none] at hnd
  rcases hnd with ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩
  simp only [isSpCls, Bool.or_eq_true, beq_iff_eq] at hcls
  rcases hcls with ((rfl | rfl) | rfl) | rfl
  · exact ⟨h1, h2⟩
  · exact ⟨h3, h4⟩
  · exact ⟨h5, h6⟩
  · exact ⟨h7, h8⟩

theorem evalVtableElems_fn_isSome {ctx : Ctx} {es : List Const} {k : Nat} {sym : String}
    (h : evalVtableElems ctx es k = some (.ptr (.fn sym))) :
    (ctx.mod.findFunc? sym).isSome = true := by
  induction es generalizing k with
  | nil => cases h
  | cons c es ih =>
    cases k with
    | zero =>
      cases c with
      | ptrInt v => revert h; simp only [evalVtableElems, Ctx.constVal]; split <;> intro h <;> cases h
      | vtableAddr vt i k => revert h; simp only [evalVtableElems, Ctx.constVal]; split <;> intro h <;> cases h
      | globalAddr gsym idx =>
        revert h
        simp only [evalVtableElems, Ctx.constVal, Ctx.symAddr?]
        cases ctx.mod.findGlobal? gsym <;> cases ctx.gaddr gsym <;> simp <;> (rintro _ hf rfl; exact hf)
      | _ => cases h
    | succ k => exact ih h

theorem evalVtableArrays_fn_isSome {ctx : Ctx} {cs : List Const} {i k : Nat} {sym : String}
    (h : evalVtableArrays ctx cs i k = some (.ptr (.fn sym))) :
    (ctx.mod.findFunc? sym).isSome = true := by
  induction cs generalizing i with
  | nil => cases h
  | cons c cs ih =>
    cases i with
    | zero =>
      cases c <;> try cases h
      exact evalVtableElems_fn_isSome h
    | succ i =>
      cases c <;> exact ih h

theorem vtableSlot?_fn_isSome {ctx : Ctx} {vt : String} {i k : Nat} {sym : String}
    (h : ctx.vtableSlot? vt i k = some (.ptr (.fn sym))) :
    (ctx.mod.findFunc? sym).isSome = true := by
  rw [vtableSlot?_eq_evalVtableAt] at h
  unfold evalVtableAt at h
  rcases hbind : (ctx.mod.globals.find? (·.sym == vt)).bind vtableInit with _ | cs <;> rw [hbind] at h
  · cases h
  · exact evalVtableArrays_fn_isSome h

def SpVcallSymSpec (ctx₁ ctx₂ : Ctx) (goodSym : String → Bool) (sym : String) : Prop :=
  goodSym sym = true ∨
  ctx₂.mod.findFunc? sym = none ∨
  (∃ fd₁ fd₂ d,
    ctx₁.mod.findFunc? sym = some fd₁ ∧
    ctx₂.mod.findFunc? sym = some fd₂ ∧
    fd₁.params.head? = some (.ptr (.record d)) ∧
    fd₂.params.head? = some (.ptr (.record d)) ∧
    NotSpDerived ctx₂ d = true ∧
    isThunk sym = false)

theorem spVcallSpec_of_symSpec {ctx₁ ctx₂ : Ctx} {goodSym : String → Bool} {clsName vt : String} {i k : Nat} {sym : String}
    (hcls : isSpCls clsName = true)
    (hslot : ctx₂.vtableSlot? vt i k = some (.ptr (.fn sym)))
    (h : SpVcallSymSpec ctx₁ ctx₂ goodSym sym) :
    SpVcallSpec ctx₁ ctx₂ goodSym clsName sym := by
  rcases h with h1 | hnone | ⟨fd₁, fd₂, d, hf1, hf2, hp1, hp2, hnd, hthk⟩
  · exact Or.inl h1
  · have his := vtableSlot?_fn_isSome hslot
    rw [hnone] at his; cases his
  · have ⟨hne, hbp⟩ := notSpDerived_elim hcls hnd
    exact Or.inr ⟨fd₁, fd₂, d, hf1, hp1, hf2, hp2, hne, hbp, hthk⟩

theorem evalCall_eq_of_spClosed {ctx₁ ctx₂ : Ctx} {goodSym : String → Bool}
    (hr : ∀ name, ctx₁.record? name = ctx₂.record? name)
    (hp : ctx₁.mod.ptrBytes = ctx₂.mod.ptrBytes)
    (hv : ctx₁.vtableSlot? = ctx₂.vtableSlot?)
    (hg : ctx₁.symAddr? "__libc_single_threaded" [] = ctx₂.symAddr? "__libc_single_threaded" [])
    (hfuncs : ∀ sym, goodSym sym = true → SpFuncSpec ctx₁ ctx₂ goodSym sym)
    (hvcall : ∀ vt i k sym, ctx₂.vtableSlot? vt i k = some (.ptr (.fn sym)) → SpVcallSymSpec ctx₁ ctx₂ goodSym sym)
    (hcxx : ctx₁.mod.cxx = ctx₂.mod.cxx := by rfl)
    {sym : String} (hsym : goodSym sym = true) (vs : List Val) (m : Mem) :
    evalCall ctx₁ sym vs m = evalCall ctx₂ sym vs m := by
  have hr' : ∀ name, ctx₂.record? name = ctx₁.record? name := fun name => (hr name).symm
  have hfuncs' : ∀ s, goodSym s = true → SpFuncSpec ctx₂ ctx₁ goodSym s := by
    intro s hs
    obtain ⟨fd₁, fd₂, hf1, hf2, hpar, hnt, hsp, hspec⟩ := hfuncs s hs
    refine ⟨fd₂, fd₁, hf2, hf1, hpar.symm, hnt.symm, hsp.symm, ?_⟩
    rcases hspec with ⟨hm1, hm2⟩ | ⟨hm1, hm2⟩ | ⟨hm1, hm2, b₁, b₂, hb1, hb2, hok1, hok2, hbeq⟩
    · exact Or.inl ⟨hm2, hm1⟩
    · exact Or.inr (Or.inl ⟨hm2, hm1⟩)
    · exact Or.inr (Or.inr ⟨hm2, hm1, b₂, b₁, hb2, hb1, hok2, hok1, fun ctx args σ => (hbeq ctx args σ).symm⟩)
  have hvcall1 : ∀ clsName vt i k s, isSpCls clsName = true →
      ctx₂.vtableSlot? vt i k = some (.ptr (.fn s)) → SpVcallSpec ctx₁ ctx₂ goodSym clsName s :=
    fun _ vt i k s hcls hslot => spVcallSpec_of_symSpec hcls hslot (hvcall vt i k s hslot)
  have hvcall2 : ∀ clsName vt i k s, isSpCls clsName = true →
      ctx₁.vtableSlot? vt i k = some (.ptr (.fn s)) → SpVcallSpec ctx₂ ctx₁ goodSym clsName s := by
    intro clsName vt i k s hcls hslot
    rw [hv] at hslot
    rcases hvcall vt i k s hslot with h1 | hnone | ⟨fd₁, fd₂, d, hf1, hf2, hp1, hp2, hnd, hthk⟩
    · exact Or.inl h1
    · have his := vtableSlot?_fn_isSome hslot
      rw [hnone] at his; cases his
    · have ⟨hne, hbp⟩ := notSpDerived_elim hcls hnd
      rw [← basePath_congr hr hp] at hbp
      exact Or.inr ⟨fd₂, fd₁, d, hf2, hp2, hf1, hp1, hne, hbp, hthk⟩
  exact relEq_antisymm
    (evalCall_relEq_of_spClosed hr hp hv hg hfuncs hvcall1 hcxx sym vs m hsym)
    (evalCall_relEq_of_spClosed hr' hp.symm hv.symm hg.symm hfuncs' hvcall2 hcxx.symm sym vs m hsym)

theorem all_spFuncSpec_nil {ctx₁ ctx₂ : Ctx} {goodSym : String → Bool}
    (sym : String) (h : ([].contains sym) = true) : SpFuncSpec ctx₁ ctx₂ goodSym sym := by
  cases h

theorem all_spFuncSpec_cons {ctx₁ ctx₂ : Ctx} {goodSym : String → Bool} {s : String} {ss : List String}
    (hs : SpFuncSpec ctx₁ ctx₂ goodSym s)
    (hss : ∀ sym, ss.contains sym = true → SpFuncSpec ctx₁ ctx₂ goodSym sym)
    (sym : String) (h : ((s :: ss).contains sym) = true) : SpFuncSpec ctx₁ ctx₂ goodSym sym := by
  rw [List.contains_cons, Bool.or_eq_true, beq_iff_eq] at h
  rcases h with h | h
  · subst h; exact hs
  · exact hss sym h

theorem spFuncSpec_of_find {ctx₁ ctx₂ : Ctx} {goodSym : String → Bool} {s : String} {fd : FuncDecl}
    (hf1 : ctx₁.mod.findFunc? s = some fd) (hf2 : ctx₂.mod.findFunc? s = some fd)
    (hok : (match fd.model, fd.body with
            | some .pureVirtual, _ => true
            | some .operatorDelete, _ => true
            | none, some b => spOkRegion goodSym b
            | _, _ => false) = true) :
    SpFuncSpec ctx₁ ctx₂ goodSym s := by
  refine ⟨fd, fd, hf1, hf2, rfl, rfl, rfl, ?_⟩
  rcases hm : fd.model with _ | mdl <;> rw [hm] at hok
  · rcases hb : fd.body with _ | b <;> rw [hb] at hok
    · cases hok
    · exact Or.inr (Or.inr ⟨rfl, rfl, b, b, rfl, rfl, hok, hok, fun _ _ _ => rfl⟩)
  · cases mdl <;> first | exact Or.inl ⟨rfl, rfl⟩ | exact Or.inr (Or.inl ⟨rfl, rfl⟩) | cases hok

abbrev mkDispose2IfThen (loc : Loc) : Region := .mk [
  .mk [] [
    .vtableGetVptr 7 4 (.record "apache::thrift::transport::TMemoryBuffer"),
    .load 8 7 .vptr,
    .vtableGetVirtualFnAddr 9 8 1,
    .load 10 9 (.ptr (.func [(.ptr (.record "apache::thrift::transport::TMemoryBuffer"))] .void false)),
    .call loc none (.indirect 10) [4] [(.ptr (.record "apache::thrift::transport::TMemoryBuffer"))] .void true]]

abbrev mkDispose2Body (loc : Loc) : Region := .mk [
  .mk [0] [
    .alloca 1 (.ptr (.record "std::_Sp_counted_ptr<apache::thrift::transport::TMemoryBuffer *, __gnu_cxx::_S_atomic>")) "this",
    .tryOp (.mk [
      .mk [] [
        .store 0 1 (.ptr (.record "std::_Sp_counted_ptr<apache::thrift::transport::TMemoryBuffer *, __gnu_cxx::_S_atomic>")),
        .load 2 1 (.ptr (.record "std::_Sp_counted_ptr<apache::thrift::transport::TMemoryBuffer *, __gnu_cxx::_S_atomic>")),
        .getMember 3 2 1 (.record "std::_Sp_counted_ptr<apache::thrift::transport::TMemoryBuffer *, __gnu_cxx::_S_atomic>") (.ptr (.record "apache::thrift::transport::TMemoryBuffer")),
        .load 4 3 (.ptr (.record "apache::thrift::transport::TMemoryBuffer")),
        .const 5 (.ptr (.record "apache::thrift::transport::TMemoryBuffer")) .null,
        .cmp 6 .ne 4 5 (.ptr (.record "apache::thrift::transport::TMemoryBuffer")),
        .ifOp 6 (mkDispose2IfThen loc) (.mk []),
        .yield []]])
      [(.all, (.mk [
        .mk [11] [
          .ehTerminate 11]]))]
      none,
    .ret none]]

theorem evalOp_call_loc_eq (ctx : Ctx) (loc₁ loc₂ : Loc) (res : Option VId) (callee : Callee)
    (args : List VId) (argTys : List Ty) (retTy : Ty) (nt : Bool) (σ : State) :
    evalOp ctx (.call loc₁ res callee args argTys retTy nt) σ =
    evalOp ctx (.call loc₂ res callee args argTys retTy nt) σ := by
  rw [evalOp, evalOp]

theorem evalOp_tryOp_body_eq {ctx : Ctx} {b₁ b₂ : Region} {hs : List (CatchKind × Region)} {u : Option Region}
    (hb : ∀ args σ, evalRegion ctx b₁ args σ = evalRegion ctx b₂ args σ) (σ : State) :
    evalOp ctx (.tryOp b₁ hs u) σ = evalOp ctx (.tryOp b₂ hs u) σ := by
  rw [evalOp, evalOp, hb [] σ]

theorem evalRegion_mkDispose2Body_eq (loc₁ loc₂ : Loc) (ctx : Ctx) (args : List Val) (σ : State) :
    evalRegion ctx (mkDispose2Body loc₁) args σ = evalRegion ctx (mkDispose2Body loc₂) args σ := by
  dsimp only [mkDispose2Body, mkDispose2IfThen]
  revert args σ
  repeat' first
    | (intro σ; rfl)
    | (intro args σ; refine evalRegion_single_congr rfl rfl rfl ?_ args σ)
    | refine evalRegion_single_congr rfl rfl rfl ?_ _ _
    | (intro σ; refine evalOps_cons_congr (fun _ => rfl) ?_ σ)
    | (intro σ; refine evalOps_cons_congr (evalOp_call_loc_eq ctx loc₁ loc₂ _ _ _ _ _ _) (fun _ => rfl) σ)
    | (intro σ; refine evalOps_cons_congr (evalOp_ifOp_congr (fun σ => ?_) (fun _ => rfl)) ?_ σ)
    | (intro σ; refine evalOps_cons_congr (evalOp_tryOp_body_eq ?_) ?_ σ)

theorem spFuncSpec_of_mkDispose2Body {ctx₁ ctx₂ : Ctx} {goodSym : String → Bool} {s : String} {fd₁ fd₂ : FuncDecl} {loc₁ loc₂ : Loc}
    (hf1 : ctx₁.mod.findFunc? s = some fd₁) (hf2 : ctx₂.mod.findFunc? s = some fd₂)
    (hpar : fd₁.params = fd₂.params) (hnt : fd₁.nothrow = fd₂.nothrow) (hsp : fd₁.special = fd₂.special)
    (hm1 : fd₁.model = none) (hm2 : fd₂.model = none)
    (hb1 : fd₁.body = some (mkDispose2Body loc₁)) (hb2 : fd₂.body = some (mkDispose2Body loc₂))
    (hok1 : spOkRegion goodSym (mkDispose2Body loc₁) = true)
    (hok2 : spOkRegion goodSym (mkDispose2Body loc₂) = true) :
    SpFuncSpec ctx₁ ctx₂ goodSym s :=
  ⟨fd₁, fd₂, hf1, hf2, hpar, hnt, hsp,
    Or.inr (Or.inr ⟨hm1, hm2, mkDispose2Body loc₁, mkDispose2Body loc₂, hb1, hb2, hok1, hok2,
      evalRegion_mkDispose2Body_eq loc₁ loc₂⟩)⟩

theorem spVcallSymSpec_good {ctx₁ ctx₂ : Ctx} {goodSym : String → Bool} {s : String}
    (h : goodSym s = true) : SpVcallSymSpec ctx₁ ctx₂ goodSym s :=
  Or.inl h

theorem spVcallSymSpec_none {ctx₁ ctx₂ : Ctx} {goodSym : String → Bool} {s : String}
    (hf2 : ctx₂.mod.findFunc? s = none) : SpVcallSymSpec ctx₁ ctx₂ goodSym s :=
  Or.inr (Or.inl hf2)

theorem spVcallSymSpec_bad {ctx₁ ctx₂ : Ctx} {goodSym : String → Bool} {s : String} {fd : FuncDecl}
    (hf1 : ctx₁.mod.findFunc? s = some fd) (hf2 : ctx₂.mod.findFunc? s = some fd)
    (hnd : (match fd.params.head? with | some (.ptr (.record d)) => NotSpDerived ctx₂ d | _ => false) = true)
    (hthk : isThunk s = false := by rfl) :
    SpVcallSymSpec ctx₁ ctx₂ goodSym s := by
  rcases hp : fd.params.head? with _ | pty <;> rw [hp] at hnd <;> try cases hnd
  cases pty <;> try cases hnd
  rename_i rty
  cases rty <;> try cases hnd
  rename_i d
  exact Or.inr (Or.inr ⟨fd, fd, d, hf1, hf2, hp, hp, hnd, hthk⟩)

theorem evalVtableElems_imply_nil {ctx : Ctx} {P : String → Prop} :
    ∀ k sym, evalVtableElems ctx [] k = some (.ptr (.fn sym)) → P sym := by
  intro k sym h; cases h

theorem evalVtableElems_imply_null {ctx : Ctx} {P : String → Prop} {es : List Const}
    (hes : ∀ k sym, evalVtableElems ctx es k = some (.ptr (.fn sym)) → P sym) :
    ∀ k sym, evalVtableElems ctx (.null :: es) k = some (.ptr (.fn sym)) → P sym := by
  intro k sym h
  cases k with
  | zero => cases h
  | succ k => exact hes k sym h

theorem evalVtableElems_imply_global {ctx : Ctx} {P : String → Prop} {gsym : String} {idx : List Int} {es : List Const}
    {g : GlobalDecl} {b : Nat}
    (hf : ctx.mod.findGlobal? gsym = some g) (ha : ctx.gaddr gsym = some b)
    (hes : ∀ k sym, evalVtableElems ctx es k = some (.ptr (.fn sym)) → P sym) :
    ∀ k sym, evalVtableElems ctx (.globalAddr gsym idx :: es) k = some (.ptr (.fn sym)) → P sym := by
  intro k sym h
  cases k with
  | zero =>
    revert h
    simp only [evalVtableElems, Ctx.constVal, Ctx.symAddr?, hf, ha]
    generalize (List.all _ _) = c
    cases c <;> intro h <;> cases h
  | succ k => exact hes k sym h

theorem evalVtableElems_imply_func {ctx : Ctx} {P : String → Prop} {gsym : String} {es : List Const}
    {fd : FuncDecl}
    (hg : ctx.mod.findGlobal? gsym = none) (ha : ctx.gaddr gsym = none) (hf : ctx.mod.findFunc? gsym = some fd)
    (hp : P gsym)
    (hes : ∀ k sym, evalVtableElems ctx es k = some (.ptr (.fn sym)) → P sym) :
    ∀ k sym, evalVtableElems ctx (.globalAddr gsym [] :: es) k = some (.ptr (.fn sym)) → P sym := by
  intro k sym h
  cases k with
  | zero =>
    simp only [evalVtableElems, Ctx.constVal, Ctx.symAddr?, hg, ha, hf, List.isEmpty, Option.isSome,
      Option.map] at h
    cases h
    exact hp
  | succ k => exact hes k sym h

theorem evalVtableArrays_imply_nil {ctx : Ctx} {P : String → Prop} :
    ∀ i k sym, evalVtableArrays ctx [] i k = some (.ptr (.fn sym)) → P sym := by
  intro i k sym h; cases h

theorem evalVtableArrays_imply_array {ctx : Ctx} {P : String → Prop} {es : List Const} {cs : List Const}
    (hes : ∀ k sym, evalVtableElems ctx es k = some (.ptr (.fn sym)) → P sym)
    (hcs : ∀ i k sym, evalVtableArrays ctx cs i k = some (.ptr (.fn sym)) → P sym) :
    ∀ i k sym, evalVtableArrays ctx (.array es :: cs) i k = some (.ptr (.fn sym)) → P sym := by
  intro i k sym h
  cases i with
  | zero => exact hes k sym h
  | succ i => exact hcs i k sym h

theorem evalVtableArrays_imply_nonarray {ctx : Ctx} {P : String → Prop} {c : Const} {cs : List Const}
    (hc : (match c with | .array _ => false | _ => true) = true)
    (hcs : ∀ i k sym, evalVtableArrays ctx cs i k = some (.ptr (.fn sym)) → P sym) :
    ∀ i k sym, evalVtableArrays ctx (c :: cs) i k = some (.ptr (.fn sym)) → P sym := by
  intro i k sym h
  cases i with
  | zero => cases c <;> first | cases h | cases hc
  | succ i => cases c <;> exact hcs i k sym h

theorem evalVtableAt_imply_nil {ctx : Ctx} {P : String → Prop} (vt : String) (i k : Nat) (sym : String)
    (h : evalVtableAt ctx i k ([].find? (·.sym == vt)) = some (.ptr (.fn sym))) : P sym := by
  cases h

theorem evalVtableAt_imply_nonvtable {ctx : Ctx} {P : String → Prop} {vt : String} {i k : Nat} {sym : String}
    {g : GlobalDecl} {gs : List GlobalDecl}
    (h1 : vtableInit g = none)
    (hgs : evalVtableAt ctx i k (gs.find? (·.sym == vt)) = some (.ptr (.fn sym)) → P sym)
    (h : evalVtableAt ctx i k ((g :: gs).find? (·.sym == vt)) = some (.ptr (.fn sym))) : P sym := by
  revert h
  simp only [List.find?]
  cases (g.sym == vt)
  · exact hgs
  · unfold evalVtableAt; dsimp only [Option.bind]; rw [h1]; intro h; cases h

theorem evalVtableAt_imply_vtable {ctx : Ctx} {P : String → Prop} {vt : String} {i k : Nat} {sym : String}
    {g : GlobalDecl} {gs : List GlobalDecl} {cs : List Const}
    (h1 : vtableInit g = some cs)
    (hcs : ∀ i k sym, evalVtableArrays ctx cs i k = some (.ptr (.fn sym)) → P sym)
    (hgs : evalVtableAt ctx i k (gs.find? (·.sym == vt)) = some (.ptr (.fn sym)) → P sym)
    (h : evalVtableAt ctx i k ((g :: gs).find? (·.sym == vt)) = some (.ptr (.fn sym))) : P sym := by
  revert h
  simp only [List.find?]
  cases (g.sym == vt)
  · exact hgs
  · unfold evalVtableAt; dsimp only [Option.bind]; rw [h1]; exact hcs i k sym

def spSyms : List String := [
  "__cxa_pure_virtual",
  "_ZdlPv",
  "_ZNSt10unique_ptrIN6apache6thrift5async13TEvhttpServer14RequestContextESt14default_deleteIS4_EEC2IS6_vEEPS4_",
  "_ZNSt15__uniq_ptr_dataIN6apache6thrift5async13TEvhttpServer14RequestContextESt14default_deleteIS4_ELb1ELb1EECI2St15__uniq_ptr_implIS4_S6_EEPS4_",
  "_ZNSt15__uniq_ptr_implIN6apache6thrift5async13TEvhttpServer14RequestContextESt14default_deleteIS4_EEC2EPS4_",
  "_ZNSt5tupleIJPN6apache6thrift5async13TEvhttpServer14RequestContextESt14default_deleteIS4_EEEC2ILb1ETnNSt9enable_ifIXclsr17_TupleConstraintsIXT_ES5_S7_EE37__is_implicitly_default_constructibleEEbE4typeELb1EEEv",
  "_ZNSt11_Tuple_implILm0EJPN6apache6thrift5async13TEvhttpServer14RequestContextESt14default_deleteIS4_EEEC2Ev",
  "_ZNSt11_Tuple_implILm1EJSt14default_deleteIN6apache6thrift5async13TEvhttpServer14RequestContextEEEEC2Ev",
  "_ZNSt10_Head_baseILm1ESt14default_deleteIN6apache6thrift5async13TEvhttpServer14RequestContextEELb1EEC2Ev",
  "_ZNSt10_Head_baseILm0EPN6apache6thrift5async13TEvhttpServer14RequestContextELb0EEC2Ev",
  "_ZNSt15__uniq_ptr_implIN6apache6thrift5async13TEvhttpServer14RequestContextESt14default_deleteIS4_EE6_M_ptrEv",
  "_ZSt3getILm0EJPN6apache6thrift5async13TEvhttpServer14RequestContextESt14default_deleteIS4_EEERNSt13tuple_elementIXT_ESt5tupleIJDpT0_EEE4typeERSC_",
  "_ZSt12__get_helperILm0EPN6apache6thrift5async13TEvhttpServer14RequestContextEJSt14default_deleteIS4_EEERT0_RSt11_Tuple_implIXT_EJS8_DpT1_EE",
  "_ZNSt11_Tuple_implILm0EJPN6apache6thrift5async13TEvhttpServer14RequestContextESt14default_deleteIS4_EEE7_M_headERS8_",
  "_ZNSt10_Head_baseILm0EPN6apache6thrift5async13TEvhttpServer14RequestContextELb0EE7_M_headERS6_",
  "_ZNKSt19__shared_ptr_accessIN6apache6thrift9transport13TMemoryBufferELN9__gnu_cxx12_Lock_policyE2ELb0ELb0EEptEv",
  "_ZNKSt19__shared_ptr_accessIN6apache6thrift9transport13TMemoryBufferELN9__gnu_cxx12_Lock_policyE2ELb0ELb0EE6_M_getEv",
  "_ZNKSt12__shared_ptrIN6apache6thrift9transport13TMemoryBufferELN9__gnu_cxx12_Lock_policyE2EE3getEv",
  "_ZN6apache6thrift9transport13TMemoryBuffer9getBufferEPPhPj",
  "_ZNSt10unique_ptrIN6apache6thrift5async13TEvhttpServer14RequestContextESt14default_deleteIS4_EED2Ev",
  "_ZNSt10unique_ptrIN6apache6thrift5async13TEvhttpServer14RequestContextESt14default_deleteIS4_EE11get_deleterEv",
  "_ZNSt15__uniq_ptr_implIN6apache6thrift5async13TEvhttpServer14RequestContextESt14default_deleteIS4_EE10_M_deleterEv",
  "_ZSt3getILm1EJPN6apache6thrift5async13TEvhttpServer14RequestContextESt14default_deleteIS4_EEERNSt13tuple_elementIXT_ESt5tupleIJDpT0_EEE4typeERSC_",
  "_ZSt12__get_helperILm1ESt14default_deleteIN6apache6thrift5async13TEvhttpServer14RequestContextEEJEERT0_RSt11_Tuple_implIXT_EJS7_DpT1_EE",
  "_ZNSt11_Tuple_implILm1EJSt14default_deleteIN6apache6thrift5async13TEvhttpServer14RequestContextEEEE7_M_headERS7_",
  "_ZNSt10_Head_baseILm1ESt14default_deleteIN6apache6thrift5async13TEvhttpServer14RequestContextEELb1EE7_M_headERS7_",
  "_ZNKSt14default_deleteIN6apache6thrift5async13TEvhttpServer14RequestContextEEclEPS4_",
  "_ZN6apache6thrift5async13TEvhttpServer14RequestContextD2Ev",
  "_ZNSt10shared_ptrIN6apache6thrift9transport13TMemoryBufferEED2Ev",
  "_ZNSt12__shared_ptrIN6apache6thrift9transport13TMemoryBufferELN9__gnu_cxx12_Lock_policyE2EED2Ev",
  "_ZNSt14__shared_countILN9__gnu_cxx12_Lock_policyE2EED2Ev",
  "_ZNSt16_Sp_counted_baseILN9__gnu_cxx12_Lock_policyE2EE10_M_releaseEv",
  "_ZN9__gnu_cxx27__exchange_and_add_dispatchEPii",
  "_ZN9__gnu_cxx20__is_single_threadedEv",
  "_ZN9__gnu_cxx25__exchange_and_add_singleEPii",
  "_ZN9__gnu_cxx18__exchange_and_addEPVii",
  "_ZNSt16_Sp_counted_baseILN9__gnu_cxx12_Lock_policyE2EE24_M_release_last_use_coldEv",
  "_ZNSt16_Sp_counted_baseILN9__gnu_cxx12_Lock_policyE2EE19_M_release_last_useEv",
  "_ZNSt15_Sp_counted_ptrIPN6apache6thrift14TConfigurationELN9__gnu_cxx12_Lock_policyE2EED2Ev",
  "_ZNSt16_Sp_counted_baseILN9__gnu_cxx12_Lock_policyE2EED2Ev",
  "_ZNSt15_Sp_counted_ptrIPN6apache6thrift14TConfigurationELN9__gnu_cxx12_Lock_policyE2EED0Ev",
  "_ZNSt15_Sp_counted_ptrIPN6apache6thrift14TConfigurationELN9__gnu_cxx12_Lock_policyE2EE10_M_disposeEv",
  "_ZNSt15_Sp_counted_ptrIPN6apache6thrift14TConfigurationELN9__gnu_cxx12_Lock_policyE2EE10_M_destroyEv",
  "_ZNSt15_Sp_counted_ptrIPN6apache6thrift14TConfigurationELN9__gnu_cxx12_Lock_policyE2EE14_M_get_deleterERKSt9type_info",
  "_ZNSt16_Sp_counted_baseILN9__gnu_cxx12_Lock_policyE2EED0Ev",
  "_ZNSt16_Sp_counted_baseILN9__gnu_cxx12_Lock_policyE2EE10_M_destroyEv",
  "_ZNSt15_Sp_counted_ptrIPN6apache6thrift9transport13TMemoryBufferELN9__gnu_cxx12_Lock_policyE2EED2Ev",
  "_ZNSt15_Sp_counted_ptrIPN6apache6thrift9transport13TMemoryBufferELN9__gnu_cxx12_Lock_policyE2EED0Ev",
  "_ZNSt15_Sp_counted_ptrIPN6apache6thrift9transport13TMemoryBufferELN9__gnu_cxx12_Lock_policyE2EE10_M_disposeEv",
  "_ZNSt15_Sp_counted_ptrIPN6apache6thrift9transport13TMemoryBufferELN9__gnu_cxx12_Lock_policyE2EE10_M_destroyEv",
  "_ZNSt15_Sp_counted_ptrIPN6apache6thrift9transport13TMemoryBufferELN9__gnu_cxx12_Lock_policyE2EE14_M_get_deleterERKSt9type_info"
]

def goodSpSym (s : String) : Bool := spSyms.contains s

def nonSpClasses : List String := [
  "apache::thrift::async::TEvhttpServer",
  "apache::thrift::TException",
  "apache::thrift::transport::TVirtualTransport<apache::thrift::transport::TMemoryBuffer, apache::thrift::transport::TBufferBase>",
  "apache::thrift::transport::TTransport",
  "apache::thrift::transport::TBufferBase",
  "apache::thrift::transport::TVirtualTransport<apache::thrift::transport::TBufferBase, apache::thrift::transport::TTransportDefaults>",
  "apache::thrift::transport::TTransportDefaults"
]

theorem spVcallSymSpec_bad_of_classes {ctx₁ ctx₂ : Ctx} {goodSym : String → Bool} {s : String} {fd₁ fd₂ : FuncDecl}
    (hall : (nonSpClasses.all (NotSpDerived ctx₂)) = true)
    (hf1 : ctx₁.mod.findFunc? s = some fd₁) (hf2 : ctx₂.mod.findFunc? s = some fd₂)
    (hp12 : fd₁.params.head? = fd₂.params.head?)
    (hmem : (match fd₂.params.head? with | some (.ptr (.record d)) => nonSpClasses.contains d | _ => false) = true)
    (hthk : isThunk s = false := by rfl) :
    SpVcallSymSpec ctx₁ ctx₂ goodSym s := by
  rcases hp : fd₂.params.head? with _ | pty <;> rw [hp] at hmem <;> try cases hmem
  cases pty <;> try cases hmem
  rename_i rty
  cases rty <;> try cases hmem
  rename_i d
  rw [List.all_eq_true] at hall
  exact Or.inr (Or.inr ⟨fd₁, fd₂, d, hf1, hf2, hp12.trans hp, hp, hall d (List.mem_of_elem_eq_true hmem), hthk⟩)

macro "cir_prove_one_sp_func" : tactic => `(tactic| first
  | exact spFuncSpec_of_find (by cir_lookup) (by cir_lookup) (by rfl)
  | exact spFuncSpec_of_mkDispose2Body (by cir_lookup) (by cir_lookup) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl))

macro "cir_prove_sp_funcs" : tactic => `(tactic| (
  dsimp only [spSyms]
  repeat' first
    | exact all_spFuncSpec_nil
    | (refine all_spFuncSpec_cons ?_ ?_; · cir_prove_one_sp_func)))

macro "cir_prove_one_sp_vcall_sym" hall:term:max : tactic => `(tactic| first
  | exact spVcallSymSpec_good rfl
  | exact spVcallSymSpec_bad_of_classes $hall (by cir_lookup) (by cir_lookup) (by rfl) (by rfl))

macro "cir_prove_vtable_arrays_imply" hall:term:max : tactic => `(tactic| (
  repeat' first
    | exact evalVtableArrays_imply_nil
    | refine evalVtableArrays_imply_nonarray rfl ?_
    | (refine evalVtableArrays_imply_array ?_ ?_; · repeat' first
        | exact evalVtableElems_imply_nil
        | refine evalVtableElems_imply_null ?_
        | refine evalVtableElems_imply_func (by cir_lookup) (by cir_lookup) (by cir_lookup) (by cir_prove_one_sp_vcall_sym $hall) ?_
        | refine evalVtableElems_imply_global (by cir_lookup) (by cir_lookup) ?_)))

open Lean Meta Elab Tactic in
elab "cir_prove_sp_vcall " hall:term:max : tactic => withTheReader Core.Context (fun c => { c with maxRecDepth := 100000 }) do
  evalTactic (← `(tactic| intro $(mkIdent `vt):ident $(mkIdent `i):ident $(mkIdent `k):ident $(mkIdent `sym):ident))
  evalTactic (← `(tactic| rw [vtableSlot?_eq_evalVtableAt]))
  let g ← getMainGoal
  let tgt ← g.withContext do instantiateMVars (← g.getType)
  let .forallE _ lhs _ _ := tgt | throwError "not forall"
  let some (_, callE, _) := lhs.eq? | throwError "not eq"
  let ctx2 := callE.getArg! 0
  let M2 ← mkAppM ``CIR.Ctx.mod #[ctx2]
  let gs2 ← mkAppM ``CIR.Module.globals #[M2]
  let some elems2 ← CIR.Tactic.listElems gs2 | throwError "gs2 not list"
  let mod2I := mkIdent (Name.str ctx2.constName!.getPrefix "module")
  let vtI := mkIdent `vt
  let iI := mkIdent `i
  let kI := mkIdent `k
  let symI := mkIdent `sym
  let ctx2I := mkIdent ctx2.constName!
  evalTactic (← `(tactic| change evalVtableAt $ctx2I $iI $kI (List.find? (·.sym == $vtI) (CIR.Module.globals $mod2I)) = some (.ptr (.fn $symI)) → _))
  evalTactic (← `(tactic| dsimp only [$mod2I:ident]))
  for idx in [0:elems2.size] do
    let e2 := elems2[idx]!
    let vtInit ← whnfD (← mkAppM ``vtableInit #[e2])
    if vtInit.isAppOf ``Option.none then
      evalTactic (← `(tactic| refine evalVtableAt_imply_nonvtable rfl ?_))
    else
      evalTactic (← `(tactic| refine evalVtableAt_imply_vtable rfl (by cir_prove_vtable_arrays_imply $hall) ?_))
  evalTactic (← `(tactic| exact evalVtableAt_imply_nil _ _ _ _))

theorem evalOp_getGlobal_congr_rfl {ctx₁ ctx₂ : Ctx} {r : VId} {sym : String} {ty : Ty}
    (hsym : ctx₁.symAddr? sym [] = ctx₂.symAddr? sym []) (σ : State) :
    evalOp ctx₁ (.getGlobal r sym ty) σ = evalOp ctx₂ (.getGlobal r sym ty) σ := by
  simp only [evalOp, evalSimple, hsym]

theorem evalOp_getGlobal_congr' {ctx₁ ctx₂ : Ctx} {r : VId} {sym : String} {ty : Ty} {b : Nat}
    (ha₁ : ctx₁.gaddr sym = some b) (ha₂ : ctx₂.gaddr sym = some b) :
    ∀ σ, evalOp ctx₁ (.getGlobal r sym ty) σ = evalOp ctx₂ (.getGlobal r sym ty) σ :=
  evalOp_getGlobal_congr ha₁ ha₂

theorem evalCall_model_congr' {ctx₁ ctx₂ : Ctx}
    {sym : String} {fd₁ fd₂ : FuncDecl} {mdl : Model}
    (hf₁ : ctx₁.mod.findFunc? sym = some fd₁) (hm₁ : fd₁.model = some mdl)
    (hf₂ : ctx₂.mod.findFunc? sym = some fd₂) (hm₂ : fd₂.model = some mdl)
    (hmdl : ∀ vs m, Std.runModel ctx₁ mdl vs m = Std.runModel ctx₂ mdl vs m) :
    ∀ vs m, evalCall ctx₁ sym vs m = evalCall ctx₂ sym vs m :=
  evalCall_model_congr hf₁ hm₁ hf₂ hm₂ hmdl

theorem evalCall_body_congr' {ctx₁ ctx₂ : Ctx} {sym : String} {fd₁ fd₂ : FuncDecl} {body₁ body₂ : Region}
    (hf₁ : ctx₁.mod.findFunc? sym = some fd₁) (hm₁ : fd₁.model = none) (hb₁ : fd₁.body = some body₁) (hnt₁ : fd₁.nothrow = false)
    (hf₂ : ctx₂.mod.findFunc? sym = some fd₂) (hm₂ : fd₂.model = none) (hb₂ : fd₂.body = some body₂) (hnt₂ : fd₂.nothrow = false)
    (hbody : ∀ args σ, evalRegion ctx₁ body₁ args σ = evalRegion ctx₂ body₂ args σ)
    (hs₁ : fd₁.special ≠ .dtor := by decide) (hs₂ : fd₂.special ≠ .dtor := by decide) :
    ∀ vs m, evalCall ctx₁ sym vs m = evalCall ctx₂ sym vs m :=
  evalCall_body_congr hf₁ hm₁ hb₁ hf₂ hm₂ hb₂ (hnt₁.trans hnt₂.symm) hs₁ hs₂ hbody

theorem dropEnv_cerrLineTail_congr' {ctx₁ ctx₂ : Ctx}
    {fd_i1 fd_i2 fd_c1 fd_c2 : FuncDecl}
    {loc₁ loc₂ : Loc} {r_line r_os r_out1 r_nl r_out2 : VId} {L₁ L₂ : Int}
    (hfi1 : ctx₁.mod.findFunc? "_ZNSolsEi" = some fd_i1) (hmi1 : fd_i1.model = some (.ostreamOut 0))
    (hfi2 : ctx₂.mod.findFunc? "_ZNSolsEi" = some fd_i2) (hmi2 : fd_i2.model = some (.ostreamOut 0))
    (hfc1 : ctx₁.mod.findFunc? "_ZStlsISt11char_traitsIcEERSt13basic_ostreamIcT_ES5_c" = some fd_c1) (hmc1 : fd_c1.model = some (.ostreamOut 0))
    (hfc2 : ctx₂.mod.findFunc? "_ZStlsISt11char_traitsIcEERSt13basic_ostreamIcT_ES5_c" = some fd_c2) (hmc2 : fd_c2.model = some (.ostreamOut 0))
    (hne1 : r_os ≠ r_line) (hne2 : r_out1 ≠ r_nl)
    (hL₁ : inRange true 32 L₁ = true) (hL₂ : inRange true 32 L₂ = true) :
    ∀ σ, dropEnv (evalOps ctx₁
      [.const r_line (.int true 32) (.int L₁),
       .call loc₁ (some r_out1) (.direct "_ZNSolsEi") [r_os, r_line] [(.ptr (.record "std::basic_ostream<char, std::char_traits<char>>")), (.int true 32)] (.ptr (.record "std::basic_ostream<char, std::char_traits<char>>")) false,
       .const r_nl (.int true 8) (.int 10),
       .call loc₁ (some r_out2) (.direct "_ZStlsISt11char_traitsIcEERSt13basic_ostreamIcT_ES5_c") [r_out1, r_nl] [(.ptr (.record "std::basic_ostream<char, std::char_traits<char>>")), (.int true 8)] (.ptr (.record "std::basic_ostream<char, std::char_traits<char>>")) false] σ) =
    dropEnv (evalOps ctx₂
      [.const r_line (.int true 32) (.int L₂),
       .call loc₂ (some r_out1) (.direct "_ZNSolsEi") [r_os, r_line] [(.ptr (.record "std::basic_ostream<char, std::char_traits<char>>")), (.int true 32)] (.ptr (.record "std::basic_ostream<char, std::char_traits<char>>")) false,
       .const r_nl (.int true 8) (.int 10),
       .call loc₂ (some r_out2) (.direct "_ZStlsISt11char_traitsIcEERSt13basic_ostreamIcT_ES5_c") [r_out1, r_nl] [(.ptr (.record "std::basic_ostream<char, std::char_traits<char>>")), (.int true 8)] (.ptr (.record "std::basic_ostream<char, std::char_traits<char>>")) false] σ) :=
  dropEnv_cerrLineTail_congr hfi1 hmi1 hfi2 hmi2 hfc1 hmc1 hfc2 hmc2 loc₁ loc₂ r_line r_os r_out1 r_nl r_out2 hne1 hne2 L₁ L₂ hL₁ hL₂

theorem dropEnv_nil_congr (ctx₁ ctx₂ : Ctx) (σ : State) :
    dropEnv (evalOps ctx₁ [] σ) = dropEnv (evalOps ctx₂ [] σ) := by
  simp only [dropEnv, evalOps.eq_1]

macro "cir_complete_call" hr:term:max hsp:term:max : tactic => `(tactic| first
  | exact $hsp rfl
  | exact evalCall_model_congr' (by cir_lookup) rfl (by cir_lookup) rfl (runModel_evhttpAddHeader_congr $hr)
  | exact evalCall_model_congr' (by cir_lookup) rfl (by cir_lookup) rfl (runModel_evbufferNew_congr _ _)
  | exact evalCall_model_congr' (by cir_lookup) rfl (by cir_lookup) rfl (runModel_evbufferAdd_congr $hr rfl)
  | exact evalCall_model_congr' (by cir_lookup) rfl (by cir_lookup) rfl (runModel_evhttpSendReply_congr $hr)
  | exact evalCall_model_congr' (by cir_lookup) rfl (by cir_lookup) rfl (runModel_evbufferFree_congr _ _)
  | exact evalCall_model_congr' (by cir_lookup) rfl (by cir_lookup) rfl (runModel_ostreamOut_congr _ _ 1 (by decide))
  | exact evalCall_model_congr' (by cir_lookup) rfl (by cir_lookup) rfl (runModel_ostreamOut_congr _ _ 0 (by decide)))

macro "cir_complete_cerr" hr:term:max hv:term:max hsp:term:max : tactic => `(tactic| (
  intro σ; refine evalRegion_congr_of_dropEnv rfl rfl rfl rfl ?_ σ
  repeat' first
    | (intro σ; exact dropEnv_nil_congr _ _ σ)
    | exact dropEnv_cerrLineTail_congr' (by cir_lookup) rfl (by cir_lookup) rfl (by cir_lookup) rfl (by cir_lookup) rfl (by decide) (by decide) rfl rfl
    | (intro σ; refine dropEnv_cons_congr ?_ ?_ σ)
    | exact evalOp_getGlobal_congr' (by cir_lookup) (by cir_lookup)
    | (intro σ; exact evalOp_simple_congr $hr rfl $hv rfl rfl σ)
    | (intro σ; refine evalOp_call_direct_congr ?_ σ)
    | cir_complete_call $hr $hsp))

macro "cir_complete_congr" hr:term:max hv:term:max hsp:term:max : tactic => `(tactic| (
  refine evalCall_body_congr' (by cir_lookup) rfl rfl rfl (by cir_lookup) rfl rfl rfl ?_ (by decide) (by decide)
  repeat' first
    | (intro σ; exact evalOps_nil_congr _ _ σ)
    | (intro σ; exact evalRegion_nil_congr _ _ _ σ)
    | (intro args σ; refine evalRegion_single_congr rfl rfl rfl ?_ args σ)
    | (intro σ; refine evalRegion_single_congr rfl rfl rfl ?_ _ σ)
    | (intro σ; refine evalOps_const_cmp_congr' rfl rfl ?_ σ)
    | (intro σ; refine evalOps_cons_congr ?_ ?_ σ)
    | (intro σ; exact evalOp_simple_congr $hr rfl $hv rfl rfl σ)
    | (intro σ; exact evalOp_terminator_congr rfl σ)
    | exact evalOp_getGlobal_congr' (by cir_lookup) (by cir_lookup)
    | (intro σ; refine evalOp_call_direct_congr ?_ σ)
    | cir_complete_call $hr $hsp
    | (intro σ; refine evalOp_scope_congr ?_ σ)
    | (intro σ; refine evalOp_cleanupScope_congr ?_ ?_ (callsDestructor_single_call (by cir_lookup) rfl (by cir_lookup) rfl) σ)
    | (intro σ; refine evalOp_ifOp_congr (by cir_complete_cerr $hr $hv $hsp) ?_ σ)
    | (intro σ; refine evalOp_ifOp_congr ?_ ?_ σ)))

def badSpVcallSyms : List String := [
  "_ZN6apache6thrift10TExceptionD0Ev",
  "_ZN6apache6thrift10TExceptionD2Ev",
  "_ZN6apache6thrift5async13TEvhttpServerD0Ev",
  "_ZN6apache6thrift5async13TEvhttpServerD1Ev",
  "_ZN6apache6thrift9transport10TTransport10write_virtEPKhj",
  "_ZN6apache6thrift9transport10TTransport11borrow_virtEPhPj",
  "_ZN6apache6thrift9transport10TTransport12consume_virtEj",
  "_ZN6apache6thrift9transport10TTransport12readAll_virtEPhj",
  "_ZN6apache6thrift9transport10TTransport14onewayCompleteEv",
  "_ZN6apache6thrift9transport10TTransport4openEv",
  "_ZN6apache6thrift9transport10TTransport4peekEv",
  "_ZN6apache6thrift9transport10TTransport5closeEv",
  "_ZN6apache6thrift9transport10TTransport5flushEv",
  "_ZN6apache6thrift9transport10TTransport7readEndEv",
  "_ZN6apache6thrift9transport10TTransport8writeEndEv",
  "_ZN6apache6thrift9transport10TTransport9read_virtEPhj",
  "_ZN6apache6thrift9transport10TTransportD0Ev",
  "_ZN6apache6thrift9transport10TTransportD2Ev",
  "_ZN6apache6thrift9transport11TBufferBaseD0Ev",
  "_ZN6apache6thrift9transport11TBufferBaseD2Ev",
  "_ZN6apache6thrift9transport17TVirtualTransportINS1_11TBufferBaseENS1_18TTransportDefaultsEE10write_virtEPKhj",
  "_ZN6apache6thrift9transport17TVirtualTransportINS1_11TBufferBaseENS1_18TTransportDefaultsEE11borrow_virtEPhPj",
  "_ZN6apache6thrift9transport17TVirtualTransportINS1_11TBufferBaseENS1_18TTransportDefaultsEE12consume_virtEj",
  "_ZN6apache6thrift9transport17TVirtualTransportINS1_11TBufferBaseENS1_18TTransportDefaultsEE12readAll_virtEPhj",
  "_ZN6apache6thrift9transport17TVirtualTransportINS1_11TBufferBaseENS1_18TTransportDefaultsEE9read_virtEPhj",
  "_ZN6apache6thrift9transport17TVirtualTransportINS1_11TBufferBaseENS1_18TTransportDefaultsEED0Ev",
  "_ZN6apache6thrift9transport17TVirtualTransportINS1_11TBufferBaseENS1_18TTransportDefaultsEED2Ev",
  "_ZN6apache6thrift9transport17TVirtualTransportINS1_13TMemoryBufferENS1_11TBufferBaseEE10write_virtEPKhj",
  "_ZN6apache6thrift9transport17TVirtualTransportINS1_13TMemoryBufferENS1_11TBufferBaseEE11borrow_virtEPhPj",
  "_ZN6apache6thrift9transport17TVirtualTransportINS1_13TMemoryBufferENS1_11TBufferBaseEE12consume_virtEj",
  "_ZN6apache6thrift9transport17TVirtualTransportINS1_13TMemoryBufferENS1_11TBufferBaseEE12readAll_virtEPhj",
  "_ZN6apache6thrift9transport17TVirtualTransportINS1_13TMemoryBufferENS1_11TBufferBaseEE9read_virtEPhj",
  "_ZN6apache6thrift9transport17TVirtualTransportINS1_13TMemoryBufferENS1_11TBufferBaseEED0Ev",
  "_ZN6apache6thrift9transport17TVirtualTransportINS1_13TMemoryBufferENS1_11TBufferBaseEED2Ev",
  "_ZN6apache6thrift9transport18TTransportDefaultsD0Ev",
  "_ZN6apache6thrift9transport18TTransportDefaultsD2Ev",
  "_ZNK6apache6thrift10TException4whatEv",
  "_ZNK6apache6thrift9transport10TTransport6isOpenEv",
  "_ZNK6apache6thrift9transport10TTransport9getOriginB5cxx11Ev"
]

abbrev badSpVcallSym (s : String) : Bool := badSpVcallSyms.contains s

theorem all_spVcallSymSpec_nil {ctx₁ ctx₂ : Ctx} {goodSym : String → Bool}
    (sym : String) (h : ([].contains sym) = true) : SpVcallSymSpec ctx₁ ctx₂ goodSym sym := by
  cases h

theorem all_spVcallSymSpec_cons {ctx₁ ctx₂ : Ctx} {goodSym : String → Bool} {s : String} {ss : List String}
    (hs : SpVcallSymSpec ctx₁ ctx₂ goodSym s)
    (hss : ∀ sym, ss.contains sym = true → SpVcallSymSpec ctx₁ ctx₂ goodSym sym)
    (sym : String) (h : ((s :: ss).contains sym) = true) : SpVcallSymSpec ctx₁ ctx₂ goodSym sym := by
  rw [List.contains_cons, Bool.or_eq_true, beq_iff_eq] at h
  rcases h with h | h
  · subst h; exact hs
  · exact hss sym h

macro "cir_prove_bad_vcall_syms" hall:term:max : tactic => `(tactic| (
  dsimp only [badSpVcallSym, badSpVcallSyms]
  repeat' first
    | exact all_spVcallSymSpec_nil
    | (refine all_spVcallSymSpec_cons ?_ ?_; · first
        | exact spVcallSymSpec_bad_of_classes $hall (by cir_lookup) (by cir_lookup) (by rfl) (by rfl)
        | exact spVcallSymSpec_none (by cir_lookup))))

def checkVtableElem (ctx : Ctx) (okSym : String → Bool) : Const → Bool
  | .null => true
  | .globalAddr gsym _ => okSym gsym || ((ctx.mod.findGlobal? gsym).isSome && (ctx.gaddr gsym).isSome)
  | _ => false

def checkVtableArray (ctx : Ctx) (okSym : String → Bool) : Const → Bool
  | .array es => es.all (checkVtableElem ctx okSym)
  | _ => true

def checkGlobalVtable (ctx : Ctx) (okSym : String → Bool) (g : GlobalDecl) : Bool :=
  match vtableInit g with
  | none => true
  | some cs => cs.all (checkVtableArray ctx okSym)

def checkAllVtables (ctx : Ctx) (okSym : String → Bool) (gs : List GlobalDecl) : Bool :=
  gs.all (checkGlobalVtable ctx okSym)

theorem evalVtableElems_imply_of_all {ctx : Ctx} {okSym : String → Bool} {es : List Const}
    (h : es.all (checkVtableElem ctx okSym) = true) :
    ∀ k sym, evalVtableElems ctx es k = some (.ptr (.fn sym)) → okSym sym = true := by
  induction es with
  | nil => intro k sym hk; cases hk
  | cons c es ih =>
    simp only [List.all_cons, Bool.and_eq_true] at h
    intro k sym hk
    cases k with
    | zero =>
      cases c <;> try cases h.1
      · cases hk
      · rename_i gsym idx
        have h1 := h.1
        simp only [checkVtableElem, Bool.or_eq_true, Bool.and_eq_true] at h1
        revert hk h1
        simp only [evalVtableElems, Ctx.constVal, Ctx.symAddr?]
        cases ctx.mod.findGlobal? gsym <;> cases ctx.gaddr gsym <;> simp <;> (rintro _ _ rfl hok; exact hok)
    | succ k => exact ih h.2 k sym hk

theorem evalVtableArrays_imply_of_all {ctx : Ctx} {okSym : String → Bool} {cs : List Const}
    (h : cs.all (checkVtableArray ctx okSym) = true) :
    ∀ i k sym, evalVtableArrays ctx cs i k = some (.ptr (.fn sym)) → okSym sym = true := by
  induction cs with
  | nil => intro i k sym hi; cases hi
  | cons c cs ih =>
    simp only [List.all_cons, Bool.and_eq_true] at h
    intro i k sym hi
    cases i with
    | zero =>
      cases c <;> try cases hi
      exact evalVtableElems_imply_of_all h.1 k sym hi
    | succ i =>
      cases c <;> exact ih h.2 i k sym hi

theorem vtableSlot?_imply_of_checkAllVtables {ctx₁ ctx₂ : Ctx} {goodSym badSym : String → Bool}
    (hchk : checkAllVtables ctx₂ (fun s => goodSym s || badSym s) ctx₂.mod.globals = true)
    (hbad : ∀ sym, badSym sym = true → SpVcallSymSpec ctx₁ ctx₂ goodSym sym) :
    ∀ vt i k sym, ctx₂.vtableSlot? vt i k = some (.ptr (.fn sym)) → SpVcallSymSpec ctx₁ ctx₂ goodSym sym := by
  intro vt i k sym hslot
  rw [vtableSlot?_eq_evalVtableAt] at hslot
  rcases hf : ctx₂.mod.globals.find? (·.sym == vt) with _ | g <;> rw [hf] at hslot
  · cases hslot
  · have hmem := List.mem_of_find?_eq_some hf
    rw [checkAllVtables, List.all_eq_true] at hchk
    have hg := hchk g hmem
    unfold checkGlobalVtable at hg
    unfold evalVtableAt at hslot
    dsimp only [Option.bind] at hslot
    rcases hv : vtableInit g with _ | cs <;> rw [hv] at hslot hg
    · cases hslot
    · have hok := evalVtableArrays_imply_of_all hg i k sym hslot
      rw [Bool.or_eq_true] at hok
      rcases hok with h1 | h2
      · exact Or.inl h1
      · exact hbad sym h2

def mkReqCtxVal : Val :=
  .agg [.ptr (.loc 84 []),
        .agg [.agg [.ptr .null, .agg [.ptr .null]]],
        .agg [.agg [.ptr (.loc 87 []), .agg [.ptr .null]]]]

def mkEvReqVal : Val :=
  .agg [.agg [.ptr .null, .ptr .null], .ptr .null, .int 0,
        .ptr (.loc 85 []), .ptr (.loc 86 []),
        .ptr .null, .int 0, .ptr .null, .int 0, .int 0, .int 0, .int 0,
        .ptr .null, .ptr .null, .int 0, .int 0, .int 0, .ptr .null,
        .ptr .null, .int 0, .int 0, .ptr .null,
        .ptr .null, .ptr .null, .ptr .null, .ptr .null, .ptr .null, .ptr .null, .ptr .null]

def mkEvKeyValQ (b : Nat) : Val :=
  .agg [.ptr .null, .ptr (.loc b [.idx 0])]

def mkTMemBufVal : Val :=
  .agg [.agg [.agg [.agg [.agg [.ptr .null, .ptr .null, .int 0, .int 0]],
                    .ptr (.loc 88 [.idx 0]), .ptr (.loc 88 [.idx 0]), .ptr (.loc 88 [.idx 0]), .ptr (.loc 88 [.idx 0]), .bool false]],
        .arr (List.replicate 7 (.int 0)),
        .ptr (.loc 88 [.idx 0]), .int 0, .int 0, .bool false,
        .arr (List.replicate 7 (.int 0))]

def mkCompleteWitnessMem (mod : Module) : Mem :=
  let init := Module.initMem mod
  let b0 := init.blocks
  let b1 := upd b0 83 (some ⟨.heap, true, .record "apache::thrift::async::TEvhttpServer::RequestContext", mkReqCtxVal⟩)
  let b2 := upd b1 84 (some ⟨.heap, true, .record "evhttp_request", mkEvReqVal⟩)
  let b3 := upd b2 85 (some ⟨.heap, true, .record "evkeyvalq", mkEvKeyValQ 85⟩)
  let b4 := upd b3 86 (some ⟨.heap, true, .record "evkeyvalq", mkEvKeyValQ 86⟩)
  let b5 := upd b4 87 (some ⟨.heap, true, .record "apache::thrift::transport::TMemoryBuffer", mkTMemBufVal⟩)
  let b6 := upd b5 88 (some ⟨.heap, true, .array (.int false 8) 1, .arr [.int 0]⟩)
  { blocks := b6, next := 89 }

end EquivLean.Cir
