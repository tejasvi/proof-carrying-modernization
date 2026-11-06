import CIR.Module
import CIR.Std.Models
import Std.Data.HashMap

/-!
  The types of variadic arguments. A call to a variadic function with a body
  passes each argument after the parameters as an object of the type the call
  site gives it (after the default argument promotions, already applied by
  clang): the frontend puts a `va_box` (`Op.vaBox`) before the call for each
  of them and passes its pointer instead, so that `cir.va_arg` can check the
  type it reads against the type passed (C11 7.16.1.1p2). Calls to library
  models, calls with no more arguments than parameters, and indirect calls
  (whose callee is known only at run time) are unchanged; `cir.va_arg` checks
  only the kind of a value passed without its type.
-/

namespace CIR.Frontend

open CIR

/-- The pointer type of a `va_box` of an argument of type `t`. -/
def vaBoxTy (t : Ty) : Ty := .ptr (.func [t] .void false)

def isVaBoxTy : Ty → Bool
  | .ptr (.func [_] .void false) => true
  | _ => false

mutual
/-- `op`, preceded by the `va_box`es of a call's variadic arguments; `nfix` gives the number of
parameters of each variadic function with a body; fresh value ids come from the state. -/
partial def boxOp (nfix : Std.HashMap String Nat) (op : Op) : StateM VId (List Op) := do
  match op with
  | .call loc res (.direct s) args argTys rt nt =>
    match nfix[s]? with
    | some n =>
      if n < args.length && argTys.length == args.length then
        let mut pre : Array Op := #[]
        let mut args' : Array VId := #[]
        let mut tys' : Array Ty := #[]
        for (a, t, i) in args.zip (argTys.zip (List.range args.length)) do
          -- a call boxed before (a unit boxed again after linking) is kept
          if i < n || isVaBoxTy t then
            args' := args'.push a; tys' := tys'.push t
          else
            let v ← get
            set (v + 1)
            pre := pre.push (.vaBox v a t)
            args' := args'.push v; tys' := tys'.push (vaBoxTy t)
        return pre.toList ++ [.call loc res (.direct s) args'.toList tys'.toList rt nt]
      else return [op]
    | none => return [op]
  | .scope res r => return [.scope res (← boxRegion nfix r)]
  | .cleanupScope k a b => return [.cleanupScope k (← boxRegion nfix a) (← boxRegion nfix b)]
  | .ifOp c a b => return [.ifOp c (← boxRegion nfix a) (← boxRegion nfix b)]
  | .ternary res c a b => return [.ternary res c (← boxRegion nfix a) (← boxRegion nfix b)]
  | .forOp loc a b c cl =>
    let cl ← match cl with
      | some (k, r) => pure (some (k, ← boxRegion nfix r))
      | none => pure none
    return [.forOp loc (← boxRegion nfix a) (← boxRegion nfix b) (← boxRegion nfix c) cl]
  | .whileOp loc a b cl =>
    let cl ← match cl with
      | some (k, r) => pure (some (k, ← boxRegion nfix r))
      | none => pure none
    return [.whileOp loc (← boxRegion nfix a) (← boxRegion nfix b) cl]
  | .doWhileOp loc a b => return [.doWhileOp loc (← boxRegion nfix a) (← boxRegion nfix b)]
  | .switch c t r => return [.switch c t (← boxRegion nfix r)]
  | .case k vs r => return [.case k vs (← boxRegion nfix r)]
  | .setjmp r e vol svol ok b => return [.setjmp r e vol svol ok (← boxRegion nfix b)]
  | .tryOp b hs u =>
    let hs ← hs.mapM fun (k, r) => do pure (k, ← boxRegion nfix r)
    let u ← match u with
      | some r => pure (some (← boxRegion nfix r))
      | none => pure none
    return [.tryOp (← boxRegion nfix b) hs u]
  | op => return [op]

partial def boxRegion (nfix : Std.HashMap String Nat) : Region → StateM VId Region
  | .mk bs => do
    let bs ← bs.mapM fun (.mk args ops) => do
      let ops ← ops.mapM (boxOp nfix)
      pure (Block.mk args ops.flatten)
    pure (.mk bs)
end

/-- Box the variadic arguments of the module's calls to its variadic functions with a body (and
no library model): each `va_box` result gets a fresh value id, recorded in `ssaNames`. -/
def boxVarargs (m : Module) : Module :=
  let nfix : Std.HashMap String Nat := m.funcs.foldl (fun h f =>
    if f.body.isSome && f.model.isNone then h.insert f.sym f.params.length else h) {}
  { m with funcs := m.funcs.map fun f =>
    match f.body with
    | none => f
    | some body =>
      let start := f.ssaNames.foldl (fun k (v, _) => max k (v + 1)) 0
      let (body', next) := (boxRegion nfix body).run start
      if next == start then f
      else { f with body := some body',
                    ssaNames := f.ssaNames ++ (List.range (next - start)).map fun i =>
                      (start + i, s!"%va_box{start + i}") } }

end CIR.Frontend

/-! ### The argument types of `printf` conversions

A `printf`, `fprintf`, `sprintf` or `snprintf` argument must have the type its conversion needs
(C11 7.21.6.1p9; after the default argument promotions, which the call site's types already
show). The models see values only, and a model call keeps them unboxed (the calls of the verified
units stay as they are), so the frontend checks the calls whose format is a string literal (a
constant global): before a call with an argument of another type it puts a `fail`, before one
with an argument of the other signedness a `fitsCheck` of its value (read as that type only when
it fits both, as `va_arg` would, 7.16.1.1p2). A format that is not a literal is not checked, nor
is a call through a function pointer. -/

namespace CIR.Frontend

open CIR

/-- The checks before a call of `fname` with format `fmt` and the arguments after it (`small v`:
`v` is a promoted value of a narrower unsigned type, which fits both signednesses). The type each
conversion needs: `Std.convArgTy`, which the `v*printf` models check at run time too. -/
def fmtChecks (fname : String) (fmt : List Int) (args : List (VId × Ty)) (small : VId → Bool) :
    List Op :=
  let verdicts := (Std.fmtNeeds fmt 0).filterMap fun (i, need) =>
    match need, args[i]? with
    | some e, some (v, t) =>
      match e, t with
      | .ptr (.int _ 8), .ptr (.int _ 8) => none
      | .int s w, .int s' w' =>
        if w != w' then some (Sum.inl ())
        else if s == s' || small v then none
        else some (Sum.inr (Op.fitsCheck v e s!"{fname}: an argument of the other signedness that does not fit the type its conversion needs (C11 7.21.6.1p9, 7.16.1.1p2)"))
      | e, t => if e == t then none else some (Sum.inl ())
    | _, _ => none
  if verdicts.any (·.isLeft) then
    [.fail s!"{fname}: an argument of another type than its conversion needs (C11 7.21.6.1p9)"]
  else verdicts.filterMap fun d => match d with | .inr op => some op | .inl _ => none

/-- The string literal a value is, through casts (`defs`: the function's casts and global
addresses by their results). -/
def fmtLiteral (strs : Std.HashMap String (List Int)) (defs : List (VId × Op)) :
    Nat → VId → Option (List Int)
  | fuel + 1, v =>
    match defs.lookup v with
    | some (.cast _ _ a _ _) => fmtLiteral strs defs fuel a
    | some (.getGlobal _ g _) => strs[g]?
    | _ => none
  | 0, _ => none

mutual
partial def fmtOps (calls : Std.HashMap String (String × Nat)) (strs : Std.HashMap String (List Int))
    (defs : List (VId × Op)) : List Op → List Op
  | [] => []
  | op :: rest =>
    let checks : List Op := match op with
      | .call _ _ (.direct s) args argTys _ _ =>
        match calls[s]? with
        | some (fname, n) =>
          match args[n - 1]?.bind (fmtLiteral strs defs 8) with
          | some fmt =>
            let small (v : VId) : Bool := match defs.lookup v with
              | some (.cast _ .integral _ (.int false w) _) => w < 32
              | _ => false
            if argTys.length == args.length then fmtChecks fname fmt ((args.drop n).zip (argTys.drop n)) small
            else []
          | none => []
        | none => []
      | _ => []
    -- the definitions in scope: the earlier ops of this block and of the enclosing ones, the
    -- latest first (sibling regions reuse SSA names)
    let defs' := match op with
      | .getGlobal r _ _ | .cast r _ _ _ _ => (r, op) :: defs
      | _ => defs
    checks ++ [fmtOp calls strs defs op] ++ fmtOps calls strs defs' rest
partial def fmtOp (calls : Std.HashMap String (String × Nat)) (strs : Std.HashMap String (List Int))
    (defs : List (VId × Op)) : Op → Op
  | .scope res r => .scope res (fmtRegion calls strs defs r)
  | .cleanupScope k a b => .cleanupScope k (fmtRegion calls strs defs a) (fmtRegion calls strs defs b)
  | .ifOp c a b => .ifOp c (fmtRegion calls strs defs a) (fmtRegion calls strs defs b)
  | .ternary res c a b => .ternary res c (fmtRegion calls strs defs a) (fmtRegion calls strs defs b)
  | .forOp loc a b c cl =>
    .forOp loc (fmtRegion calls strs defs a) (fmtRegion calls strs defs b) (fmtRegion calls strs defs c)
      (cl.map fun (k, r) => (k, fmtRegion calls strs defs r))
  | .whileOp loc a b cl =>
    .whileOp loc (fmtRegion calls strs defs a) (fmtRegion calls strs defs b)
      (cl.map fun (k, r) => (k, fmtRegion calls strs defs r))
  | .doWhileOp loc a b => .doWhileOp loc (fmtRegion calls strs defs a) (fmtRegion calls strs defs b)
  | .switch c t r => .switch c t (fmtRegion calls strs defs r)
  | .case k vs r => .case k vs (fmtRegion calls strs defs r)
  | .tryOp b hs u =>
    .tryOp (fmtRegion calls strs defs b) (hs.map fun (k, r) => (k, fmtRegion calls strs defs r))
      (u.map (fmtRegion calls strs defs))
  -- the rest of a block after a `setjmp` (`nestSetjmps`)
  | .setjmp r e vol svol ok b => .setjmp r e vol svol ok (fmtRegion calls strs defs b)
  | .setjmpRun r t v b => .setjmpRun r t v (fmtRegion calls strs defs b)
  | op => op
partial def fmtRegion (calls : Std.HashMap String (String × Nat)) (strs : Std.HashMap String (List Int))
    (defs : List (VId × Op)) : Region → Region
  | .mk bs => .mk (bs.map fun (.mk args ops) => .mk args (fmtOps calls strs defs ops))
end

/-- Check the argument types of the module's `printf` / `fprintf` / `sprintf` / `snprintf` calls
whose format is a string literal (see above). -/
def checkFormats (m : Module) : Module :=
  let calls : Std.HashMap String (String × Nat) := m.funcs.foldl (fun h f =>
    match f.model with
    | some (.printf k) => h.insert f.sym (if k == 0 then "printf" else "fprintf", 1 + k)
    | some .sprintf => h.insert f.sym ("sprintf", 2)
    | some .snprintf => h.insert f.sym ("snprintf", 3)
    | _ => h) {}
  if calls.isEmpty then m else
  -- a literal is a constant global (`cir.global constant`, as Clang makes string literals): a
  -- `static char fmt[] = "%d"` the program may change before the call
  let strs : Std.HashMap String (List Int) := m.globals.foldl (fun h g =>
    match g.init with
    | some (.str bytes _) => if g.constant then h.insert g.sym (bytes.takeWhile (· != 0)) else h
    | _ => h) {}
  { m with funcs := m.funcs.map fun f =>
    match f.body with
    | some body => { f with body := some (fmtRegion calls strs [] body) }
    | none => f }

end CIR.Frontend
