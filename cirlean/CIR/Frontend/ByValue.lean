import CIR.Frontend.Parser

/-!
  By-value parameters of classes that are non-trivial for calls.

  ClangIR before calling-convention lowering passes a record argument as a value: the caller
  constructs a temporary (`agg.tmp`, by the copy or move constructor), loads it and passes the
  value; the callee stores the value into its parameter's slot (an `init` alloca); the caller
  destroys the temporary at the end of the full expression, and the callee never destroys its
  slot. Executed as written, that makes two objects of what C++ makes one: the parameter is
  initialized from the argument by the copy or move constructor (C++ [expr.call]p7), no further
  copy may be made of a class with a non-trivial copy or move constructor or destructor
  ([class.temporary]p3), and the Itanium ABI passes it by address, the caller destroying it at the
  end of the full expression ([expr.call]p6 leaves that choice to the implementation). When the
  callee moves from its parameter, the caller's temporary keeps the old representation, and its
  destruction frees what the callee's result now owns (math_fibonacci_sum: a matrix returned
  from its by-value parameter).

  For a record that is non-trivial for calls (the module has a copy or move constructor or a
  destructor of it, `nonTrivialRecords`), the frontend makes the parameter that object: the
  parameter becomes a pointer to the record, its slot becomes that pointer (the slot's alloca is
  replaced by a bitcast of the parameter, the store into it is dropped), and each call passes the
  temporary its argument was loaded from. A call whose argument of such a type is no load of a
  local object of the caller, and a call of a function whose parameter is used otherwise than by
  that store, are not modelled (UB, `byValNotModelled`), never a silent copy. Trivially copyable
  records keep the value copy, which [class.temporary]p3 allows. Calls of library models keep
  their values.
-/

namespace CIR.Frontend

/-- The values an operation reads (every operand, not those of its nested regions). -/
def opUses : Op → List VId
  | .const .. | .alloca .. | .allocaConst .. | .getGlobal .. | .blockAddress .. | .vtableAddressPoint ..
  | .vttGlobalAddr .. => []
  | .vttParamAddr _ v _ => [v]
  | .load _ a _ | .retLoad _ a _ => [a]
  | .store v a _ => [v, a]
  | .copy s d _ => [s, d]
  | .getMember _ b _ _ _ | .unionMember _ b _ _ _ => [b]
  | .getElement _ b i _ _ => [b, i]
  | .ptrStride _ b o _ _ => [b, o]
  | .ptrDiff _ a b _ _ => [a, b]
  | .baseClassAddr _ b _ _ _ | .derivedClassAddr _ b _ _ _ => [b]
  | .vtableGetVptr _ o _ => [o]
  | .vtableGetVirtualFnAddr _ v _ => [v]
  | .extractMember _ a _ _ _ => [a]
  | .binop _ _ _ _ a b _ => [a, b]
  | .fbinop _ _ a b _ => [a, b]
  | .fmuladd _ a b c _ => [a, b, c]
  | .shift _ _ a n _ _ => [a, n]
  | .unop _ _ _ a _ => [a]
  | .fneg _ a _ | .fmath _ _ a _ | .isFpClass _ a _ _ | .bitCount _ _ _ a _ | .bitOp _ _ a _ => [a]
  | .isConstant _ a => [a]
  | .rotate _ _ a n _ => [a, n]
  | .copysign _ a b _ | .fminmax _ _ a b _ => [a, b]
  | .prefetch p => [p]
  | .allocaN _ _ _ n => [n]
  | .stackSave _ => []
  | .stackRestore p => [p]
  | .vaCopy s d => [s, d]
  | .vaStart a | .vaEnd a => [a]
  | .vaArg _ a _ | .vaArgP _ a _ => [a]
  | .vaBox _ a _ => [a]
  | .vaEndCheck | .fail _ => []
  | .vaEndCheckOf aps => aps
  | .fitsCheck a _ _ | .alignCheck a _ => [a]
  | .arithOverflow _ _ _ a b _ _ => [a, b]
  | .iabs _ _ a _ => [a]
  | .atomicFetch _ _ _ p v _ => [p, v]
  | .atomicXchg _ p v _ => [p, v]
  | .atomicCmpXchg _ _ p e d _ _ _ => [p, e, d]
  | .getBitfield _ p _ _ _ _ _ => [p]
  | .setBitfield _ p v _ _ _ _ _ => [p, v]
  | .cmp _ _ a b _ => [a, b]
  | .cast _ _ a _ _ => [a]
  | .select _ c a b _ => [c, a, b]
  | .complexCreate _ a b _ => [a, b]
  | .complexPart _ _ c _ => [c]
  | .complexArith _ _ a b _ | .complexEq _ _ a b _ => [a, b]
  | .vecCreate _ xs _ => xs
  | .vecSplat _ x _ _ => [x]
  | .vecExtract _ v i _ => [v, i]
  | .vecInsert _ v x i _ => [v, x, i]
  | .vecCmp _ _ a b _ _ => [a, b]
  | .vecShuffle _ a b _ => [a, b]
  | .vecTernary _ c a b => [c, a, b]
  | .x86Intrinsic _ _ as _ => as
  | .call _ _ callee args _ _ _ => (match callee with | .indirect f => [f] | .direct _ => []) ++ args
  | .scope .. | .cleanupScope .. | .forOp .. | .whileOp .. | .doWhileOp .. | .case .. | .tryOp .. => []
  | .ifOp c _ _ | .ternary _ c _ _ | .switch c _ _ => [c]
  | .setjmp _ e vol svol _ _ => e :: vol ++ svol.map (·.1)
  | .setjmpRun .. => []
  | .sjNote p _ _ => [p]
  | .yield vs => vs
  | .condition c => [c]
  | .brk | .cont | .goto _ | .label _ | .trap | .unreachable | .asmBarrier => []
  | .libc _ args => args
  | .indirectGoto t _ => [t]
  | .ret v => v.toList
  | .br _ args => args
  | .brcond c _ ta _ fa => c :: ta ++ fa
  | .throw o _ _ => o.toList
  | .resume t => [t]
  | .allocException .. => []
  | .beginCatch _ _ e => [e]
  | .endCatch t => [t]
  | .initCatchParam _ e d _ => [e, d]
  | .ehTerminate e => [e]
  | .assume c => [c]
  | .asmTied _ ins _ => ins
  | .unknown _ _ => []

/-- The records of `m` that are non-trivial for calls: a copy or move constructor of `R` (two
pointers to `R`: `R(R&)`, `R(const R&)`, `R(R&&)`) or a destructor of `R` is among its
functions. -/
def nonTrivialRecords (m : Module) : List String :=
  (m.funcs.filterMap fun f => match f.special, f.params with
    | .ctor, [.ptr (.record r), .ptr (.record r')] => if r == r' then some r else none
    | .dtor, [.ptr (.record r)] => some r
    | _, _ => none).eraseDups

/-- The positions of the parameters of types `tys` that are records of `nt`. -/
def byValPositions (nt : List String) (tys : List Ty) : List Nat :=
  (tys.zipIdx.filterMap fun (t, i) => match t with
    | .record r => if nt.contains r then some i else none
    | _ => none)

/-- The operation that a call becomes when one of its by-value arguments of a class non-trivial
for calls cannot be passed as the object (UB when it runs). -/
def byValNotModelled : String := "a by-value argument of a class non-trivial for calls, not modelled"

/-- How `f`'s by-value parameters at `pos` become the caller's objects: for each, the parameter
(an argument of the entry block) and the slot it is stored into (`none` for a parameter it never
uses); `none` when a parameter is used otherwise than by one store into an alloca of its type. -/
def byValSlots (f : FuncDecl) (pos : List Nat) : Option (List (VId × Option VId)) := do
  let some (.mk (.mk args _ :: _)) := f.body | none
  let ops := match f.body with
    | some b => allOpsRegion b
    | none => []
  pos.mapM fun i => do
    let a ← args[i]?
    let t ← f.params[i]?
    let uses := ops.foldl (fun n op => n + ((opUses op).filter (· == a)).length) 0
    if uses == 0 then pure (a, none) else
    guard (uses == 1)
    let s ← ops.findSome? fun op => match op with
      | .store v s ty => if v == a && ty == t then some s else none
      | _ => none
    guard (ops.any fun op => match op with
      | .alloca s' ty _ => s' == s && ty == t
      | _ => false)
    pure (a, some s)

mutual
/-- `ops` with the slots of `slots` (slot, parameter, record type) made the parameters: each
slot's alloca becomes a bitcast of its parameter, the store of the parameter into it goes. -/
partial def slotOps (slots : List (VId × VId × Ty)) : List Op → List Op
  | [] => []
  | op :: rest =>
    match op with
    | .alloca s t _ =>
      match slots.find? (·.1 == s) with
      | some (_, a, _) => .cast s .bitcast a (.ptr t) (.ptr t) :: slotOps slots rest
      | none => op :: slotOps slots rest
    | .store v s _ =>
      if slots.any (fun (s', a, _) => s' == s && a == v) then slotOps slots rest
      else op :: slotOps slots rest
    | .setjmp r e vol svol ok b => .setjmp r e vol svol ok (slotRegion slots b) :: slotOps slots rest
    | op => mapRegions (slotRegion slots) op :: slotOps slots rest
partial def slotRegion (slots : List (VId × VId × Ty)) : Region → Region
  | .mk bs => .mk (bs.map fun (.mk ps ops) => .mk ps (slotOps slots ops))
end

/-- The arguments at `pos` of a call passed as the local objects they were loaded from
(`loads`: `v` loaded from `t`; `allocas`: the function's local objects), their types made
pointers; `none` when one of them is no such load. -/
def passObjects (loads : List (VId × VId)) (allocas : List VId) (pos : List Nat)
    (args : List VId) (tys : List Ty) : Option (List VId × List Ty) :=
  pos.foldlM (init := (args, tys)) fun (args, tys) i => do
    let v ← args[i]?
    let t ← tys[i]?
    let o ← loads.lookup v
    guard (allocas.contains o)
    pure (args.set i o, tys.set i (.ptr t))

/-- A call with its by-value arguments of the records `nt` passed as objects: `direct` gives the
positions for a direct callee (`none`: a callee whose parameters could not become objects, whose
calls are not modelled); an indirect call takes the positions of its argument types. -/
def objCall (nt : List String) (direct : String → Option (List Nat)) (loads : List (VId × VId))
    (allocas : List VId) (op : Op) : Op :=
  match op with
  | .call l r callee args tys rt nth =>
    -- positions whose argument is still a record value (a call passing the object already, after
    -- the unit's own pass, is kept)
    let still := byValPositions nt tys
    let pos? : Option (List Nat) := match callee with
      | .direct s => (direct s).map (·.filter still.contains)
      | .indirect _ => some still
    match pos? with
    | some [] => op
    | some pos =>
      match passObjects loads allocas pos args tys with
      | some (args', tys') => .call l r callee args' tys' rt nth
      | none => .unknown byValNotModelled r.toList
    | none => if still.isEmpty then op else .unknown byValNotModelled r.toList
  | op => op

mutual
/-- `ops` with their calls passing objects (`objCall`). `loads` and `allocas` are the record
loads and local objects in scope, latest first: a value name can come back in a sibling region
(ClangIR numbers each region on from its parent), so a nested region sees its enclosing ones'
and its own, never a sibling's. -/
partial def objCallOps (nt : List String) (direct : String → Option (List Nat))
    (loads : List (VId × VId)) (allocas : List VId) : List Op → List Op
  | [] => []
  | op :: rest =>
    let op' := match op with
      | .call .. => objCall nt direct loads allocas op
      | .setjmp r e vol svol ok b => .setjmp r e vol svol ok (objCallRegion nt direct loads allocas b)
      | op => mapRegions (objCallRegion nt direct loads allocas) op
    let loads := match op with
      | .load v t (.record _) => (v, t) :: loads
      | _ => loads
    let allocas := match op with
      | .alloca t (.record _) _ => t :: allocas
      | _ => allocas
    op' :: objCallOps nt direct loads allocas rest
partial def objCallRegion (nt : List String) (direct : String → Option (List Nat))
    (loads : List (VId × VId)) (allocas : List VId) : Region → Region
  | .mk bs => .mk (bs.map fun (.mk ps ops) => .mk ps (objCallOps nt direct loads allocas ops))
end

/-- Rewrite by-value parameters only in modules that use libc++ (a `std::__1::` function): the
T2/T3 units (libstdc++) keep their Gen. -/
def byValLibcxxOnly : Bool := false

/-- By-value parameters of the records of `m` that are non-trivial for calls made the caller's
objects (see the module docstring); idempotent, so a linked module can run it again. -/
def objectParams (m : Module) : Module := Id.run do
  if byValLibcxxOnly && !(m.funcs.any fun f => (f.demangled.splitOn "std::__1::").length > 1) then
    return m
  let nt := nonTrivialRecords m
  if nt.isEmpty then return m
  -- each function's by-value positions, and its slots when they can become the objects
  let plan : List (FuncDecl × List Nat × Option (List (VId × Option VId))) := m.funcs.map fun f =>
    let pos := if f.model.isSome then [] else byValPositions nt f.params
    (f, pos, if pos.isEmpty || f.body.isNone then some [] else byValSlots f pos)
  let bySym : Std.HashMap String (List Nat × Bool) :=
    plan.foldl (fun h (f, pos, slots?) => h.insert f.sym (pos, slots?.isSome)) {}
  let direct (s : String) : Option (List Nat) :=
    match bySym[s]? with
    | some (pos, true) => some pos
    | some ([], false) => some []
    | some (_, false) => none
    | none => some []
  let funcs := plan.map fun (f, pos, slots?) =>
    -- the parameters become pointers (also in declarations, for calls into other units)
    let f := match slots? with
      | some slots =>
        let params := f.params.zipIdx.map fun (t, i) => if pos.contains i then Ty.ptr t else t
        let sl : List (VId × VId × Ty) := (slots.zip pos).filterMap fun (p : (VId × Option VId) × Nat) =>
          match p.1.2, f.params[p.2]? with
          | some s, some t => some (s, p.1.1, t)
          | _, _ => none
        { f with params := params, body := f.body.map (slotRegion sl) }
      | none => f
    -- the calls pass the objects
    { f with body := f.body.map (objCallRegion nt direct [] []) }
  return { m with funcs := funcs }

end CIR.Frontend
