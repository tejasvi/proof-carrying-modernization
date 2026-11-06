import CIR.Module
import CIR.Frontend.Parser

/-!
  Reaching the closing brace of a non-void function, which is undefined only
  if the caller uses the value (C11 6.9.1p12). CIRGen gives the function a
  return slot, `cir.alloca "__retval"`: each `return e` stores `e` into it and
  returns a load of it, and the closing brace gets a load of the slot and a
  `cir.return` too (C++ gets a `cir.trap` there instead; `main` has its slot
  set to 0 at entry, C11 5.1.2.2.3). That last load must not be undefined
  itself when control gets there. The frontend marks a load of the slot (of a
  scalar or an aggregate, `retMarked`) that feeds a `cir.return` as
  `Op.retLoad` unless it can show a store to the
  slot on every path from the function's entry, by a forward pass over the
  structured regions: a store or copy into the slot sets the state; the
  branches of `cir.if` and `cir.ternary` are joined, without those that never
  complete (they end in a return, trap, goto, break, continue, ...); a loop
  whose condition is the constant true and whose body has no break never
  completes, nor does a switch with a default case, no break and a last case
  that never completes (the others fall through into it); any other loop,
  switch or try leaves the state it was
  entered with, and every block but the entry block of a region starts from the
  state at the region's entry. Every `return` statement follows its store, so
  its load stays a plain load, as do the closing-brace loads that cannot be
  reached without one.
-/

namespace CIR.Frontend

open CIR

/-- A loop condition region that always yields true: `cir.const #true`, or a nonzero integer
constant through `int_to_bool` (CIRGen's `for (;;)` and `while (1)`). -/
def condAlwaysTrue : Region → Bool
  | .mk [.mk [] [.const r _ (.bool true), .condition c]] => r == c
  | .mk [.mk [] [.const r _ (.int v), .cast b .intToBool a _ _, .condition c]] =>
    v != 0 && a == r && b == c
  | _ => false

/-- A type whose missing return value `Op.retLoad` gives as `.undef`: a scalar type (as
`Ty.isScalar` of the semantics), whose use is undefined like that of any indeterminate scalar,
and, when `agg` (a C module), a structure, union or array type, whose use (initializing or
assigning an object, an argument, a member access, a return) the semantics makes undefined
although its indeterminate members could be copied. In C++ the closing brace has a `cir.trap`, so
a load of an aggregate slot that feeds a `cir.return` is a return statement's, of an object built
in the slot (the named return value). -/
def retMarked (agg : Bool) : Ty → Bool
  | .int .. | .bool | .float _ | .ptr _ | .vptr => true
  | .record _ | .array .. => agg
  | _ => false

/-- The state where two branches complete; `none`: never (a branch that never completes adds
nothing). -/
def joinSt : Option Bool → Option Bool → Option Bool
  | none, s => s
  | s, none => s
  | some a, some b => some (a && b)

mutual
/-- Whether `ops` contain a `cir.break` of their innermost enclosing loop or switch (one inside
a nested loop or switch breaks that one). -/
partial def breaksOps : List Op → Bool
  | [] => false
  | op :: rest => breaksOp op || breaksOps rest

partial def breaksOp : Op → Bool
  | .brk => true
  | .scope _ b | .case _ _ b => breaksRegion b
  | .cleanupScope _ b c | .ifOp _ b c | .ternary _ _ b c => breaksRegion b || breaksRegion c
  | .tryOp b hs u =>
    breaksRegion b || hs.any (fun (_, r) => breaksRegion r) || (u.map breaksRegion).getD false
  | _ => false

partial def breaksRegion : Region → Bool
  | .mk bs => bs.any fun (.mk _ ops) => breaksOps ops
end

mutual
/-- `ops` with the loads of the return slot `slot` that feed a `cir.return` marked where the
slot may be unstored (`st`: stored on every path to the start of `ops`), and the state where
`ops` complete, `none` if they never do. -/
partial def retOps (agg : Bool) (slot : VId) (st : Bool) : List Op → List Op × Option Bool
  | [] => ([], some st)
  | op :: rest =>
    let (op', s) := match op, rest with
      | .load r a ty, .ret (some r') :: _ =>
        (if a == slot && r == r' && !st && retMarked agg ty then .retLoad r a ty else op, some st)
      | _, _ => retOp agg slot st op
    match s with
    | some st' => let (rest', e) := retOps agg slot st' rest; (op' :: rest', e)
    | none => (op' :: rest, none)

partial def retOp (agg : Bool) (slot : VId) (st : Bool) (op : Op) : Op × Option Bool :=
  let sub (r : Region) : Region := (retRegion agg slot st r).1
  let loop (c b : Region) : Option Bool :=
    if condAlwaysTrue c && !breaksRegion b then none else some st
  match op with
  | .store _ a _ => (op, some (st || a == slot))
  | .copy _ d _ => (op, some (st || d == slot))
  | .ret _ | .trap | .unreachable | .goto _ | .indirectGoto .. | .brk | .cont | .br .. | .brcond ..
  | .throw .. | .resume _ => (op, none)
  | .scope res b => let (b', e) := retRegion agg slot st b; (.scope res b', e)
  | .cleanupScope k b c => let (b', e) := retRegion agg slot st b; (.cleanupScope k b' (sub c), e)
  | .ifOp c a b =>
    let (a', ea) := retRegion agg slot st a
    let (b', eb) := retRegion agg slot st b
    (.ifOp c a' b', joinSt ea eb)
  | .ternary res c a b =>
    let (a', ea) := retRegion agg slot st a
    let (b', eb) := retRegion agg slot st b
    (.ternary res c a' b', joinSt ea eb)
  | .forOp loc c b s cl =>
    (.forOp loc (sub c) (sub b) (sub s) (cl.map fun (k, r) => (k, sub r)), loop c b)
  | .whileOp loc c b cl => (.whileOp loc (sub c) (sub b) (cl.map fun (k, r) => (k, sub r)), loop c b)
  | .doWhileOp loc b c => (.doWhileOp loc (sub b) (sub c), loop c b)
  | .switch c ty b =>
    (.switch c ty (sub b), if switchNeverCompletes agg slot st b then none else some st)
  | .case k vs b => (.case k vs (sub b), some st)
  | .tryOp b hs u => (.tryOp (sub b) (hs.map fun (k, r) => (k, sub r)) (u.map sub), some st)
  -- the rest of a block after a `setjmp` (`nestSetjmps`), from the state at the call (again after
  -- a `longjmp`)
  | .setjmp r e vol svol ok b => let (b', s) := retRegion agg slot st b; (.setjmp r e vol svol ok b', s)
  | .setjmpRun r t v b => let (b', s) := retRegion agg slot st b; (.setjmpRun r t v b', s)
  | _ => (op, some st)

/-- A switch body made of cases, one of them `default`, none of which breaks, the last of which
never completes (a case that completes falls through into the next one): control never leaves
the switch normally. -/
partial def switchNeverCompletes (agg : Bool) (slot : VId) (st : Bool) : Region → Bool
  | .mk [.mk [] ops] =>
    match ops.getLast?, ops.dropLast with
    | some (.yield []), cases@(_ :: _) =>
      cases.all (fun | .case _ _ b => !breaksRegion b | _ => false) &&
      cases.any (fun | .case .default _ _ => true | _ => false) &&
      (match cases.getLast? with
        | some (.case _ _ b) => (retRegion agg slot st b).2.isNone
        | _ => false)
    | _, _ => false
  | _ => false

/-- `retOps` on each block of a region (blocks after the entry block start from the state at
the region's entry), and the state where the region completes. -/
partial def retRegion (agg : Bool) (slot : VId) (st : Bool) : Region → Region × Option Bool
  | .mk [] => (.mk [], some st)
  | .mk bs =>
    let rs := bs.map fun (.mk args ops) =>
      let (ops', e) := retOps agg slot st ops
      (Block.mk args ops', e)
    (.mk (rs.map (·.1)), rs.foldl (fun acc (_, e) => joinSt acc e) none)
end

/-- The return slot of a function body: the result of its `cir.alloca "__retval"`. -/
def retSlot? : Region → Option VId
  | .mk (.mk _ ops :: _) => ops.findSome? fun
    | .alloca r _ "__retval" => some r
    | _ => none
  | _ => none

/-- Mark the loads of each function's return slot that feed a `cir.return` where the slot may
be unstored (`Op.retLoad`). -/
def markRetLoads (m : Module) : Module :=
  { m with funcs := m.funcs.map fun f =>
    match f.body with
    | some body =>
      match retSlot? body with
      | some slot => { f with body := some (retRegion (!m.cxx) slot false body).1 }
      | none => f
    | none => f }

/-! ### Discarded aggregate results

  A caller that discards a structure or union value still stores it: CIRGen makes a temporary
  for it, `cir.alloca "agg.tmpN"`, and stores the call's result there. The semantics makes any
  store of the missing value of a call that reached its function's closing brace undefined (a
  use of it, C11 6.9.1p12: `Op.retLoad` gives it as `.undef`, `missingAggCheck`), so the
  frontend drops those stores: the temporary is used by nothing else, the result by nothing
  else.
-/

/-- A structure, union or array type. -/
def aggTy : Ty → Bool
  | .record _ | .array .. => true
  | _ => false

/-- The calls of `body` whose aggregate result only goes into an `agg.tmp` temporary that nothing
else uses: the results, and each with its temporary. -/
def retDiscards (body : Region) : List (VId × VId) :=
  let ops := allOpsRegion body
  let aggCalls := ops.filterMap fun op => match op with
    | .call _ (some r) _ _ _ retTy _ => if aggTy retTy then some r else none
    | _ => none
  ops.filterMap fun op => match op with
    | .alloca t _ name =>
      if !name.startsWith "agg.tmp" then none else
      match usesInRegion t body with
      | [.store r t' _] =>
        if t' == t && aggCalls.contains r && (usesInRegion r body).length == 1 then some (r, t)
        else none
      | _ => none
    | _ => none

mutual
/-- `ops` without the stores of `ds` (result, temporary). -/
partial def discardOps (ds : List (VId × VId)) : List Op → List Op
  | [] => []
  | op :: rest =>
    let rest' := discardOps ds rest
    match op with
    | .store r t _ => if ds.contains (r, t) then rest' else op :: rest'
    | .setjmp r env vol svol ok b => .setjmp r env vol svol ok (discardRegion ds b) :: rest'
    | .setjmpRun r tok v b => .setjmpRun r tok v (discardRegion ds b) :: rest'
    | op => mapRegions (discardRegion ds) op :: rest'

partial def discardRegion (ds : List (VId × VId)) : Region → Region
  | .mk bs => .mk (bs.map fun (.mk args ops) => .mk args (discardOps ds ops))
end

/-- Drop the stores of discarded aggregate call results into `agg.tmp` temporaries
(`retDiscards`), in every function. -/
def markRetDiscards (m : Module) : Module :=
  { m with funcs := m.funcs.map fun f =>
    match f.body with
    | some body =>
      match retDiscards body with
      | [] => f
      | ds => { f with body := some (discardRegion ds body) }
    | none => f }

end CIR.Frontend
