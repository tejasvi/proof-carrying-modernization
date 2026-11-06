import CIR.Frontend.ByValue
import CIR.Frontend.Retval

/-!
  Returns of classes that are non-trivial for calls.

  ClangIR before calling-convention lowering returns a record as a value: the callee builds the
  result in its return slot (`cir.alloca "__retval"`, also the named object of a named return
  value) and returns a load of it; the caller stores the value into the object the call
  initializes (a variable, a temporary, a member, its own return slot). Executed as written, that
  makes two objects of what C++ makes one: a prvalue result initializes that object directly
  (C++ [dcl.init.general]p16.6.1, [stmt.return]p2), no further copy may be made of a class with a
  non-trivial copy or move constructor or destructor ([class.temporary]p3), and the Itanium ABI
  passes the object's address to the callee. The callee's slot dies at its return, so an object
  that points into itself (a list's end node, the header of a map or a set) or that registered
  its address keeps pointing at the dead slot from the caller's copy.

  For a record that is non-trivial for calls (`nonTrivialRecords`), the frontend makes the
  caller's object the result object: a function returning one gets a hidden parameter after its
  named ones, a pointer to the record (`FuncDecl.retObj`), and returns nothing; its return slot
  becomes that pointer (the slot's alloca is replaced by a bitcast of the parameter), and each
  `return` of a load of the slot returns nothing. Each call passes the object its result was
  stored into, and the store goes. A function that returns anything else, and a call whose result
  is used otherwise than by one store right after the call, are not modelled (UB,
  `retNotModelled`), never a silent copy. Trivially copyable records keep the value copy, which
  [class.temporary]p3 allows. Calls of library models keep their values.
-/

namespace CIR.Frontend

/-- The operation that a call becomes when its result of a class non-trivial for calls cannot be
built in the caller's object (UB when it runs). -/
def retNotModelled : String := "a return value of a class non-trivial for calls, not modelled"

/-- How a call returning a record that is non-trivial for calls gets its result: as a value (a
library model, a callee the module does not have), in the caller's object passed after the `k`
named arguments, or not at all (a callee whose result could not become the caller's object). -/
inductive ResultPass where
  | value
  | object (k : Nat)
  | notModelled

mutual
/-- The operations among `ops` and their regions that read `v` (every operand, `opUses`). -/
partial def readersOps (v : VId) (ops : List Op) : List Op :=
  ops.flatMap fun op =>
    (if (opUses op).contains v then [op] else []) ++ (opRegions op).flatMap (readersRegion v)
partial def readersRegion (v : VId) : Region → List Op
  | .mk bs => bs.flatMap fun (.mk _ ops) => readersOps v ops
end

mutual
/-- Whether every `cir.return` with a value among `ops` returns a load of `slot` made right
before it. -/
partial def retsOfSlotOps (slot : VId) : List Op → Bool
  | [] => true
  | .load r a _ :: .ret (some r') :: rest => a == slot && r == r' && retsOfSlotOps slot rest
  | .ret (some _) :: _ => false
  | op :: rest => (opRegions op).all (retsOfSlotRegion slot) && retsOfSlotOps slot rest
partial def retsOfSlotRegion (slot : VId) : Region → Bool
  | .mk bs => bs.all fun (.mk _ ops) => retsOfSlotOps slot ops
end

mutual
/-- `ops` with the return slot `slot` (of record type `t`) made the result object `obj`: the
slot's alloca becomes a bitcast of `obj`, a `return` of a load of the slot returns nothing. -/
partial def resultOps (slot obj : VId) (t : Ty) : List Op → List Op
  | [] => []
  | op :: rest =>
    match op, rest with
    | .load r a _, .ret (some r') :: rest' =>
      if a == slot && r == r' then .ret none :: resultOps slot obj t rest'
      else op :: resultOps slot obj t rest
    | _, _ =>
      let op' := match op with
        | .alloca s _ _ => if s == slot then .cast s .bitcast obj (.ptr t) (.ptr t) else op
        | .setjmp r e vol svol ok b => .setjmp r e vol svol ok (resultRegion slot obj t b)
        | .setjmpRun r tok v b => .setjmpRun r tok v (resultRegion slot obj t b)
        | op => mapRegions (resultRegion slot obj t) op
      op' :: resultOps slot obj t rest
partial def resultRegion (slot obj : VId) (t : Ty) : Region → Region
  | .mk bs => .mk (bs.map fun (.mk ps ops) => .mk ps (resultOps slot obj t ops))
end

mutual
/-- `ops` with their calls returning records of `nt` passing the caller's objects (`how`, for a
direct callee; an indirect call takes the object last): the call and the store of its result
right after it become one call passing the store's destination. A call whose result anything
else reads, or that has none, is not modelled. -/
partial def resultCallOps (nt : List String) (how : String → ResultPass) : List Op → List Op
  | [] => []
  | op :: rest =>
    let op : Op := match op with
      | .setjmp r e vol svol ok b => .setjmp r e vol svol ok (resultCallRegion nt how b)
      | .setjmpRun r tok v b => .setjmpRun r tok v (resultCallRegion nt how b)
      | op => mapRegions (resultCallRegion nt how) op
    match op with
    | .call l res callee args tys (.record r) nth =>
      if !nt.contains r then op :: resultCallOps nt how rest else
      let pass := match callee with
        | .direct s => how s
        | .indirect _ => .object args.length
      match pass, res, rest with
      | .value, _, _ => op :: resultCallOps nt how rest
      | .object k, some v, .store v' d _ :: rest' =>
        if v' == v && (readersOps v rest').isEmpty then
          .call l none callee (args.take k ++ d :: args.drop k)
            (tys.take k ++ Ty.ptr (.record r) :: tys.drop k) .void nth :: resultCallOps nt how rest'
        else .unknown retNotModelled res.toList :: resultCallOps nt how rest
      | _, _, _ => .unknown retNotModelled res.toList :: resultCallOps nt how rest
    | op => op :: resultCallOps nt how rest
partial def resultCallRegion (nt : List String) (how : String → ResultPass) : Region → Region
  | .mk bs => .mk (bs.map fun (.mk ps ops) => .mk ps (resultCallOps nt how ops))
end

/-- A value id that `f` does not use: past its SSA names (the parser's, block arguments included,
and those of the frontend's own values) and every value its body reads. -/
def freshVId (f : FuncDecl) : VId :=
  let n := f.ssaNames.foldl (fun k (v, _) => max k (v + 1)) 0
  match f.body with
  | some b => (allOpsRegion b).foldl (fun k op => (opUses op).foldl (fun k v => max k (v + 1)) k) n
  | none => n

/-- How the module's calls get the results of each function returning a record of `nt`: library
models give values; a function already rewritten (`retObj`) or whose result can become the
caller's object (a declaration, or a body whose returns all return a load of its return slot of
that record, or none) takes it after its named parameters; any other is not modelled. -/
def resultPass (nt : List String) (f : FuncDecl) : Option ResultPass :=
  if f.model.isSome then some .value
  else if f.retObj then some (.object (f.params.length - 1))
  else match f.ret with
    | .record r =>
      if !nt.contains r then none else
      match f.body with
      | none => some (.object f.params.length)
      | some b =>
        match retSlot? b with
        | some slot =>
          let typed := (allOpsRegion b).any fun op => match op with
            | .alloca s t _ => s == slot && t == .record r
            | _ => false
          if typed && retsOfSlotRegion slot b then some (.object f.params.length) else some .notModelled
        | none =>
          -- no return slot: no return with a value either (a function that only throws)
          if retsOfSlotRegion (freshVId f) b then some (.object f.params.length) else some .notModelled
    | _ => none

/-- The results of the records of `m` that are non-trivial for calls built in the caller's
objects (see the module docstring); idempotent, so a linked module can run it again. -/
def retObjects (m : Module) : Module := Id.run do
  let nt := nonTrivialRecords m
  if nt.isEmpty then return m
  let plan : Std.HashMap String ResultPass :=
    m.funcs.foldl (fun h f => match resultPass nt f with
      | some p => h.insert f.sym p
      | none => h) {}
  let how (s : String) : ResultPass := plan.getD s .value
  let funcs := m.funcs.map fun f =>
    let f := match plan[f.sym]?, f.ret with
      | some (.object _), t@(.record _) =>
        if f.retObj then f else
        match f.body with
        | none => { f with params := f.params ++ [Ty.ptr t], ret := .void, retObj := true }
        | some b@(.mk (.mk ps ops :: bs)) =>
          let obj := freshVId f
          let b' : Region := .mk (.mk (ps ++ [obj]) ops :: bs)
          let b' := match retSlot? b with
            | some slot => resultRegion slot obj t b'
            | none => b'
          { f with params := f.params ++ [Ty.ptr t], ret := .void, retObj := true, body := some b',
                   ssaNames := f.ssaNames ++ [(obj, "%retobj")] }
        | some _ => f
      | _, _ => f
    { f with body := f.body.map (resultCallRegion nt how) }
  return { m with funcs := funcs }

end CIR.Frontend
