import Cobol
open Lean Cobol

/-! ar2-fix (stages A, B, C): the resolved IR of the theorem programs is the same before and after the
fixes (`scripts/lrun.sh scripts/lean1.sh tests/Ar2Resolve.lean`, from the tree root).

`Cobol.Resolve.Old.*` are `expr`, `cond`, the `stmts` / `stmt` / `varyingParts` / `varyingIdxParts`
block and `program` of the resolver before the fixes (the merge-11 snapshot's
`Cobol/Frontend/Resolve.lean`, lines 298-356, 397-473, 618-875 and 1011-1058), copied verbatim by
program; inside `namespace Cobol.Resolve.Old` they call each other and every other function of
`Cobol.Resolve` (the current one, whose other functions the fixes leave as they were; `operandExpr`
calls the current `expr` on a data reference only, which the fixes do not change), as in the original
file.
`Ar2Resolve.thmIRs`: the 15 surface IRs the theorems load (`examples/*/*.ir.json`); the `#eval`
resolves each with both resolvers and compares the results as terms (`toExpr`, the literal the
`cobol_program` command elaborates) and as `repr` text: "same" for all 15. With the environment
variable `AR2_LIST` naming a file of surface-IR paths (one per line), it compares those too and
prints each that differs, statement by statement, with the number of `Expr.ir30`, `Expr.ir30open`
and `Expr.pow0` nodes in the new resolution (the exposure of the fixes). -/

namespace Cobol.Resolve.Old
open Surface

/-- The decimal places that give the `dmax` of the expressions inside a `COMPUTE`'s function
arguments: `dScales` as it was before `INTEGER`, `INTEGER-PART` and `MOD` counted as integer
functions (their arguments' places count here), kept for function arguments (IBM's inner `dmax`
is an open reading). -/
def dScalesIn (ctx : Ctx) : Surface.Expr → List Int
  | .lit _ s => [s]
  | .ref r => [refScale ctx r.item]
  | .idx _ => [0]
  | .neg a => dScalesIn ctx a
  | .add a b | .sub a b | .mul a b => dScalesIn ctx a ++ dScalesIn ctx b
  | .div a _ _ => dScalesIn ctx a
  | .pow a _ => dScalesIn ctx a
  | .fn name args =>
    -- integer functions of integer arguments contribute no decimal places (IBM outer-dmax 0)
    if ["FACTORIAL", "INTEGER-OF-DATE", "DATE-OF-INTEGER", "INTEGER-OF-DAY",
        "DAY-OF-INTEGER"].contains name.toUpper then [0]
    -- ORD-MAX / ORD-MIN are integer functions of arguments of any scale
    else if ["ORD-MAX", "ORD-MIN"].contains name.toUpper then [0]
    else args.flatMap (dScalesIn ctx)
  | .afn _ _ => [0]
  | .powE a _ => dScalesIn ctx a

/-- Lower an arithmetic expression; `dmax` and `rounded` drive the division rule. -/
partial def expr (ctx : Ctx) (dmax : Int) (rounded : Bool) : Surface.Expr → Except String Cobol.Expr
  | .lit v s => pure (.lit v s)
  | .ref r => do
    let d ← ref ctx r
    match d.desc.kind with
    | .num _ => if d.refmod.isNone then pure (.ref d) else throw "reference-modified operand in arithmetic"
    | _ => throw s!"non-numeric item {r.item} in an arithmetic expression"
  | .idx i => pure (.idx i)
  | .neg a => do pure (.neg (← expr ctx dmax rounded a))
  | .add a b => do pure (.add (← expr ctx dmax rounded a) (← expr ctx dmax rounded b))
  | .sub a b => do pure (.sub (← expr ctx dmax rounded a) (← expr ctx dmax rounded b))
  | .mul a b => do pure (.mul (← expr ctx dmax rounded a) (← expr ctx dmax rounded b))
  | .div a b s => do
    let a' ← expr ctx dmax rounded a
    let b' ← expr ctx dmax rounded b
    -- IBM: "(d2 - d1) or dmax, whichever is greater" decimal places (d2 the dividend's, d1 the
    -- divisor's), one more when a receiver is ROUNDED
    let sc := match s with
      | some s => s
      | none => max (decPlaces a' - decPlaces b') dmax + (if rounded && ctx.dialect.divExtraForRounded then 1 else 0)
    pure (.div a' b' sc .truncation)
  | .pow a n => do
    let a' ← expr ctx dmax rounded a
    pure ((List.replicate n a').foldl (fun acc x => .mul acc x) (.lit 1 0))
  | .fn name args => do
    let as ← args.mapM (expr ctx (ctx.dmaxIn.getD dmax) rounded)
    match name.toUpper, as with
    | "ABS", [a] => pure (.abs a)
    | "INTEGER", [a] => pure (.integer a)
    | "INTEGER-PART", [a] => pure (.integerPart a)
    | "MOD", [a, b] => pure (.mod a b)
    | "REM", [a, b] => pure (.rem a b)
    | "MIN", a :: rest => pure (rest.foldl .min a)
    | "MAX", a :: rest => pure (rest.foldl .max a)
    -- IBM: SUM adds the arguments in order to 0; RANGE subtracts MIN from MAX (exact)
    | "SUM", a :: rest => pure (rest.foldl .add a)
    | "RANGE", a :: rest => pure (.sub (rest.foldl .max a) (rest.foldl .min a))
    | "FACTORIAL", [a] => pure (.factorial a)
    | "INTEGER-OF-DATE", [a] => pure (.dateFn .integerOfDate a)
    | "DATE-OF-INTEGER", [a] => pure (.dateFn .dateOfInteger a)
    | "INTEGER-OF-DAY", [a] => pure (.dateFn .integerOfDay a)
    | "DAY-OF-INTEGER", [a] => pure (.dateFn .dayOfInteger a)
    | "ORD-MAX", a :: rest => pure (ordMinMax true a rest)
    | "ORD-MIN", a :: rest => pure (ordMinMax false a rest)
    | n, _ => throw s!"unsupported intrinsic function {n}"
  | .afn name args => do
    let as ← args.mapM (operand ctx)
    let pos := (ctx.seq.getD .native).pos
    match name.toUpper, as with
    | "ORD", [a] => pure (.ord a pos)
    | "ORD-MAX", _ :: _ => pure (.ordA true as pos)
    | "ORD-MIN", _ :: _ => pure (.ordA false as pos)
    | n, _ => throw s!"unsupported intrinsic function {n}"
  | .powE a e => do
    -- IBM: with an integral data-name or variable as the exponent, the power is held with dmax
    -- decimal places; with ROUNDED one more place "might be carried", which is not modelled
    if rounded then throw "exponent other than a literal under ROUNDED"
    pure (.powInt (← expr ctx dmax rounded a) (← expr ctx dmax rounded e) dmax)

partial def cond (ctx : Ctx) : Surface.Cond → Except String Cobol.Cond
  | .const b => pure (.const b)
  | .rel op a b => do
    let o ← cmpOp op
    if (isNumeric ctx a || isZeroFig a) && (isNumeric ctx b || isZeroFig b) &&
        (isNumeric ctx a || isNumeric ctx b) then
      pure (.numCmp o (← operandExpr ctx a) (← operandExpr ctx b))
    else if let some s := ctx.seq then
      -- PROGRAM COLLATING SEQUENCE: nonnumeric comparisons by its positions
      pure (.alnumCmpSeq o (← operand ctx a) (← operand ctx b) s.pos)
    else pure (.alnumCmp o (← operand ctx a) (← operand ctx b))
  | .relExpr op a b => do
    -- IBM: in a relation condition with an arithmetic expression, `dmax` is the most decimal
    -- places of any operand of either comparand, divisors and exponents excluded
    let dmax := (dScales ctx a ++ dScales ctx b).foldl max 0
    let c := { ctx with dmaxIn := some 0 }
    pure (.numCmp (← cmpOp op) (← expr c dmax false a) (← expr c dmax false b))
  | .cls t r => do
    let test ← match t.toUpper with
      | "NUMERIC" => pure ClassTest.numeric
      | "ALPHABETIC" => pure .alphabetic
      | "ALPHABETIC-LOWER" => pure .alphabeticLower
      | "ALPHABETIC-UPPER" => pure .alphabeticUpper
      | n => throw s!"unknown class {n}"
    pure (.cls test (← ref ctx r))
  | .sign t e => do
    -- the expression with the `dmax` of its own operands (no relational operator, IBM)
    let e' ← expr { ctx with dmaxIn := some 0 } ((dScales ctx e).foldl max 0) false e
    match t.toUpper with
    | "POSITIVE" => pure (.numCmp .gt e' (.lit 0 0))
    | "NEGATIVE" => pure (.numCmp .lt e' (.lit 0 0))
    | "ZERO" => pure (.numCmp .eq e' (.lit 0 0))
    | n => throw s!"unknown sign condition {n}"
  | .cond88 id subs => do
    let some (parent, vals) := ctx.conds.lookup id | throw s!"unknown condition name {id}"
    let pr : Surface.Operand := .ref { item := parent, subs }
    -- `pr op v`: an `ALL literal` value is compared as the relation with that figurative constant
    -- is (nonnumeric, the literal repeated to the size of the conditional variable, IBM)
    let rel (op : String) (v : Value) (o : Surface.Operand) : Except String Cobol.Cond :=
      match v with
      | .fig (.all bs) => do
        let c ← cmpOp op
        let a ← operand ctx pr
        match ctx.seq with
        | some s => pure (.alnumCmpSeq c a (.fig (.all bs)) s.pos)
        | none => pure (.alnumCmp c a (.fig (.all bs)))
      | _ => cond ctx (.rel op pr o)
    let arms ← vals.mapM (fun v => do
      let lo ← valueOperand ctx v.lo
      match v.hi with
      | none => rel "=" v.lo lo
      | some h => do
        let hi ← valueOperand ctx h
        pure (Cobol.Cond.and (← rel ">=" v.lo lo) (← rel "<=" h hi)))
    match arms with
    | [] => pure (.const false)
    | a :: rest => pure (rest.foldl .or a)
  | .not c => do pure (.not (← cond ctx c))
  | .and a b => do pure (.and (← cond ctx a) (← cond ctx b))
  | .or a b => do pure (.or (← cond ctx a) (← cond ctx b))
  | .odoCheck s => do
    -- the object as the subscript of a dimension of `integer-2 - integer-1 + 1` occurrences and
    -- stride 0 (`object + 1 - integer-1`): in range exactly when the object is, and then the
    -- reference is the object itself, equal to itself
    let some o := ctx.odo.find? (·.subject == s) | throw s!"unknown OCCURS DEPENDING ON table {s}"
    let (_, _, mx) ← odoTable ctx o
    let op ← item ctx o.obj
    let chk : DataRef := { item := o.obj, desc := op.desc,
                           subs := [{ e := .ref op.desc (1 - (o.min : Int)), stride := 0,
                                      max := mx - o.min + 1 }] }
    pure (.numCmp .eq (.ref chk) (.ref chk))
  | .relOwn op a b => do
    -- an `EVALUATE` subject and object: each "evaluated without regard to the attributes of its
    -- comparand" (IBM), with the `dmax` of its own operands
    let c := { ctx with dmaxIn := some 0 }
    pure (.numCmp (← cmpOp op) (← expr c ((dScales ctx a).foldl max 0) false a)
      (← expr c ((dScales ctx b).foldl max 0) false b))

mutual
partial def stmts (ctx : Ctx) (ss : List Surface.Stmt) : RM (List Cobol.Stmt) := do
  let r ← ss.mapM (stmt ctx)
  pure r.flatten

partial def stmt (ctx : Ctx) : Surface.Stmt → RM (List Cobol.Stmt)
  | .move src dsts => liftE do pure [.move (← operand ctx src) (← dsts.mapM (ref ctx))]
  | .compute rcv e onSize notOnSize => do
    -- IBM's dmax: the receivers' places (a numeric-edited receiver's too, `rcvScale`) and the operands'
    let dmax := (rcv.map (fun r => rcvScale ctx r.ref.item) ++ dScales ctx e).foldl max 0
    -- function arguments keep the dmax the resolver has always given them: the numeric receivers'
    -- places and the operands' (`dScalesIn`)
    let dmaxIn := (rcv.map (fun r => refScale ctx r.ref.item) ++ dScalesIn ctx e).foldl max 0
    let rounded := rcv.any (·.rounded.isSome)
    let e' ← liftE (expr { ctx with dmaxIn := some dmaxIn } dmax rounded e)
    -- one division as the whole expression, no ROUNDED receiver, every receiver a numeric item with
    -- at most both scales' places: the quotient keeps the scale max(d1, dmax) of earlier versions,
    -- which stores the same values as IBM's (truncation toward zero: trunc_r (trunc_s q) = trunc_r q
    -- for r ≤ s)
    let e' := match e, e' with
      | .div _ _ none, .div a' b' sc m =>
        let old := max b'.scale dmax
        if !rounded && rcv.all (fun r => numRcvWithin ctx r.ref old sc) then .div a' b' old m else e'
      | _, _ => e'
    let rs ← liftE (rcv.mapM (receiver ctx))
    pure [.arith (.giving e') rs onSize.isSome (← stmts ctx (onSize.getD [])) (← stmts ctx notOnSize)]
  | .add ops rcv giving onSize notOnSize => do
    let es ← liftE (ops.mapM (expr ctx 0 false))
    let sum ← match es with
      | [] => liftE (throw "ADD without operands")
      | e :: rest => pure (rest.foldl .add e)
    let rs ← liftE (rcv.mapM (receiver ctx))
    let op := if giving then ArithOp.giving sum else ArithOp.addTo sum
    pure [.arith op rs onSize.isSome (← stmts ctx (onSize.getD [])) (← stmts ctx notOnSize)]
  | .subtract ops rcv giving onSize notOnSize => do
    let es ← liftE (ops.mapM (expr ctx 0 false))
    let sum ← match es with
      | [] => liftE (throw "SUBTRACT without operands")
      | e :: rest => pure (rest.foldl .add e)
    let rs ← liftE (rcv.mapM (receiver ctx))
    let op ← match giving with
      | some m => do pure (ArithOp.giving (.sub (← liftE (expr ctx 0 false m)) sum))
      | none => pure (ArithOp.subFrom sum)
    pure [.arith op rs onSize.isSome (← stmts ctx (onSize.getD [])) (← stmts ctx notOnSize)]
  | .multiply a rcv giving onSize notOnSize => do
    let a' ← liftE (expr ctx 0 false a)
    let rs ← liftE (rcv.mapM (receiver ctx))
    let op ← match giving with
      | some b => do pure (ArithOp.giving (.mul a' (← liftE (expr ctx 0 false b))))
      | none => pure (ArithOp.mulBy a')
    pure [.arith op rs onSize.isSome (← stmts ctx (onSize.getD [])) (← stmts ctx notOnSize)]
  | .divide dividend divisor rcv giving rem onSize notOnSize => do
    let a ← liftE (expr ctx 0 false dividend)
    let b ← liftE (expr ctx 0 false divisor)
    let rs ← liftE (rcv.mapM (receiver ctx))
    let hs ← stmts ctx (onSize.getD [])
    let ns ← stmts ctx notOnSize
    match rem, rs with
    | some r, [q] => do
      let rr ← liftE (ref ctx r)
      pure [.divRem a b q { ref := rr } onSize.isSome hs ns]
    | some _, _ => liftE (throw "DIVIDE ... REMAINDER needs exactly one quotient")
    | none, _ =>
      pure [.arith (if giving then .divGiving a b else .divInto b) rs onSize.isSome hs ns]
  | .ite c t e => do
    pure [.ite (← liftE (cond ctx c)) (← stmts ctx t) (← stmts ctx e)]
  | .evaluate arms other => do
    let o ← stmts ctx other
    let rec build : List (Surface.Cond × List Surface.Stmt) → RM (List Cobol.Stmt)
      | [] => pure o
      | (c, body) :: rest => do
        pure [.ite (← liftE (cond ctx c)) (← stmts ctx body) (← build rest)]
    build arms
  | .perform first last loop => do
    let (f, l) ← liftE (range ctx first last)
    let id ← nextId
    match loop with
    | .once => pure [.perform id f l]
    | .times n => do pure [.performTimes id (← liftE (expr ctx 0 false n)) f l]
    | .until ta c => do pure [.performUntil id ta (← liftE (cond ctx c)) f l]
    | .varying ta var fromE byE c => do
      let (ini, step) ← liftE (varyingParts ctx var fromE byE)
      pure [.performVarying id ta ini (← liftE (cond ctx c)) step f l]
    | .varyingIdx ta i fromE byE c => do
      let (ini, step) ← liftE (varyingIdxParts ctx i fromE byE)
      pure [.performVarying id ta ini (← liftE (cond ctx c)) step f l]
  | .performInline body loop => do
    let b ← stmts ctx body
    match loop with
    | .once => pure [.block b]
    | .times n => do pure [.inlineTimes (← liftE (expr ctx 0 false n)) b]
    | .until ta c => do pure [.inlineUntil ta (← liftE (cond ctx c)) b]
    | .varying ta var fromE byE c => do
      let (ini, step) ← liftE (varyingParts ctx var fromE byE)
      pure [.inlineVarying ta ini (← liftE (cond ctx c)) step b]
    | .varyingIdx ta i fromE byE c => do
      let (ini, step) ← liftE (varyingIdxParts ctx i fromE byE)
      pure [.inlineVarying ta ini (← liftE (cond ctx c)) step b]
  | .goTo t => do pure [.goTo (← liftE (target ctx t))]
  | .goToDep ts e => do
    pure [.goToDep (← liftE (expr ctx 0 false e)) (← liftE (ts.mapM (target ctx)))]
  | .exitPerform => pure [.exitPerform]
  | .exitCycle => pure [.exitCycle]
  | .exitPara => pure [.exitPara]
  | .exitSection => pure [.exitSection]
  | .nextSentence => pure [.nextSentence]
  | .cont => pure [.cont]
  | .stopRun => pure [.stop .run]
  | .goback => pure [.stop .goback]
  | .exitProgram => pure [.stop .exitProgram]
  | .setIdx i e => do pure [.setIdx i (← liftE (expr ctx 0 false e))]
  | .setIdxBy i e down => do pure [.setIdxBy i (← liftE (expr ctx 0 false e)) down]
  | .setTrue id subs => liftE do
    let some (parent, vals) := ctx.conds.lookup id | throw s!"unknown condition name {id}"
    let some v := vals.head? | throw "condition name without values"
    let src ← valueSrc ctx v.lo
    pure [.move src [← ref ctx { item := parent, subs }]]
  | .display ops => liftE do pure [.display (← ops.mapM (operand ctx))]
  | .initialize dsts => liftE do
    let mut out : List Cobol.Stmt := []
    for d in dsts do
      if d.refStart.isSome then
        out := out ++ (← initRefMod ctx d)
        continue
      let some root := findItem d.item ctx.data | throw s!"unknown item {d.item}"
      let rootP ← item ctx d.item
      for leaf in initTargets root do
        let lp ← item ctx leaf.id
        -- occurrences of tables inside the root: literal subscripts
        let inner := lp.dims.drop rootP.dims.length
        for o in litOccs inner do
          let r ← ref ctx { item := leaf.id, subs := d.subs ++ o }
          let src : Cobol.Operand := match lp.desc.kind with
            | .num _ | .numEdited _ _ => .fig .zero
            | _ => .fig .space
          out := out ++ [.move src [r]]
    pure out
  | .call prog args => liftE do pure [.call prog (← args.mapM (ref ctx))]
  | .read file r into atEnd notAtEnd => do
    let rr ← liftE (ref ctx r)
    let ii ← liftE (into.mapM (ref ctx))
    pure [.read file rr ii (← stmts ctx atEnd) (← stmts ctx notAtEnd)]
  | .write file r => liftE do pure [.write file (← ref ctx r)]
  | .unsupported w => pure [.unsupported w]
  | .fopen file mode => liftE do pure [.fopen file (← openMode mode)]
  | .fclose file => pure [.fclose file]
  | .fread file key into trap exc noExc => do
    let some fd := ctx.files.find? (·.id == file) | liftE (throw s!"READ of undeclared file {file}")
    let k ← liftE (key.mapM (keyIndex fd))
    let ii ← liftE (into.mapM (ref ctx))
    pure [.fread file k ii trap (← stmts ctx exc) (← stmts ctx noExc)]
  | .fwrite file r trap exc noExc => do
    let rr ← liftE (ref ctx r)
    pure [.fwrite file rr trap (← stmts ctx exc) (← stmts ctx noExc)]
  | .frewrite file r trap exc noExc => do
    let rr ← liftE (ref ctx r)
    pure [.frewrite file rr trap (← stmts ctx exc) (← stmts ctx noExc)]
  | .fdelete file trap exc noExc => do
    pure [.fdelete file trap (← stmts ctx exc) (← stmts ctx noExc)]
  | .fstart file op key trap exc noExc => do
    let some fd := ctx.files.find? (·.id == file)
      | liftE (throw s!"START of an undeclared file {file}")
    let d ← liftE (fileDecl ctx fd)
    let some rk := d.key | liftE (throw s!"START of file {file}, which is not indexed")
    let op' ← liftE (match op with
      | "=" => pure CmpOp.eq
      | ">" => pure .gt
      | ">=" => pure .ge
      | o => throw s!"START KEY {o}")
    -- the record key or an alternate key, or a leading part of one (IBM: a data item whose
    -- leftmost character position is the key's, of at most the key's size)
    let k ← match key with
      | none => pure (some rk)
      | some i => liftE do
        let it ← item ctx i
        pure (((rk :: d.alt).find? fun kd =>
            it.desc.off == d.area.off + kd.off && it.desc.len ≤ kd.len).map fun kd =>
          { kd with len := it.desc.len })
    match k with
    | none => pure [.unsupported "START KEY item that is not a key of the file or a leading part of one"]
    | some k => pure [.fstart file op' k trap (← stmts ctx exc) (← stmts ctx noExc)]
  | .clock dst start len => liftE do pure [.clock (← ref ctx dst) start len]
  | .abend code => liftE do pure [.abend (← expr ctx 0 false code)]
  | .inspect target tally repl => liftE do
    let phrase (p : Surface.InspPhrase) : Except String InspPhrase := do
      let kind ← match p.kind with
        | "chars" => pure InspKind.chars
        | "all" => pure .all
        | "leading" => pure .leading
        | "first" => pure .first
        | k => throw s!"unknown INSPECT phrase {k}"
      pure { kind, pat := ← p.pat.mapM (operand ctx), rep := ← p.rep.mapM (operand ctx),
             before := ← p.before.mapM (operand ctx), after := ← p.after.mapM (operand ctx),
             counter := ← p.counter.mapM (ref ctx) }
    pure [.inspect (← ref ctx target) (← tally.mapM phrase) (← repl.mapM phrase)]
  | .search idx occurs varIdx varRef atEnd conds bodies => do
    let cs ← liftE (conds.mapM (cond ctx))
    let bs ← bodies.mapM fun b => do pure (Cobol.Stmt.block (← stmts ctx b))
    -- the index, and the `VARYING` index or item, go up by one per step
    let vbump ← match varIdx, varRef with
      | some j, _ => pure [Cobol.Stmt.setIdxBy j (.lit 1) false]
      | none, some r => liftE do
        pure [Cobol.Stmt.arith (.addTo (.lit 1)) [{ ref := ← ref ctx r }] false [] []]
      | none, none => pure []
    pure [.search (.numCmp .gt (.idx idx) (.lit occurs)) cs bs
      (Cobol.Stmt.setIdxBy idx (.lit 1) false :: vbump) (← stmts ctx atEnd)]
  | .searchAll idx occurs keys atEnd c body => do
    let ks ← liftE (keys.mapM fun k => do pure (k.asc, ← ref ctx k.key))
    -- the KEY-order check of `Sem.searchAllPick` compares alphanumeric keys in native order
    if ctx.seq.isSome && ks.any (fun (_, r) => match r.desc.kind with | .num _ => false | _ => true) then
      return [.unsupported "SEARCH ALL with an alphanumeric KEY in a program collating sequence"]
    pure [.searchAll idx occurs ks (← liftE (cond ctx c)) (← stmts ctx body) (← stmts ctx atEnd)]
  | .unstring src delims into ptr tally onOvf notOnOvf => do
    let ds ← liftE (delims.mapM fun d => do pure (d.all, ← operand ctx d.op))
    let rs ← liftE (into.mapM fun r => do
      pure ({ rcv := ← ref ctx r.rcv, delim := ← r.delim.mapM (ref ctx),
              count := ← r.count.mapM (ref ctx) } : UnstrInto))
    pure [.unstring (← liftE (ref ctx src)) ds rs (← liftE (ptr.mapM (ref ctx)))
      (← liftE (tally.mapM (ref ctx))) onOvf.isSome (← stmts ctx (onOvf.getD []))
      (← stmts ctx notOnOvf)]
  | .stringInto groups into ptr onOvf notOnOvf => do
    let srcs ← liftE ((groups.flatMap fun g => g.srcs.map (·, g.delim)).mapM fun (s, d) => do
      pure (← operand ctx s, ← d.mapM (operand ctx)))
    pure [.stringInto srcs (← liftE (ref ctx into)) (← liftE (ptr.mapM (ref ctx))) onOvf.isSome
      (← stmts ctx (onOvf.getD [])) (← stmts ctx notOnOvf)]
  | .setAddress dst ptr => liftE do pure [.setAddress (← ref ctx dst) (← ref ctx ptr)]
  | .callLocal para binds => liftE do
    pure [.callLocal (← target ctx para) (← binds.mapM fun (a, p) => do pure (← ref ctx a, ← ref ctx p))]
  | .callDyn prog _ _ _ _ =>
    -- (messages short enough for one line of `repr`)
    pure [.unsupported (match prog with
      | some p => s!"CALL {p} ON EXCEPTION: not in the run unit, availability not modelled"
      | none => "CALL identifier: no program of the run unit has that name")]
  | .cancel prog _ =>
    pure [.unsupported (match prog with
      | some p => s!"CANCEL {p}: not linked into the program that cancels it"
      | none => "CANCEL identifier: no linked program has that name")]
  | .convert target src dst before after => liftE do
    pure [.convert (← ref ctx target) (← operand ctx src) (← operand ctx dst)
      (← before.mapM (operand ctx)) (← after.mapM (operand ctx))]
  | .accept dst => liftE do pure [.accept (← ref ctx dst)]
  | .fcloseOpt file opt => liftE do pure [.fcloseOpt file (← closeOpt opt)]
  | .fopenRev file => pure [.fopenRev file]

/-- `VARYING v FROM f BY b`: initialization and augmentation statements. -/
partial def varyingParts (ctx : Ctx) (var : Ref) (fromE byE : Surface.Expr) :
    Except String (List Cobol.Stmt × List Cobol.Stmt) := do
  let v ← ref ctx var
  let f ← expr ctx 0 false fromE
  let b ← expr ctx 0 false byE
  pure ([.arith (.giving f) [{ ref := v }] false [] []],
        [.arith (.addTo b) [{ ref := v }] false [] []])

/-- `VARYING i FROM f BY b` of an index name: `SET i TO f` and `SET i UP BY b`. -/
partial def varyingIdxParts (ctx : Ctx) (i : Nat) (fromE byE : Surface.Expr) :
    Except String (List Cobol.Stmt × List Cobol.Stmt) := do
  pure ([.setIdx i (← expr ctx 0 false fromE)], [.setIdxBy i (← expr ctx 0 false byE) false])
end

/-- Resolve a surface program. -/
def program (sp : Surface.Program) : Except String Cobol.Program := do
  let L := layout sp.config sp.data
  let paraIdx := sp.paras.zipIdx.map (fun (p, i) => (p.name, i))
  let sectNames := (sp.paras.filterMap (·.sect)).eraseDups
  let sections := sectNames.filterMap (fun s =>
    let idxs := sp.paras.zipIdx.filterMap (fun (p, i) => if p.sect == some s then some i else none)
    match idxs.head?, idxs.getLast? with
    | some f, some l => some (s, f, l)
    | _, _ => none)
  let seq ← sp.collating.mapM (collation sp.config)
  let ctx : Ctx := { cfg := sp.config, dialect := sp.dialect, L, data := sp.data,
                     conds := collectConds sp.data, paraIdx, sections, files := sp.files, seq,
                     odo := sp.odo.getD [] }
  for o in ctx.odo do odoDeclOk ctx o
  -- `State.files` holds the system input device under the id 0 (`Stmt.accept`): no file may have it
  if sp.files.any (·.id == 0) then throw "file id 0 is reserved for the system input device"
  let files ← sp.files.mapM (fileDecl ctx)
  let (paras, nid) ← (sp.paras.mapM (fun (p : Surface.Paragraph) => do
      let body ← p.sentences.mapM (stmts ctx)
      pure ({ name := p.name, body } : Cobol.Paragraph))).run 0
  -- files whose key of reference can be an alternate key, or with an alternate key that allows
  -- duplicates (`FileDecl.keyRef`)
  let files := files.map fun d =>
    if d.alt.any (·.dups) || paras.any (·.body.any (anyStmt (altKeyUse d))) then
      { d with keyRef := true } else d
  -- files that some `CLOSE … WITH LOCK` names (`FileDecl.lockable`)
  let files := files.map fun d =>
    if paras.any (·.body.any (anyStmt (lockUse d))) then { d with lockable := true } else d
  let secEnd := sp.paras.zipIdx.map (fun ((p : Surface.Paragraph), i) =>
    match p.sect with
    | some s => match sections.lookup s with | some (_, l) => l | none => i
    | none => i)
  -- a declarative runs as an out-of-line PERFORM of its section, with a statement number of
  -- its own (after those of the PERFORM statements)
  let useProcs ← sp.use.zipIdx.mapM (fun ((u : Surface.UseDecl), i) => do
    let (f, l) ← match sections.lookup u.sect with
      | some fl => pure fl
      | none => throw s!"USE: unknown section {u.sect}"
    let mode ← match u.mode with
      | some m => some <$> openMode m
      | none => pure none
    pure ({ files := u.files, mode, id := nid + i, first := f, exit := .sect l } : UseProc))
  let inits := match seq with
    | none => L.inits sp.config
    | some s => (layout sp.config (sp.data.map (seqValues s))).inits sp.config
  pure { name := sp.name, cfg := sp.config, paras := paras.toArray, secEnd := secEnd.toArray,
         memSize := L.size, inits := inits, isMain := sp.isMain, files, useProcs }

end Cobol.Resolve.Old

namespace Ar2Resolve

/-- The surface IRs the theorem files load. -/
def thmIRs : List String :=
  ["examples/acctint/acctint.gnucobol.ir.json", "examples/acctint/acctint.ir.json",
   "examples/binary/bincnt.gnucobol.ir.json", "examples/binary/bincnt.ir.json",
   "examples/carddemo/cbact01c.ir.json", "examples/carddemo/cbact02c.ir.json",
   "examples/carddemo/cbact03c.ir.json", "examples/carddemo/cbact04c.ir.json",
   "examples/carddemo/cbcus01c.ir.json", "examples/carddemo/cbstm03ab.ir.json",
   "examples/carddemo/cbtrn01c.ir.json", "examples/carddemo/cbtrn02c.ir.json",
   "examples/carddemo/cbtrn03c.ir.json", "examples/recsum/recsum.gnucobol.ir.json",
   "examples/recsum/recsum.ir.json"]

/-- The statements of a program, with their paragraph names, in order (nested statement lists stay
inside their statement). -/
def stmtsOf (P : Program) : List (String × Stmt) :=
  P.paras.toList.flatMap (fun p => p.body.flatten.map (p.name, ·))

/-- Occurrences of `pat` in `s`. -/
def count (s pat : String) : Nat := (s.splitOn pat).length - 1

/-- A line per statement whose old and new resolutions differ (paragraph, both `repr` texts cut
to 300 characters), and the other fields of the program that differ. -/
def diffLines (n o : Program) : List String :=
  let ns := stmtsOf n
  let os := stmtsOf o
  let cut (s : String) : String := if s.length ≤ 300 then s else String.ofList (s.toList.take 300) ++ "..."
  let st := (ns.zip os).filterMap (fun ((pn, a), (_, b)) =>
    if toExpr a == toExpr b then none
    else some s!"  in {pn}:\n    new {cut (reprStr a)}\n    old {cut (reprStr b)}")
  let len := if ns.length == os.length then [] else [s!"  statement counts {ns.length} / {os.length}"]
  let rest := (if toExpr n.inits == toExpr o.inits then [] else ["  inits differ"]) ++
    (if toExpr n.files == toExpr o.files then [] else ["  files differ"]) ++
    (if toExpr n.useProcs == toExpr o.useProcs then [] else ["  useProcs differ"]) ++
    (if n.memSize == o.memSize && n.secEnd == o.secEnd && n.isMain == o.isMain && n.name == o.name
      then [] else ["  name / memSize / secEnd / isMain differ"])
  len ++ st ++ rest

/-- Resolve one surface-IR file with both resolvers: (`true` iff the results are equal as terms and
as `repr` text, or both refuse it with the same message; the report lines). -/
def cmpFile (path : String) : IO (Bool × List String) := do
  let txt ← IO.FS.readFile path
  let j ← IO.ofExcept (Json.parse txt)
  let sp ← IO.ofExcept (surfaceOfJson j)
  match Resolve.program sp, Resolve.Old.program sp with
  | .ok n, .ok o =>
    let r := reprStr n
    let same := toExpr n == toExpr o && r == reprStr o
    let k := (stmtsOf n).length
    let op := count r "Cobol.Expr.ir30open"
    let nodes := s!"ir30 nodes {count r "Cobol.Expr.ir30" - op} ir30open nodes {op} pow0 nodes {count r "Cobol.Expr.pow0"}"
    if same then pure (true, [s!"{path}: same ({n.paras.size} paragraphs, {k} statements, {nodes})"])
    else pure (false, s!"{path}: DIFFERENT ({n.paras.size} paragraphs, {k} statements, {nodes})" :: diffLines n o)
  | .error a, .error b =>
    pure (a == b, [s!"{path}: both refuse it ({if a == b then "same message" else "DIFFERENT messages"})"])
  | .ok _, .error b => pure (false, [s!"{path}: DIFFERENT: only the old resolver refuses it: {b}"])
  | .error a, .ok _ => pure (false, [s!"{path}: DIFFERENT: only the new resolver refuses it: {a}"])

#eval show IO Unit from do
  let mut same := 0
  for p in thmIRs do
    let (ok, ls) ← cmpFile p
    for l in ls do IO.println l
    if ok then same := same + 1
  IO.println s!"theorem IRs: {same} of {thmIRs.length} same"
  match ← IO.getEnv "AR2_LIST" with
  | none => IO.println "AR2_LIST not set: no exposure run"
  | some lf =>
    let paths := ((← IO.FS.readFile lf).splitOn "\n").filter (· ≠ "")
    let mut s := 0
    let mut d := 0
    let mut r := 0
    for p in paths do
      match ← (cmpFile p).toBaseIO with
      | .ok (ok, ls) =>
        if ok then
          s := s + 1
        else
          d := d + 1
          for l in ls do IO.println l
      | .error e =>
        r := r + 1
        IO.println s!"{p}: unreadable: {e}"
    IO.println s!"exposure list {lf}: {paths.length} files, {s} same, {d} different, {r} unreadable"

end Ar2Resolve
