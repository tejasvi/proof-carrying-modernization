/-
`examples/Async/rename.ts`: an async function that awaits two calls of an external database
library (declared in `node_modules/fakedb/index.d.ts`; `Db` and `Doc` are external types):

    const doc = await getDoc(db, id);
    if (doc === undefined) return false;
    await setName(db, id, name);
    return true;

`RenameEx.lean` was produced by the translator of the `frontend` branch, which emits external
calls (`Expr.externAsync`, `Ty.ext`). Nothing is assumed about the library's code: the theorems
quantify over the oracle that answers the calls, and state answers by call number (`n` is the
number of the first call).
(a) If `getDoc` answers `undefined`, the promise is fulfilled with `false` after one external
call: `setName` is never called.
(b) If `getDoc` answers a document, the next call is `setName(db, id, name)` (an answer to any
other call would be unconstrained), and the promise ends as `setName`'s answer says:
fulfilled with `true`, or rejected with its error.
(c) For every oracle, the call and its microtask queue neither panic nor throw (a rejection by
the library is a rejected promise).
-/
import Async.RenameEx
import StrictTS.Proof.Extern
import StrictTS.Proof.Contract

open StrictTS JS RenameEx

/-- `getDoc(db: Db, id: string): Promise<Doc | undefined>` -/
abbrev getDoc : ExtFun := ⟨"fakedb:getDoc", [.ext "fakedb:Db", .str], .opt (.ext "fakedb:Doc")⟩
/-- `setName(db: Db, id: string, name: string): Promise<void>` -/
abbrev setName : ExtFun := ⟨"fakedb:setName", [.ext "fakedb:Db", .str, .str], .undef⟩

/-- (a) No document: the promise is fulfilled with `false` and only `getDoc` was called. -/
theorem rename_missing (I : Impl) (w : World TT) (n db : Nat) (id name : JSStr) (hj : w.jobs = [])
    (hn : w.extIdx = n)
    (hget : w.answer getDoc (.cons (.ext db) (.cons (.str id) .nil)) n = .ok (.val .none)) :
    ∃ p w₁ w₂ c,
      exec (callFun I program renameRef (.cons (.ext db) (.cons (.str id) (.cons (.str name) .nil)))) w =
        some (.ok (.promise p), w₁) ∧
      exec (drain I program) w₁ = some (.ok (), w₂) ∧
      w₂.heap.get? (.promise .bool, p) = some c ∧ c.state = .fulfilled (.bool false) ∧
      w₂.extIdx = n + 1 := by
  ts_drain [rename_call, renameDef, hj, hn, hget]

/-- (b) A document: `setName(db, id, name)` is the second call, and the promise is fulfilled
with `true` when it succeeds, rejected with its error when it fails. -/
theorem rename_found (I : Impl) (w : World TT) (n db d : Nat) (id name : JSStr) (hj : w.jobs = [])
    (hn : w.extIdx = n)
    (hget : w.answer getDoc (.cons (.ext db) (.cons (.str id) .nil)) n = .ok (.val (.some (.ext d))))
    (o : Except ErrVal (EVal TT .undef))
    (hset : w.answer setName (.cons (.ext db) (.cons (.str id) (.cons (.str name) .nil))) (n + 1) = o) :
    ∃ p w₁ w₂ c,
      exec (callFun I program renameRef (.cons (.ext db) (.cons (.str id) (.cons (.str name) .nil)))) w =
        some (.ok (.promise p), w₁) ∧
      exec (drain I program) w₁ = some (.ok (), w₂) ∧
      w₂.heap.get? (.promise .bool, p) = some c ∧
      c.state = (match o with | .ok _ => .fulfilled (.bool true) | .error e => .rejected e) ∧
      w₂.extIdx = n + 2 := by
  rcases o with e | ⟨⟨⟩⟩
  · ts_drain [rename_call, renameDef, hj, hn, hget, hset]
  · ts_drain [rename_call, renameDef, hj, hn, hget, hset]

/-- A failing `getDoc` rejects the promise with its error. -/
theorem rename_getDoc_fails (I : Impl) (w : World TT) (n db : Nat) (id name : JSStr) (e : ErrVal)
    (hj : w.jobs = []) (hn : w.extIdx = n)
    (hget : w.answer getDoc (.cons (.ext db) (.cons (.str id) .nil)) n = .error e) :
    ∃ p w₁ w₂ c,
      exec (callFun I program renameRef (.cons (.ext db) (.cons (.str id) (.cons (.str name) .nil)))) w =
        some (.ok (.promise p), w₁) ∧
      exec (drain I program) w₁ = some (.ok (), w₂) ∧
      w₂.heap.get? (.promise .bool, p) = some c ∧ c.state = .rejected e ∧ w₂.extIdx = n + 1 := by
  ts_drain [rename_call, renameDef, hj, hn, hget]

/-- (c) For every oracle (every answer and every failure of the library), running `rename` and
its microtask queue neither panics nor throws. -/
theorem rename_noFault (I : Impl) (w : World TT) (db : Nat) (id name : JSStr) (hj : w.jobs = []) :
    NoFault (do
      let r ← callFun I program renameRef (.cons (.ext db) (.cons (.str id) (.cons (.str name) .nil)))
      drain I program
      pure r) w := by
  apply Returns.noFault
  rcases h₁ : w.answer getDoc (.cons (.ext db) (.cons (.str id) .nil)) w.extIdx with e | ev
  · ts_drain [Returns, rename_call, renameDef, hj, h₁]
  · cases ev with
    | val v =>
      cases v with
      | none => ts_drain [Returns, rename_call, renameDef, hj, h₁]
      | some d =>
        rcases h₂ : w.answer setName (.cons (.ext db) (.cons (.str id) (.cons (.str name) .nil)))
            (w.extIdx + 1) with e | ev
        · ts_drain [Returns, rename_call, renameDef, hj, h₁, h₂]
        · cases ev with
          | val v =>
            cases v
            ts_drain [Returns, rename_call, renameDef, hj, h₁, h₂]
