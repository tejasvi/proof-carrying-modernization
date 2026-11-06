/-
StrictTS proof layer: calls of external functions (libraries, the host).

An external call `name(vs)` is answered by the world's oracle `w.ext`, indexed by the number of
external calls made so far, `w.extIdx` (`Expr.extern`: the answer is the call's value or the
exception it throws; `Expr.externAsync`: the answer settles a fresh promise at once). Proofs
make assumptions about the answers, never about the library's code.

* **Exec lemmas** `exec_extern`, `exec_externAsync`: what each form does to the world.
* **Stating the answers to a sequence of calls.** Declare each external function's signature
  as an `ExtFun` (an `abbrev`, e.g. `abbrev getDoc : ExtFun := ⟨"fakedb:getDoc", [.ext
  "fakedb:Db", .str], .opt (.ext "fakedb:Doc")⟩`), fix the number of the first call
  (`hn : w.extIdx = n`) and state the answers by absolute call number:
  `w.answer getDoc (.cons db (.cons id .nil)) n = .ok (.val v)`,
  `w.answer setName (…) (n + 1) = .ok .undef`, … An answer that is not assumed is arbitrary,
  so a proof that uses only these hypotheses shows that the calls are made in this order with
  exactly these arguments.
* **Running async code.** `ts_drain [f_call, fDef, hn, h₀, h₁, …]` executes an async function
  that awaits external calls, and its microtask queue, with these hypotheses; a case split on
  an answer (`rcases h : w.answer f vs n with e | v`) covers every oracle.
* **Libraries that do not throw.** `World.ExtReturns w f`: every answer of `f` is a value. For
  synchronous code `ts_auto` splits on each answer that no hypothesis fixes (an error, or a value
  of each form); with this hypothesis the error case is skipped, so that `JS.Returns` can hold for
  code calling `f` (a regex test, a string method, `JSON.parse` on its argument).
* **What the standard fixes about an answer.** `World.ExtSpec w f pre post`: every value that `f`
  answers to arguments satisfying `pre` satisfies `post` (errors stay possible), e.g.
  `World.MatchAllFresh` (`matchAll` gives a fresh array) and `World.MatchElementZero` (element 0
  of a match result is a string), ECMA-262's guarantees for the regular-expression methods;
  `ts_auto` keeps only the values of that form.
* **Answers only allocate.** `exec_materialize_ok`: materializing an answer changes the world only
  in its heap and next address, so hypotheses about the oracle still apply afterwards.
-/
import StrictTS.Proof.AsyncRace

namespace StrictTS
open JS

variable {TT : TypeTable}

/-- The signature of an external function: its name (as the translator emits it, e.g.
`"package:name"`), parameter types and result type (for an async function, the type its
promise is fulfilled with). -/
structure ExtFun where
  name : String
  args : List Ty
  ret : Ty

/-- The answer of the oracle of `w` to the external call number `n`, if that call is
`f(vs)`: a value (`.ok (.val v)`), the elements of a fresh array (`.ok (.arr es)`, at array
types), or an error. -/
abbrev World.answer (w : World TT) (f : ExtFun) (vs : Vals TT f.args) (n : Nat) :
    Except ErrVal (EVal TT f.ret) :=
  w.ext f.name f.args f.ret vs n

/-- The external function `f` answers every call with a value, never with an error (e.g. a
regular-expression test or a string method of the host, which do not throw on the arguments the
program passes): an optional hypothesis for statements about code that calls `f`, such as
`JS.Returns`. The values themselves stay arbitrary; `ts_auto` uses the hypothesis to skip the
error case of each answer. -/
def World.ExtReturns (w : World TT) (f : ExtFun) : Prop :=
  ∀ (vs : Vals TT f.args) (n : Nat), ∃ ev, w.answer f vs n = .ok ev

/-- The external function `f` answers every call whose arguments satisfy `pre` with an error or
with a value satisfying `post`: what the language standard fixes about the host's answers (e.g.
ECMA-262 for the regular-expression methods). An optional hypothesis, like `World.ExtReturns`;
`ts_auto` uses it to keep only the answers of that form. -/
def World.ExtSpec (w : World TT) (f : ExtFun) (pre : Vals TT f.args → Prop) (post : EVal TT f.ret → Prop) :
    Prop :=
  ∀ (vs : Vals TT f.args) (n : Nat), pre vs → ∀ ev, w.answer f vs n = .ok ev → post ev

/-- `str.matchAll(re)` with a global regular expression (ECMA-262 §22.1.3.14 and §22.2.9.2): the
host answers with a fresh array of match results (or throws). -/
abbrev World.MatchAllFresh (w : World TT) : Prop :=
  w.ExtSpec ⟨"String.matchAll", [.str, .str, .str], .arr (.ext "RegExpExecArray")⟩ (fun _ => True)
    (fun ev => ∃ es, ev = .arr es)

/-- Element 0 of a match result is the matched substring (ECMA-262 §22.2.7.2,
RegExpBuiltinExec): the host's `m[0]` is a string. -/
abbrev World.MatchElementZero (w : World TT) : Prop :=
  w.ExtSpec ⟨"RegExpExecArray.get:[]", [.ext "RegExpExecArray", .num], .opt .str⟩
    (fun vs => vs.a1 = .num (F64.ofNat 0)) (fun ev => ∃ s, ev = .val (.some (.str s)))

/-- What ECMA-262 fixes about the host's regular-expression answers that the translated code
relies on: `matchAll` gives a fresh array, and element 0 of a match result is a string. -/
def World.RegExpSpec (w : World TT) : Prop := w.MatchAllFresh ∧ w.MatchElementZero

/-- The elements of a fresh array of plain values. -/
def EVals.ofList {t : Ty} : List (Val TT t) → EVals TT t
  | [] => .nil
  | v :: vs => .cons (.val v) (EVals.ofList vs)

@[simp, ts_sym] theorem exec_materializeList_ofList {t : Ty} (vs : List (Val TT t)) (w : World TT) :
    exec (JS.materializeList (EVals.ofList vs)) w = some (.ok vs, w) := by
  induction vs with
  | nil => simp [EVals.ofList, JS.materializeList]
  | cons v vs ih => simp [EVals.ofList, JS.materializeList, ih]

/-- An answer that is a fresh array of plain values is allocated at the next address. -/
@[simp, ts_sym] theorem exec_materialize_ofList {t : Ty} (vs : List (Val TT t)) (w : World TT) :
    exec (JS.materialize (.arr (EVals.ofList vs))) w =
      some (.ok (.arr w.next),
        { w with heap := w.heap.insert (.arr t, w.next) vs.toArray, next := w.next + 1 }) := by
  simp [JS.materialize, exec_materializeList_ofList]

mutual
/-- Materializing an answer of the oracle always succeeds, and it only allocates fresh cells (the
world changes only in its heap and next address; the oracles stay): the form `ts_auto` uses when
an answer's fresh array is symbolic. -/
theorem exec_materialize_ok : ∀ {t : Ty} (ev : EVal TT t) (w : World TT),
    ∃ v h n, exec (materialize ev) w = some (.ok v, { w with heap := h, next := n })
  | _, .val v, w => ⟨v, w.heap, w.next, rfl⟩
  | _, .arr es, w => by
    obtain ⟨vs, h1, n1, e1⟩ := exec_materializeList_ok es w
    simp only [materialize, allocArr, exec_bind, e1, exec_alloc, bind_pure_comp, exec_map]
    exact ⟨_, _, _, rfl⟩
  | _, .dyn t e, w => by
    obtain ⟨v, h1, n1, e1⟩ := exec_materialize_ok e w
    simp only [materialize, exec_bind, e1, exec_pure]
    exact ⟨_, _, _, rfl⟩
  | _, .dict ks es, w => by
    obtain ⟨vs, h1, n1, e1⟩ := exec_materializeList_ok es w
    simp only [materialize, exec_bind, e1, exec_alloc, exec_pure]
    exact ⟨_, _, _, rfl⟩
/-- Materializing the elements of a fresh array always succeeds, and it only allocates. -/
theorem exec_materializeList_ok : ∀ {t : Ty} (es : EVals TT t) (w : World TT),
    ∃ vs h n, exec (materializeList es) w = some (.ok vs, { w with heap := h, next := n })
  | _, .nil, w => ⟨[], w.heap, w.next, rfl⟩
  | _, .cons e es, w => by
    obtain ⟨v, h1, n1, e1⟩ := exec_materialize_ok e w
    obtain ⟨vs, h2, n2, e2⟩ := exec_materializeList_ok es { w with heap := h1, next := n1 }
    simp only [materializeList, exec_bind, e1, e2, exec_pure]
    exact ⟨_, _, _, rfl⟩
end

/-- The promise cell of an asynchronous external call once the oracle's answer is in. -/
def extPromiseCell {t : Ty} (out : Except ErrVal (Val TT t)) : PromiseCell TT t :=
  { state := match out with | .ok v => .fulfilled v | .error e => .rejected e }

/-- **A synchronous external call** evaluates its arguments, then the oracle answers call
number `w.extIdx` (and the counter advances): a value is the call's value (its fresh arrays are
allocated first, `JS.materialize`), an error is thrown as a JavaScript exception. An answer
`.ok (.val v)` returns `v` and changes nothing else (`exec_materialize_val`). -/
theorem exec_extern (I : Impl) (P : Program TT) {Γ : Ctx} {args : List Ty} {t : Ty} (name : String)
    (as : Args TT Γ args) (env : Env TT Γ) (w : World TT) :
    exec (evalE I P (.extern (t := t) name as) env) w =
      match exec (evalArgs I P as env) w with
      | some (.ok vs, w₁) =>
        match w₁.ext name args t vs w₁.extIdx with
        | .ok ev => exec (JS.materialize ev) { w₁ with extIdx := w₁.extIdx + 1 }
        | .error e => some (.error (.thrown e), { w₁ with extIdx := w₁.extIdx + 1 })
      | some (.error e, w₁) => some (.error e, w₁)
      | none => none := by
  simp only [evalE, exec_bind, exec_extAnswer]
  rcases exec (evalArgs I P as env) w with _ | ⟨_ | vs, w₁⟩
  · rfl
  · rfl
  · dsimp only
    cases w₁.ext name args t vs w₁.extIdx <;> rfl

/-- **An asynchronous external call** evaluates its arguments, then the oracle answers call
number `w.extIdx` (the counter advances); the fresh arrays of a value are allocated, and a fresh
promise is settled with the answer at once. A rejection is recorded as unhandled until a
reaction is attached (Node's rule). An answer `.ok (.val v)` allocates only the promise. -/
theorem exec_externAsync (I : Impl) (P : Program TT) {Γ : Ctx} {args : List Ty} {t : Ty}
    (name : String) (as : Args TT Γ args) (env : Env TT Γ) (w : World TT) :
    exec (evalE I P (.externAsync (t := t) name as) env) w =
      match exec (evalArgs I P as env) w with
      | some (.ok vs, w₁) =>
        match w₁.ext name args t vs w₁.extIdx with
        | .ok ev =>
          match exec (JS.materialize ev) { w₁ with extIdx := w₁.extIdx + 1 } with
          | some (.ok v, w₂) => some (.ok (.promise w₂.next), { w₂ with
              heap := w₂.heap.insert (.promise t, w₂.next) (extPromiseCell (.ok v)),
              next := w₂.next + 1 })
          | some (.error e, w₂) => some (.error e, w₂)
          | none => none
        | .error e => some (.ok (.promise w₁.next), { w₁ with
            heap := w₁.heap.insert (.promise t, w₁.next) (extPromiseCell (.error e)),
            next := w₁.next + 1, extIdx := w₁.extIdx + 1,
            unhandled := w₁.unhandled ++ [(w₁.next, e)] })
      | some (.error e, w₁) => some (.error e, w₁)
      | none => none := by
  simp only [evalE, exec_bind, exec_extAnswer]
  rcases exec (evalArgs I P as env) w with _ | ⟨_ | vs, w₁⟩
  · rfl
  · rfl
  · dsimp only
    cases w₁.ext name args t vs w₁.extIdx with
    | error e => simp [ts_sym, extPromiseCell]
    | ok ev =>
      simp only [exec_bind, exec_pure]
      rcases exec (JS.materialize ev) { w₁ with extIdx := w₁.extIdx + 1 } with _ | ⟨_ | v, w₂⟩
      · rfl
      · rfl
      · simp [ts_sym, extPromiseCell]

end StrictTS
