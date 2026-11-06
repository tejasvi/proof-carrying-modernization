/-
  Jimple/Verify.lean

  Whole-program verification with contract tables.

  A `Contracts` table lists method references with their contracts. `Contracts.allVC`
  reduces `AllVC` (and hence, by `AllVC.valid`, the validity of every contract) to one
  `ContractVC` per table entry; `forall_targets_iff` and `forall_progClass_of_mem` turn the
  quantifiers over call targets and implementing classes into finite, computable checks,
  which `jcontracts` discharges with `jverify` on every implementation.
-/
import Jimple.Tactic

namespace Jimple

/-- Method references with their contracts. -/
abbrev Contracts := List (MethodSig × Spec)

def Contracts.env (T : Contracts) : SpecEnv := fun sig => T.lookup sig

attribute [jsimp] Contracts.env

theorem lookup_mem_dec {α β : Type} [DecidableEq α] :
    ∀ {l : List (α × β)} {a : α} {b : β}, l.lookup a = some b → (a, b) ∈ l
  | [], _, _, h => by simp [List.lookup] at h
  | (x, y) :: l, a, b, h => by
    simp only [List.lookup] at h
    split at h
    · next hx =>
      cases h
      have : a = x := by simpa using hx
      subst this; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (lookup_mem_dec h)

/-- The obligations of one contract: every method a call of `sig` can reach. -/
def ContractVC (P : Program) (Γ : SpecEnv) (d : Nat) (Ann : Annotations) (sig : MethodSig)
    (S : Spec) : Prop :=
  (∀ m, Targets P sig m → MethodVC P Γ d m S (Ann.inv m) (Ann.fuel m)) ∧
  (∀ c, P.isProgClass c = true → P.isSubclass c sig.cls = some true → P.staticDecl sig = false →
    match P.selectVirtual c sig.sub with
    | .jimple m => MethodVC P Γ d m S (Ann.inv m) (Ann.fuel m)
    | .native lc => NativeVC P Γ d sig c lc S
    | .none _ => P.concrete c = false)

theorem Contracts.allVC {P : Program} {T : Contracts} {d : Nat} {Ann : Annotations}
    (h : ∀ p ∈ T, ContractVC P T.env d Ann p.1 p.2) : AllVC P T.env d Ann := by
  intro sig S hΓ
  exact h (sig, S) (lookup_mem_dec hΓ)

/-- Validity of a contract table from its verification conditions. -/
theorem Contracts.valid {P : Program} {T : Contracts} {d : Nat} {Ann : Annotations}
    (h : ∀ p ∈ T, ContractVC P T.env d Ann p.1 p.2) : Valid P T.env :=
  (Contracts.allVC h).valid

/-- Call targets of a method reference: its static and special selection and its class's
    static initializer, when they have a body. -/
theorem forall_targets_iff (P : Program) (sig : MethodSig) (Φ : MethodRef → Prop) :
    (∀ m, Targets P sig m → Φ m) ↔
      (match P.selectStatic sig with | .jimple m => m.decl.body.isSome → Φ m | _ => True) ∧
      (match P.selectSpecial sig with | .jimple m => m.decl.body.isSome → Φ m | _ => True) ∧
      (match P.clinitOf sig.cls with
       | some decl => sig = clinitSig sig.cls → decl.body.isSome → Φ ⟨sig.cls, decl⟩
       | none => True) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · split
      · next m hm => exact fun hb => h m ⟨Or.inl hm, hb⟩
      · trivial
    · split
      · next m hm => exact fun hb => h m ⟨Or.inr (Or.inl hm), hb⟩
      · trivial
    · split
      · next decl hd =>
        intro hs hb
        exact h ⟨sig.cls, decl⟩ ⟨Or.inr (Or.inr ⟨hs, hd⟩), hb⟩
      · trivial
  · rintro ⟨h1, h2, h3⟩ m ⟨(hm | hm | ⟨hs, hd⟩), hb⟩
    · rw [hm] at h1; exact h1 hb
    · rw [hm] at h2; exact h2 hb
    · obtain ⟨mc, md⟩ := m
      have hc : sig.cls = mc := by rw [hs]; rfl
      subst hc
      simp only at hd
      rw [hd] at h3
      exact h3 hs hb

/-- A contract holds: for every method a call of `sig` can reach (static, special or class
    initializer selection) and, unless `sig` is static, for every application class implementing
    `sig` (behavioural subtyping). `Valid P Γ` is exactly `ContractOK` for every contract of
    `Γ`. -/
def ContractOK (P : Program) (sig : MethodSig) (S : Spec) : Prop :=
  (∀ m, Targets P sig m → Sat P m S) ∧
  (∀ c, P.isProgClass c = true → P.isSubclass c sig.cls = some true → P.staticDecl sig = false →
    VSat P sig c S)

theorem valid_iff_contractOK {P : Program} {Γ : SpecEnv} :
    Valid P Γ ↔ ∀ sig S, Γ sig = some S → ContractOK P sig S := Iff.rfl

/-- The contracts of a table hold when each of them does. -/
theorem Contracts.valid_of_ok {P : Program} {T : Contracts}
    (h : ∀ p ∈ T, ContractOK P p.1 p.2) : Valid P T.env := by
  intro sig S hΓ
  exact h (sig, S) (lookup_mem_dec hΓ)

/-- A virtual call selecting an application method satisfies what the method satisfies. -/
theorem vsat_of_jimple {P : Program} {sig : MethodSig} {c : ClassName} {m : MethodRef} {S : Spec}
    (hsel : P.selectVirtual c sig.sub = .jimple m) (hm : Sat P m S) : VSat P sig c S := by
  intro args σ o hpre hv
  cases hv with
  | jimple hsel' hm' => rw [hsel] at hsel'; cases hsel'; exact hm args σ o hpre hm'
  | native hsel' => rw [hsel] at hsel'; cases hsel'
  | noModel hsel' => rw [hsel] at hsel'; cases hsel'
  | none hsel' => rw [hsel] at hsel'; cases hsel'

/-- No virtual call reaches an abstract class whose selection fails. -/
theorem vsat_of_none {P : Program} {sig : MethodSig} {c : ClassName} {why : String} {S : Spec}
    (hsel : P.selectVirtual c sig.sub = .none why) (hc : P.concrete c = false) : VSat P sig c S := by
  intro args σ o hpre hv
  cases hv with
  | jimple hsel' => rw [hsel] at hsel'; cases hsel'
  | native hsel' => rw [hsel] at hsel'; cases hsel'
  | noModel hsel' => rw [hsel] at hsel'; cases hsel'
  | none hsel' hconc => rw [hc] at hconc; cases hconc

/-- A library implementation verified against the callee contracts `Γ` satisfies the
    contract when `Γ` holds. -/
theorem vsat_of_nativeVC {P : Program} {Γ : SpecEnv} {d : Nat} {sig : MethodSig} {c lc : ClassName}
    {S : Spec} (hV : Valid P Γ) (hsel : P.selectVirtual c sig.sub = .native lc)
    (h : NativeVC P Γ d sig c lc S) : VSat P sig c S := by
  intro args σ o hpre hv
  cases hv with
  | jimple hsel' => rw [hsel] at hsel'; cases hsel'
  | native hsel' hheap hpl hr =>
    rw [hsel] at hsel'; cases hsel'
    have h2 := h _ _ _ _ hpre hheap
    rw [hpl] at h2
    exact rexec_okV hV hr d _ h2
  | noModel hsel' hheap hpl =>
    rw [hsel] at hsel'; cases hsel'
    have h2 := h _ _ _ _ hpre hheap
    rw [hpl] at h2
    exact h2
  | none hsel' => rw [hsel] at hsel'; cases hsel'

/-- **Bottom-up linking**: a contract whose verification conditions were proved against the
    contracts `Γ` of its callees holds when `Γ` does. Each contract is proved once, against its
    callees' contracts only; callers then use it through `Contracts.valid_of_ok`. -/
theorem ContractVC.ok {P : Program} {Γ : SpecEnv} {d : Nat} {Ann : Annotations} {sig : MethodSig}
    {S : Spec} (hV : Valid P Γ) (h : ContractVC P Γ d Ann sig S) : ContractOK P sig S := by
  refine ⟨fun m ht => MethodVC.sat_of_valid hV (h.1 m ht), fun c hpc hsub hst => ?_⟩
  have h2 := h.2 c hpc hsub hst
  revert h2
  split
  · next m hsel => exact fun hm => vsat_of_jimple hsel (MethodVC.sat_of_valid hV hm)
  · next lc hsel => exact fun hn => vsat_of_nativeVC hV hsel hn
  · next why hsel => exact fun hc => vsat_of_none hsel hc

/-- A method's verification conditions give its contract, when the conditions of the
    contracts it relies on hold too. -/
theorem MethodVC.sat_of_allVC {P : Program} {Γ : SpecEnv} {d : Nat} {Ann : Annotations}
    {m : MethodRef} {S : Spec} (hAll : AllVC P Γ d Ann)
    (h : MethodVC P Γ d m S (Ann.inv m) (Ann.fuel m)) : Sat P m S :=
  fun _ _ _ hpre hm => mexec_ok_vc hAll hm h hpre

/-- A method verified without contracts (its calls are library calls, answered by the library
    models) satisfies its contract: every terminating execution from a state satisfying the
    precondition ends in an outcome satisfying the postcondition. -/
theorem MethodVC.sat {P : Program} {m : MethodRef} {S : Spec} {A : Invariants} {fuel : Nat}
    (h : MethodVC P (fun _ => none) 0 m S A fuel) : Sat P m S :=
  MethodVC.sat_of_allVC (Ann := { inv := fun _ => A, fuel := fun _ => fuel })
    (fun _ _ h => by cases h) h

/-- The verification conditions of method `m` in every program that satisfies the facts `F`
    (lookup equations: the classes, fields and selections the body uses). A proof of
    `BodyVC` depends only on `m` with its body, the callee contracts `Γ` and the facts, not on
    the rest of the program: it survives (and can be cached across) changes to other classes.
    `jverify_body` proves it. -/
def BodyVC (F : Program → Prop) (Γ : SpecEnv) (d : Nat) (m : MethodRef) (S : Spec)
    (A : Invariants) (fuel : Nat) : Prop :=
  ∀ P, F P → MethodVC P Γ d m S A fuel

theorem BodyVC.methodVC {F : Program → Prop} {Γ : SpecEnv} {d : Nat} {m : MethodRef} {S : Spec}
    {A : Invariants} {fuel : Nat} {P : Program} (h : BodyVC F Γ d m S A fuel) (hF : F P) :
    MethodVC P Γ d m S A fuel := h P hF

/-- A body verified once, linked into a program that satisfies its facts and its callees'
    contracts. -/
theorem BodyVC.sat {F : Program → Prop} {Γ : SpecEnv} {d : Nat} {m : MethodRef} {S : Spec}
    {A : Invariants} {fuel : Nat} {P : Program} (h : BodyVC F Γ d m S A fuel) (hF : F P)
    (hV : Valid P Γ) : Sat P m S :=
  MethodVC.sat_of_valid hV (h P hF)

/-- `BodyVC` for contracts that mention the program, such as `genericSpec P m` (arguments and
    heap typed by the program's classes): the callee contracts `Γ P` and the contract `S P` are
    taken in each program that satisfies the facts. -/
def BodyVCP (F : Program → Prop) (Γ : Program → SpecEnv) (d : Nat) (m : MethodRef)
    (S : Program → Spec) (A : Invariants) (fuel : Nat) : Prop :=
  ∀ P, F P → MethodVC P (Γ P) d m (S P) A fuel

theorem BodyVCP.sat {F : Program → Prop} {Γ : Program → SpecEnv} {d : Nat} {m : MethodRef}
    {S : Program → Spec} {A : Invariants} {fuel : Nat} {P : Program}
    (h : BodyVCP F Γ d m S A fuel) (hF : F P) (hV : Valid P (Γ P)) : Sat P m (S P) :=
  MethodVC.sat_of_valid hV (h P hF)

/-- `NoShadow` of a concrete program, by evaluation over its classes. -/
theorem NoShadow.of_check {P : Program} (h : (P.index.toList.all fun cd => !isLibClass cd.name) = true) :
    NoShadow P := by
  intro c hc
  cases hf : P.findClass c with
  | none => rfl
  | some d =>
    have hfind : P.index.find (nameHash c) c = some d := hf
    have hmem := ClassTree.mem_toList_of_find hfind
    have := List.all_eq_true.mp h d hmem.1
    rw [hmem.2, hc] at this
    simp at this

/-- The canonical facts of a body: the program contains the classes `cs` (typically the
    method's own class) and shadows no library class. Every lookup of such a body is decided by
    them, and they are checked for an assembled program by evaluation (`Contains.of_check`). -/
def Contains (P : Program) (cs : List ClassDecl) : Prop :=
  NoShadow P ∧ ∀ d ∈ cs, P.findClass d.name = some d

theorem Contains.of_check {P : Program} {cs : List ClassDecl}
    (h1 : (P.index.toList.all fun cd => !isLibClass cd.name) = true)
    (h2 : ∀ d ∈ cs, P.findClass d.name = some d) : Contains P cs :=
  ⟨NoShadow.of_check h1, h2⟩

/-- The class named `s.name` exists in `P` and has shape `s` (its declaration without method
    bodies, `ClassDecl.erase`). -/
def ShapeIs (P : Program) (s : ClassDecl) : Prop := ∃ d, P.findClass s.name = some d ∧ d.erase = s

/-- Method-level facts: no library class is shadowed and the classes have the shapes `ss`.
    Unlike `Contains`, they do not mention method bodies, so a body proof assuming them is not
    affected by edits of other methods' bodies (the shapes change only with signatures,
    modifiers, fields or the hierarchy). Shapes are imported with `jimple_shape`; calls to
    other methods go through their contracts. -/
def Shapes (P : Program) (ss : List ClassDecl) : Prop := NoShadow P ∧ ∀ s ∈ ss, ShapeIs P s

/-- A class of the program has the shape of its erasure. -/
theorem ShapeIs.of_findClass {P : Program} {d s : ClassDecl} (h : P.findClass s.name = some d)
    (he : d.erase = s) : ShapeIs P s := ⟨d, h, he⟩

/-- `Shapes` of a concrete program, by evaluation. -/
theorem Shapes.of_check {P : Program} {ss : List ClassDecl}
    (h1 : (P.index.toList.all fun cd => !isLibClass cd.name) = true)
    (h2 : ∀ s ∈ ss, ShapeIs P s) : Shapes P ss :=
  ⟨NoShadow.of_check h1, h2⟩

/-- No callee contracts: valid in every program. -/
theorem valid_none (P : Program) : Valid P (fun _ => none) := fun _ _ h => by cases h

/-- Implementing classes range over the application classes of the index. -/
theorem forall_progClass_of_mem (P : Program) (Φ : ClassName → Prop)
    (h : ∀ cd ∈ P.index.toList, Φ cd.name) : ∀ c, P.isProgClass c = true → Φ c := by
  intro c hc
  simp only [Program.isProgClass, Option.isSome_iff_exists, Program.findClass] at hc
  obtain ⟨d, hd⟩ := hc
  have := ClassTree.mem_toList_of_find hd
  rw [← this.2]
  exact h d this.1

end Jimple

namespace Jimple

/-- Annotations from a list of `((class, method name), invariants, fuel)` entries. -/
def Annotations.ofList (l : List ((ClassName × String) × Invariants × Nat)) (dfuel : Nat := 1000) :
    Annotations where
  inv m := ((l.find? fun e => e.1.1 == m.cls && e.1.2 == m.decl.name).map (·.2.1)).getD []
  fuel m := ((l.find? fun e => e.1.1 == m.cls && e.1.2 == m.decl.name).map (·.2.2)).getD dfuel

open Lean Elab Tactic

/-- `jcontracts`: prove `∀ p ∈ T, ContractVC P T.env d Ann p.1 p.2` for a concrete contract
    table — one goal per contract, call targets and implementing classes enumerated, and
    `jverify` run on every implementation. Remaining goals are left to the user. -/
syntax (name := jcontractsTac) "jcontracts" (" [" ident,* "]")? : tactic

@[tactic jcontractsTac] def evalJcontracts : Tactic := fun stx => do
  let extra : Array Ident := optIdents stx[1]
  let extra' : Array (TSyntax `Lean.Parser.Tactic.simpLemma) ←
    extra.mapM fun i => `(Lean.Parser.Tactic.simpLemma| $i:ident)
  -- split the table into one `ContractVC` goal per entry, each into its two parts
  evalTactic (← `(tactic| simp only [List.forall_mem_cons, List.not_mem_nil, false_implies,
    implies_true, and_true, ContractVC, $extra',*]))
  evalTactic (← `(tactic| repeat' constructor))
  let gs ← getGoals
  let mut out := []
  for g in gs do
    setGoals [g]
    -- each goal: the target part or the virtual part of a ContractVC
    try
      evalTactic (← `(tactic| first
        | (rw [forall_targets_iff])
        | (refine forall_progClass_of_mem _ _ ?_)
        | skip))
      evalTactic (← `(tactic| simp (config := { decide := true }) only
        [jground, List.forall_mem_cons, List.forall_mem_nil, and_true, imp_self, implies_true,
         Option.some.injEq, reduceCtorEq, false_implies, true_implies, forall_const,
         Annotations.ofList, List.find?, Contracts.env, Bool.false_and, Bool.and_false,
         Bool.true_and, Bool.and_true, Option.map_none, Option.map_some, Option.getD_none,
         Option.getD_some, List.map_nil, List.map_cons, $extra',*]))
    catch _ => pure ()
    for g' in (← getGoals) do
      setGoals [g']
      try evalTactic (← `(tactic| repeat' constructor)) catch _ => pure ()
      for g'' in (← getGoals) do
        setGoals [g'']
        let ty ← instantiateMVars (← g''.getType)
        if ty.isAppOf ``MethodVC then
          try
            evalTactic (← `(tactic| jverify [$extra,*]))
          catch _ => pure ()
        else
          let ids := extra.push (mkIdent ``NativeVC)
          try
            evalTactic (← `(tactic| jvc [$ids,*]))
          catch _ => pure ()
        out := out ++ (← getGoals)
  setGoals out

/-- The program-structure lookups on the program variable `P` that block the remaining goals,
    each with its value in the concrete program `Q`: the facts a `BodyVC` needs. -/
def stuckFacts (P Q : Lean.Expr) (goals : List MVarId) : MetaM (Array (Lean.Expr × Lean.Expr)) := do
  let env ← getEnv
  -- full applications only (a partial application is a function, not a fact)
  let arity : Name → Nat := fun c => match env.find? c with
    | some info => info.type.getForallBinderNames.length
    | none => 0
  let mut out : Array (Lean.Expr × Lean.Expr) := #[]
  for g in goals do
    let terms ← g.withContext do
      let mut acc : Array Lean.Expr := #[]
      let mut exprs := #[← instantiateMVars (← g.getType)]
      for d in (← getLCtx) do
        if !d.isImplementationDetail then exprs := exprs.push (← instantiateMVars d.type)
      -- applications of a program query whose arguments are closed except `P`
      let isFact (t : Lean.Expr) : Bool :=
        match t.getAppFn.constName? with
        | some c => groundFns.contains c && t.getAppNumArgs == arity c && t.getAppArgs.any (· == P) &&
            !(t.replaceFVar P (mkConst ``Unit.unit)).hasFVar && !t.hasLooseBVars
        | none => false
      let rec go (t : Lean.Expr) (acc : Array Lean.Expr) : Array Lean.Expr :=
        -- the largest such applications only (not their partial applications)
        if isFact t then acc.push t else
        match t with
        | .app f a => go a (go f acc)
        | .lam _ ty b _ | .forallE _ ty b _ => go b (go ty acc)
        | .letE _ ty v b _ => go b (go v (go ty acc))
        | .mdata _ b | .proj _ _ b => go b acc
        | _ => acc
      for e in exprs do
        acc := go e acc
      return acc
    -- lookups already given by a fact hypothesis `t = v` are not reported again
    let known ← g.withContext do
      return (← getLCtx).foldl (init := #[]) fun acc d =>
        let ty := d.type.consumeMData
        if ty.isAppOfArity ``Eq 3 then acc.push ty.appFn!.appArg! else acc
    for t in terms do
      unless out.any (·.1 == t) || known.contains t do
        let v ← groundEvalClean (t.replaceFVar P Q)
        out := out.push (t, v)
  return out

open Lean Elab Tactic in
/-- `jfacts Q`: after a `jverify` on an abstract program `P` (inside `jverify_body`), list the
    lookups on `P` that the remaining goals need, with their values in the program `Q`, as
    facts to add to `BodyVC`'s `F`. -/
elab "jfacts " q:term : tactic => do
  let gs ← getGoals
  let some g := gs.head? | return
  let fs ← g.withContext do
    let Q ← Term.elabTerm q (some (mkConst ``Jimple.Program))
    let some P := (← getLCtx).findDecl? fun d =>
        if d.userName.eraseMacroScopes == `P && d.type.isConstOf ``Jimple.Program then some d.toExpr else none
      | throwError "jfacts: no program variable P in the context"
    stuckFacts P Q gs
  if fs.isEmpty then logInfo "jfacts: no lookup on P blocks the remaining goals"
  for (t, v) in fs do
    g.withContext do logInfo m!"fact: {t} = {v}"

/-! ### Hierarchy walks without lambda-bound class names

  On an abstract program, unfolding `Program.supersN` / `Program.resolveFieldN` by their own
  equations puts recursive calls under `foldlM`/`findSome?` lambdas, whose class argument is
  a bound variable; simp then unfolds them through all the fuel. These restatements recurse
  over the (literal) list of direct supertypes instead. -/

/-- `supersN`'s fold over direct supertypes, by recursion on the list. -/
def supersFold (P : Program) (n : Nat) : List ClassName → List ClassName → Option (List ClassName)
  | acc, [] => some acc
  | acc, p :: ps =>
    match P.supersN n p with
    | some s => supersFold P n (acc ++ s) ps
    | none => none

theorem foldlM_supers_eq (P : Program) (n : Nat) : ∀ (ps acc : List ClassName),
    ps.foldlM (fun acc p => (fun s => acc ++ s) <$> P.supersN n p) acc = supersFold P n acc ps
  | [], acc => rfl
  | p :: ps, acc => by
    simp only [List.foldlM_cons, supersFold]
    cases h : P.supersN n p with
    | none => rfl
    | some s => exact foldlM_supers_eq P n ps (acc ++ s)

theorem supersN_succ_eq (P : Program) (n : Nat) (c : ClassName) :
    P.supersN (n + 1) c = match P.findClass c with
      | some d => supersFold P n [c] (d.super.toList ++ d.interfaces)
      | none => preludeAncestors c := by
  rw [Program.supersN]
  cases P.findClass c <;> simp only [foldlM_supers_eq]

/-- `resolveFieldN`'s search of the direct superinterfaces, by recursion on the list. -/
def resolveIfaces (P : Program) (n : Nat) (name : String) :
    List ClassName → Option (ClassName × FieldDecl)
  | [] => none
  | i :: is =>
    match P.resolveFieldN n i name with
    | some r => some r
    | none => resolveIfaces P n name is

theorem findSome_resolve_eq (P : Program) (n : Nat) (name : String) : ∀ (is : List ClassName),
    is.findSome? (fun i => P.resolveFieldN n i name) = resolveIfaces P n name is
  | [] => rfl
  | i :: is => by
    simp only [List.findSome?, resolveIfaces]
    cases P.resolveFieldN n i name with
    | none => exact findSome_resolve_eq P n name is
    | some r => rfl

theorem resolveFieldN_succ_eq (P : Program) (n : Nat) (c : ClassName) (name : String) :
    P.resolveFieldN (n + 1) c name = match P.lookup c with
      | none => none
      | some d =>
        match d.fields.find? (·.name == name) with
        | some f => some (c, f)
        | none =>
          match resolveIfaces P n name d.interfaces with
          | some r => some r
          | none =>
            match d.super with
            | some s => P.resolveFieldN n s name
            | none => none := by
  rw [Program.resolveFieldN]
  cases P.lookup c with
  | none => rfl
  | some d =>
    simp only [findSome_resolve_eq]
    cases d.fields.find? (·.name == name) <;> simp only
    cases resolveIfaces P n name d.interfaces <;> simp only
    cases d.super <;> rfl

/-- Recursive hierarchy walks of the semantics, unfolded on an abstract program one step at a
    time and only for a literal class name: unfolding them under a binder (inside their own
    `foldlM`/`findSome?` lambdas) would recurse through all the fuel. -/
def litUnfoldFns : List (Name × Nat) :=
  [(``Program.supersN, 2), (``Program.resolveFieldN, 2), (``Program.chainN, 2),
   (``Program.superChainN, 2), (``Program.instanceFieldsN, 2)]

open Lean Meta in
/-- `jlitunfold`: one unfolding step of a `litUnfoldFns` application whose class argument is a
    string literal and whose fuel is a numeral, by the equation of the `n + 1` case. -/
simproc jlitunfold (_) := fun e => do
  let some fn := e.getAppFn.constName? | return .continue
  let some (_, i) := litUnfoldFns.find? (·.1 == fn) | return .continue
  let args := e.getAppArgs
  let some c := args[i]? | return .continue
  let some n := (args[1]?.bind (·.nat?)) | return .continue
  unless c.isStringLit && n > 0 do return .continue
  try
    -- instantiate the `n + 1` equation by unification with `e` (equations are generated on demand)
    let some eqns ← getEqnsFor? fn | return .continue
    let some eq2 := eqns[1]? | return .continue
    let thm := mkConst eq2
    let (mvars, _, ty) ← forallMetaTelescope (← inferType thm)
    let some (_, lhs, rhs) := ty.eq? | return .continue
    unless ← isDefEq lhs e do return .continue
    let rhs ← instantiateMVars rhs
    let pf ← instantiateMVars (mkAppN thm mvars)
    if pf.hasMVar then return .continue
    return .visit { expr := rhs, proof? := some pf }
  catch _ => return .continue

open Lean Elab Tactic in
/-- `jcontract_ok [h₁, …]`: prove `ContractOK P sig S` for a concrete program from facts
    `hᵢ : Sat P mᵢ S` about the implementations: every call target and every implementing
    application class is enumerated by evaluation; abstract classes and methods are discharged,
    every other case must be one of the given facts. -/
syntax (name := jcontractOkTac) "jcontract_ok" (" [" term,* "]")? : tactic

open Lean Elab Tactic in
@[tactic jcontractOkTac] def evalJcontractOk : Tactic := fun stx => do
  let facts : Array Term :=
    let s := stx[1]
    let s := if s.getNumArgs == 1 then s[0] else s
    if s.getNumArgs == 3 then s[1].getSepArgs.map (⟨·⟩) else #[]
  let useFact : TacticM Unit := do
    for f in facts do
      let s ← saveState
      try evalTactic (← `(tactic| exact $f)); return catch _ => s.restore
    throwError "jcontract_ok: no given fact closes {← getMainTarget}"
  evalTactic (← `(tactic| refine ⟨?_, ?_⟩))
  -- call targets (static, special, class initializer)
  let gs ← getGoals
  setGoals [gs[0]!]
  evalTactic (← `(tactic| intro m ht))
  evalTactic (← `(tactic| obtain ⟨hsel, hb⟩ := ht))
  evalTactic (← `(tactic| rcases hsel with h | h | ⟨hs, _⟩))
  for g in (← getGoals) do
    setGoals [g]
    -- (no nested `by` inside `first`: a failing nested proof is logged, not backtracked)
    evalTactic (← `(tactic| first
      | (have hn := congrArg MethodSig.name hs
         simp (config := { decide := true }) only [jground, clinitSig] at hn)
      | (simp (config := { decide := true }) only [jground, reduceCtorEq, Program.Target.jimple.injEq] at h
         try subst h
         try simp (config := { decide := true }) only [jground] at hb)))
    for g' in (← getGoals) do
      setGoals [g']
      useFact
  -- implementing application classes
  setGoals [gs[1]!]
  evalTactic (← `(tactic| apply forall_progClass_of_mem))
  evalTactic (← `(tactic| simp (config := { decide := true }) only [jground, List.forall_mem_cons,
    List.forall_mem_nil, List.not_mem_nil, false_implies, implies_true, and_true, true_implies]))
  evalTactic (← `(tactic| repeat' constructor))
  for g in (← getGoals) do
    setGoals [g]
    evalTactic (← `(tactic| first
      | (intro hf; exact False.elim hf)
      | (exact vsat_of_none rfl rfl)
      | skip))
    for g' in (← getGoals) do
      setGoals [g']
      let mut done := false
      let mut lastErr : MessageData := m!""
      for f in facts do
        let s ← saveState
        try
          -- the method is fixed by the fact, then its selection is checked by evaluation
          evalTactic (← `(tactic| exact vsat_of_jimple (by exact rfl) $f))
          done := true
          break
        catch e => lastErr := e.toMessageData; s.restore
      unless done do
        throwError "jcontract_ok: no given fact implements {← getMainTarget}\n{lastErr}"

/-- `jverify_body [defs]`: prove `BodyVC F Γ d m S A fuel` (or `BodyVCP`) — for an arbitrary
    program `P` satisfying the facts `F`, with `jverify`; the facts are used as rewrite rules. -/
syntax (name := jverifyBodyTac) "jverify_body" (" [" ident,* "]")? : tactic

-- lookups on the abstract program are unfolded, down to the facts that decide them
-- (`P.findClass c = …`, `NoShadow P`)
macro_rules
  | `(tactic| jverify_body) => `(tactic| ((first | unfold BodyVC | unfold BodyVCP); intro P hF; (try dsimp only); jverify [findHandler, Program.subtype, Program.isSubclass, Program.supers, supersN_succ_eq, supersFold, Program.fuel, Program.lookup, fieldKey, Program.resolveField, resolveFieldN_succ_eq, resolveIfaces, Program.isProgClass, Program.selectStatic, Program.chainN, Program.selectSpecial,
      Program.staticDecl, Targets, Shapes, ShapeIs]))
  | `(tactic| jverify_body [$ids,*]) => `(tactic| ((first | unfold BodyVC | unfold BodyVCP); intro P hF; (try dsimp only); jverify [findHandler, Program.subtype, Program.isSubclass, Program.supers, supersN_succ_eq, supersFold, Program.fuel, Program.lookup, fieldKey, Program.resolveField, resolveFieldN_succ_eq, resolveIfaces, Program.isProgClass, Program.selectStatic, Program.chainN, Program.selectSpecial,
      Program.staticDecl, Targets, Shapes, ShapeIs, $ids,*]))

end Jimple
