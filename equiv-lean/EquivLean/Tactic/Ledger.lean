import Lean

/-!
# Assumption ledger

`#ledger thm₁ thm₂ ...` prints, for each theorem, what a reader has to trust besides the kernel:

* the **hypotheses** of its statement: the Prop binders after unfolding the statement's definitions
  (`forallTelescopeReducing`), and its other binders (the inputs);
* the **axioms** in its dependency closure (anything beyond `propext`, `Classical.choice`,
  `Quot.sound` is flagged) and the `opaque` constants outside Lean's core;
* per **bridge**, the library-model, oracle and external-model constants that the statement depends
  on, found by their defining module (`bridges` below). Only the statement's closure (its type,
  through the definitions it uses) is what a reader trusts; constants only the proof uses are checked
  by the kernel. For each bridge it lists the model definitions that EquivLean definitions in that
  closure refer to directly, and, for libraries that dispatch calls by name, the names the program
  data uses (string literals both in the dispatcher, its matchers included, and in EquivLean
  definitions).

Closures are walked like `Lean.collectAxioms`, but every constant is kept: the theorem's whole
closure for the axioms and `opaque` constants, the statement's closure for the bridges.
-/

namespace EquivLean.Ledger
open Lean Meta Elab Command

/-- A library whose constants model library code, external code or an oracle. -/
structure Bridge where
  label : String
  /-- module prefixes of the model constants -/
  modules : List Name
  /-- also count modules whose last component is one of these (e.g. Aeneas' `FunsExternal`) -/
  moduleLast : List String := []
  /-- constants that dispatch calls by name: their string literals are the callable names -/
  dispatchers : List Name := []
  /-- only keys with one of these prefixes count (empty: all) -/
  keyPrefixes : List String := []
  /-- EquivLean constants whose type has one of these heads are declarations of external code
  (e.g. StrictTS `ExtFun`s) and are listed -/
  declTypes : List Name := []

/-- The bridges of the five encodings, from the vendored sources (10-25):
* cirlean: C/C++ library calls run Lean models (`CIR/Std/*.lean`); the frontend attaches a
  `CIR.Model` constructor to each modelled function declaration, so the constructors that the
  program data refers to are the models the program can call.
* JimpleLean: Java library methods are natives in `Jimple/Native.lean`, dispatched on class and
  method name; `Jimple.Decimal`, `Jimple.JString`, `Jimple.Numeric` model the Java value types.
* StrictTS: external functions are declared as `ExtFun`s and answered by an oracle in the world
  (`ExtOracle`, `StrictTS.Core.World`; also `Math.random`, `Date.now`).
* coblean: external programs called by `CALL` (e.g. COBDATFT) are Lean functions in `Cobol.Ext`,
  dispatched by program name (`cardDemoCalls`); `Cobol.Target.*` model the target languages'
  library behaviour (`BigDecimal`, `Math.*Exact`, checked `i64`/`i128`, `ByteBuffer`, CP037).
* Aeneas: the Rust standard library model `Aeneas.Std`, and `FunsExternal` modules of the
  extracted crates (external functions). -/
def bridges : List Bridge := [
  { label := "CIR library models (cirlean)", modules := [`CIR.Std, `CIR.Model] },
  { label := "JimpleLean natives and value models", modules := [`Jimple.Native, `Jimple.Decimal,
      `Jimple.DecimalLemmas, `Jimple.JString, `Jimple.Numeric, `Jimple.Unicode],
    dispatchers := [`Jimple.Native.staticCall, `Jimple.Native.stringInst, `Jimple.Native.decInst,
      `Jimple.Native.bigIntInst, `Jimple.Native.ctorCall],
    keyPrefixes := ["java.", "javax."] },
  { label := "StrictTS externs and world oracles", modules := [`StrictTS.Proof.Extern, `StrictTS.Core.World],
    declTypes := [`StrictTS.ExtFun] },
  { label := "coblean external programs (Cobol.Ext)", modules := [`Cobol.Ext],
    dispatchers := [`Cobol.Ext.cardDemoCalls] },
  { label := "coblean target-language models (Cobol.Target)", modules := [`Cobol.Target] },
  { label := "Aeneas std and FunsExternal", modules := [`Aeneas.Std], moduleLast := ["FunsExternal"] }
]

def stdAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

def coreModule (m : Name) : Bool :=
  match m.getRoot with
  | `Init | `Lean | `Std | `Lake => true
  | _ => false

def moduleOf (env : Environment) (n : Name) : Name :=
  match env.getModuleIdxFor? n with
  | some i => env.header.moduleNames[i.toNat]!
  | none => env.mainModule

def Bridge.owns (b : Bridge) (m : Name) : Bool :=
  b.modules.any (·.isPrefixOf m) ||
    (match m with
     | .str _ s => b.moduleLast.contains s
     | _ => false)

/-- Every constant `roots` depend on, through types and values. -/
def closure (env : Environment) (roots : Array Name) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut todo := roots
  while 0 < todo.size do
    let n := todo.back!
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    if let some ci := env.find? n then
      for c in ci.getUsedConstantsAsSet do
        unless seen.contains c do todo := todo.push c
  return seen

/-- The string literals of an expression (shared subterms visited once). -/
partial def strLits (e : Expr) : StateM (Std.HashSet Expr × Std.HashSet String) Unit := do
  if (← get).1.contains e then return
  modify fun (v, s) => (v.insert e, s)
  match e with
  | .lit (.strVal s) => modify fun (v, ss) => (v, ss.insert s)
  | .app f a => strLits f; strLits a
  | .lam _ t b _ | .forallE _ t b _ => strLits t; strLits b
  | .letE _ t v b _ => strLits t; strLits v; strLits b
  | .mdata _ b | .proj _ _ b => strLits b
  | _ => pure ()

def litsOf (env : Environment) (ns : Array Name) : Std.HashSet String := Id.run do
  let mut st : Std.HashSet Expr × Std.HashSet String := ({}, {})
  for n in ns do
    if let some ci := env.find? n then
      st := ((strLits ci.type *> (match ci.value? (allowOpaque := true) with
        | some v => strLits v
        | none => pure ())).run st).2
  return st.2

def short (xs : Array String) (k : Nat := 40) : String :=
  let xs := xs.qsort (· < ·)
  if xs.isEmpty then "none"
  else ", ".intercalate (xs.toList.take k) ++ (if xs.size > k then s!" … (+{xs.size - k} more)" else "")

def clip (s : String) (k : Nat := 240) : String :=
  let cs := s.toList.map (fun c => if c == '\n' then ' ' else c)
  let cs := cs.foldr (fun c acc => if c == ' ' && acc.head? == some ' ' then acc else c :: acc) []
  if cs.length ≤ k then String.ofList cs else String.ofList (cs.take k) ++ " …"

/-- The hypotheses and inputs of a theorem's statement, its definitions unfolded. Anonymous
binders (from `→`) are shown as `h₁`, `h₂`, ... -/
def binders (ci : ConstantInfo) : MetaM (Array String × Array String) :=
  forallTelescopeReducing ci.type fun xs _ => do
    let mut hs := #[]
    let mut ins := #[]
    for x in xs do
      let d ← x.fvarId!.getDecl
      if ← isProp d.type then
        let nm := if d.userName.hasMacroScopes then s!"h{hs.size + 1}" else toString d.userName
        hs := hs.push s!"`{nm} : {clip (toString (← ppExpr (← Core.betaReduce d.type)))}`"
      else
        ins := ins.push s!"`{d.userName.eraseMacroScopes} : {clip (toString (← ppExpr d.type))}`"
    return (hs, ins)

/-- Compiler, equation and proof auxiliaries: not part of what a model says. -/
def isAux (env : Environment) (n : Name) : Bool :=
  n.isInternal || n.hasMacroScopes || Meta.isMatcherCore env n ||
    (match n with
     | .str _ s => s.startsWith "match_" || s.startsWith "proof_" || s.startsWith "eq_" ||
         s == "congr_simp" || s.endsWith "_def" || s == "sizeOf_spec" || s == "inj" || s == "injEq"
     | _ => false)

/-- The model definitions (not lemmas, not auxiliaries) among `ns`. -/
def defsOf (env : Environment) (ns : Array Name) : Array Name :=
  ns.filter fun n => !isAux env n && !(env.find? n).any (· matches .thmInfo _)

/-- The ledger of one theorem, as markdown. -/
def ledger (thm : Name) : MetaM String := do
  let env ← getEnv
  let some ci := env.find? thm | throwError "unknown constant {thm}"
  let (hs, ins) ← binders ci
  let cl := closure env #[thm]
  let all := cl.toArray
  let mods := all.map (moduleOf env)
  let own := (all.zip mods).filter (fun (_, m) => (`EquivLean).isPrefixOf m) |>.map (·.1)
  -- the statement's closure: what its meaning depends on
  let scl := closure env ci.type.getUsedConstants
  let sall := scl.toArray
  let smods := sall.map (moduleOf env)
  let sown := (sall.zip smods).filter (fun (n, m) => (`EquivLean).isPrefixOf m &&
    !(env.find? n).any (· matches .thmInfo _)) |>.map (·.1)
  let mut ownUses : NameSet := {}
  for n in sown do
    if let some c := env.find? n then
      for u in c.getUsedConstantsAsSet do
        ownUses := ownUses.insert u
  let ownLits := litsOf env sown
  let axs := all.filter (fun n => (env.find? n).any (· matches .axiomInfo _))
  let nonstd := axs.filter (fun n => !stdAxioms.contains n)
  let ops := (all.zip mods).filter (fun (n, m) => !coreModule m && (env.find? n).any (· matches .opaqueInfo _))
  let opMods := ops.foldl (fun (acc : Std.HashMap Name Nat) (_, m) => acc.insert m (acc.getD m 0 + 1)) {}
  let nCore := mods.filter coreModule |>.size
  let mut out := s!"### `{thm}`\n\n"
  out := out ++ s!"- module `{moduleOf env thm}`; dependency closure {all.size} constants" ++
    s!" ({own.size} EquivLean, {all.size - own.size - nCore} other libraries, {nCore} Lean core);" ++
    s!" the statement's closure {sall.size} ({sown.size} EquivLean definitions)\n"
  out := out ++ s!"- hypotheses (Prop binders of the statement, definitions unfolded): " ++
    (if hs.isEmpty then "none" else "; ".intercalate hs.toList) ++ "\n"
  out := out ++ s!"- inputs: " ++ (if ins.isEmpty then "none" else "; ".intercalate ins.toList) ++ "\n"
  out := out ++ s!"- axioms: {short (axs.map toString)}" ++
    (if nonstd.isEmpty then " (standard only)" else s!" — NON-STANDARD: {short (nonstd.map toString)}") ++ "\n"
  out := out ++ s!"- opaque constants outside Lean core: {ops.size}" ++
    (if ops.isEmpty then "" else
      s!" (by module: {short (opMods.toArray.map (fun (m, k) => s!"{m} {k}")) 10}; names: " ++
      s!"{short (ops.map (fun (n, _) => toString n.eraseMacroScopes) |>.toList.eraseDups.toArray) 12})") ++ "\n"
  for b in bridges do
    let mine := (sall.zip smods).filter (fun (_, m) => b.owns m)
    let inProof := (all.zip mods).filter (fun (_, m) => b.owns m) |>.size
    if mine.isEmpty then
      out := out ++ s!"- {b.label}: none in the statement's closure" ++
        (if inProof > 0 then s!" ({inProof} constants only in the proof's closure)" else "") ++ "\n"
      continue
    let byMod := mine.foldl (fun (acc : Std.HashMap Name Nat) (_, m) => acc.insert m (acc.getD m 0 + 1)) {}
    let modList := byMod.toArray.qsort (fun a b => a.2 > b.2) |>.map (fun (m, k) => s!"{m} {k}")
    let names := mine.map (·.1)
    let defs := defsOf env names
    let used := defsOf env (names.filter ownUses.contains)
    out := out ++ s!"- {b.label}: {mine.size} constants in the statement's closure, {defs.size} of them" ++
      s!" model definitions ({short modList 8}); {inProof} in the whole closure\n"
    out := out ++ s!"  - model definitions referred to by EquivLean definitions of the statement ({used.size}): " ++
      s!"{short (used.map toString) 60}\n"
    unless b.declTypes.isEmpty do
      let decls := sown.filter (fun n => (env.find? n).any (fun c => b.declTypes.contains c.type.getAppFn.constName))
      out := out ++ s!"  - external code declared by EquivLean code: {short (decls.map toString)}\n"
    let ds := b.dispatchers.filter scl.contains
    unless ds.isEmpty do
      -- string patterns live in the dispatchers' matchers (`d.match_1`, ...)
      let dsAux := sall.filter (fun n => ds.any (·.isPrefixOf n))
      let keys := litsOf env dsAux
      let keys := keys.toArray.filter (fun k => b.keyPrefixes.isEmpty || b.keyPrefixes.any (k.startsWith ·))
      let hit := keys.filter ownLits.contains
      out := out ++ s!"  - names the program data calls that these models answer ({ds.length} dispatchers, " ++
        s!"{keys.size} names): {short hit}\n"
  return out

/-- `#ledger thm₁ thm₂ ...`: the assumption ledger of each theorem (markdown). -/
elab "#ledger " ids:ident+ : command => do
  for id in ids do
    let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
    let s ← liftTermElabM <| ledger n
    logInfo m!"{s}"

end EquivLean.Ledger
