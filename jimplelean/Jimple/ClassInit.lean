/-
  Jimple/ClassInit.lean

  Class initialization (JVMS 5.5): the initialization order of an application class
  (superclasses, superinterfaces with default methods), running the static initializers, the
  erroneous state and `NoClassDefFoundError`. Below `Native`, so that library models can
  initialize a class before calling its (bytecode) static methods.
-/
import Jimple.Monad

namespace Jimple

inductive InitOut where
  | ok (σ : State)
  | thr (e : Addr) (σ : State)
  | wrong (msg : String)
  deriving Inhabited

/-- The static initializer of an application class. -/
def Program.clinitOf (P : Program) (c : ClassName) : Option MethodDecl :=
  (P.findClass c).bind Program.ClassDecl.findClinit

/-- Whether an application interface declares a non-abstract, non-static method (such
    interfaces are initialized with their implementing classes, JVMS 5.5 step 7). -/
def Program.hasDefaults (P : Program) (i : ClassName) : Bool :=
  match P.findClass i with
  | some d => d.isInterface && Program.ClassDecl.hasDefaultMethods d
  | none => false

/-- Superinterfaces (with default methods) in JVMS 5.5 order: for each direct interface, its
    superinterfaces first, then the interface itself. -/
def Program.ifaceInitOrderN (P : Program) : Nat → List ClassName → List ClassName
  | 0, _ => []
  | n + 1, is => is.flatMap fun i =>
    match P.findClass i with
    | some d => P.ifaceInitOrderN n d.interfaces ++ (if P.hasDefaults i then [i] else [])
    | none => []

/-- Initialization order of `c`: superclass chain (topmost first) with, for each class, the
    superinterfaces that declare default methods, then the class itself; each with its
    `<clinit>`. -/
def Program.superChainN (P : Program) : Nat → ClassName → List (ClassName × Option MethodDecl)
  | 0, _ => []
  | n + 1, c =>
    match P.findClass c with
    | none => []
    | some d =>
      if d.isInterface then [(c, P.clinitOf c)]
      else
        (match d.super with | some s => P.superChainN n s | none => []) ++
          (P.ifaceInitOrderN P.fuel d.interfaces).map (fun i => (i, P.clinitOf i)) ++ [(c, P.clinitOf c)]

def Program.initChain (P : Program) (c : ClassName) : List (ClassName × Option MethodDecl) :=
  (P.superChainN P.fuel c).foldl (fun acc p => if acc.any (·.1 == p.1) then acc else acc ++ [p]) []

def clinitSig (c : ClassName) : MethodSig := ⟨c, .void, "<clinit>", []⟩

/-- Run the static initializers of `pending` (already marked in progress), topmost first;
    a failing initializer marks the remaining classes erroneous and throws (wrapped in
    `ExceptionInInitializerError` unless it is an `Error`). -/
def runClinits (P : Program) : List (ClassName × Option MethodDecl) → State → Res InitOut
  | [], σ => .ret (.ok σ)
  | (c, cl) :: rest, σ =>
    match cl with
    | none => runClinits P rest σ
    | some m =>
      .call (clinitSig c) (.method ⟨c, m⟩) [] σ fun out =>
        match out with
        | .normal _ σ' => runClinits P rest σ'
        | .exc e σ' =>
          let σ'' := ((c, cl) :: rest).foldl (fun σ p => σ.setInit p.1 .failed) σ'
          match σ''.heap e with
          | some o =>
            match P.subtype o.ty (.cls "java.lang.Error") with
            | some true => .ret (.thr e σ'')
            | some false =>
              let (w, σ3) := mkExc "java.lang.ExceptionInInitializerError" none σ''
              let σ4 := match σ3.heap w with
                | some (.plain wc fs) =>
                  σ3.setObj w (.plain wc (Fields.set fs ("java.lang.Throwable", "cause") (.ref e)))
                | _ => σ3
              .ret (.thr w σ4)
            | none => .ret (.wrong "exception class unknown")
          | none => .ret (.wrong "dangling exception")
        | .wrong msg => .ret (.wrong msg)

/-- Initialize application class `c` (and its superclasses) if necessary. -/
def ensureInit (P : Program) (c : ClassName) (σ : State) : Res InitOut :=
  if !P.isProgClass c then .ret (.ok σ)
  else
    match σ.initOf c with
    | .done => .ret (.ok σ)
    | .failed => .ret (match throwNew "java.lang.NoClassDefFoundError"
        (some (JStr.ofString ("Could not initialize class " ++ c))) σ with
        | .thr e σ => .thr e σ
        | _ => .wrong "unreachable")
    | .none =>
      let chain := P.initChain c
      if chain.any (fun p => σ.initOf p.1 == .failed) then
        .ret (match throwNew "java.lang.NoClassDefFoundError"
            (some (JStr.ofString ("Could not initialize class " ++ c))) σ with
          | .thr e σ => .thr e (σ.setInit c .failed)
          | _ => .wrong "unreachable")
      else
        let pending := chain.filter (fun p => σ.initOf p.1 == .none)
        let σ1 := pending.foldl (fun σ p => σ.setInit p.1 .done) σ
        runClinits P pending σ1

def initThen (P : Program) (c : ClassName) (σ : State) (k : State → Res EvOut) : Res EvOut :=
  (ensureInit P c σ).bind fun r =>
    match r with
    | .ok σ => k σ
    | .thr e σ => .ret (.thr e σ)
    | .wrong m => .ret (.wrong m)

end Jimple
