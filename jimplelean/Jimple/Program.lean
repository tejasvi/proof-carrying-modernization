/-
  Jimple/Program.lean

  Class hierarchy: the JDK prelude, class lookup, subtyping (JVMS 4.10 / checkcast rules),
  field resolution (JVMS 5.4.3.2) and method selection for `virtualinvoke`,
  `interfaceinvoke`, `specialinvoke` and `staticinvoke` (JVMS 5.4.3.3, 5.4.6),
  including interface default methods.
-/
import Jimple.Prelude

namespace Jimple

namespace Program

/-- Program classes take precedence over the prelude. -/
def lookup (P : Program) (c : ClassName) : Option ClassDecl :=
  match P.findClass c with
  | some d => some d
  | none => preludeFind c

def isProgClass (P : Program) (c : ClassName) : Bool := (P.findClass c).isSome

/-- Fuel bound for hierarchy walks over application classes (hierarchies are acyclic in
    well-formed programs, so walks stop at their roots; library ancestry is precomputed). A
    constant: computing the number of classes would make every lookup traverse the class list. -/
def fuel (_ : Program) : Nat := 4096

/-- All supertypes of `c` (reflexive, with repetitions); `none` if the hierarchy mentions
    an unknown (phantom) class or is cyclic. -/
def supersN (P : Program) : Nat → ClassName → Option (List ClassName)
  | 0, _ => none
  | n + 1, c =>
    match P.findClass c with
    | some d =>
      (d.super.toList ++ d.interfaces).foldlM
        (fun acc p => (fun s => acc ++ s) <$> P.supersN n p) [c]
    | none => preludeAncestors c

def supers (P : Program) (c : ClassName) : Option (List ClassName) := P.supersN P.fuel c

def isSubclass (P : Program) (c d : ClassName) : Option Bool :=
  (P.supers c).map (·.contains d)

/-- Assignment compatibility of runtime types (`checkcast`/`instanceof`/`aastore`). -/
def subtype (P : Program) : JType → JType → Option Bool
  | .null, t => some t.isRef
  | .cls c, .cls d => P.isSubclass c d
  | .array _, .cls d =>
    some (d == "java.lang.Object" || d == "java.lang.Cloneable" || d == "java.io.Serializable")
  | .array (.prim p), .array (.prim q) => some (p == q)
  | .array (.prim _), .array _ => some false
  | .array _, .array (.prim _) => some false
  | .array s, .array t => P.subtype s t
  | _, _ => some false

/-- Resolve a field reference to its declaring class (JVMS 5.4.3.2: the class itself,
    then its superinterfaces, then its superclass). -/
def resolveFieldN (P : Program) : Nat → ClassName → String → Option (ClassName × FieldDecl)
  | 0, _, _ => none
  | n + 1, c, name =>
    match P.lookup c with
    | none => none
    | some d =>
      match d.fields.find? (·.name == name) with
      | some f => some (c, f)
      | none =>
        match d.interfaces.findSome? (fun i => P.resolveFieldN n i name) with
        | some r => some r
        | none => d.super.bind (fun s => P.resolveFieldN n s name)

def resolveField (P : Program) (f : FieldSig) : Option (ClassName × FieldDecl) :=
  P.resolveFieldN P.fuel f.cls f.name

/-- Instance fields of a class and all its superclasses, with their types. -/
def instanceFieldsN (P : Program) : Nat → ClassName → List (FieldKey × JType)
  | 0, _ => []
  | n + 1, c =>
    match P.lookup c with
    | none => []
    | some d =>
      (d.fields.filter (!·.isStatic)).map (fun f => ((c, f.name), f.ty)) ++
        (match d.super with | some s => P.instanceFieldsN n s | none => [])

def instanceFields (P : Program) (c : ClassName) : List (FieldKey × JType) :=
  P.instanceFieldsN P.fuel c

/-- The instance fields that `d`, the declaration of class `c`, declares itself. -/
def ClassDecl.ownFields (d : ClassDecl) (c : ClassName) : List (FieldKey × JType) :=
  (d.fields.filter (!·.isStatic)).map (fun f => ((c, f.name), f.ty))

/-- The instance fields class `c` declares itself (inherited ones are declared by its
    supertypes). -/
def declaredFields (P : Program) (c : ClassName) : List (FieldKey × JType) :=
  match P.lookup c with
  | some d => ClassDecl.ownFields d c
  | none => []

/-- The method `name` (with parameter types `ps`, if given) of application class `cls`. -/
def method? (P : Program) (cls name : String) (ps : Option (List JType) := none) : Option MethodRef :=
  (P.findClass cls).bind fun d =>
    (d.methods.find? fun m => m.name == name && ps.all (m.params == ·)).map (⟨cls, ·⟩)

/-- `method?`, for statements about a method known to exist. -/
def method! (P : Program) (cls name : String) (ps : Option (List JType) := none) : MethodRef :=
  (P.method? cls name ps).getD ⟨cls, default⟩

/-- The application classes that are subclasses of `d` (reflexive). In a JVM state an object
    whose class is a subclass of an application class is an instance of one of these. -/
def progSubclasses (P : Program) (d : ClassName) : List ClassName :=
  (P.index.toList.filter (fun cd => P.isSubclass cd.name d == some true)).map (·.name)

/-- Declared type of a static field (`void` for an unknown field). -/
def staticFieldType (P : Program) (k : FieldKey) : JType :=
  match P.lookup k.1 with
  | some d => match d.fields.find? (fun f => f.name == k.2 && f.isStatic) with
    | some f => f.ty
    | none => .void
  | none => .void

/-- Result of method selection. -/
inductive Target where
  /-- a Jimple method body (or abstract/native declaration) of an application class -/
  | jimple (m : MethodRef)
  /-- behaviour provided by the library model, found starting from library class `cls` -/
  | native (cls : ClassName)
  /-- selection failed (`AbstractMethodError`, phantom class, ...) -/
  | none (why : String)
  deriving Inhabited

def ClassDecl.findMethod (d : ClassDecl) (sub : SubSig) (static : Bool) : Option MethodDecl :=
  d.methods.find? (fun m => m.sub == sub && m.mods.isStatic == static)

/-- The static initializer declared by `d`. -/
def ClassDecl.findClinit (d : ClassDecl) : Option MethodDecl :=
  d.methods.find? (·.name == "<clinit>")

/-- Whether `d` declares a non-abstract, non-static method other than `<clinit>` (for an
    interface: a default method). -/
def ClassDecl.hasDefaultMethods (d : ClassDecl) : Bool :=
  d.methods.any (fun m => !m.mods.isStatic && m.body.isSome && m.name != "<clinit>")

/-! ### Class shapes: declarations without method bodies

A proof about one method depends on its own body and on the *shape* of the classes it uses
(names, hierarchy, fields, method signatures and modifiers, which methods have a body), not on
the other methods' bodies: `Shapes` (`Jimple/Verify.lean`) states the facts in these terms. -/

/-- The placeholder body of an erased method. -/
def _root_.Jimple.Body.erased : Body := { locals := [], stmts := #[], traps := [] }

/-- A method declaration without its body (`Body.erased` in place of a body). -/
def _root_.Jimple.MethodDecl.erase (m : MethodDecl) : MethodDecl :=
  { m with body := m.body.map fun _ => Body.erased }

/-- A class declaration without method bodies. -/
def _root_.Jimple.ClassDecl.erase (d : ClassDecl) : ClassDecl :=
  { d with methods := d.methods.map MethodDecl.erase }

theorem findMethod_erase (d : ClassDecl) (sub : SubSig) (static : Bool) :
    ClassDecl.findMethod d.erase sub static =
      (ClassDecl.findMethod d sub static).map MethodDecl.erase := by
  unfold ClassDecl.findMethod Jimple.ClassDecl.erase
  rw [List.find?_map]
  rfl

theorem _root_.Jimple.MethodDecl.erase_body_isSome (m : MethodDecl) : m.erase.body.isSome = m.body.isSome := by
  cases h : m.body <;> simp [Jimple.MethodDecl.erase, h]

theorem findClinit_erase (d : ClassDecl) :
    ClassDecl.findClinit d.erase = (ClassDecl.findClinit d).map MethodDecl.erase := by
  unfold ClassDecl.findClinit Jimple.ClassDecl.erase
  rw [List.find?_map]
  rfl

theorem hasDefaultMethods_erase (d : ClassDecl) :
    ClassDecl.hasDefaultMethods d.erase = ClassDecl.hasDefaultMethods d := by
  unfold ClassDecl.hasDefaultMethods Jimple.ClassDecl.erase
  rw [List.any_map]
  congr 1
  funext m
  simp only [Function.comp, MethodDecl.erase_body_isSome]
  rfl

/-- A method that the shape `s` of the class lacks is missing from the class. -/
theorem findMethod_none_of_erase {d s : ClassDecl} {sub : SubSig} {static : Bool}
    (h : d.erase = s) (hs : ClassDecl.findMethod s sub static = none) :
    ClassDecl.findMethod d sub static = none := by
  rw [← h, findMethod_erase] at hs
  simpa using hs

/-- The static initializer of the shape `s` (or its absence) is that of the class. -/
theorem findClinit_none_of_erase {d s : ClassDecl} (h : d.erase = s)
    (hs : ClassDecl.findClinit s = none) : ClassDecl.findClinit d = none := by
  rw [← h, findClinit_erase] at hs
  simpa using hs

theorem findClinit_some_of_erase {d s : ClassDecl} {y : MethodDecl} (h : d.erase = s)
    (hs : ClassDecl.findClinit s = some y) :
    ∃ x, ClassDecl.findClinit d = some x ∧ x.erase = y := by
  rw [← h, findClinit_erase] at hs
  cases hx : ClassDecl.findClinit d with
  | none => rw [hx] at hs; cases hs
  | some x => rw [hx] at hs; exact ⟨x, rfl, Option.some.inj hs⟩

/-- A method of the shape `s` is a method of the class, whose erasure it is. -/
theorem findMethod_some_of_erase {d s : ClassDecl} {sub : SubSig} {static : Bool} {y : MethodDecl}
    (h : d.erase = s) (hs : ClassDecl.findMethod s sub static = some y) :
    ∃ x, ClassDecl.findMethod d sub static = some x ∧ x.erase = y := by
  rw [← h, findMethod_erase] at hs
  cases hx : ClassDecl.findMethod d sub static with
  | none => rw [hx] at hs; cases hs
  | some x => rw [hx] at hs; exact ⟨x, rfl, Option.some.inj hs⟩

/-- Walk the superclass chain from `c` looking for a method with subsignature `sub`
    among application classes; stops at the first library class. -/
def chainN (P : Program) : Nat → ClassName → SubSig → Bool → Target
  | 0, _, _, _ => .none "hierarchy too deep"
  | n + 1, c, sub, static =>
    match P.findClass c with
    | none => if isLibClass c then .native c else .none s!"unknown class {c}"
    | some d =>
      match ClassDecl.findMethod d sub static with
      | some m => .jimple ⟨c, m⟩
      | none =>
        match d.super with
        | some s => P.chainN n s sub static
        | none => .none s!"no method {sub.name} in {c}"

/-- Default methods (JVMS 5.4.3.3/5.4.6): among the application superinterfaces of `c` that
    declare an instance method with subsignature `sub` (abstract redeclarations included),
    keep the maximally specific ones (no other candidate is declared in a subinterface); the
    selected method is the unique non-abstract one among them, if exactly one exists. -/
def defaultMethod (P : Program) (c : ClassName) (sub : SubSig) : Option MethodRef :=
  match P.supers c with
  | none => none
  | some cs =>
    let cands : List (ClassName × MethodDecl) := cs.eraseDups.filterMap fun i =>
      match P.findClass i with
      | some d =>
        if d.isInterface then (ClassDecl.findMethod d sub false).map (i, ·) else none
      | none => none
    let maxs := cands.filter fun (i, _) =>
      !cands.any fun (j, _) => j != i && P.isSubclass j i == some true
    match maxs.filter (·.2.body.isSome) with
    | [(i, m)] => some ⟨i, m⟩
    | _ => none

/-- Method selection for `virtualinvoke`/`interfaceinvoke` on an object of runtime class `c`. -/
def selectVirtual (P : Program) (c : ClassName) (sub : SubSig) : Target :=
  match P.chainN P.fuel c sub false with
  | .jimple m =>
    if m.decl.mods.isAbstract then
      match P.defaultMethod c sub with
      | some dm => .jimple dm
      | none => .none s!"AbstractMethodError: {sub.name}"
    else .jimple m
  | .native lc =>
    match P.defaultMethod c sub with
    | some dm => .jimple dm
    | none => .native lc
  | .none why =>
    match P.defaultMethod c sub with
    | some dm => .jimple dm
    | none => .none why

/-- Method resolution for `specialinvoke` (constructors, private methods, `super` calls):
    the named class, then its superclasses, then default methods. -/
def selectSpecial (P : Program) (m : MethodSig) : Target :=
  match P.chainN P.fuel m.cls m.sub false with
  | .none why =>
    match P.defaultMethod m.cls m.sub with
    | some dm => .jimple dm
    | none => .none why
  | t => t

/-- Method resolution for `staticinvoke`. -/
def selectStatic (P : Program) (m : MethodSig) : Target := P.chainN P.fuel m.cls m.sub true

/-- `sig` names a static method declared by its class: it is called by `staticinvoke`, never
    virtually, so its contract owes nothing to subclasses. -/
def staticDecl (P : Program) (sig : MethodSig) : Bool :=
  match P.findClass sig.cls with
  | some d => (ClassDecl.findMethod d sig.sub true).isSome
  | none => false

end Program

end Jimple
