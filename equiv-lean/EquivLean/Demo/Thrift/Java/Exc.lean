import EquivLean.Demo.Thrift.Java.Rv32L

/-!
# Thrift → Java (T4): allocating a `TProtocolException`

`new TProtocolException` allocates an object with the instance fields of the class and its
superclasses (`P.instanceFields`); on an abstract program the symbolic execution does not compute
them, so they are given here from the classes' declarations (`Contains`) and the library prelude
(`NoShadow`).
-/

open Jimple

namespace EquivLean.Demo.Thrift.Java

abbrev tpeC := EquivLean.Gen.ThriftJ.«org.apache.thrift.protocol.TProtocolException»
abbrev teC := EquivLean.Gen.ThriftJ.«org.apache.thrift.TException»

theorem lookup_prog {P : Program} {c : ClassName} {d : ClassDecl} (h : P.findClass c = some d) :
    P.lookup c = some d := by
  unfold Program.lookup; rw [h]

theorem lookup_lib {P : Program} {c : ClassName} {d : ClassDecl} (h : P.findClass c = none)
    (hp : preludeFind c = some d) : P.lookup c = some d := by
  unfold Program.lookup; rw [h]; exact hp

theorem ifN_step {P : Program} {n : Nat} {c s : ClassName} {d : ClassDecl} (h : P.lookup c = some d)
    (hs : d.super = some s) :
    P.instanceFieldsN (n + 1) c =
      (d.fields.filter (!·.isStatic)).map (fun f => ((c, f.name), f.ty)) ++ P.instanceFieldsN n s := by
  rw [Program.instanceFieldsN.eq_2, h]; simp only [hs]

theorem ifN_last {P : Program} {n : Nat} {c : ClassName} {d : ClassDecl} (h : P.lookup c = some d)
    (hs : d.super = none) :
    P.instanceFieldsN (n + 1) c = (d.fields.filter (!·.isStatic)).map (fun f => ((c, f.name), f.ty)) := by
  rw [Program.instanceFieldsN.eq_2, h]; simp only [hs, List.append_nil]

theorem instanceFields_tpe {P : Program} (hns : NoShadow P)
    (h1 : P.findClass "org.apache.thrift.protocol.TProtocolException" = some tpeC)
    (h2 : P.findClass "org.apache.thrift.TException" = some teC) :
    P.instanceFields "org.apache.thrift.protocol.TProtocolException" =
      [(("org.apache.thrift.protocol.TProtocolException", "type_"), .prim .int),
       (("java.lang.Throwable", "detailMessage"), .cls "java.lang.String"),
       (("java.lang.Throwable", "cause"), .cls "java.lang.Throwable")] := by
  have h3 : P.findClass "java.lang.Exception" = none := findClass_of_noShadow hns (by decide)
  have h4 : P.findClass "java.lang.Throwable" = none := findClass_of_noShadow hns (by decide)
  have h5 : P.findClass "java.lang.Object" = none := findClass_of_noShadow hns (by decide)
  have p3 : preludeFind "java.lang.Exception" = some { name := "java.lang.Exception", isInterface := false, isAbstract := false, super := some "java.lang.Throwable", interfaces := [], fields := [] } := rfl
  have p4 : preludeFind "java.lang.Throwable" = some { name := "java.lang.Throwable", isInterface := false, isAbstract := false, super := some "java.lang.Object", interfaces := ["java.io.Serializable"], fields := [{ name := "detailMessage", ty := (.cls "java.lang.String") }, { name := "cause", ty := (.cls "java.lang.Throwable") }] } := rfl
  have p5 : preludeFind "java.lang.Object" = some { name := "java.lang.Object", isInterface := false, isAbstract := false, super := none, interfaces := [], fields := [] } := rfl
  rw [show P.instanceFields "org.apache.thrift.protocol.TProtocolException" =
      P.instanceFieldsN (4091 + 1 + 1 + 1 + 1 + 1) "org.apache.thrift.protocol.TProtocolException" from rfl,
    ifN_step (lookup_prog h1) rfl, ifN_step (lookup_prog h2) rfl, ifN_step (lookup_lib h3 p3) rfl,
    ifN_step (lookup_lib h4 p4) rfl, ifN_last (lookup_lib h5 p5) rfl]
  rfl

theorem isSubclass_exc_throwable {P : Program} (hns : NoShadow P) :
    P.isSubclass "java.lang.Exception" "java.lang.Throwable" = some true := by
  have hf : P.findClass "java.lang.Exception" = none := findClass_of_noShadow hns (by decide)
  unfold Program.isSubclass Program.supers
  rw [show Program.fuel P = 4095 + 1 from rfl, supersN_succ_eq, hf]
  rfl

/-- `super(message)` of an exception class below `java.lang.Exception`: the library constructor
`Exception(String)` sets the message and the cause (the exception itself). -/
theorem ctorCall_exc_str {P : Program} (hns : NoShadow P) (a : Addr) (c : ClassName)
    (fs : List (FieldKey × Value)) (r : Addr) (σ : State) :
    Native.ctorCall P ⟨"java.lang.Exception", .void, "<init>", [.cls "java.lang.String"]⟩ a (.plain c fs)
        [.ref r] σ =
      some (Native.okVoid (σ.setObj a (.plain c (Fields.set (Fields.set fs ("java.lang.Throwable", "detailMessage")
        (.ref r)) ("java.lang.Throwable", "cause") (.ref a))))) := by
  have h := isSubclass_exc_throwable hns
  have e : Native.ctorCall P ⟨"java.lang.Exception", .void, "<init>", [.cls "java.lang.String"]⟩ a
      (.plain c fs) [.ref r] σ =
      (if (P.isSubclass "java.lang.Exception" "java.lang.Throwable" == some true) = true ∧
          isLibClass "java.lang.Exception" = true then
        some (Native.okVoid (σ.setObj a (.plain c (Fields.set (Fields.set fs ("java.lang.Throwable", "detailMessage")
          (.ref r)) ("java.lang.Throwable", "cause") (.ref a)))))
       else none) := rfl
  rw [e, h]
  rfl

end EquivLean.Demo.Thrift.Java
