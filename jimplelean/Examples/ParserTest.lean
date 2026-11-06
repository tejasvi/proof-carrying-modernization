/-
  Examples/ParserTest.lean

  Tests of `Jimple/Parser.lean` and `jimple_import`:
  * the Soot 4.7.1 output in `probe/java1/jimple` and `probe/java2/jimple` (10 classes):
    method, statement and trap counts (cross-checked against an independent line count of
    the files), specific statements and constants, and `main` run by the interpreter of
    `Jimple/Interp.lean` against the JVM's output;
  * a synthetic class with the constructs the probes do not contain, and error messages;
  * Java line numbers from Soot's line number tags (`examples_java/hello/jimple_lines`).
-/
import Jimple.Import
import Jimple.Interp

open Jimple

jimple_import "examples_java/hello/jimple" as Java1
jimple_import "examples_java/probe/jimple" as Java2
jimple_import "examples_java/hello/jimple_lines" as JavaL

namespace ParserTest

/-- For each class: its name, its number of methods, and for each method with a body
    `(name(params), #statements, #traps)`. -/
def summary (p : Program) : List (String × Nat × List (String × Nat × Nat)) :=
  p.classes.map fun c =>
    (c.name, c.methods.length, c.methods.filterMap fun m =>
      m.body.map fun b => (s!"{m.name}({Parser.paramsStr m.params})", b.stmts.size, b.traps.length))

#eval summary Java1.prog
#guard summary Java1.prog ==
  [("Hello", 5, [("<init>()", 3, 0), ("sum(int[])", 10, 0), ("total(java.util.List)", 11, 0),
                 ("safeDiv(int,int)", 18, 4), ("main(java.lang.String[])", 29, 0)]),
   ("Item", 2, [("<init>(java.math.BigDecimal,int)", 7, 0), ("price()", 7, 0)]),
   ("Priced", 1, [])]

#eval summary Java2.prog
#guard summary Java2.prog ==
  [("Base", 3, [("<init>()", 3, 0), ("g()", 4, 0)]),
   ("Color", 5, [("values()", 4, 0), ("valueOf(java.lang.String)", 4, 0),
                 ("<init>(java.lang.String,int)", 5, 0), ("$values()", 6, 0), ("<clinit>()", 9, 0)]),
   ("Derived", 2, [("<init>()", 3, 0), ("f(int)", 4, 0)]),
   ("Probe$1", 1, [("<clinit>()", 11, 1)]),
   ("Probe$lambda_lam_0__1", 3,
     [("bootstrap$()", 3, 0), ("<init>()", 3, 0), ("apply(java.lang.Object)", 5, 0)]),
   ("Probe", 10, [("<init>()", 3, 0), ("ops(int,int,long,float,double,byte,short,char)", 76, 0),
                  ("sw(int,java.lang.String)", 35, 0), ("misc(java.lang.Object)", 26, 3),
                  ("concat11(java.lang.String,int)", 4, 0), ("lam(java.util.List)", 16, 0),
                  ("col(Color)", 7, 0), ("main(java.lang.String[])", 10, 0),
                  ("lambda$lam$0(java.lang.Integer)", 5, 0), ("<clinit>()", 11, 0)]),
   ("Shape", 2, [("kind()", 2, 0)])]

/-! The class constants refer to the body constants by name. -/

#print Java1.Item
example : Java1.Item.methods.map (·.body) =
    [some Java1.Item.«<init>(java.math.BigDecimal,int)», some Java1.Item.«price()»] := rfl

/-! `Hello.safeDiv`: four traps, each handler is a `@caughtexception` identity statement. -/

#eval Java1.Hello.«safeDiv(int,int)».traps
#guard Java1.Hello.«safeDiv(int,int)».traps.length == 4
#guard Java1.Hello.«safeDiv(int,int)».traps.all fun t =>
  match Java1.Hello.«safeDiv(int,int)».stmts[t.handler]? with
  | some (.identity _ .caught) => true
  | _ => false

/-! `Probe.sw`: one tableswitch, on the cases 1, 2, 3. -/

def swTables : List (Int × List Label × Label) :=
  Java2.Probe.«sw(int,java.lang.String)».stmts.toList.filterMap fun
    | .tableSwitch _ low ts d => some (low, ts, d)
    | _ => none

#eval swTables
#guard swTables.map (fun (low, ts, _) => (low, ts.length)) == [(1, 3)]

/-! `Probe.<clinit>`: the constants stored into the static fields. -/

def clinitConsts : List (String × Const) :=
  Java2.Probe.«<clinit>()».stmts.toList.filterMap fun
    | .assign (.ref (.staticField f)) (.imm (.const c)) => some (f.name, c)
    | _ => none

#eval clinitConsts
#guard clinitConsts.lookup "s" == some (.str "a\"b\\c\n\té")
#guard clinitConsts.lookup "dd" == some (.double (JFloat.decimalToDouble false 225 8))
#guard clinitConsts.lookup "ff" == some (.float (JFloat.decimalToFloat false 15 (-1)))
#guard clinitConsts.lookup "BIG" == some (.long 123456789012)
#guard clinitConsts.lookup "c" == some (.int 120)

/-! End to end: `main` run by the interpreter, compared with the output of `java Hello` and
`java Probe` on the compiled probe classes. -/

/-- info: "3.75\n-1 1\n" -/
#guard_msgs in
#eval Jimple.runMainOutput Java1.prog "Hello"

/-- info: "91\n" -/
#guard_msgs in
#eval Jimple.runMainOutput Java2.prog "Probe"

/-! ## Constructs not in the probes -/

def weirdSrc : String := r#"/* block
   comment */
// line comment
@Deprecated
public abstract class pkg.'enum'.Weird extends java.lang.'annotation'.Foo implements A, b.C
{
    @Visibility(x = 1, y = { 2, 3 })
    static volatile transient 'long' 'from';

    public native 'int' nat('int', @Foo 'double'[][]) throws java.io.IOException, E2;

    synchronized strictfp 'void' m(unknown, null_type)
    {
        unknown u;
        'int' i, $j;
        'long' l;
        'float' f;
        'double' d;
        java.lang.Object o;
        java.lang.String s;
        'int'[][][] arr;
        pkg.'enum'.Weird w;

        w := @this: pkg.'enum'.Weird;
        u := @parameter0: ;
        i = 2147483647;
        i = -2147483648;
        i = 017;
        i = 0xFFFFFFFF;
        i = 65B;
        l = -9223372036854775808L;
        l = 0xFFFFFFFFFFFFFFFFL;
        f = #InfinityF;
        f = #-InfinityF;
        f = #NaNF;
        f = -0.0F;
        d = #Infinity;
        d = -#Infinity;
        d = #NaN;
        d = 1.0E-5;
        d = 4.9E-324;
        d = 1.7976931348623157E308;
        s = "😀";
        s = "\ud83d";
        s = "\'\.\#\ \r\b\f";
        o = class "[I";
        o = methodhandle: "REF_INVOKE_STATIC" <A: 'int' f('int')>;
        o = methodhandle: "REF_GET_FIELD" <A: 'int' fld>;
        arr = newmultiarray ('int')[3][][];
        breakpoint;
        nop;
        if i == -1 goto label1;
        $j = i cmpl i;
        tableswitch(i)
        {
            case -1: goto label1;
            case 0: goto label2;
            default: goto label3;
        };
        lookupswitch(i)
        {
            case -2: goto label1;
            case 5: goto label2;
            default: goto label1;
        };
        w.<pkg.'enum'.Weird: 'long' 'from'> = l;
        <pkg.'enum'.Weird: 'long' 'from'> = 3L;
        $j = interfaceinvoke o.<b.C: 'int' 'to'('int')>(-7);
        o = dynamicinvoke "apply" <java.util.function.Function ()>() <java.lang.invoke.LambdaMetafactory: java.lang.invoke.CallSite metafactory(java.lang.invoke.MethodHandles$Lookup,java.lang.String,java.lang.invoke.MethodType,java.lang.invoke.MethodType,java.lang.invoke.MethodHandle,java.lang.invoke.MethodType)>(methodtype: java.lang.Object __METHODTYPE__(java.lang.Object), methodhandle: "REF_INVOKE_STATIC" <Probe: java.lang.Integer lambda$lam$0(java.lang.Integer)>, methodtype: 'int' __METHODTYPE__('int'));
     label1:
        ret i;
     label2:
        return;
     label3:
        catch java.lang.Throwable from label1 to label3 with label2;
    }
}
"#

def weird : ClassDecl :=
  match Parser.parseClass weirdSrc with
  | .ok c => c
  | .error e => panic! e

#guard weird.name == "pkg.enum.Weird" && weird.isAbstract && !weird.isInterface &&
  weird.super == some "java.lang.annotation.Foo" && weird.interfaces == ["A", "b.C"]
#guard weird.fields == [{ name := "from", ty := .prim .long, isStatic := true }]
#guard (weird.methods.map fun m =>
    (m.name, m.params, m.throws, m.mods.isNative, m.mods.isSynchronized, m.body.isSome)) ==
  [("nat", [.prim .int, .array (.array (.prim .double))], ["java.io.IOException", "E2"], true,
    false, false),
   ("m", [.unknown, .null], [], false, true, true)]

def wm : Body := ((weird.methods.find? (·.name == "m")).bind (·.body)).get!

#eval wm.stmts
#guard wm.locals.map (·.1) == ["u", "i", "$j", "l", "f", "d", "o", "s", "arr", "w"]
#guard wm.stmts.size == 38
#guard wm.stmts[0]! == .identity 9 (.this (.cls "pkg.enum.Weird"))
#guard wm.stmts[1]! == .identity 0 (.param 0 .unknown)

/-- the constant assigned by statement `i` -/
def rhs (i : Nat) : Option Const :=
  match wm.stmts[i]? with
  | some (.assign _ (.imm (.const c))) => some c
  | _ => none

#guard (List.range 22).filterMap (fun i => (rhs (i + 2)).map (i + 2, ·)) ==
  [(2, .int 2147483647), (3, .int (-2147483648)), (4, .int 15), (5, .int (-1)), (6, .int 65),
   (7, .long (-9223372036854775808)), (8, .long (-1)),
   (9, .float JFloat.posInf32), (10, .float JFloat.negInf32), (11, .float JFloat.nan32),
   (12, .float 0x80000000),
   (13, .double JFloat.posInf64), (14, .double JFloat.negInf64), (15, .double JFloat.nan64),
   (16, .double 0x3ee4f8b588e368f1), (17, .double 1), (18, .double 0x7fefffffffffffff),
   (19, .str "😀"), (20, .strUnits [0xD83D]), (21, .str "'.# \r\x08\x0c"),
   (22, .clazz "[I"), (23, .methodHandle "REF_INVOKE_STATIC <A: int f(int)>")]
#guard rhs 24 == some (.methodHandle "REF_GET_FIELD <A: int fld>")
#guard wm.stmts[25]! == .assign (.loc 8) (.newMultiArray (.prim .int) [.const (.int 3)] 3)
#guard wm.stmts[26]! == .breakpoint && wm.stmts[27]! == .nop
#guard wm.stmts[28]! == .ifGoto .eq (.loc 1) (.const (.int (-1))) 36
#guard wm.stmts[29]! == .assign (.loc 2) (.binop .cmpl (.loc 1) (.loc 1))
#guard wm.stmts[30]! == .tableSwitch (.loc 1) (-1) [36, 37] 38
#guard wm.stmts[31]! == .lookupSwitch (.loc 1) [(-2, 36), (5, 37)] 36
#guard wm.stmts[32]! == .assign (.ref (.instField 9 ⟨"pkg.enum.Weird", .prim .long, "from"⟩)) (.imm (.loc 3))
#guard wm.stmts[33]! == .assign (.ref (.staticField ⟨"pkg.enum.Weird", .prim .long, "from"⟩)) (.imm (.const (.long 3)))
#guard wm.stmts[34]! == .assign (.loc 2)
  (.invoke (.inst .interface 6 ⟨"b.C", .prim .int, "to", [.prim .int]⟩ [.const (.int (-7))]))
#guard match wm.stmts[35]! with
  | .assign (.loc 6) (.invoke (.dynamic "apply" (.cls "java.util.function.Function") [] [] bsm args)) =>
    bsm.name == "metafactory" && args ==
      [.const (.methodHandle "methodtype: java.lang.Object __METHODTYPE__(java.lang.Object)"),
       .const (.methodHandle "REF_INVOKE_STATIC <Probe: java.lang.Integer lambda$lam$0(java.lang.Integer)>"),
       .const (.methodHandle "methodtype: int __METHODTYPE__(int)")]
  | _ => false
#guard wm.stmts[36]! == .ret 1 && wm.stmts[37]! == .returnVoid
-- `label3` ends the body, so it denotes `stmts.size`
#guard wm.traps == [{ exc := "java.lang.Throwable", first := 36, last := 38, handler := 37 }]

/-! Method handle constants name fields and methods without quoting keywords (the getters of a
record with components `from` and `to`, as `javac` 17 and Soot print them). -/

def recordSrc : String := r#"class A extends java.lang.Record
{
    public final java.lang.String toString()
    {
        A r0;
        java.lang.String $r1;

        r0 := @this: A;

        $r1 = dynamicinvoke "toString" <java.lang.String (A)>(r0) <java.lang.runtime.ObjectMethods: java.lang.Object bootstrap(java.lang.invoke.MethodHandles$Lookup,java.lang.String,java.lang.invoke.TypeDescriptor,java.lang.Class,java.lang.String,java.lang.invoke.MethodHandle[])>(class "LA;", "from;to", methodhandle: "REF_GET_FIELD" <A: B from>, methodhandle: "REF_GET_FIELD" <A: 'int' to>);

        return $r1;
    }
}
"#

#guard match Parser.parseClass recordSrc with
  | .ok c => (c.methods.head?.bind (·.body)).map (fun b => b.stmts.toList.filterMap fun
      | .assign _ (.invoke (.dynamic _ _ _ _ _ bs)) => some bs
      | _ => none) ==
    some [[.const (.clazz "LA;"), .const (.str "from;to"),
           .const (.methodHandle "REF_GET_FIELD <A: B from>"),
           .const (.methodHandle "REF_GET_FIELD <A: int to>")]]
  | .error _ => false

/-! ## Errors carry line numbers -/

def errOf (src : String) : String :=
  match Parser.parseClass src with
  | .ok _ => "no error"
  | .error e => e

#guard errOf "class A extends B\n{\n    'void' m()\n    {\n        x = 1;\n    }\n}\n" ==
  "line 5: undeclared local 'x'"
#guard errOf "class A extends B\n{\n    'void' m()\n    {\n        goto nowhere;\n    }\n}\n" ==
  "line 5: undefined label 'nowhere'"
#guard errOf "class A extends B\n{\n    'void' m('int')\n    {\n        'int' i;\n\n        i := @parameter0: 'int';\n        tableswitch(i)\n        {\n            case 1: goto l1;\n            case 3: goto l1;\n            default: goto l1;\n        };\n     l1:\n        return;\n    }\n}\n" ==
  "line 8: tableswitch cases must be consecutive and ascending"
#guard errOf "class A extends B\n{\n    'void' m()\n    {\n        java.lang.String s;\n\n        s = \"abc;\n    }\n}\n" ==
  "line 7: unterminated string constant"
#guard errOf "class A extends B\n{\n    'void' m()\n    {\n        'int' i;\n\n        i = ;\n    }\n}\n" ==
  "line 7: expected a local or a constant, found ';'"
#guard errOf "class A extends B\n{\n    'void' m()\n    {\n        'int' i;\n\n        i = 2147483649;\n    }\n}\n" ==
  "line 7: integer constant out of range"
#guard errOf "class A extends B\n{\n    'void' m()\n    {\n        'int' i, i;\n    }\n}\n" ==
  "line 5: local 'i' declared twice"
#guard errOf "class A extends B\n{\n}\n}\n" == "line 4: expected end of file, found '}'"

/-! ## Java line numbers

`examples_java/hello/jimple_lines` is Soot's output for the classes of `examples_java/hello`
with `-keep-line-number -print-tags`, which prints the line number tag of each statement as a
comment `/*12*/` after it. `Body.lines` maps statement indices to Java lines (`0`: no tag, as
for identity statements). -/

/-- `(Java line, statement)` for each statement of a body. -/
def withLines (b : Body) : List (Nat × Stmt) := b.lines.toList.zip b.stmts.toList

#eval JavaL.Hello.«total(java.util.List)».lines
#guard JavaL.Hello.«sum(int[])».lines == #[0, 13, 13, 13, 13, 13, 13, 13, 13, 13]
#guard JavaL.Hello.«total(java.util.List)».lines == #[0, 15, 16, 16, 16, 16, 16, 16, 16, 16, 17]
#guard JavaL.Hello.«safeDiv(int,int)».lines ==
  #[0, 0, 20, 20, 20, 20, 20, 20, 20, 20, 20, 0, 20, 20, 20, 20, 20, 20]
-- parameter identity statements have no tag; the handlers' `@caughtexception` statements
-- have the line of the `try` statement
#guard withLines JavaL.Hello.«safeDiv(int,int)» |>.all fun
  | (l, .identity _ (.param ..)) => l == 0
  | (l, .identity _ .caught) => l == 20
  | _ => true
-- `main`: one line per statement, ending with the `return` of the closing brace (line 29)
#guard JavaL.Hello.«main(java.lang.String[])».lines.size == 29
#guard (withLines JavaL.Hello.«main(java.lang.String[])»).getLast? == some (29, .returnVoid)
#guard JavaL.Item.«<init>(java.math.BigDecimal,int)».lines == #[0, 0, 0, 8, 8, 8, 8]
-- the tags change nothing else
#guard JavaL.prog.classes.map (·.methods.map (·.body.map (·.stmts))) ==
  Java1.prog.classes.map (·.methods.map (·.body.map (·.stmts)))
-- without tags, `lines` stays empty
#guard Java1.prog.classes.all (·.methods.all (·.body.all (·.lines.isEmpty)))

end ParserTest
