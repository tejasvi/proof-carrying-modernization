-- Copied from JimpleLean (frozen snapshot ~/jimplelean_work/snapshots/JimpleLean-20261025T2312Z,
-- Examples/CardDemo/Cbact03cRun.lean); proved by JimpleLean's own session.  Only the imports, the
-- program (`C3`, the same Jimple files, is equiv-lean's generated
-- `EquivLean.Modernize.Cbact03c.Java.Gen`) and the namespace differ (tools/modernize/import_jl.py).
/-
  Examples/CardDemo/Cbact03cRun.lean

  `Cbact03c.run(CardXrefRecord[])`, the read loop of CBACT03C as translated to Java: the list
  `displays` of the result holds the start line, each record's line twice (once in `getNext`,
  once in the loop, as the COBOL program displays it) and the end line, and `abended` stays
  `false`. The state lives in one `Cbact03c$State` object; `getNext`, `xreffileOpen`,
  `xreffileClose` and `finish` are inlined (no loops), `spaces`, `fixLen` and `recordText` are
  called through their contracts. One loop invariant, at the head of the read loop
  (statement 29); the paths are checked as one lemma per segment (`Cbact03cRun*.lean`).
-/
import EquivLean.Modernize.JL.Cbact03cProg
import EquivLean.Modernize.JL.Cbcus01cRun

open Jimple

namespace EquivLean.Modernize.JL

def c3StartText : JStr := JStr.ofString "START OF EXECUTION OF PROGRAM CBACT03C"
def c3EndText : JStr := JStr.ofString "END OF EXECUTION OF PROGRAM CBACT03C"

def xrefCls : ClassName := "Cbact03c$CardXrefRecord"

/-- Field `f` of the cross-reference record object at `c` (`null` if absent). -/
def xfieldOf (σ : State) (c : Addr) (f : String) : Value :=
  match σ.heap c with
  | some (.plain _ fs) => (Fields.get fs (xrefCls, f)).getD .null
  | _ => .null

def xfieldLong (σ : State) (c : Addr) (f : String) : I64 :=
  match xfieldOf σ c f with
  | .long x => x
  | _ => 0

/-- The line displayed for the cross-reference record at `c`. -/
def xrefLine (σ : State) (c : Addr) : JStr :=
  fixStr (argText σ (xfieldOf σ c "xrefCardNum")) 16 ++ zpadStr (xfieldLong σ c "xrefCustId").toNat 9 ++
    zpadStr (xfieldLong σ c "xrefAcctId").toNat 11 ++ fixStr (argText σ (xfieldOf σ c "filler1")) 14

def XStrField (σ : State) (fs : List (FieldKey × Value)) (f : String) : Prop :=
  ∃ x s, Fields.get fs (xrefCls, f) = some (.ref x) ∧ σ.heap x = some (.str s) ∧ s.length < 2147483648

def XLongField (fs : List (FieldKey × Value)) (f : String) : Prop :=
  ∃ a : I64, Fields.get fs (xrefCls, f) = some (.long a) ∧ 0 ≤ a.toInt

/-- A cross-reference record as the program reads it (as the records of the file are). -/
def XrefOk (σ : State) (c : Addr) : Prop :=
  ∃ fs, σ.heap c = some (.plain xrefCls fs) ∧ XStrField σ fs "xrefCardNum" ∧
    XLongField fs "xrefCustId" ∧ XLongField fs "xrefAcctId" ∧ XStrField σ fs "filler1"

def xrecLineV (σ : State) : Value → JStr
  | .ref c => xrefLine σ c
  | _ => []

/-- The lines displayed for the first `n` records: each record's line twice. -/
def xrefLines (σ : State) (xs : List Value) : Nat → List JStr
  | 0 => []
  | n + 1 => xrefLines σ xs n ++ [xrecLineV σ (xs.getD n .null), xrecLineV σ (xs.getD n .null)]

theorem xrefLines_eq_flatMap (σ : State) (xs : List Value) :
    ∀ n, n ≤ xs.length → xrefLines σ xs n = (xs.take n).flatMap (fun v => [xrecLineV σ v, xrecLineV σ v])
  | 0, _ => by simp [xrefLines]
  | n + 1, h => by
    have hn : n < xs.length := by omega
    rw [xrefLines, xrefLines_eq_flatMap σ xs n (by omega), List.take_succ, List.getElem?_eq_getElem hn,
      List.flatMap_append]
    simp only [Option.toList_some, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hn, Option.getD_some, List.cons_append,
      List.nil_append]

/-- All the lines: each record's line twice. -/
theorem xrefLines_length (σ : State) (xs : List Value) :
    xrefLines σ xs xs.length = xs.flatMap (fun v => [xrecLineV σ v, xrecLineV σ v]) := by
  rw [xrefLines_eq_flatMap σ xs _ (Nat.le_refl _), List.take_length]

abbrev c3RunRef : MethodRef := EquivLean.Modernize.Cbact03c.Java.Gen.Cbact03c.«run(Cbact03c$CardXrefRecord[])».ref

/-- The contract of `run`: an array of cross-reference records (`XrefOk`). -/
def c3RunSpecJ : Spec := Spec.of
  (fun args σ => ∃ a et xs, args = [.ref a] ∧ σ.heap a = some (.array et xs) ∧
     xs.length < 2147483648 ∧ (∀ v ∈ xs, ∃ c, v = .ref c ∧ XrefOk σ c) ∧
     σ.initOf "Cbact03c" = .done ∧ σ.initOf "Cbact03c$Result" = .done ∧
     σ.initOf "Cbact03c$CardXrefRecord" = .done ∧ σ.initOf "Cbact03c$State" = .done)
  (fun args σ r σ' => ∀ a et xs, args = [.ref a] → σ.heap a = some (.array et xs) →
     ∃ res fs l k ys m, r = some (.ref res) ∧ σ'.heap res = some (.plain "Cbact03c$Result" fs) ∧
       Fields.get fs ("Cbact03c$Result", "displays") = some (.ref l) ∧
       σ'.heap l = some (.list k ys m) ∧
       StrsAt σ' ys (c3StartText :: (xrefLines σ xs xs.length ++ [c3EndText])) ∧
       Fields.get fs ("Cbact03c$Result", "abended") = some (.int 0))

/-- The facts at the head of the read loop (statement 29), for given values of the invariant's
    variables: the state object `st` (local `$r1` 2) with `pos = i` records read, `atEof = z`,
    `endOfFile` the string `"N"` or `"Y"` as `z` is clear or set (and then all records read),
    the other fields present (`sv`, `ap`, `rc`, `rcu`, `rac`, `rf`: overwritten before use);
    the result object `res` with the display list `l`: the start line, then each read record's
    line twice. -/
def C3RunAt (σ0 : State) (fr : Frame) (σ : State) (a : Addr) (xs : List Value) (st : Addr)
    (sfs : List (FieldKey × Value)) (res : Addr) (fs : List (FieldKey × Value)) (l : Addr)
    (ys : List Value) (m : Nat) (i z : I32) (e : Addr) (sv ap rc rcu rac rf : Value) : Prop :=
  fr.get 2 = some (.ref st) ∧ σ.heap st = some (.plain stCls sfs) ∧
  Fields.get sfs (stCls, "result") = some (.ref res) ∧ Fields.get sfs (stCls, "file") = some (.ref a) ∧
  Fields.get sfs (stCls, "pos") = some (.int i) ∧ Fields.get sfs (stCls, "atEof") = some (.int z) ∧
  Fields.get sfs (stCls, "xreffileStatus") = some sv ∧ Fields.get sfs (stCls, "applResult") = some ap ∧
  Fields.get sfs (stCls, "endOfFile") = some (.ref e) ∧
  σ.heap e = some (.str (if z = 0 then textN else textY)) ∧
  Fields.get sfs (stCls, "recCardNum") = some rc ∧ Fields.get sfs (stCls, "recCustId") = some rcu ∧
  Fields.get sfs (stCls, "recAcctId") = some rac ∧ Fields.get sfs (stCls, "recFiller") = some rf ∧
  Fields.get sfs (stCls, "abended") = some (.int 0) ∧
  σ.heap res = some (.plain "Cbact03c$Result" fs) ∧
  Fields.get fs ("Cbact03c$Result", "displays") = some (.ref l) ∧
  Fields.get fs ("Cbact03c$Result", "abended") = some (.int 0) ∧
  σ.heap l = some (.list .arrayList ys m) ∧
  StrsAt σ ys (c3StartText :: xrefLines σ0 xs i.toInt.toNat) ∧
  0 ≤ i.toInt ∧ i.toInt ≤ xs.length ∧ (z ≠ 0 → i.toInt = xs.length) ∧
  σ0.next ≤ st ∧ st < res ∧ res < l ∧ Grows σ0 σ ∧ σ.inits = σ0.inits ∧ σ.statics = σ0.statics

/-- The loop invariant of `run`. -/
def c3RunInv29 (args : List Value) (σ0 : State) (fr : Frame) (σ : State) : Prop :=
  ∀ a et xs, args = [.ref a] → σ0.heap a = some (.array et xs) →
    ∃ st sfs res fs l ys m i z e sv ap rc rcu rac rf,
      C3RunAt σ0 fr σ a xs st sfs res fs l ys m i z e sv ap rc rcu rac rf

def c3RunInv : Invariants := [(29, c3RunInv29)]

def c3SpacesSig : MethodSig := ⟨"Cbact03c", .cls "java.lang.String", "spaces", [.prim .int]⟩
def c3FixLenSig : MethodSig :=
  ⟨"Cbact03c", .cls "java.lang.String", "fixLen", [.cls "java.lang.String", .prim .int]⟩
def c3RecordTextSig : MethodSig :=
  ⟨"Cbact03c", .cls "java.lang.String", "recordText", [.cls "Cbact03c$State"]⟩

/-- The callee contracts of `run` (`getNext` and the others are inlined). -/
def c3RunCallees : Contracts :=
  [(c3SpacesSig, spacesSpec), (c3FixLenSig, fixLenSpec), (c3RecordTextSig, recordTextSpec)]

/-- The paths of `run` from statement `pc`. -/
def c3RunWP (args : List Value) (σ0 : State) (pc : Nat) (fr : Frame) (σ : State) : Prop :=
  bodyWP EquivLean.Modernize.Cbact03c.Java.Gen.prog (callWP EquivLean.Modernize.Cbact03c.Java.Gen.prog c3RunCallees.env 1) EquivLean.Modernize.Cbact03c.Java.Gen.Cbact03c.«run(Cbact03c$CardXrefRecord[])»
    (c3RunInv.inst args σ0) (c3RunSpecJ.post args σ0) 200 pc fr σ

end EquivLean.Modernize.JL
