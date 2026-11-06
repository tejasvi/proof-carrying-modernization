-- Copied from JimpleLean (frozen snapshot ~/jimplelean_work/snapshots/JimpleLean-20261025T2312Z,
-- Examples/CardDemo/Cbcus01cRun.lean); proved by JimpleLean's own session.  Only the imports, the
-- program (`CU`, the same Jimple files, is equiv-lean's generated
-- `EquivLean.Modernize.Cbcus01c.Java.Gen`) and the namespace differ (tools/modernize/import_jl.py).
/-
  Examples/CardDemo/Cbcus01cRun.lean

  `Cbcus01c.run(CustomerRecord[])`, the read loop of CBCUS01C as translated to Java: the list
  `displays` of the result holds the start line, each record's line twice (as the COBOL program
  displays it) and the end line, and `abended` stays `false`. Against the contracts of
  `fmtRecordInitial` and `fmtRecord`; one loop invariant, at the head of the read loop
  (statement 26). The paths are checked as one lemma per segment (`Cbcus01cRun*.lean`).
-/
import EquivLean.Modernize.JL.Cbcus01cFormat
import EquivLean.Modernize.JL.Cbact02cRun

open Jimple

namespace EquivLean.Modernize.JL

def cuStartText : JStr := JStr.ofString "START OF EXECUTION OF PROGRAM CBCUS01C"
def cuEndText : JStr := JStr.ofString "END OF EXECUTION OF PROGRAM CBCUS01C"

/-- The line of the customer record a value refers to. -/
def crecLineV (σ : State) : Value → JStr
  | .ref c => custLine σ c
  | _ => []

/-- The lines displayed for the first `n` records: each record's line twice. -/
def custLines (σ : State) (xs : List Value) : Nat → List JStr
  | 0 => []
  | n + 1 => custLines σ xs n ++ [crecLineV σ (xs.getD n .null), crecLineV σ (xs.getD n .null)]

theorem custLines_eq_flatMap (σ : State) (xs : List Value) :
    ∀ n, n ≤ xs.length → custLines σ xs n = (xs.take n).flatMap (fun v => [crecLineV σ v, crecLineV σ v])
  | 0, _ => by simp [custLines]
  | n + 1, h => by
    have hn : n < xs.length := by omega
    rw [custLines, custLines_eq_flatMap σ xs n (by omega), List.take_succ, List.getElem?_eq_getElem hn,
      List.flatMap_append]
    simp only [Option.toList_some, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hn, Option.getD_some, List.cons_append,
      List.nil_append]

/-- All the lines: each record's line twice. -/
theorem custLines_length (σ : State) (xs : List Value) :
    custLines σ xs xs.length = xs.flatMap (fun v => [crecLineV σ v, crecLineV σ v]) := by
  rw [custLines_eq_flatMap σ xs _ (Nat.le_refl _), List.take_length]

/-- Two references appended to a list of strings. -/
@[jsimp] theorem StrsAt_snoc2 (σ : State) (ys : List Value) (y1 y2 : Value) (s0 : JStr)
    (ss : List JStr) (s1 s2 : JStr) :
    StrsAt σ (ys ++ [y1, y2]) (s0 :: (ss ++ [s1, s2])) ↔
      StrsAt σ ys (s0 :: ss) ∧ strOf σ y1 = some s1 ∧ strOf σ y2 = some s2 := by
  have e1 : ys ++ [y1, y2] = (ys ++ [y1]) ++ [y2] := by simp
  have e2 : s0 :: (ss ++ [s1, s2]) = ((s0 :: ss) ++ [s1]) ++ [s2] := by simp
  rw [e1, e2, StrsAt_snoc, StrsAt_snoc, and_assoc]

abbrev cuRunRef : MethodRef := EquivLean.Modernize.Cbcus01c.Java.Gen.Cbcus01c.«run(Cbcus01c$CustomerRecord[])».ref

/-- The contract of `run`: an array of customer records as `fmtRecord` reads them (`CustOk`). -/
def cuRunSpecJ : Spec := Spec.of
  (fun args σ => ∃ a et xs, args = [.ref a] ∧ σ.heap a = some (.array et xs) ∧
     xs.length < 2147483648 ∧ (∀ v ∈ xs, ∃ c, v = .ref c ∧ CustOk σ c) ∧
     σ.initOf "Cbcus01c" = .done ∧ σ.initOf "Cbcus01c$Result" = .done ∧
     σ.initOf "Cbcus01c$CustomerRecord" = .done)
  (fun args σ r σ' => ∀ a et xs, args = [.ref a] → σ.heap a = some (.array et xs) →
     ∃ res fs l k ys m, r = some (.ref res) ∧ σ'.heap res = some (.plain "Cbcus01c$Result" fs) ∧
       Fields.get fs ("Cbcus01c$Result", "displays") = some (.ref l) ∧
       σ'.heap l = some (.list k ys m) ∧
       StrsAt σ' ys (cuStartText :: (custLines σ xs xs.length ++ [cuEndText])) ∧
       Fields.get fs ("Cbcus01c$Result", "abended") = some (.int 0))

/-- The facts at the head of the read loop (statement 26), for given values of the invariant's
    variables: `i` records read, their lines (twice each) displayed after the start line; the
    end-of-file flag `z` (local `$z0`) is set exactly when the three copies of `END-OF-FILE`
    (`b12`, `b13`, `b14`) hold `'Y'` (89) instead of `'N'` (78), and then all records have been
    read. Locals: `b12` 3, `b13` 4, `b14` 5, `i5` 7, `$z0` 10, `$r1` 14, `r0` 15. -/
def CuRunAt (σ0 : State) (fr : Frame) (σ : State) (a : Addr) (xs : List Value) (res : Addr)
    (fs : List (FieldKey × Value)) (l : Addr) (ys : List Value) (m : Nat) (i z : I32) : Prop :=
  fr.get 15 = some (.ref a) ∧ fr.get 14 = some (.ref res) ∧
  σ.heap res = some (.plain "Cbcus01c$Result" fs) ∧
  Fields.get fs ("Cbcus01c$Result", "displays") = some (.ref l) ∧
  Fields.get fs ("Cbcus01c$Result", "abended") = some (.int 0) ∧
  σ.heap l = some (.list .arrayList ys m) ∧
  StrsAt σ ys (cuStartText :: custLines σ0 xs i.toInt.toNat) ∧
  fr.get 7 = some (.int i) ∧ 0 ≤ i.toInt ∧ i.toInt ≤ xs.length ∧
  fr.get 10 = some (.int z) ∧
  fr.get 3 = some (.int (if z = 0 then 78 else 89)) ∧
  fr.get 4 = some (.int (if z = 0 then 78 else 89)) ∧
  fr.get 5 = some (.int (if z = 0 then 78 else 89)) ∧
  (z ≠ 0 → i.toInt = xs.length) ∧
  σ0.next ≤ res ∧ res < l ∧ Grows σ0 σ ∧ σ.inits = σ0.inits ∧ σ.statics = σ0.statics

/-- The loop invariant of `run`. -/
def cuRunInv26 (args : List Value) (σ0 : State) (fr : Frame) (σ : State) : Prop :=
  ∀ a et xs, args = [.ref a] → σ0.heap a = some (.array et xs) →
    ∃ res fs l ys m i z, CuRunAt σ0 fr σ a xs res fs l ys m i z

def cuRunInv : Invariants := [(26, cuRunInv26)]

def cuFmtRecordInitialSig : MethodSig :=
  ⟨"Cbcus01c", .cls "java.lang.String", "fmtRecordInitial", []⟩
def cuFmtRecordSig : MethodSig :=
  ⟨"Cbcus01c", .cls "java.lang.String", "fmtRecord", [.cls "Cbcus01c$CustomerRecord"]⟩

/-- The callee contracts of `run`. -/
def cuRunCallees : Contracts :=
  [(cuFmtRecordInitialSig, fmtRecordInitialSpec), (cuFmtRecordSig, fmtRecordSpec)]

/-- The paths of `run` from statement `pc`. -/
def cuRunWP (args : List Value) (σ0 : State) (pc : Nat) (fr : Frame) (σ : State) : Prop :=
  bodyWP EquivLean.Modernize.Cbcus01c.Java.Gen.prog (callWP EquivLean.Modernize.Cbcus01c.Java.Gen.prog cuRunCallees.env 1) EquivLean.Modernize.Cbcus01c.Java.Gen.Cbcus01c.«run(Cbcus01c$CustomerRecord[])»
    (cuRunInv.inst args σ0) (cuRunSpecJ.post args σ0) 200 pc fr σ

end EquivLean.Modernize.JL
