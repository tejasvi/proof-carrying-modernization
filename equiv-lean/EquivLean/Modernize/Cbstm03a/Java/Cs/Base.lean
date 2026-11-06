import EquivLean.Modernize.Cbstm03a.Java.Iface3
import EquivLean.Modernize.Cbstm03a.Java.Iface1
import EquivLean.Modernize.Cbstm03b.Java.TrnxFin

/-!
# CBSTM03A → Java: `createStatement`, the contract with fixed ghost values and the cut points

`createStatement(res, custRec, acctRec)` is straight-line code (148 statements, 72 calls of `stmt`/`html`).
It is verified against `specG g` (the ghost values of `createStatementSpec` fixed) with a cut point right after
every call of `stmt` or `html` (and two inside the name and address builders): each cut point states the
locals still to be used, and the `Result` holding the first `ns` statement lines and `nh` HTML lines of
`jCreateStatement` (`CutI`).

Locals (index: name): 0 `currBal`, 1 `custRec`, 2 `acctRec`, 3 `custFirst`, 4 `custMiddle`, 5 `custLast`,
6 `addr1`, 7 `addr2`, 8 `addr3`, 9 `state`, 10 `country`, 11 `zip`, 12 `fico`, 13 `acctId`, 14 `$r2`,
15 `stName`, 16 `stAdd3`, 17 `stAcctId`, 18 `stCurrBal`, 19 `stFico`, 20 `l23Name`, 21 `dashes`, 22 `res`,
23 `nm`, 24 `a3`.
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows Keeps fixStr zpadStr argText StrOk space Kept GrowsK grows_split
  growsK_elim grows_refl grows_trans keeps_refl keeps_trans)

namespace EquivLean.Modernize.Cbstm03a.Java

/-- The callee contracts of `createStatement`, all from the frozen interfaces. -/
def csCallees : Contracts :=
  [(stmtSig, stmtSpec), (htmlSig, htmlSpec), (fixSig, fixSpecI), (spacesSig, spacesSpecI),
   (repeatSig, repeatSpec), (appSig, appSpec), (paraSig, paraSpec), (starSig, starSpec),
   (fmtCurrBalSig, fmtCurrBalSpec), (decodeZonedSig, decodeZonedSpec)]

namespace Cs

abbrev body : Body := Gen.Cbstm03a.«createStatement(Cbstm03a$Result,java.lang.String,java.lang.String)»

/-- The ghost values of `createStatementSpec`. -/
structure G where
  res : Addr
  ld : Addr
  ls : Addr
  lh : Addr
  disp : List JStr
  st : List JStr
  ht : List JStr
  ab : Bool
  xc : Addr
  xa : Addr
  c : JStr
  a : JStr

/-- `createStatementSpec` for fixed ghost values. -/
def specG (g : G) : Spec := Spec.of
  (fun args σ => args = [.ref g.res, .ref g.xc, .ref g.xa] ∧
     ResAtL σ g.res g.ld g.ls g.lh g.disp g.st g.ht g.ab ∧
     σ.heap g.xc = some (.str g.c) ∧ σ.heap g.xa = some (.str g.a) ∧
     332 ≤ g.c.length ∧ g.c.length < 2147483648 ∧ 24 ≤ g.a.length ∧ g.a.length < 2147483648 ∧
     σ.initOf "Cbstm03a" = .done)
  (fun _ σ r σ' => r = none ∧
     ResAtL σ' g.res g.ld g.ls g.lh g.disp (g.st ++ (jCreateStatement g.c g.a).1)
       (g.ht ++ (jCreateStatement g.c g.a).2) g.ab ∧
     KeepsRes g.res g.ld g.ls g.lh σ σ' ∧ σ'.inits = σ.inits ∧ σ'.statics = σ.statics)

/-- String locals: local `i` holds a string with the text `s` (of `int` length). -/
def LocsAt (σ : State) (fr : Frame) : List (Nat × JStr) → Prop
  | [] => True
  | (i, s) :: rest => (∃ x, fr.get i = some (.ref x) ∧ σ.heap x = some (.str s) ∧ s.length < 2147483648) ∧
      LocsAt σ fr rest

/-- The state at a cut point: `res` in its local, the first `ns` statement lines and `nh` HTML lines written,
the frame and the class state of the entry kept. -/
def At (g : G) (σ0 : State) (fr : Frame) (σ : State) (ns nh : Nat) : Prop :=
  fr.get 22 = some (.ref g.res) ∧
  ResAtL σ g.res g.ld g.ls g.lh g.disp (g.st ++ (jCreateStatement g.c g.a).1.take ns)
    (g.ht ++ (jCreateStatement g.c g.a).2.take nh) g.ab ∧
  KeepsRes g.res g.ld g.ls g.lh σ0 σ ∧ σ.inits = σ0.inits ∧ σ.statics = σ0.statics ∧
  σ.initOf "Cbstm03a" = .done

/-- A cut point: `At`, the string locals `locs`, and (`bal`) `currBal`. -/
def CutI (g : G) (ns nh : Nat) (locs : List (Nat × JStr)) (bal : Bool) (σ0 : State) (fr : Frame) (σ : State) :
    Prop :=
  At g σ0 fr σ ns nh ∧ LocsAt σ fr locs ∧
  (bal = true → fr.get 0 = some (.long (BitVec.ofInt 64 (zonedVal (sub g.a 12 24)))))

/-! ## The texts of the locals -/

def tFirst (g : G) : JStr := sub g.c 9 34
def tMiddle (g : G) : JStr := sub g.c 34 59
def tLast (g : G) : JStr := sub g.c 59 84
def tAddr1 (g : G) : JStr := sub g.c 84 134
def tAddr2 (g : G) : JStr := sub g.c 134 184
def tAddr3 (g : G) : JStr := sub g.c 184 234
def tState (g : G) : JStr := sub g.c 234 236
def tCountry (g : G) : JStr := sub g.c 236 239
def tZip (g : G) : JStr := sub g.c 239 249
def tFico (g : G) : JStr := sub g.c 329 332
def tAcctId (g : G) : JStr := sub g.a 0 11
def tStName (g : G) : JStr := stNameT g.c
def tStAdd3 (g : G) : JStr := stAdd3T g.c
def tStAcctId (g : G) : JStr := fixStr (sub g.a 0 11) 20
def tStCurrBal (g : G) : JStr := fmtCurrBalI (decodeZonedI (sub g.a 12 24))
def tStFico (g : G) : JStr := fixStr (sub g.c 329 332) 20
def tDashes : JStr := List.replicate 80 chDash

/-- The arguments of the `stmt`/`html` calls that are computed (the lines before `fix`). -/
def tStart : JStr := List.replicate 31 chStar ++ jl "START OF STATEMENT" ++ List.replicate 31 chStar
def tH3 (g : G) : JStr := jl "<h3>Statement for Account Number: " ++ fixStr (sub g.a 0 11) 20 ++ jl "</h3>"
def tPara1 (g : G) : JStr := paraT (jl "<p style=\"font-size:16px\">") (sub (stNameT g.c) 0 50)
def tPara2 (g : G) : JStr := paraT (jl "<p>") (sub g.c 84 134)
def tPara3 (g : G) : JStr := paraT (jl "<p>") (sub g.c 134 184)
def tPara4 (g : G) : JStr := paraT (jl "<p>") (stAdd3T g.c)
def tStar1 (g : G) : JStr := starT (jl "<p>Account ID         : ") (fixStr (sub g.a 0 11) 20)
def tStar2 (g : G) : JStr := starT (jl "<p>Current Balance    : ") (fmtCurrBalI (decodeZonedI (sub g.a 12 24)))
def tStar3 (g : G) : JStr := starT (jl "<p>FICO Score         : ") (fixStr (sub g.c 329 332) 20)
def tL2 (g : G) : JStr := stNameT g.c ++ List.replicate 5 space
def tL3 (g : G) : JStr := sub g.c 84 134 ++ List.replicate 30 space
def tL4 (g : G) : JStr := sub g.c 134 184 ++ List.replicate 30 space
def tL7 : JStr := List.replicate 33 space ++ jl "Basic Details " ++ List.replicate 33 space
def tL9 (g : G) : JStr := jl "Account ID         :" ++ fixStr (sub g.a 0 11) 20 ++ List.replicate 40 space
def tL10 (g : G) : JStr :=
  jl "Current Balance    :" ++ fmtCurrBalI (decodeZonedI (sub g.a 12 24)) ++ List.replicate 47 space
def tL11 (g : G) : JStr := jl "FICO Score         :" ++ fixStr (sub g.c 329 332) 20 ++ List.replicate 40 space
def tL13 : JStr := List.replicate 30 space ++ jl "TRANSACTION SUMMARY " ++ List.replicate 30 space
def tL15 : JStr := jl "Tran ID         " ++ fixStr (jl "Tran Details    ") 51 ++ jl "  Tran Amount"

/-! ## The live locals at the cut points (the argument of the next call first) -/

def LA (g : G) : List (Nat × JStr) :=
  [(3, tFirst g), (4, tMiddle g), (5, tLast g), (6, tAddr1 g), (7, tAddr2 g), (8, tAddr3 g), (9, tState g),
   (10, tCountry g), (11, tZip g), (12, tFico g), (13, tAcctId g)]
def LA19 (g : G) : List (Nat × JStr) := (2, tStart) :: LA g
def LA32 (g : G) : List (Nat × JStr) := (2, tH3 g) :: LA g
def LB (g : G) : List (Nat × JStr) :=
  [(6, tAddr1 g), (7, tAddr2 g), (8, tAddr3 g), (9, tState g), (10, tCountry g), (11, tZip g), (12, tFico g),
   (13, tAcctId g), (15, tStName g)]
def LC (g : G) : List (Nat × JStr) :=
  [(6, tAddr1 g), (7, tAddr2 g), (12, tFico g), (13, tAcctId g), (15, tStName g), (16, tStAdd3 g)]
def LD (g : G) : List (Nat × JStr) :=
  [(6, tAddr1 g), (7, tAddr2 g), (15, tStName g), (16, tStAdd3 g), (17, tStAcctId g), (18, tStCurrBal g),
   (19, tStFico g)]
def LD71 (g : G) : List (Nat × JStr) := (13, tPara1 g) :: LD g
def LD73 (g : G) : List (Nat × JStr) := (13, tPara2 g) :: LD g
def LD75 (g : G) : List (Nat × JStr) := (13, tPara3 g) :: LD g
def LD77 (g : G) : List (Nat × JStr) := (13, tPara4 g) :: LD g
def LD88 (g : G) : List (Nat × JStr) := (13, tStar1 g) :: LD g
def LD90 (g : G) : List (Nat × JStr) := (13, tStar2 g) :: LD g
def LD92 (g : G) : List (Nat × JStr) := (13, tStar3 g) :: LD g
def LE (g : G) : List (Nat × JStr) :=
  [(6, tAddr1 g), (7, tAddr2 g), (16, tStAdd3 g), (17, tStAcctId g), (18, tStCurrBal g), (19, tStFico g),
   (21, tDashes)]
def LE114 (g : G) : List (Nat × JStr) := (3, tL2 g) :: LE g
def LF (g : G) : List (Nat × JStr) :=
  [(7, tAddr2 g), (16, tStAdd3 g), (17, tStAcctId g), (18, tStCurrBal g), (19, tStFico g), (21, tDashes)]
def LF117 (g : G) : List (Nat × JStr) := (6, tL3 g) :: LF g
def LG (g : G) : List (Nat × JStr) :=
  [(16, tStAdd3 g), (21, tDashes), (17, tStAcctId g), (18, tStCurrBal g), (19, tStFico g)]
def LG120 (g : G) : List (Nat × JStr) := (7, tL4 g) :: LG g
def LH (g : G) : List (Nat × JStr) := [(21, tDashes), (17, tStAcctId g), (18, tStCurrBal g), (19, tStFico g)]
def LH126 (g : G) : List (Nat × JStr) := (7, tL7) :: LH g
def LI (g : G) : List (Nat × JStr) := [(21, tDashes), (18, tStCurrBal g), (19, tStFico g)]
def LJ (g : G) : List (Nat × JStr) := [(21, tDashes), (19, tStFico g)]
def LK (_ : G) : List (Nat × JStr) := [(21, tDashes)]
def LH130 (g : G) : List (Nat × JStr) := (7, tL9 g) :: LI g
def LI133 (g : G) : List (Nat × JStr) := (2, tL10 g) :: LJ g
def LJ136 (g : G) : List (Nat × JStr) := (1, tL11 g) :: LK g
def LK141 (g : G) : List (Nat × JStr) := (1, tL13) :: LK g
def LK145 (g : G) : List (Nat × JStr) := (1, tL15) :: LK g

/-- The invariant of a cut point (folded: the symbolic executor leaves it to the closers). -/
@[irreducible] def cut (g : G) (ns nh : Nat) (L : G → List (Nat × JStr)) (bal : Bool) :
    List Value → State → Frame → State → Prop :=
  fun _ σ0 fr σ => CutI g ns nh (L g) bal σ0 fr σ

/-- The cut points of `createStatement`. -/
def inv (g : G) : Invariants :=
  [(19, cut g 0 0 LA19 true),
   (20, cut g 1 0 LA true), (21, cut g 1 1 LA true), (22, cut g 1 2 LA true), (23, cut g 1 3 LA true),
   (24, cut g 1 4 LA true), (25, cut g 1 5 LA true), (26, cut g 1 6 LA true), (27, cut g 1 7 LA true),
   (28, cut g 1 8 LA true), (29, cut g 1 9 LA true), (30, cut g 1 10 LA true),
   (32, cut g 1 10 LA32 true),
   (33, cut g 1 11 LA true), (34, cut g 1 12 LA true), (35, cut g 1 13 LA true), (36, cut g 1 14 LA true),
   (37, cut g 1 15 LA true), (38, cut g 1 16 LA true), (39, cut g 1 17 LA true), (40, cut g 1 18 LA true),
   (41, cut g 1 19 LA true), (42, cut g 1 20 LA true), (43, cut g 1 21 LA true), (44, cut g 1 22 LA true),
   (54, cut g 1 22 LB true), (66, cut g 1 22 LC true),
   (71, cut g 1 22 LD71 false), (72, cut g 1 23 LD false), (73, cut g 1 23 LD73 false),
   (74, cut g 1 24 LD false), (75, cut g 1 24 LD75 false), (76, cut g 1 25 LD false),
   (77, cut g 1 25 LD77 false), (78, cut g 1 26 LD false),
   (79, cut g 1 27 LD false), (80, cut g 1 28 LD false), (81, cut g 1 29 LD false), (82, cut g 1 30 LD false),
   (83, cut g 1 31 LD false), (84, cut g 1 32 LD false), (85, cut g 1 33 LD false), (86, cut g 1 34 LD false),
   (87, cut g 1 35 LD false), (88, cut g 1 35 LD88 false), (89, cut g 1 36 LD false),
   (90, cut g 1 36 LD90 false), (91, cut g 1 37 LD false), (92, cut g 1 37 LD92 false),
   (93, cut g 1 38 LD false),
   (94, cut g 1 39 LD false), (95, cut g 1 40 LD false), (96, cut g 1 41 LD false), (97, cut g 1 42 LD false),
   (98, cut g 1 43 LD false), (99, cut g 1 44 LD false), (100, cut g 1 45 LD false),
   (101, cut g 1 46 LD false), (102, cut g 1 47 LD false), (103, cut g 1 48 LD false),
   (104, cut g 1 49 LD false), (105, cut g 1 50 LD false), (106, cut g 1 51 LD false),
   (107, cut g 1 52 LD false), (108, cut g 1 53 LD false), (109, cut g 1 54 LD false),
   (110, cut g 1 55 LD false), (111, cut g 1 56 LD false),
   (114, cut g 1 56 LE114 false), (115, cut g 2 56 LE false), (117, cut g 2 56 LF117 false),
   (118, cut g 3 56 LF false), (120, cut g 3 56 LG120 false), (121, cut g 4 56 LG false),
   (122, cut g 5 56 LH false), (123, cut g 6 56 LH false), (126, cut g 6 56 LH126 false),
   (127, cut g 7 56 LH false), (128, cut g 8 56 LH false), (130, cut g 8 56 LH130 false),
   (131, cut g 9 56 LI false), (133, cut g 9 56 LI133 false), (134, cut g 10 56 LJ false),
   (136, cut g 10 56 LJ136 false), (137, cut g 11 56 LK false), (138, cut g 12 56 LK false),
   (141, cut g 12 56 LK141 false), (142, cut g 13 56 LK false), (143, cut g 14 56 LK false),
   (145, cut g 14 56 LK145 false), (146, cut g 15 56 LK false)]

/-- The paths of `createStatement` from statement `pc`. -/
@[irreducible] def wp (g : G) (args : List Value) (σ0 : State) (pc : Nat) (fr : Frame) (σ : State) : Prop :=
  bodyWP Gen.prog (callWP Gen.prog csCallees.env 1) body ((inv g).inst args σ0) ((specG g).post args σ0) 60 pc fr σ

/-- The entry path. -/
def EntryVC (g : G) : Prop :=
  ∀ args σ0, (specG g).pre args σ0 → wp g args σ0 0 (Frame.init true args) σ0

/-- The paths from the cut point `pc` with the invariant `cut g ns nh L bal`. -/
def CutVC (g : G) (pc ns nh : Nat) (L : G → List (Nat × JStr)) (bal : Bool) : Prop :=
  ∀ args σ0, (specG g).pre args σ0 → ∀ fr σ, cut g ns nh L bal args σ0 fr σ → wp g args σ0 pc fr σ

end Cs

end EquivLean.Modernize.Cbstm03a.Java
