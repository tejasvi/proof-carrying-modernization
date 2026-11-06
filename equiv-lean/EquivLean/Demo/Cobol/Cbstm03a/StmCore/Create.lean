/-
# Phase 5 of `CBSTM03AB`: `5000-CREATE-STATEMENT`

For one account, `5000-CREATE-STATEMENT` (paragraph 8, with `5100-WRITE-HTML-HEADER` and
`5200-WRITE-HTML-NMADBS` performed) writes the 16 statement-header records of `STMT-FILE`
(`stmtHead`) and the 56 HTML records of `HTML-FILE` (`htmlHead`), from the customer record's
name and address fields, the account id and balance, and the FICO score.  `STRING … DELIMITED
BY ' '` / `'*'` / `'  '` contribute first tokens (`tokB`, `tok2`, `EquivLean.Demo.Cobol.Cbstm03a.StmCore.Str`), and
the `STRING` receivers are spaces before (`ovw … (sp n)`: the pieces' bytes, as many as fit,
then spaces).
-/
import EquivLean.Demo.Cobol.Cbstm03a.StmCore.Summ
import EquivLean.Demo.Cobol.Cbstm03a.StmCore.Str
import EquivLean.Demo.Cobol.Cbstm03a.StmCore.Text
import EquivLean.Demo.Cobol.Cbstm03a.StmCore.Lits

open Cobol Cobol.Stm

namespace Cobol.StmCore

/-- `<p>` -/
def tP : List UInt8 := ebc "<p>"

set_option maxRecDepth 100000 in
theorem tP_lit : tP = [76, 151, 110] := by decide +kernel

/-- `</p>` -/
def tEndP : List UInt8 := ebc "</p>"

set_option maxRecDepth 100000 in
theorem tEndP_lit : tEndP = [76, 97, 151, 110] := by decide +kernel

/-- `<p style="font-size:16px">` -/
def tPStyle : List UInt8 := ebc "<p style=\"font-size:16px\">"

set_option maxRecDepth 100000 in
theorem tPStyle_lit : tPStyle = [76, 151, 64, 162, 163, 168, 147, 133, 126, 127, 134, 150, 149, 163, 96, 162, 137, 169, 133, 122, 241, 246, 151, 167, 127, 110] := by decide +kernel

/-- `<p>Account ID         : ` -/
def tAcct : List UInt8 := ebc "<p>Account ID         : "

set_option maxRecDepth 100000 in
theorem tAcct_lit : tAcct = [76, 151, 110, 193, 131, 131, 150, 164, 149, 163, 64, 201, 196, 64, 64, 64, 64, 64, 64, 64, 64, 64, 122, 64] := by decide +kernel

/-- `<p>Current Balance    : ` -/
def tBal : List UInt8 := ebc "<p>Current Balance    : "

set_option maxRecDepth 100000 in
theorem tBal_lit : tBal = [76, 151, 110, 195, 164, 153, 153, 133, 149, 163, 64, 194, 129, 147, 129, 149, 131, 133, 64, 64, 64, 64, 122, 64] := by decide +kernel

/-- `<p>FICO Score         : ` -/
def tFico : List UInt8 := ebc "<p>FICO Score         : "

set_option maxRecDepth 100000 in
theorem tFico_lit : tFico = [76, 151, 110, 198, 201, 195, 214, 64, 226, 131, 150, 153, 133, 64, 64, 64, 64, 64, 64, 64, 64, 64, 122, 64] := by decide +kernel

/-- The picture of `ST-CURR-BAL`, `9(9).99-`. -/
def curBalPic : List ESym :=
  [.nine, .nine, .nine, .nine, .nine, .nine, .nine, .nine, .nine, .dot, .nine, .nine, .minus]

/-- `ST-NAME`: the first, middle and last names up to their first space, each followed by a
space, in 75 bytes. -/
def stName (first middle last : List UInt8) : List UInt8 :=
  ovw (tokB 64 first ++ [64] ++ tokB 64 middle ++ [64] ++ tokB 64 last ++ [64]) (sp 75)

/-- `ST-ADD3`: address line 3, state, country and zip up to their first space, each followed by
a space, in 80 bytes. -/
def stAdd3 (a3 st co zip : List UInt8) : List UInt8 :=
  ovw (tokB 64 a3 ++ [64] ++ tokB 64 st ++ [64] ++ tokB 64 co ++ [64] ++ tokB 64 zip ++ [64]) (sp 80)

/-- `ST-ACCT-ID` (`X(20)`) after `MOVE ACCT-ID` (`9(11)`). -/
def stAcctId (aid : Int) : List UInt8 := Sem.digitChars {} 11 aid.natAbs ++ sp 9

/-- `ST-FICO-SCORE` (`X(20)`) after `MOVE CUST-FICO-CREDIT-SCORE` (`9(3)`). -/
def stFico (fico : Int) : List UInt8 := Sem.digitChars {} 3 fico.natAbs ++ sp 17

/-- The 16 statement-header records: `ST-LINE0 … ST-LINE13` as written by
`5000-CREATE-STATEMENT` (name, address, basic details, transaction-summary heading). -/
def stmtHead (nm a1 a2 a3 aidT balT ficoT : List UInt8) : List (List UInt8) :=
  [c2470, nm ++ c2625, a1 ++ c2680, a2 ++ c2760, a3, c2870, c2950, c2870,
   c3030 ++ aidT ++ c3070, c3110 ++ balT ++ c3143, c3190 ++ ficoT ++ c3230,
   c3270, c3350, c3430, c3510, c3430]

/-- An HTML record built by `STRING pre field post INTO` 100 spaces. -/
def hfield (pre x post : List UInt8) : List UInt8 := ovw (pre ++ x ++ post) (sp 100)

/-- The 56 HTML records of the statement head: `5100-WRITE-HTML-HEADER` (22, with the account
number in `HTML-L11`), then `5200-WRITE-HTML-NMADBS` (34: name and address, basic details,
transaction-table heading). -/
def htmlHead (nm a1 a2 a3 aidT balT ficoT : List UInt8) : List (List UInt8) :=
  [hL01, hL02, hL03, hL04, hL05, hL06, hL07, hL08, hLTRS, hL10, c3930 ++ aidT ++ c3984 ++ sp 41,
   hLTDE, hLTRE, hLTRS, hL15, hL16, hL17, hL18, hLTDE, hLTRE, hLTRS, hL22_35,
   hfield tPStyle (tok2 (nm.take 50) ++ [64, 64]) tEndP, hfield tP (tok2 a1 ++ [64, 64]) tEndP,
   hfield tP (tok2 a2 ++ [64, 64]) tEndP, hfield tP (tok2 a3 ++ [64, 64]) tEndP,
   hLTDE, hLTRE, hLTRS, hL30_42, hL31, hLTDE, hLTRE, hLTRS, hL22_35,
   hfield tAcct (tokB 92 aidT) tEndP, hfield tBal (tokB 92 balT) tEndP,
   hfield tFico (tokB 92 ficoT) tEndP,
   hLTDE, hLTRE, hLTRS, hL30_42, hL43, hLTDE, hLTRE, hLTRS, hL47, hL48, hLTDE, hL50, hL51, hLTDE,
   hL53, hL54, hLTDE, hLTRE]

/-- The output events of `5000-CREATE-STATEMENT`, in program order. -/
def headEvents (nm a1 a2 a3 aidT balT ficoT : List UInt8) : List Event :=
  [.write 1 c2470] ++ (htmlHead nm a1 a2 a3 aidT balT ficoT).map (.write 2) ++
    ((stmtHead nm a1 a2 a3 aidT balT ficoT).drop 1).map (.write 1)
/-- The `ConstsOk` facts as hypotheses (for `stm_summary … with_pre`). -/
macro "consts_intro" h:ident : tactic =>
  `(tactic| (simp only [ConstsOk] at $h:ident; obtain ⟨k01, k02, k03, k04, k05, k06, k07, k08, k09, k10, k11, k12, k13, k14, k15, k16, k17, k18, k19, k20, k21, k22, k23⟩ := $h:ident))

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 50000 in
/-- `5100-WRITE-HTML-HEADER`: 22 HTML records, the account number in `HTML-L11`. -/
stm_summary html5100 (env : Env) (rec : Nat → State → Sem.Res) (fuel : Nat) (mem : Mem)
    (hm : mem.size = 178495)
    (idx : List (Nat × Int)) (slots : List (ExitPt × Nat)) (saves : List (Nat × Nat))
    (active : List Nat) (out : List Event) (inp : List (Nat × List (List UInt8))) (clockN : Nat)
    (f1 f3 f4 f5 f6 : FileSt) (r2 : List (List UInt8))
    (hl1 : mem.read 3930 34 = [76, 136, 243, 110, 226, 163, 129, 163, 133, 148, 133, 149, 163, 64, 134,
      150, 153, 64, 193, 131, 131, 150, 164, 149, 163, 64, 213, 164, 148, 130, 133, 153, 122, 64])
    (hl2 : mem.read 3984 5 = [76, 97, 136, 243, 110])
    (aid : Int) (haid : decodeNum {} { digits := 11 } (mem.read 1080 11) = some aid) :
    Sem.execSentences Stm env rec fuel Stm.«5100-WRITE-HTML-HEADER».body
      ⟨mem, idx, slots, saves, active, out, inp,
        [(1, f1), (2, { mode := some .output, recs := r2 }), (3, f3), (4, f4), (5, f5), (6, f6)],
        clockN⟩

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 50000 in
/-- `5200-WRITE-HTML-NMADBS`: 34 HTML records from `ST-NAME`, the address lines and the basic
details. -/
stm_summary html5200 (env : Env) (rec : Nat → State → Sem.Res) (fuel : Nat) (mem : Mem)
    (hm : mem.size = 178495)
    (idx : List (Nat × Int)) (slots : List (ExitPt × Nat)) (saves : List (Nat × Nat))
    (active : List Nat) (out : List Event) (inp : List (Nat × List (List UInt8))) (clockN : Nat)
    (f1 f3 f4 f5 f6 : FileSt) (r2 : List (List UInt8))
    (hl3 : mem.read 3989 26 = [76, 151, 64, 162, 163, 168, 147, 133, 126, 127, 134, 150, 149, 163, 96,
      162, 137, 169, 133, 122, 241, 246, 151, 167, 127, 110])
    (nm a1 a2 a3 aidT balT ficoT : List UInt8)
    (hnm : mem.read 2550 75 = nm) (hnml : nm.length = 75)
    (ha1 : mem.read 2630 50 = a1) (ha1l : a1.length = 50)
    (ha2 : mem.read 2710 50 = a2) (ha2l : a2.length = 50)
    (ha3 : mem.read 2790 80 = a3) (ha3l : a3.length = 80)
    (haid : mem.read 3050 20 = aidT) (haidl : aidT.length = 20)
    (hbal : mem.read 3130 13 = balT) (hball : balT.length = 13)
    (hfico : mem.read 3210 20 = ficoT) (hficol : ficoT.length = 20) :
    Sem.execSentences Stm env rec fuel Stm.«5200-WRITE-HTML-NMADBS».body
      ⟨mem, idx, slots, saves, active, out, inp,
        [(1, f1), (2, { mode := some .output, recs := r2 }), (3, f3), (4, f4), (5, f5), (6, f6)],
        clockN⟩
  using [strPiece_match_single, strPiece_match_double, tokB_cons, tokB_nil, length_ovw, strRun_one,
    List.mapM_cons, List.mapM_nil, Option.mapM_some, Option.mapM_none]

/-- The constant texts as byte lists (to compare the model with symbolic execution's output). -/
macro "text_simp" : tactic => `(tactic| simp only [stmtHead, htmlHead, headEvents, hfield, sp,
  List.replicate_succ, List.replicate_zero, List.append_assoc, List.cons_append, List.nil_append,
  List.map_cons, List.map_nil, List.map_append, List.reverse_cons, List.reverse_nil, List.reverse_append,
  List.drop_succ_cons, List.drop_zero, List.singleton_append,
  hL01_lit, hL02_lit, hL03_lit, hL04_lit, hL05_lit, hL06_lit, hL07_lit, hL08_lit, hLTRS_lit, hLTRE_lit, hLTDS_lit, hLTDE_lit, hL10_lit, hL15_lit, hL16_lit, hL17_lit, hL18_lit, hL22_35_lit, hL30_42_lit, hL31_lit, hL43_lit, hL47_lit, hL48_lit, hL50_lit, hL51_lit, hL53_lit, hL54_lit, hL58_lit, hL61_lit, hL64_lit, hL75_lit, hL78_lit, hL79_lit, hL80_lit, c2470_lit, c2625_lit, c2680_lit, c2760_lit, c2870_lit, c2950_lit, c3030_lit, c3070_lit, c3110_lit, c3143_lit, c3190_lit, c3230_lit, c3270_lit, c3350_lit, c3430_lit, c3510_lit, c3606_lit, c3656_lit, c3670_lit, c3750_lit, c3930_lit, c3984_lit, c3989_lit, tP_lit, tEndP_lit, tPStyle_lit, tAcct_lit, tBal_lit, tFico_lit])

/-- What `5000-CREATE-STATEMENT` leaves: the head records appended to both files, their events,
the rest of the state as before but for storage below 180 (record areas) and in 2470 … 4364
(`STATEMENT-LINES`, `HTML-LINES`), where the constant texts stay. -/
def CreateOk (mem : Mem) (idx : List (Nat × Int)) (out : List Event)
    (inp : List (Nat × List (List UInt8))) (clockN : Nat) (r1 r2 : List (List UInt8))
    (f3 f4 f5 f6 : FileSt) (hs hh : List (List UInt8)) (evs : List Event) (r : Sem.Res) : Prop :=
  r.1 = .normal ∧ r.2.idx = idx ∧ r.2.slots = [(.para 8, 3)] ∧ r.2.saves = [] ∧
    r.2.active = [3] ∧ r.2.inp = inp ∧ r.2.clockN = clockN ∧
    r.2.files = [(1, { mode := some .output, recs := r1 ++ hs }),
      (2, { mode := some .output, recs := r2 ++ hh }), (3, f3), (4, f4), (5, f5), (6, f6)] ∧
    r.2.out = evs.reverse ++ out ∧
    r.2.mem.size = 178495 ∧ ConstsOk r.2.mem ∧
    (∀ o l, 180 ≤ o → o + l ≤ 2470 → r.2.mem.read o l = mem.read o l) ∧
    (∀ o l, 4365 ≤ o → r.2.mem.read o l = mem.read o l)

end Cobol.StmCore
