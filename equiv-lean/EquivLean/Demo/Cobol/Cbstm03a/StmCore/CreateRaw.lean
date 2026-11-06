/-
# Phase 5 of `CBSTM03AB`: the summary of `5000-CREATE-STATEMENT`
-/
import EquivLean.Demo.Cobol.Cbstm03a.StmCore.Create

open Cobol Cobol.Stm

namespace Cobol.StmCore

attribute [local cobol_eval high] html5100 html5200

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 50000 in
/-- `5000-CREATE-STATEMENT` on a symbolic state, as computed by symbolic execution (the two
`PERFORM … THRU` ranges by `html5100` and `html5200`): the right-hand side spells out the
records written. -/
stm_summary create_raw (env : Env) (n : Nat) (mem : Mem) (hm : mem.size = 178495)
    (idx : List (Nat × Int)) (out : List Event) (inp : List (Nat × List (List UInt8))) (clockN : Nat)
    (r1 r2 : List (List UInt8)) (f3 f4 f5 f6 : FileSt) (hc : ConstsOk mem)
    (first middle last a1 a2 a3 st co zip : List UInt8)
    (h1 : mem.read 589 25 = first) (h2 : mem.read 614 25 = middle) (h3 : mem.read 639 25 = last)
    (h4 : mem.read 664 50 = a1) (h5 : mem.read 714 50 = a2) (h6 : mem.read 764 50 = a3)
    (h7 : mem.read 814 2 = st) (h8 : mem.read 816 3 = co) (h9 : mem.read 819 10 = zip)
    (l1 : first.length = 25) (l2 : middle.length = 25) (l3 : last.length = 25) (l4 : a1.length = 50)
    (l5 : a2.length = 50) (l6 : a3.length = 50) (l7 : st.length = 2) (l8 : co.length = 3)
    (l9 : zip.length = 10)
    (aid bal fico : Int)
    (haid : decodeNum {} { digits := 11 } (mem.read 1080 11) = some aid)
    (hbal : decodeNum {} { digits := 12, scale := 2, signed := true } (mem.read 1092 12) = some bal)
    (hfico : decodeNum {} { digits := 3 } (mem.read 909 3) = some fico)
    (balT : List UInt8)
    (hed : Edit.edit {} [.nine, .nine, .nine, .nine, .nine, .nine, .nine, .nine, .nine, .dot, .nine,
      .nine, .minus] false bal 2 = some balT) (hbl : balT.length = 13) :
    Sem.execSentences Stm env (Sem.runFrom Stm env (n + 10)) (n + 10)
      Stm.«5000-CREATE-STATEMENT».body
      ⟨mem, idx, [(.para 8, 3)], [], [3], out, inp,
        [(1, { mode := some .output, recs := r1 }), (2, { mode := some .output, recs := r2 }),
         (3, f3), (4, f4), (5, f5), (6, f6)], clockN⟩
  using [strPiece_match_single, strPiece_match_double, length_ovw, strRun_one,
    List.mapM_cons, List.mapM_nil, Option.mapM_some, Option.mapM_none, edit9_zero, editZ_zero]
  with_pre (consts_intro hc)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 50000 in
/-- **Phase 5: `5000-CREATE-STATEMENT`.** Performed from `1000-MAINLINE` (`PERFORM` statement 3
active, no other `PERFORM` pending), on storage holding the customer's name and address fields,
the account id, balance and FICO score (valid numbers; `balT` the edited balance, 13 bytes) and
the constant texts: the paragraph ends normally after appending `stmtHead` to `STMT-FILE` and
`htmlHead` to `HTML-FILE` (with their output events); storage changes only below 180 and in
2470 … 4364, keeping the constant texts. -/
theorem create_stmt (env : Env) (n : Nat) (mem : Mem) (hm : mem.size = 178495)
    (idx : List (Nat × Int)) (out : List Event) (inp : List (Nat × List (List UInt8))) (clockN : Nat)
    (r1 r2 : List (List UInt8)) (f3 f4 f5 f6 : FileSt) (hc : ConstsOk mem)
    (first middle last a1 a2 a3 st co zip : List UInt8)
    (h1 : mem.read 589 25 = first) (h2 : mem.read 614 25 = middle) (h3 : mem.read 639 25 = last)
    (h4 : mem.read 664 50 = a1) (h5 : mem.read 714 50 = a2) (h6 : mem.read 764 50 = a3)
    (h7 : mem.read 814 2 = st) (h8 : mem.read 816 3 = co) (h9 : mem.read 819 10 = zip)
    (l1 : first.length = 25) (l2 : middle.length = 25) (l3 : last.length = 25) (l4 : a1.length = 50)
    (l5 : a2.length = 50) (l6 : a3.length = 50) (l7 : st.length = 2) (l8 : co.length = 3)
    (l9 : zip.length = 10)
    (aid bal fico : Int)
    (haid : decodeNum {} { digits := 11 } (mem.read 1080 11) = some aid)
    (hbal : decodeNum {} { digits := 12, scale := 2, signed := true } (mem.read 1092 12) = some bal)
    (hfico : decodeNum {} { digits := 3 } (mem.read 909 3) = some fico)
    (balT : List UInt8)
    (hed : Edit.edit {} [.nine, .nine, .nine, .nine, .nine, .nine, .nine, .nine, .nine, .dot, .nine,
      .nine, .minus] false bal 2 = some balT) (hbl : balT.length = 13) :
    CreateOk mem idx out inp clockN r1 r2 f3 f4 f5 f6
      (stmtHead (stName first middle last) a1 a2 (stAdd3 a3 st co zip) (stAcctId aid) balT (stFico fico))
      (htmlHead (stName first middle last) a1 a2 (stAdd3 a3 st co zip) (stAcctId aid) balT (stFico fico))
      (headEvents (stName first middle last) a1 a2 (stAdd3 a3 st co zip) (stAcctId aid) balT (stFico fico))
      (Sem.execSentences Stm env (Sem.runFrom Stm env (n + 10)) (n + 10)
        Stm.«5000-CREATE-STATEMENT».body
        ⟨mem, idx, [(.para 8, 3)], [], [3], out, inp,
          [(1, { mode := some .output, recs := r1 }), (2, { mode := some .output, recs := r2 }),
           (3, f3), (4, f4), (5, f5), (6, f6)], clockN⟩) := by
  rw [create_raw env n mem hm idx out inp clockN r1 r2 f3 f4 f5 f6 hc first middle last a1 a2 a3 st co
    zip h1 h2 h3 h4 h5 h6 h7 h8 h9 l1 l2 l3 l4 l5 l6 l7 l8 l9 aid bal fico haid hbal hfico balT hed hbl]
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [stName, stAdd3, stAcctId, stFico]
    text_simp
  · simp only [stName, stAdd3, stAcctId, stFico]
    text_simp
  · simp [hm]
  · consts_intro hc
    simp only [ConstsOk]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_⟩ <;> stm_auto [length_ovw]
  · intro o l ho hl
    stm_auto [length_ovw]
  · intro o l ho
    stm_auto [length_ovw]

end Cobol.StmCore
