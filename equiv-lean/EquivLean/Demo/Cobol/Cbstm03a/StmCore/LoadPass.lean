/-
# Phase 3 of `CBSTM03AB`: one pass of `8500-READTRNX-READ`

The ways a pass of the table-load paragraph can go, as summaries (right-hand sides computed by
`stm_summary`).  The record in `TRNX-RECORD` has the saved card (`same`: one more transaction
of the current card, `TR-CNT + 1`) or another one (`diff`: the current card's count goes to
`WS-TRCT (CR-CNT)`, card `CR-CNT + 1` begins).  Then the `CALL` of `CBSTM03B` reads the next
record (`GO TO 8500-READTRNX-READ`, paragraph 19) or finds the end of the file
(`..._eof`: `GO TO 8599-EXIT`, paragraph 20).  The counters are `Int`s with two-sided bounds.
-/
import EquivLean.Demo.Cobol.Cbstm03a.StmCore.Summ

open Cobol Cobol.Stm

namespace Cobol.StmCore

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 20000 in
/-- Transaction `t + 1` of card `c`, then record `p` is read. -/
stm_summary pass_same (env : Env) (m' : Nat) (mem : Mem) (hm : mem.size = 178495)
    (idx : List (Nat × Int)) (slots : List (ExitPt × Nat)) (saves : List (Nat × Nat))
    (active : List Nat) (out : List Event) (inp : List (Nat × List (List UInt8))) (clockN : Nat)
    (f1 f2 : FileSt) (trs : List (List UInt8)) (p : Nat) (cu : Option Nat)
    (x : List UInt8) (hxl : x.length = 350) (hx : mem.read 180 350 = x)
    (hs : mem.read 1413 16 = x.take 16)
    (c t : Int) (hca : c.natAbs < 52) (hc1 : 1 ≤ c) (hc2 : c ≤ 51)
    (hta : t.natAbs < 10) (ht1 : 0 ≤ t) (ht2 : t ≤ 9)
    (hc : mem.read 1380 2 = encodeNum {} { digits := 4, signed := true, usage := .binary } c)
    (ht : mem.read 1382 2 = encodeNum {} { digits := 4, signed := true, usage := .binary } t)
    (y : List UInt8) (hy : trs[p]? = some y) (hyl : y.length = 350) :
    Sem.execSentences Stm env (Sem.runFrom Stm env (m' + 40)) (m' + 40)
      Stm.«8500-READTRNX-READ».body
      ⟨mem, idx, slots, saves, active, out, inp,
        [(1, f1), (2, f2), (3, { mode := some .input, recs := trs, pos := p, eof := false, cur := cu })],
        clockN⟩

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 20000 in
/-- Count `t` of card `c` stored, transaction 1 of card `c + 1`, then record `p` is read. -/
stm_summary pass_diff (env : Env) (m' : Nat) (mem : Mem) (hm : mem.size = 178495)
    (idx : List (Nat × Int)) (slots : List (ExitPt × Nat)) (saves : List (Nat × Nat))
    (active : List Nat) (out : List Event) (inp : List (Nat × List (List UInt8))) (clockN : Nat)
    (f1 f2 : FileSt) (trs : List (List UInt8)) (p : Nat) (cu : Option Nat)
    (x : List UInt8) (hxl : x.length = 350) (hx : mem.read 180 350 = x)
    (s : List UInt8) (hsl : s.length = 16) (hs : mem.read 1413 16 = s) (hne : s ≠ x.take 16)
    (c t : Int) (hca : c.natAbs < 51) (hc1 : 1 ≤ c) (hc2 : c ≤ 50)
    (hta : t.natAbs < 11) (ht1 : 0 ≤ t) (ht2 : t ≤ 10)
    (hc : mem.read 1380 2 = encodeNum {} { digits := 4, signed := true, usage := .binary } c)
    (ht : mem.read 1382 2 = encodeNum {} { digits := 4, signed := true, usage := .binary } t)
    (y : List UInt8) (hy : trs[p]? = some y) (hyl : y.length = 350) :
    Sem.execSentences Stm env (Sem.runFrom Stm env (m' + 40)) (m' + 40)
      Stm.«8500-READTRNX-READ».body
      ⟨mem, idx, slots, saves, active, out, inp,
        [(1, f1), (2, f2), (3, { mode := some .input, recs := trs, pos := p, eof := false, cur := cu })],
        clockN⟩

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 20000 in
/-- Transaction `t + 1` of card `c`, then the end of the file. -/
stm_summary pass_same_eof (env : Env) (m' : Nat) (mem : Mem) (hm : mem.size = 178495)
    (idx : List (Nat × Int)) (slots : List (ExitPt × Nat)) (saves : List (Nat × Nat))
    (active : List Nat) (out : List Event) (inp : List (Nat × List (List UInt8))) (clockN : Nat)
    (f1 f2 : FileSt) (trs : List (List UInt8)) (p : Nat) (cu : Option Nat)
    (x : List UInt8) (hxl : x.length = 350) (hx : mem.read 180 350 = x)
    (hs : mem.read 1413 16 = x.take 16)
    (c t : Int) (hca : c.natAbs < 52) (hc1 : 1 ≤ c) (hc2 : c ≤ 51)
    (hta : t.natAbs < 10) (ht1 : 0 ≤ t) (ht2 : t ≤ 9)
    (hc : mem.read 1380 2 = encodeNum {} { digits := 4, signed := true, usage := .binary } c)
    (ht : mem.read 1382 2 = encodeNum {} { digits := 4, signed := true, usage := .binary } t)
    (hy : trs[p]? = none) :
    Sem.execSentences Stm env (Sem.runFrom Stm env (m' + 40)) (m' + 40)
      Stm.«8500-READTRNX-READ».body
      ⟨mem, idx, slots, saves, active, out, inp,
        [(1, f1), (2, f2), (3, { mode := some .input, recs := trs, pos := p, eof := false, cur := cu })],
        clockN⟩

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 20000 in
/-- Count `t` of card `c` stored, transaction 1 of card `c + 1`, then the end of the file. -/
stm_summary pass_diff_eof (env : Env) (m' : Nat) (mem : Mem) (hm : mem.size = 178495)
    (idx : List (Nat × Int)) (slots : List (ExitPt × Nat)) (saves : List (Nat × Nat))
    (active : List Nat) (out : List Event) (inp : List (Nat × List (List UInt8))) (clockN : Nat)
    (f1 f2 : FileSt) (trs : List (List UInt8)) (p : Nat) (cu : Option Nat)
    (x : List UInt8) (hxl : x.length = 350) (hx : mem.read 180 350 = x)
    (s : List UInt8) (hsl : s.length = 16) (hs : mem.read 1413 16 = s) (hne : s ≠ x.take 16)
    (c t : Int) (hca : c.natAbs < 51) (hc1 : 1 ≤ c) (hc2 : c ≤ 50)
    (hta : t.natAbs < 11) (ht1 : 0 ≤ t) (ht2 : t ≤ 10)
    (hc : mem.read 1380 2 = encodeNum {} { digits := 4, signed := true, usage := .binary } c)
    (ht : mem.read 1382 2 = encodeNum {} { digits := 4, signed := true, usage := .binary } t)
    (hy : trs[p]? = none) :
    Sem.execSentences Stm env (Sem.runFrom Stm env (m' + 40)) (m' + 40)
      Stm.«8500-READTRNX-READ».body
      ⟨mem, idx, slots, saves, active, out, inp,
        [(1, f1), (2, f2), (3, { mode := some .input, recs := trs, pos := p, eof := false, cur := cu })],
        clockN⟩

end Cobol.StmCore
