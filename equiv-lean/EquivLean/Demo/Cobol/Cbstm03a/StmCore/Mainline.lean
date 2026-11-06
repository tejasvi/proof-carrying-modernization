/-
# Phase 4 of `CBSTM03AB`: the cross-reference loop (`1000-MAINLINE`)

`1000-MAINLINE` (paragraph 2) reads the cross-reference file through `CBSTM03B`
(`1000-XREFFILE-GET-NEXT`) until its end; for each record it reads the customer and the account
by key (`2000-CUSTFILE-GET`, `3000-ACCTFILE-GET`, keyed `READ`s in `CBSTM03B`), writes the
statement head (`5000-CREATE-STATEMENT`, phase 5) and the transactions of the card
(`4000-TRNXFILE-GET`, phase 6).  Then it closes the four files through `CBSTM03B`, closes its
own two files, and ends with `GOBACK`.
-/
import EquivLean.Demo.Cobol.Cbstm03a.StmCore.Trans
import EquivLean.Demo.Cobol.Cbstm03a.StmCore.CreateRaw

open Cobol Cobol.Stm

namespace Cobol.StmCore

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 50000 in
/-- `1000-XREFFILE-GET-NEXT` reading record `p` (`CARD-XREF-RECORD`). -/
stm_summary xref_found (env : Env) (n : Nat) (mem : Mem) (hm : mem.size = 178495)
    (idx : List (Nat × Int)) (out : List Event) (inp : List (Nat × List (List UInt8))) (clockN : Nat)
    (f1 f2 f3 f5 f6 : FileSt) (xrs : List (List UInt8)) (p : Nat) (cu : Option Nat)
    (x : List UInt8) (hy : xrs[p]? = some x) (hxl : x.length = 50) :
    Sem.execSentences Stm env (Sem.runFrom Stm env (n + 9)) (n + 9)
      Stm.«1000-XREFFILE-GET-NEXT».body
      ⟨mem, idx, [(.para 4, 0)], [], [0], out, inp,
        [(1, f1), (2, f2), (3, f3),
         (4, { mode := some .input, recs := xrs, pos := p, eof := false, cur := cu }),
         (5, f5), (6, f6)], clockN⟩

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 50000 in
/-- `1000-XREFFILE-GET-NEXT` at the end of the file: `END-OF-FILE = 'Y'`. -/
stm_summary xref_eof (env : Env) (n : Nat) (mem : Mem) (hm : mem.size = 178495)
    (idx : List (Nat × Int)) (out : List Event) (inp : List (Nat × List (List UInt8))) (clockN : Nat)
    (f1 f2 f3 f5 f6 : FileSt) (xrs : List (List UInt8)) (p : Nat) (cu : Option Nat)
    (hy : xrs[p]? = none) :
    Sem.execSentences Stm env (Sem.runFrom Stm env (n + 9)) (n + 9)
      Stm.«1000-XREFFILE-GET-NEXT».body
      ⟨mem, idx, [(.para 4, 0)], [], [0], out, inp,
        [(1, f1), (2, f2), (3, f3),
         (4, { mode := some .input, recs := xrs, pos := p, eof := false, cur := cu }),
         (5, f5), (6, f6)], clockN⟩

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 50000 in
/-- `2000-CUSTFILE-GET`: the customer with the cross-reference's customer id. -/
stm_summary cust_found (env : Env) (n : Nat) (mem : Mem) (hm : mem.size = 178495)
    (idx : List (Nat × Int)) (out : List Event) (inp : List (Nat × List (List UInt8))) (clockN : Nat)
    (f1 f2 f3 f4 f6 : FileSt) (cs : List (List UInt8)) (q : Nat) (e : Bool) (cu : Option Nat)
    (cid : Int) (hcid : decodeNum {} { digits := 9 } (mem.read 546 9) = some cid)
    (i : Nat) (hk : Sem.findKey { off := 0, len := 9 } (Sem.digitChars {} 9 cid.natAbs) cs = some i)
    (hrl : (cs.getD i []).length = 500) :
    Sem.execSentences Stm env (Sem.runFrom Stm env (n + 9)) (n + 9)
      Stm.«2000-CUSTFILE-GET».body
      ⟨mem, idx, [(.para 5, 1)], [], [1], out, inp,
        [(1, f1), (2, f2), (3, f3), (4, f4),
         (5, { mode := some .input, recs := cs, pos := q, eof := e, cur := cu }), (6, f6)], clockN⟩

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 50000 in
/-- `3000-ACCTFILE-GET`: the account with the cross-reference's account id. -/
stm_summary acct_found (env : Env) (n : Nat) (mem : Mem) (hm : mem.size = 178495)
    (idx : List (Nat × Int)) (out : List Event) (inp : List (Nat × List (List UInt8))) (clockN : Nat)
    (f1 f2 f3 f4 f5 : FileSt) (as : List (List UInt8)) (q : Nat) (e : Bool) (cu : Option Nat)
    (aid : Int) (haid : decodeNum {} { digits := 11 } (mem.read 555 11) = some aid)
    (haidb : aid.natAbs < 100000000000)
    (i : Nat) (hk : Sem.findKey { off := 0, len := 11 } (Sem.digitChars {} 11 aid.natAbs) as = some i)
    (hrl : (as.getD i []).length = 300) :
    Sem.execSentences Stm env (Sem.runFrom Stm env (n + 9)) (n + 9)
      Stm.«3000-ACCTFILE-GET».body
      ⟨mem, idx, [(.para 6, 2)], [], [2], out, inp,
        [(1, f1), (2, f2), (3, f3), (4, f4), (5, f5),
         (6, { mode := some .input, recs := as, pos := q, eof := e, cur := cu })], clockN⟩
  using [decodeNum_digitChars11, encodeNum_digits11]

attribute [local cobol_eval high] html5100 html5200

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 50000 in
/-- `create_raw` with the constant texts as separate facts (so that it can rewrite at a call site). -/
stm_summary create_rawE (env : Env) (n : Nat) (mem : Mem) (hm : mem.size = 178495)
    (idx : List (Nat × Int)) (out : List Event) (inp : List (Nat × List (List UInt8))) (clockN : Nat)
    (r1 r2 : List (List UInt8)) (f3 f4 f5 f6 : FileSt)
    (k01 : mem.read 2470 80 = [92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 226, 227, 193, 217, 227, 64, 214, 198, 64, 226, 227, 193, 227, 197, 212, 197, 213, 227, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92])
    (k02 : mem.read 2625 5 = [64, 64, 64, 64, 64])
    (k03 : mem.read 2680 30 = [64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64])
    (k04 : mem.read 2760 30 = [64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64])
    (k05 : mem.read 2870 80 = [96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96])
    (k06 : mem.read 2950 80 = [64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 194, 129, 162, 137, 131, 64, 196, 133, 163, 129, 137, 147, 162, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64])
    (k07 : mem.read 3030 20 = [193, 131, 131, 150, 164, 149, 163, 64, 201, 196, 64, 64, 64, 64, 64, 64, 64, 64, 64, 122])
    (k08 : mem.read 3070 40 = [64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64])
    (k09 : mem.read 3110 20 = [195, 164, 153, 153, 133, 149, 163, 64, 194, 129, 147, 129, 149, 131, 133, 64, 64, 64, 64, 122])
    (k10 : mem.read 3143 47 = [64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64])
    (k11 : mem.read 3190 20 = [198, 201, 195, 214, 64, 226, 131, 150, 153, 133, 64, 64, 64, 64, 64, 64, 64, 64, 64, 122])
    (k12 : mem.read 3230 40 = [64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64])
    (k13 : mem.read 3270 80 = [96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96])
    (k14 : mem.read 3350 80 = [64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 227, 217, 193, 213, 226, 193, 195, 227, 201, 214, 213, 64, 226, 228, 212, 212, 193, 217, 232, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64])
    (k15 : mem.read 3430 80 = [96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96])
    (k16 : mem.read 3510 80 = [227, 153, 129, 149, 64, 201, 196, 64, 64, 64, 64, 64, 64, 64, 64, 64, 227, 153, 129, 149, 64, 196, 133, 163, 129, 137, 147, 162, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 227, 153, 129, 149, 64, 193, 148, 150, 164, 149, 163])
    (k17 : mem.read 3606 1 = [64])
    (k18 : mem.read 3656 1 = [91])
    (k19 : mem.read 3670 67 = [227, 150, 163, 129, 147, 64, 197, 231, 215, 122, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 91])
    (k20 : mem.read 3750 80 = [92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 197, 213, 196, 64, 214, 198, 64, 226, 227, 193, 227, 197, 212, 197, 213, 227, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92])
    (k21 : mem.read 3930 34 = [76, 136, 243, 110, 226, 163, 129, 163, 133, 148, 133, 149, 163, 64, 134, 150, 153, 64, 193, 131, 131, 150, 164, 149, 163, 64, 213, 164, 148, 130, 133, 153, 122, 64])
    (k22 : mem.read 3984 5 = [76, 97, 136, 243, 110])
    (k23 : mem.read 3989 26 = [76, 151, 64, 162, 163, 168, 147, 133, 126, 127, 134, 150, 149, 163, 96, 162, 137, 169, 133, 122, 241, 246, 151, 167, 127, 110])
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
    Sem.execSentences Stm env (Sem.runFrom Stm env (n + 9)) (n + 9)
      Stm.«5000-CREATE-STATEMENT».body
      ⟨mem, idx, [(.para 8, 3)], [], [3], out, inp,
        [(1, { mode := some .output, recs := r1 }), (2, { mode := some .output, recs := r2 }),
         (3, f3), (4, f4), (5, f5), (6, f6)], clockN⟩
  using [strPiece_match_single, strPiece_match_double, length_ovw, strRun_one,
    List.mapM_cons, List.mapM_nil, Option.mapM_some, Option.mapM_none, edit9_zero, editZ_zero]

theorem exists_of_normalAnd {I : State → Prop} {r : Sem.Res} (h : NormalAnd I r) :
    ∃ st, r = (.normal, st) ∧ I st := ⟨r.2, res_eq_of_fst h.1, h.2⟩

/-- What `PERFORM 4000-TRNXFILE-GET` leaves (statement 6 of `1000-MAINLINE`, returned). -/
def Post4 (X : List UInt8) (gs : List (List (List UInt8))) (mem0 : Mem)
    (idx : List (Nat × Int)) (out : List Event) (inp : List (Nat × List (List UInt8)))
    (clockN : Nat) (r1 r2 : List (List UInt8)) (f3 f4 f5 f6 : FileSt) (st : State) : Prop :=
  st.idx = idx ∧ st.slots = [] ∧ st.saves = [] ∧ st.active = [] ∧ st.inp = inp ∧
    st.clockN = clockN ∧
    st.out = (trnxEvents X gs).reverse ++ out ∧
    st.files = [(1, { mode := some .output, recs := r1 ++ trnxStmt X gs }),
      (2, { mode := some .output, recs := r2 ++ trnxHtml X gs }), (3, f3), (4, f4), (5, f5),
      (6, f6)] ∧
    st.mem.size = 178495 ∧ TrnxFrame mem0 st.mem

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 50000 in
/-- `PERFORM 4000-TRNXFILE-GET` (statement 6 of `1000-MAINLINE`). -/
theorem perform4_ok (env : Env) (m : Nat) (hm50 : 50 ≤ m) (mem0 : Mem) (hm : mem0.size = 178495)
    (idx : List (Nat × Int)) (out : List Event) (inp : List (Nat × List (List UInt8))) (clockN : Nat)
    (r1 r2 : List (List UInt8)) (f3 f4 f5 f6 : FileSt)
    (gs : List (List (List UInt8))) (hG : gs.length ≤ 50) (hT : ∀ g ∈ gs, g.length ≤ 10)
    (hrecs : ∀ g ∈ gs, ∀ r ∈ g, r.length = 350 ∧ AmtOk r)
    (htab : TableOk mem0 gs) (htrct : TrctOk mem0 gs gs.length)
    (hcr : mem0.read 1380 2 = encodeNum {} { digits := 4, signed := true, usage := .binary }
      (gs.length : Int))
    (X : List UInt8) (hXl : X.length = 16) (hX : mem0.read 530 16 = X)
    (hc : ConstsOk mem0)
    (hacc : mem0.read 1388 6 =
      encodeNum {} { digits := 11, scale := 2, signed := true, usage := .packed } 0) (fuel : Nat) :
    NormalAnd (Post4 X gs mem0 idx out inp clockN r1 r2 f3 f4 f5 f6)
      (Sem.execStmt Stm env (Sem.runFrom Stm env (m + 2)) fuel Stm.«1000-MAINLINE».s6
        ⟨mem0, idx, [], [], [], out, inp,
          [(1, { mode := some .output, recs := r1 }), (2, { mode := some .output, recs := r2 }),
           (3, f3), (4, f4), (5, f5), (6, f6)], clockN⟩) := by
  obtain ⟨R, hE, hp⟩ := exists_of_normalAnd (trnx_ok env m hm50 mem0 hm idx out inp clockN r1 r2 f3
    f4 f5 f6 gs hG hT hrecs htab htrct hcr X hXl hX hc hacc)
  obtain ⟨mR, idxR, slotsR, savesR, activeR, outR, inpR, filesR, clockNR⟩ := R
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hp
  dsimp only at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  subst idxR slotsR savesR activeR inpR clockNR outR filesR
  unfold NormalAnd Post4
  stm_auto [↓hE]
  exact h10

theorem read_eq_of_region {m m0 : Mem} {a n : Nat} (h : m.read a n = m0.read a n) {o l : Nat}
    (h1 : a ≤ o) (h2 : o + l ≤ a + n) : m.read o l = m0.read o l := by
  rw [Mem.read_of_read_sub h h1 h2, Mem.read_of_read_sub rfl h1 h2]

theorem TableOk_of_region {m m0 : Mem} {gs : List (List (List UInt8))} (hT : TableOk m0 gs)
    (hG : gs.length ≤ 50) (hTl : ∀ g ∈ gs, g.length ≤ 10)
    (h : m.read 4365 171258 = m0.read 4365 171258) : TableOk m gs := by
  intro k hk1 hk2
  obtain ⟨a, b⟩ := hT k hk1 hk2
  refine ⟨(read_eq_of_region h (by omega) (by omega)).trans a, fun j hj1 hj2 => ?_⟩
  have hjl : j ≤ 10 := by
    have := hTl (gs.getD (k - 1) []) (by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
      exact List.getElem_mem _)
    omega
  obtain ⟨c, d⟩ := b j hj1 hj2
  exact ⟨(read_eq_of_region h (by omega) (by omega)).trans c,
    (read_eq_of_region h (by omega) (by omega)).trans d⟩

theorem TrctOk_of_region {m m0 : Mem} {gs : List (List (List UInt8))} {n : Nat} (hT : TrctOk m0 gs n)
    (hn : n ≤ 51) (h : m.read 4365 171258 = m0.read 4365 171258) : TrctOk m gs n := by
  intro k hk1 hk2
  exact (read_eq_of_region h (by omega) (by omega)).trans (hT k hk1 hk2)

/-- The facts about the table and the transaction file that hold for the whole loop. -/
def P4Static (m : Nat) (gs : List (List (List UInt8))) (m0 : Mem) : Prop :=
  50 ≤ m ∧ gs.length ≤ 50 ∧ (∀ g ∈ gs, g.length ≤ 10) ∧ (∀ g ∈ gs, ∀ r ∈ g, r.length = 350 ∧ AmtOk r) ∧
    TableOk m0 gs ∧ TrctOk m0 gs gs.length

/-- The state after `PERFORM 4000-TRNXFILE-GET` (statement 6 of `1000-MAINLINE`). -/
def p4st (env : Env) (m fuel : Nat) (st : State) : State :=
  (Sem.execStmt Stm env (Sem.runFrom Stm env (m + 2)) fuel Stm.«1000-MAINLINE».s6 st).2

set_option maxHeartbeats 100000000 in
/-- `PERFORM 4000-TRNXFILE-GET` as a rewrite: the files and events of `trnx_ok`, the storage
`p4st` (whose reads `p4_read` gives). -/
theorem perform4_eq (env : Env) (m : Nat) (mem : Mem) (hm : mem.size = 178495)
    (idx : List (Nat × Int)) (out : List Event) (inp : List (Nat × List (List UInt8))) (clockN : Nat)
    (r1 r2 : List (List UInt8)) (f3 f4 f5 f6 : FileSt)
    (gs : List (List (List UInt8)))
    (hcr : mem.read 1380 2 = encodeNum {} { digits := 4, signed := true, usage := .binary }
      (gs.length : Int))
    (m0 : Mem) (htbl : mem.read 4365 171258 = m0.read 4365 171258) (hS : P4Static m gs m0)
    (X : List UInt8) (hX : mem.read 530 16 = X) (hXl : X.length = 16)
    (k01 : mem.read 2470 80 = [92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 226, 227, 193, 217, 227, 64, 214, 198, 64, 226, 227, 193, 227, 197, 212, 197, 213, 227, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92])
    (k02 : mem.read 2625 5 = [64, 64, 64, 64, 64])
    (k03 : mem.read 2680 30 = [64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64])
    (k04 : mem.read 2760 30 = [64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64])
    (k05 : mem.read 2870 80 = [96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96])
    (k06 : mem.read 2950 80 = [64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 194, 129, 162, 137, 131, 64, 196, 133, 163, 129, 137, 147, 162, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64])
    (k07 : mem.read 3030 20 = [193, 131, 131, 150, 164, 149, 163, 64, 201, 196, 64, 64, 64, 64, 64, 64, 64, 64, 64, 122])
    (k08 : mem.read 3070 40 = [64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64])
    (k09 : mem.read 3110 20 = [195, 164, 153, 153, 133, 149, 163, 64, 194, 129, 147, 129, 149, 131, 133, 64, 64, 64, 64, 122])
    (k10 : mem.read 3143 47 = [64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64])
    (k11 : mem.read 3190 20 = [198, 201, 195, 214, 64, 226, 131, 150, 153, 133, 64, 64, 64, 64, 64, 64, 64, 64, 64, 122])
    (k12 : mem.read 3230 40 = [64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64])
    (k13 : mem.read 3270 80 = [96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96])
    (k14 : mem.read 3350 80 = [64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 227, 217, 193, 213, 226, 193, 195, 227, 201, 214, 213, 64, 226, 228, 212, 212, 193, 217, 232, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64])
    (k15 : mem.read 3430 80 = [96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96])
    (k16 : mem.read 3510 80 = [227, 153, 129, 149, 64, 201, 196, 64, 64, 64, 64, 64, 64, 64, 64, 64, 227, 153, 129, 149, 64, 196, 133, 163, 129, 137, 147, 162, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 227, 153, 129, 149, 64, 193, 148, 150, 164, 149, 163])
    (k17 : mem.read 3606 1 = [64])
    (k18 : mem.read 3656 1 = [91])
    (k19 : mem.read 3670 67 = [227, 150, 163, 129, 147, 64, 197, 231, 215, 122, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 91])
    (k20 : mem.read 3750 80 = [92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 197, 213, 196, 64, 214, 198, 64, 226, 227, 193, 227, 197, 212, 197, 213, 227, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92])
    (k21 : mem.read 3930 34 = [76, 136, 243, 110, 226, 163, 129, 163, 133, 148, 133, 149, 163, 64, 134, 150, 153, 64, 193, 131, 131, 150, 164, 149, 163, 64, 213, 164, 148, 130, 133, 153, 122, 64])
    (k22 : mem.read 3984 5 = [76, 97, 136, 243, 110])
    (k23 : mem.read 3989 26 = [76, 151, 64, 162, 163, 168, 147, 133, 126, 127, 134, 150, 149, 163, 96, 162, 137, 169, 133, 122, 241, 246, 151, 167, 127, 110])
    (hacc : mem.read 1388 6 =
      encodeNum {} { digits := 11, scale := 2, signed := true, usage := .packed } 0) (fuel : Nat) :
    Sem.execStmt Stm env (Sem.runFrom Stm env (m + 2)) fuel Stm.«1000-MAINLINE».s6
        ⟨mem, idx, [], [], [], out, inp,
          [(1, { mode := some .output, recs := r1 }), (2, { mode := some .output, recs := r2 }),
           (3, f3), (4, f4), (5, f5), (6, f6)], clockN⟩ =
      (.normal, ⟨(p4st env m fuel ⟨mem, idx, [], [], [], out, inp,
          [(1, { mode := some .output, recs := r1 }), (2, { mode := some .output, recs := r2 }),
           (3, f3), (4, f4), (5, f5), (6, f6)], clockN⟩).mem, idx, [], [], [],
        (trnxEvents X gs).reverse ++ out, inp,
        [(1, { mode := some .output, recs := r1 ++ trnxStmt X gs }),
         (2, { mode := some .output, recs := r2 ++ trnxHtml X gs }), (3, f3), (4, f4), (5, f5), (6, f6)],
        clockN⟩) := by
  obtain ⟨hm50, hG, hT, hrecs, hT0, hR0⟩ := hS
  have hc : ConstsOk mem := ⟨k01, k02, k03, k04, k05, k06, k07, k08, k09, k10, k11, k12, k13, k14, k15, k16, k17, k18, k19, k20, k21, k22, k23⟩
  obtain ⟨R, hE, hp⟩ := exists_of_normalAnd (perform4_ok env m hm50 mem hm idx out inp
    clockN r1 r2 f3 f4 f5 f6 gs hG hT hrecs (TableOk_of_region hT0 hG hT htbl)
    (TrctOk_of_region hR0 (by omega) htbl) hcr X hXl hX hc hacc fuel)
  obtain ⟨mR, idxR, slotsR, savesR, activeR, outR, inpR, filesR, clockNR⟩ := R
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hp
  dsimp only at h1 h2 h3 h4 h5 h6 h7 h8
  subst h1 h2 h3 h4 h5 h6 h7 h8
  simp only [p4st, hE]


/-! ## The statement of one cross-reference record -/

/-- Card number, customer id (`9(9)`) and account id (`9(11)`) of a 50-byte `CARD-XREF-RECORD`. -/
def xCard (x : List UInt8) : List UInt8 := x.take 16
def xCid (x : List UInt8) : Int := (decodeNum {} { digits := 9 } ((x.drop 16).take 9)).getD 0
def xAid (x : List UInt8) : Int := (decodeNum {} { digits := 11 } ((x.drop 25).take 11)).getD 0

/-- The customer record `CBSTM03B` reads by key (the first with the customer id's digits). -/
def custOf (custs : List (List UInt8)) (x : List UInt8) : List UInt8 :=
  custs.getD ((Sem.findKey { off := 0, len := 9 } (Sem.digitChars {} 9 (xCid x).natAbs) custs).getD 0) []

/-- The account record `CBSTM03B` reads by key. -/
def acctOf (accts : List (List UInt8)) (x : List UInt8) : List UInt8 :=
  accts.getD ((Sem.findKey { off := 0, len := 11 } (Sem.digitChars {} 11 (xAid x).natAbs) accts).getD 0)
    []

/-- Account id (`9(11)`), current balance (`S9(10)V99`) of an account record; FICO score
(`9(3)`) of a customer record. -/
def aAid (a : List UInt8) : Int := (decodeNum {} { digits := 11 } (a.take 11)).getD 0
def aBal (a : List UInt8) : Int :=
  (decodeNum {} { digits := 12, scale := 2, signed := true } ((a.drop 12).take 12)).getD 0
def cFico (c : List UInt8) : Int := (decodeNum {} { digits := 3 } ((c.drop 329).take 3)).getD 0

/-- A field of a record. -/
def fld (r : List UInt8) (o n : Nat) : List UInt8 := (r.drop o).take n

/-- The head of the statement for customer `c` and account `a`. -/
def headS (c a : List UInt8) : List (List UInt8) :=
  stmtHead (stName (fld c 9 25) (fld c 34 25) (fld c 59 25)) (fld c 84 50) (fld c 134 50)
    (stAdd3 (fld c 184 50) (fld c 234 2) (fld c 236 3) (fld c 239 10)) (stAcctId (aAid a))
    (edit9 (aBal a)) (stFico (cFico c))

def headH (c a : List UInt8) : List (List UInt8) :=
  htmlHead (stName (fld c 9 25) (fld c 34 25) (fld c 59 25)) (fld c 84 50) (fld c 134 50)
    (stAdd3 (fld c 184 50) (fld c 234 2) (fld c 236 3) (fld c 239 10)) (stAcctId (aAid a))
    (edit9 (aBal a)) (stFico (cFico c))

def headE (c a : List UInt8) : List Event :=
  headEvents (stName (fld c 9 25) (fld c 34 25) (fld c 59 25)) (fld c 84 50) (fld c 134 50)
    (stAdd3 (fld c 184 50) (fld c 234 2) (fld c 236 3) (fld c 239 10)) (stAcctId (aAid a))
    (edit9 (aBal a)) (stFico (cFico c))

/-- **The `STMT-FILE` records of one cross-reference record**: the statement head of its
customer and account, its card's transactions from the table, the total, the closing lines. -/
def stmtOf (gs : List (List (List UInt8))) (custs accts : List (List UInt8)) (x : List UInt8) :
    List (List UInt8) :=
  headS (custOf custs x) (acctOf accts x) ++ trnxStmt (xCard x) gs

/-- The `HTML-FILE` records of one cross-reference record. -/
def htmlOf (gs : List (List (List UInt8))) (custs accts : List (List UInt8)) (x : List UInt8) :
    List (List UInt8) :=
  headH (custOf custs x) (acctOf accts x) ++ trnxHtml (xCard x) gs

/-- The output events of one cross-reference record, in program order. -/
def evsOf (gs : List (List (List UInt8))) (custs accts : List (List UInt8)) (x : List UInt8) :
    List Event :=
  headE (custOf custs x) (acctOf accts x) ++ trnxEvents (xCard x) gs

/-- A cross-reference record the program processes without abending: 50 bytes, valid ids, its
customer and account found (records of 500 and 300 bytes) with valid numeric fields. -/
def XOk (custs accts : List (List UInt8)) (x : List UInt8) : Prop :=
  x.length = 50 ∧
  decodeNum {} { digits := 9 } ((x.drop 16).take 9) = some (xCid x) ∧
  decodeNum {} { digits := 11 } ((x.drop 25).take 11) = some (xAid x) ∧
  (Sem.findKey { off := 0, len := 9 } (Sem.digitChars {} 9 (xCid x).natAbs) custs).isSome ∧
  (custOf custs x).length = 500 ∧
  (Sem.findKey { off := 0, len := 11 } (Sem.digitChars {} 11 (xAid x).natAbs) accts).isSome ∧
  (acctOf accts x).length = 300 ∧
  decodeNum {} { digits := 11 } ((acctOf accts x).take 11) = some (aAid (acctOf accts x)) ∧
  decodeNum {} { digits := 12, scale := 2, signed := true } (((acctOf accts x).drop 12).take 12) =
    some (aBal (acctOf accts x)) ∧
  decodeNum {} { digits := 3 } (((custOf custs x).drop 329).take 3) = some (cFico (custOf custs x))

/-- Invariant of the cross-reference loop, indexed by the reads still to do (`some x`: a record,
`none`: the end of the file). -/
def MInv (gs : List (List (List UInt8))) (xrefs custs accts : List (List UInt8)) (m0 : Mem)
    (idx : List (Nat × Int)) (inp : List (Nat × List (List UInt8))) (clockN : Nat)
    (out0 : List Event) (r1 r2 : List (List UInt8)) (f3 : FileSt)
    (items : List (Option (List UInt8))) (st : State) : Prop :=
  ∃ done rest, xrefs = done ++ rest ∧
    st.idx = idx ∧ st.slots = [] ∧ st.saves = [] ∧ st.active = [] ∧ st.inp = inp ∧
    st.clockN = clockN ∧
    st.out = (done.flatMap (evsOf gs custs accts)).reverse ++ out0 ∧
    st.mem.size = 178495 ∧
    st.mem.read 4365 171258 = m0.read 4365 171258 ∧
    st.mem.read 1380 2 = encodeNum {} { digits := 4, signed := true, usage := .binary }
      (gs.length : Int) ∧
    ConstsOk st.mem ∧
    ∃ q5 e5 c5 q6 e6 c6 cu4,
      (items = rest.map some ++ [none] ∧ st.mem.read 1429 1 = [213] ∧
        st.files = [(1, { mode := some .output, recs := r1 ++ done.flatMap (stmtOf gs custs accts) }),
          (2, { mode := some .output, recs := r2 ++ done.flatMap (htmlOf gs custs accts) }), (3, f3),
          (4, { mode := some .input, recs := xrefs, pos := done.length, eof := false, cur := cu4 }),
          (5, { mode := some .input, recs := custs, pos := q5, eof := e5, cur := c5 }),
          (6, { mode := some .input, recs := accts, pos := q6, eof := e6, cur := c6 })]) ∨
      (items = [] ∧ rest = [] ∧ st.mem.read 1429 1 = [232] ∧
        st.files = [(1, { mode := some .output, recs := r1 ++ done.flatMap (stmtOf gs custs accts) }),
          (2, { mode := some .output, recs := r2 ++ done.flatMap (htmlOf gs custs accts) }), (3, f3),
          (4, { mode := some .input, recs := xrefs, pos := done.length, eof := true }),
          (5, { mode := some .input, recs := custs, pos := q5, eof := e5, cur := c5 }),
          (6, { mode := some .input, recs := accts, pos := q6, eof := e6, cur := c6 })])

set_option maxHeartbeats 100000000 in
/-- What `PERFORM 4000-TRNXFILE-GET` does not write. -/
theorem p4_frame (env : Env) (m : Nat) (mem : Mem) (hm : mem.size = 178495)
    (idx : List (Nat × Int)) (out : List Event) (inp : List (Nat × List (List UInt8))) (clockN : Nat)
    (r1 r2 : List (List UInt8)) (f3 f4 f5 f6 : FileSt)
    (gs : List (List (List UInt8)))
    (hcr : mem.read 1380 2 = encodeNum {} { digits := 4, signed := true, usage := .binary }
      (gs.length : Int))
    (m0 : Mem) (htbl : mem.read 4365 171258 = m0.read 4365 171258) (hS : P4Static m gs m0)
    (X : List UInt8) (hX : mem.read 530 16 = X) (hXl : X.length = 16)
    (k01 : mem.read 2470 80 = [92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 226, 227, 193, 217, 227, 64, 214, 198, 64, 226, 227, 193, 227, 197, 212, 197, 213, 227, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92])
    (k02 : mem.read 2625 5 = [64, 64, 64, 64, 64])
    (k03 : mem.read 2680 30 = [64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64])
    (k04 : mem.read 2760 30 = [64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64])
    (k05 : mem.read 2870 80 = [96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96])
    (k06 : mem.read 2950 80 = [64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 194, 129, 162, 137, 131, 64, 196, 133, 163, 129, 137, 147, 162, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64])
    (k07 : mem.read 3030 20 = [193, 131, 131, 150, 164, 149, 163, 64, 201, 196, 64, 64, 64, 64, 64, 64, 64, 64, 64, 122])
    (k08 : mem.read 3070 40 = [64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64])
    (k09 : mem.read 3110 20 = [195, 164, 153, 153, 133, 149, 163, 64, 194, 129, 147, 129, 149, 131, 133, 64, 64, 64, 64, 122])
    (k10 : mem.read 3143 47 = [64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64])
    (k11 : mem.read 3190 20 = [198, 201, 195, 214, 64, 226, 131, 150, 153, 133, 64, 64, 64, 64, 64, 64, 64, 64, 64, 122])
    (k12 : mem.read 3230 40 = [64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64])
    (k13 : mem.read 3270 80 = [96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96])
    (k14 : mem.read 3350 80 = [64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 227, 217, 193, 213, 226, 193, 195, 227, 201, 214, 213, 64, 226, 228, 212, 212, 193, 217, 232, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64])
    (k15 : mem.read 3430 80 = [96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96])
    (k16 : mem.read 3510 80 = [227, 153, 129, 149, 64, 201, 196, 64, 64, 64, 64, 64, 64, 64, 64, 64, 227, 153, 129, 149, 64, 196, 133, 163, 129, 137, 147, 162, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 227, 153, 129, 149, 64, 193, 148, 150, 164, 149, 163])
    (k17 : mem.read 3606 1 = [64])
    (k18 : mem.read 3656 1 = [91])
    (k19 : mem.read 3670 67 = [227, 150, 163, 129, 147, 64, 197, 231, 215, 122, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 91])
    (k20 : mem.read 3750 80 = [92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 197, 213, 196, 64, 214, 198, 64, 226, 227, 193, 227, 197, 212, 197, 213, 227, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92])
    (k21 : mem.read 3930 34 = [76, 136, 243, 110, 226, 163, 129, 163, 133, 148, 133, 149, 163, 64, 134, 150, 153, 64, 193, 131, 131, 150, 164, 149, 163, 64, 213, 164, 148, 130, 133, 153, 122, 64])
    (k22 : mem.read 3984 5 = [76, 97, 136, 243, 110])
    (k23 : mem.read 3989 26 = [76, 151, 64, 162, 163, 168, 147, 133, 126, 127, 134, 150, 149, 163, 96, 162, 137, 169, 133, 122, 241, 246, 151, 167, 127, 110])
    (hacc : mem.read 1388 6 =
      encodeNum {} { digits := 11, scale := 2, signed := true, usage := .packed } 0) (fuel : Nat) :
    TrnxFrame mem (p4st env m fuel ⟨mem, idx, [], [], [], out, inp,
          [(1, { mode := some .output, recs := r1 }), (2, { mode := some .output, recs := r2 }),
           (3, f3), (4, f4), (5, f5), (6, f6)], clockN⟩).mem := by
  obtain ⟨hm50, hG, hT, hrecs, hT0, hR0⟩ := hS
  have hc : ConstsOk mem := ⟨k01, k02, k03, k04, k05, k06, k07, k08, k09, k10, k11, k12, k13, k14, k15, k16, k17, k18, k19, k20, k21, k22, k23⟩
  obtain ⟨R, hE, hp⟩ := exists_of_normalAnd (perform4_ok env m hm50 mem hm idx out inp
    clockN r1 r2 f3 f4 f5 f6 gs hG hT hrecs (TableOk_of_region hT0 hG hT htbl)
    (TrctOk_of_region hR0 (by omega) htbl) hcr X hXl hX hc hacc fuel)
  simp only [p4st, hE]
  exact hp.2.2.2.2.2.2.2.2.2

set_option maxHeartbeats 100000000 in
theorem p4_size (env : Env) (m : Nat) (mem : Mem) (hm : mem.size = 178495)
    (idx : List (Nat × Int)) (out : List Event) (inp : List (Nat × List (List UInt8))) (clockN : Nat)
    (r1 r2 : List (List UInt8)) (f3 f4 f5 f6 : FileSt)
    (gs : List (List (List UInt8)))
    (hcr : mem.read 1380 2 = encodeNum {} { digits := 4, signed := true, usage := .binary }
      (gs.length : Int))
    (m0 : Mem) (htbl : mem.read 4365 171258 = m0.read 4365 171258) (hS : P4Static m gs m0)
    (X : List UInt8) (hX : mem.read 530 16 = X) (hXl : X.length = 16)
    (k01 : mem.read 2470 80 = [92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 226, 227, 193, 217, 227, 64, 214, 198, 64, 226, 227, 193, 227, 197, 212, 197, 213, 227, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92])
    (k02 : mem.read 2625 5 = [64, 64, 64, 64, 64])
    (k03 : mem.read 2680 30 = [64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64])
    (k04 : mem.read 2760 30 = [64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64])
    (k05 : mem.read 2870 80 = [96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96])
    (k06 : mem.read 2950 80 = [64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 194, 129, 162, 137, 131, 64, 196, 133, 163, 129, 137, 147, 162, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64])
    (k07 : mem.read 3030 20 = [193, 131, 131, 150, 164, 149, 163, 64, 201, 196, 64, 64, 64, 64, 64, 64, 64, 64, 64, 122])
    (k08 : mem.read 3070 40 = [64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64])
    (k09 : mem.read 3110 20 = [195, 164, 153, 153, 133, 149, 163, 64, 194, 129, 147, 129, 149, 131, 133, 64, 64, 64, 64, 122])
    (k10 : mem.read 3143 47 = [64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64])
    (k11 : mem.read 3190 20 = [198, 201, 195, 214, 64, 226, 131, 150, 153, 133, 64, 64, 64, 64, 64, 64, 64, 64, 64, 122])
    (k12 : mem.read 3230 40 = [64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64])
    (k13 : mem.read 3270 80 = [96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96])
    (k14 : mem.read 3350 80 = [64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 227, 217, 193, 213, 226, 193, 195, 227, 201, 214, 213, 64, 226, 228, 212, 212, 193, 217, 232, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64])
    (k15 : mem.read 3430 80 = [96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96])
    (k16 : mem.read 3510 80 = [227, 153, 129, 149, 64, 201, 196, 64, 64, 64, 64, 64, 64, 64, 64, 64, 227, 153, 129, 149, 64, 196, 133, 163, 129, 137, 147, 162, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 227, 153, 129, 149, 64, 193, 148, 150, 164, 149, 163])
    (k17 : mem.read 3606 1 = [64])
    (k18 : mem.read 3656 1 = [91])
    (k19 : mem.read 3670 67 = [227, 150, 163, 129, 147, 64, 197, 231, 215, 122, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 91])
    (k20 : mem.read 3750 80 = [92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 197, 213, 196, 64, 214, 198, 64, 226, 227, 193, 227, 197, 212, 197, 213, 227, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92])
    (k21 : mem.read 3930 34 = [76, 136, 243, 110, 226, 163, 129, 163, 133, 148, 133, 149, 163, 64, 134, 150, 153, 64, 193, 131, 131, 150, 164, 149, 163, 64, 213, 164, 148, 130, 133, 153, 122, 64])
    (k22 : mem.read 3984 5 = [76, 97, 136, 243, 110])
    (k23 : mem.read 3989 26 = [76, 151, 64, 162, 163, 168, 147, 133, 126, 127, 134, 150, 149, 163, 96, 162, 137, 169, 133, 122, 241, 246, 151, 167, 127, 110])
    (hacc : mem.read 1388 6 =
      encodeNum {} { digits := 11, scale := 2, signed := true, usage := .packed } 0) (fuel : Nat) :
    (p4st env m fuel ⟨mem, idx, [], [], [], out, inp,
          [(1, { mode := some .output, recs := r1 }), (2, { mode := some .output, recs := r2 }),
           (3, f3), (4, f4), (5, f5), (6, f6)], clockN⟩).mem.size = 178495 := by
  obtain ⟨hm50, hG, hT, hrecs, hT0, hR0⟩ := hS
  have hc : ConstsOk mem := ⟨k01, k02, k03, k04, k05, k06, k07, k08, k09, k10, k11, k12, k13, k14, k15, k16, k17, k18, k19, k20, k21, k22, k23⟩
  obtain ⟨R, hE, hp⟩ := exists_of_normalAnd (perform4_ok env m hm50 mem hm idx out inp
    clockN r1 r2 f3 f4 f5 f6 gs hG hT hrecs (TableOk_of_region hT0 hG hT htbl)
    (TrctOk_of_region hR0 (by omega) htbl) hcr X hXl hX hc hacc fuel)
  simp only [p4st, hE]
  exact hp.2.2.2.2.2.2.2.2.1

theorem p4_read1 (env : Env) (m : Nat) (mem : Mem) (hm : mem.size = 178495)
    (idx : List (Nat × Int)) (out : List Event) (inp : List (Nat × List (List UInt8))) (clockN : Nat)
    (r1 r2 : List (List UInt8)) (f3 f4 f5 f6 : FileSt)
    (gs : List (List (List UInt8)))
    (hcr : mem.read 1380 2 = encodeNum {} { digits := 4, signed := true, usage := .binary }
      (gs.length : Int))
    (m0 : Mem) (htbl : mem.read 4365 171258 = m0.read 4365 171258) (hS : P4Static m gs m0)
    (X : List UInt8) (hX : mem.read 530 16 = X) (hXl : X.length = 16)
    (k01 : mem.read 2470 80 = [92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 226, 227, 193, 217, 227, 64, 214, 198, 64, 226, 227, 193, 227, 197, 212, 197, 213, 227, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92])
    (k02 : mem.read 2625 5 = [64, 64, 64, 64, 64])
    (k03 : mem.read 2680 30 = [64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64])
    (k04 : mem.read 2760 30 = [64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64])
    (k05 : mem.read 2870 80 = [96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96])
    (k06 : mem.read 2950 80 = [64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 194, 129, 162, 137, 131, 64, 196, 133, 163, 129, 137, 147, 162, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64])
    (k07 : mem.read 3030 20 = [193, 131, 131, 150, 164, 149, 163, 64, 201, 196, 64, 64, 64, 64, 64, 64, 64, 64, 64, 122])
    (k08 : mem.read 3070 40 = [64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64])
    (k09 : mem.read 3110 20 = [195, 164, 153, 153, 133, 149, 163, 64, 194, 129, 147, 129, 149, 131, 133, 64, 64, 64, 64, 122])
    (k10 : mem.read 3143 47 = [64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64])
    (k11 : mem.read 3190 20 = [198, 201, 195, 214, 64, 226, 131, 150, 153, 133, 64, 64, 64, 64, 64, 64, 64, 64, 64, 122])
    (k12 : mem.read 3230 40 = [64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64])
    (k13 : mem.read 3270 80 = [96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96])
    (k14 : mem.read 3350 80 = [64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 227, 217, 193, 213, 226, 193, 195, 227, 201, 214, 213, 64, 226, 228, 212, 212, 193, 217, 232, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64])
    (k15 : mem.read 3430 80 = [96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96])
    (k16 : mem.read 3510 80 = [227, 153, 129, 149, 64, 201, 196, 64, 64, 64, 64, 64, 64, 64, 64, 64, 227, 153, 129, 149, 64, 196, 133, 163, 129, 137, 147, 162, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 227, 153, 129, 149, 64, 193, 148, 150, 164, 149, 163])
    (k17 : mem.read 3606 1 = [64])
    (k18 : mem.read 3656 1 = [91])
    (k19 : mem.read 3670 67 = [227, 150, 163, 129, 147, 64, 197, 231, 215, 122, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 91])
    (k20 : mem.read 3750 80 = [92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 197, 213, 196, 64, 214, 198, 64, 226, 227, 193, 227, 197, 212, 197, 213, 227, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92])
    (k21 : mem.read 3930 34 = [76, 136, 243, 110, 226, 163, 129, 163, 133, 148, 133, 149, 163, 64, 134, 150, 153, 64, 193, 131, 131, 150, 164, 149, 163, 64, 213, 164, 148, 130, 133, 153, 122, 64])
    (k22 : mem.read 3984 5 = [76, 97, 136, 243, 110])
    (k23 : mem.read 3989 26 = [76, 151, 64, 162, 163, 168, 147, 133, 126, 127, 134, 150, 149, 163, 96, 162, 137, 169, 133, 122, 241, 246, 151, 167, 127, 110])
    (hacc : mem.read 1388 6 =
      encodeNum {} { digits := 11, scale := 2, signed := true, usage := .packed } 0) (fuel : Nat)
    (o l : Nat) (ho : 530 ≤ o) (hl : o + l ≤ 1384) :
    (p4st env m fuel ⟨mem, idx, [], [], [], out, inp,
          [(1, { mode := some .output, recs := r1 }), (2, { mode := some .output, recs := r2 }),
           (3, f3), (4, f4), (5, f5), (6, f6)], clockN⟩).mem.read o l = mem.read o l :=
  (p4_frame env m mem hm idx out inp clockN r1 r2 f3 f4 f5 f6 gs hcr m0 htbl hS X hX hXl k01 k02 k03 k04 k05 k06 k07 k08 k09 k10 k11 k12 k13 k14 k15 k16 k17 k18 k19 k20 k21 k22 k23 hacc fuel).1 o l ho hl

theorem p4_read2 (env : Env) (m : Nat) (mem : Mem) (hm : mem.size = 178495)
    (idx : List (Nat × Int)) (out : List Event) (inp : List (Nat × List (List UInt8))) (clockN : Nat)
    (r1 r2 : List (List UInt8)) (f3 f4 f5 f6 : FileSt)
    (gs : List (List (List UInt8)))
    (hcr : mem.read 1380 2 = encodeNum {} { digits := 4, signed := true, usage := .binary }
      (gs.length : Int))
    (m0 : Mem) (htbl : mem.read 4365 171258 = m0.read 4365 171258) (hS : P4Static m gs m0)
    (X : List UInt8) (hX : mem.read 530 16 = X) (hXl : X.length = 16)
    (k01 : mem.read 2470 80 = [92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 226, 227, 193, 217, 227, 64, 214, 198, 64, 226, 227, 193, 227, 197, 212, 197, 213, 227, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92])
    (k02 : mem.read 2625 5 = [64, 64, 64, 64, 64])
    (k03 : mem.read 2680 30 = [64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64])
    (k04 : mem.read 2760 30 = [64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64])
    (k05 : mem.read 2870 80 = [96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96])
    (k06 : mem.read 2950 80 = [64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 194, 129, 162, 137, 131, 64, 196, 133, 163, 129, 137, 147, 162, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64])
    (k07 : mem.read 3030 20 = [193, 131, 131, 150, 164, 149, 163, 64, 201, 196, 64, 64, 64, 64, 64, 64, 64, 64, 64, 122])
    (k08 : mem.read 3070 40 = [64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64])
    (k09 : mem.read 3110 20 = [195, 164, 153, 153, 133, 149, 163, 64, 194, 129, 147, 129, 149, 131, 133, 64, 64, 64, 64, 122])
    (k10 : mem.read 3143 47 = [64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64])
    (k11 : mem.read 3190 20 = [198, 201, 195, 214, 64, 226, 131, 150, 153, 133, 64, 64, 64, 64, 64, 64, 64, 64, 64, 122])
    (k12 : mem.read 3230 40 = [64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64])
    (k13 : mem.read 3270 80 = [96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96])
    (k14 : mem.read 3350 80 = [64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 227, 217, 193, 213, 226, 193, 195, 227, 201, 214, 213, 64, 226, 228, 212, 212, 193, 217, 232, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64])
    (k15 : mem.read 3430 80 = [96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96])
    (k16 : mem.read 3510 80 = [227, 153, 129, 149, 64, 201, 196, 64, 64, 64, 64, 64, 64, 64, 64, 64, 227, 153, 129, 149, 64, 196, 133, 163, 129, 137, 147, 162, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 227, 153, 129, 149, 64, 193, 148, 150, 164, 149, 163])
    (k17 : mem.read 3606 1 = [64])
    (k18 : mem.read 3656 1 = [91])
    (k19 : mem.read 3670 67 = [227, 150, 163, 129, 147, 64, 197, 231, 215, 122, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 91])
    (k20 : mem.read 3750 80 = [92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 197, 213, 196, 64, 214, 198, 64, 226, 227, 193, 227, 197, 212, 197, 213, 227, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92])
    (k21 : mem.read 3930 34 = [76, 136, 243, 110, 226, 163, 129, 163, 133, 148, 133, 149, 163, 64, 134, 150, 153, 64, 193, 131, 131, 150, 164, 149, 163, 64, 213, 164, 148, 130, 133, 153, 122, 64])
    (k22 : mem.read 3984 5 = [76, 97, 136, 243, 110])
    (k23 : mem.read 3989 26 = [76, 151, 64, 162, 163, 168, 147, 133, 126, 127, 134, 150, 149, 163, 96, 162, 137, 169, 133, 122, 241, 246, 151, 167, 127, 110])
    (hacc : mem.read 1388 6 =
      encodeNum {} { digits := 11, scale := 2, signed := true, usage := .packed } 0) (fuel : Nat)
    (o l : Nat) (ho : 1394 ≤ o) (hl : o + l ≤ 1402) :
    (p4st env m fuel ⟨mem, idx, [], [], [], out, inp,
          [(1, { mode := some .output, recs := r1 }), (2, { mode := some .output, recs := r2 }),
           (3, f3), (4, f4), (5, f5), (6, f6)], clockN⟩).mem.read o l = mem.read o l :=
  (p4_frame env m mem hm idx out inp clockN r1 r2 f3 f4 f5 f6 gs hcr m0 htbl hS X hX hXl k01 k02 k03 k04 k05 k06 k07 k08 k09 k10 k11 k12 k13 k14 k15 k16 k17 k18 k19 k20 k21 k22 k23 hacc fuel).2.1 o l ho hl

theorem p4_read3 (env : Env) (m : Nat) (mem : Mem) (hm : mem.size = 178495)
    (idx : List (Nat × Int)) (out : List Event) (inp : List (Nat × List (List UInt8))) (clockN : Nat)
    (r1 r2 : List (List UInt8)) (f3 f4 f5 f6 : FileSt)
    (gs : List (List (List UInt8)))
    (hcr : mem.read 1380 2 = encodeNum {} { digits := 4, signed := true, usage := .binary }
      (gs.length : Int))
    (m0 : Mem) (htbl : mem.read 4365 171258 = m0.read 4365 171258) (hS : P4Static m gs m0)
    (X : List UInt8) (hX : mem.read 530 16 = X) (hXl : X.length = 16)
    (k01 : mem.read 2470 80 = [92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 226, 227, 193, 217, 227, 64, 214, 198, 64, 226, 227, 193, 227, 197, 212, 197, 213, 227, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92])
    (k02 : mem.read 2625 5 = [64, 64, 64, 64, 64])
    (k03 : mem.read 2680 30 = [64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64])
    (k04 : mem.read 2760 30 = [64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64])
    (k05 : mem.read 2870 80 = [96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96])
    (k06 : mem.read 2950 80 = [64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 194, 129, 162, 137, 131, 64, 196, 133, 163, 129, 137, 147, 162, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64])
    (k07 : mem.read 3030 20 = [193, 131, 131, 150, 164, 149, 163, 64, 201, 196, 64, 64, 64, 64, 64, 64, 64, 64, 64, 122])
    (k08 : mem.read 3070 40 = [64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64])
    (k09 : mem.read 3110 20 = [195, 164, 153, 153, 133, 149, 163, 64, 194, 129, 147, 129, 149, 131, 133, 64, 64, 64, 64, 122])
    (k10 : mem.read 3143 47 = [64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64])
    (k11 : mem.read 3190 20 = [198, 201, 195, 214, 64, 226, 131, 150, 153, 133, 64, 64, 64, 64, 64, 64, 64, 64, 64, 122])
    (k12 : mem.read 3230 40 = [64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64])
    (k13 : mem.read 3270 80 = [96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96])
    (k14 : mem.read 3350 80 = [64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 227, 217, 193, 213, 226, 193, 195, 227, 201, 214, 213, 64, 226, 228, 212, 212, 193, 217, 232, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64])
    (k15 : mem.read 3430 80 = [96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96])
    (k16 : mem.read 3510 80 = [227, 153, 129, 149, 64, 201, 196, 64, 64, 64, 64, 64, 64, 64, 64, 64, 227, 153, 129, 149, 64, 196, 133, 163, 129, 137, 147, 162, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 227, 153, 129, 149, 64, 193, 148, 150, 164, 149, 163])
    (k17 : mem.read 3606 1 = [64])
    (k18 : mem.read 3656 1 = [91])
    (k19 : mem.read 3670 67 = [227, 150, 163, 129, 147, 64, 197, 231, 215, 122, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 91])
    (k20 : mem.read 3750 80 = [92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 197, 213, 196, 64, 214, 198, 64, 226, 227, 193, 227, 197, 212, 197, 213, 227, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92])
    (k21 : mem.read 3930 34 = [76, 136, 243, 110, 226, 163, 129, 163, 133, 148, 133, 149, 163, 64, 134, 150, 153, 64, 193, 131, 131, 150, 164, 149, 163, 64, 213, 164, 148, 130, 133, 153, 122, 64])
    (k22 : mem.read 3984 5 = [76, 97, 136, 243, 110])
    (k23 : mem.read 3989 26 = [76, 151, 64, 162, 163, 168, 147, 133, 126, 127, 134, 150, 149, 163, 96, 162, 137, 169, 133, 122, 241, 246, 151, 167, 127, 110])
    (hacc : mem.read 1388 6 =
      encodeNum {} { digits := 11, scale := 2, signed := true, usage := .packed } 0) (fuel : Nat)
    (o l : Nat) (ho : 1413 ≤ o) (hl : o + l ≤ 3590) :
    (p4st env m fuel ⟨mem, idx, [], [], [], out, inp,
          [(1, { mode := some .output, recs := r1 }), (2, { mode := some .output, recs := r2 }),
           (3, f3), (4, f4), (5, f5), (6, f6)], clockN⟩).mem.read o l = mem.read o l :=
  (p4_frame env m mem hm idx out inp clockN r1 r2 f3 f4 f5 f6 gs hcr m0 htbl hS X hX hXl k01 k02 k03 k04 k05 k06 k07 k08 k09 k10 k11 k12 k13 k14 k15 k16 k17 k18 k19 k20 k21 k22 k23 hacc fuel).2.2.1 o l ho hl

theorem p4_read4 (env : Env) (m : Nat) (mem : Mem) (hm : mem.size = 178495)
    (idx : List (Nat × Int)) (out : List Event) (inp : List (Nat × List (List UInt8))) (clockN : Nat)
    (r1 r2 : List (List UInt8)) (f3 f4 f5 f6 : FileSt)
    (gs : List (List (List UInt8)))
    (hcr : mem.read 1380 2 = encodeNum {} { digits := 4, signed := true, usage := .binary }
      (gs.length : Int))
    (m0 : Mem) (htbl : mem.read 4365 171258 = m0.read 4365 171258) (hS : P4Static m gs m0)
    (X : List UInt8) (hX : mem.read 530 16 = X) (hXl : X.length = 16)
    (k01 : mem.read 2470 80 = [92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 226, 227, 193, 217, 227, 64, 214, 198, 64, 226, 227, 193, 227, 197, 212, 197, 213, 227, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92])
    (k02 : mem.read 2625 5 = [64, 64, 64, 64, 64])
    (k03 : mem.read 2680 30 = [64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64])
    (k04 : mem.read 2760 30 = [64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64])
    (k05 : mem.read 2870 80 = [96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96])
    (k06 : mem.read 2950 80 = [64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 194, 129, 162, 137, 131, 64, 196, 133, 163, 129, 137, 147, 162, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64])
    (k07 : mem.read 3030 20 = [193, 131, 131, 150, 164, 149, 163, 64, 201, 196, 64, 64, 64, 64, 64, 64, 64, 64, 64, 122])
    (k08 : mem.read 3070 40 = [64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64])
    (k09 : mem.read 3110 20 = [195, 164, 153, 153, 133, 149, 163, 64, 194, 129, 147, 129, 149, 131, 133, 64, 64, 64, 64, 122])
    (k10 : mem.read 3143 47 = [64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64])
    (k11 : mem.read 3190 20 = [198, 201, 195, 214, 64, 226, 131, 150, 153, 133, 64, 64, 64, 64, 64, 64, 64, 64, 64, 122])
    (k12 : mem.read 3230 40 = [64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64])
    (k13 : mem.read 3270 80 = [96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96])
    (k14 : mem.read 3350 80 = [64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 227, 217, 193, 213, 226, 193, 195, 227, 201, 214, 213, 64, 226, 228, 212, 212, 193, 217, 232, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64])
    (k15 : mem.read 3430 80 = [96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96])
    (k16 : mem.read 3510 80 = [227, 153, 129, 149, 64, 201, 196, 64, 64, 64, 64, 64, 64, 64, 64, 64, 227, 153, 129, 149, 64, 196, 133, 163, 129, 137, 147, 162, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 227, 153, 129, 149, 64, 193, 148, 150, 164, 149, 163])
    (k17 : mem.read 3606 1 = [64])
    (k18 : mem.read 3656 1 = [91])
    (k19 : mem.read 3670 67 = [227, 150, 163, 129, 147, 64, 197, 231, 215, 122, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 91])
    (k20 : mem.read 3750 80 = [92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 197, 213, 196, 64, 214, 198, 64, 226, 227, 193, 227, 197, 212, 197, 213, 227, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92])
    (k21 : mem.read 3930 34 = [76, 136, 243, 110, 226, 163, 129, 163, 133, 148, 133, 149, 163, 64, 134, 150, 153, 64, 193, 131, 131, 150, 164, 149, 163, 64, 213, 164, 148, 130, 133, 153, 122, 64])
    (k22 : mem.read 3984 5 = [76, 97, 136, 243, 110])
    (k23 : mem.read 3989 26 = [76, 151, 64, 162, 163, 168, 147, 133, 126, 127, 134, 150, 149, 163, 96, 162, 137, 169, 133, 122, 241, 246, 151, 167, 127, 110])
    (hacc : mem.read 1388 6 =
      encodeNum {} { digits := 11, scale := 2, signed := true, usage := .packed } 0) (fuel : Nat)
    (o l : Nat) (ho : 3606 ≤ o) (hl : o + l ≤ 3607) :
    (p4st env m fuel ⟨mem, idx, [], [], [], out, inp,
          [(1, { mode := some .output, recs := r1 }), (2, { mode := some .output, recs := r2 }),
           (3, f3), (4, f4), (5, f5), (6, f6)], clockN⟩).mem.read o l = mem.read o l :=
  (p4_frame env m mem hm idx out inp clockN r1 r2 f3 f4 f5 f6 gs hcr m0 htbl hS X hX hXl k01 k02 k03 k04 k05 k06 k07 k08 k09 k10 k11 k12 k13 k14 k15 k16 k17 k18 k19 k20 k21 k22 k23 hacc fuel).2.2.2.1 o l ho hl

theorem p4_read5 (env : Env) (m : Nat) (mem : Mem) (hm : mem.size = 178495)
    (idx : List (Nat × Int)) (out : List Event) (inp : List (Nat × List (List UInt8))) (clockN : Nat)
    (r1 r2 : List (List UInt8)) (f3 f4 f5 f6 : FileSt)
    (gs : List (List (List UInt8)))
    (hcr : mem.read 1380 2 = encodeNum {} { digits := 4, signed := true, usage := .binary }
      (gs.length : Int))
    (m0 : Mem) (htbl : mem.read 4365 171258 = m0.read 4365 171258) (hS : P4Static m gs m0)
    (X : List UInt8) (hX : mem.read 530 16 = X) (hXl : X.length = 16)
    (k01 : mem.read 2470 80 = [92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 226, 227, 193, 217, 227, 64, 214, 198, 64, 226, 227, 193, 227, 197, 212, 197, 213, 227, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92])
    (k02 : mem.read 2625 5 = [64, 64, 64, 64, 64])
    (k03 : mem.read 2680 30 = [64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64])
    (k04 : mem.read 2760 30 = [64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64])
    (k05 : mem.read 2870 80 = [96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96])
    (k06 : mem.read 2950 80 = [64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 194, 129, 162, 137, 131, 64, 196, 133, 163, 129, 137, 147, 162, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64])
    (k07 : mem.read 3030 20 = [193, 131, 131, 150, 164, 149, 163, 64, 201, 196, 64, 64, 64, 64, 64, 64, 64, 64, 64, 122])
    (k08 : mem.read 3070 40 = [64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64])
    (k09 : mem.read 3110 20 = [195, 164, 153, 153, 133, 149, 163, 64, 194, 129, 147, 129, 149, 131, 133, 64, 64, 64, 64, 122])
    (k10 : mem.read 3143 47 = [64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64])
    (k11 : mem.read 3190 20 = [198, 201, 195, 214, 64, 226, 131, 150, 153, 133, 64, 64, 64, 64, 64, 64, 64, 64, 64, 122])
    (k12 : mem.read 3230 40 = [64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64])
    (k13 : mem.read 3270 80 = [96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96])
    (k14 : mem.read 3350 80 = [64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 227, 217, 193, 213, 226, 193, 195, 227, 201, 214, 213, 64, 226, 228, 212, 212, 193, 217, 232, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64])
    (k15 : mem.read 3430 80 = [96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96])
    (k16 : mem.read 3510 80 = [227, 153, 129, 149, 64, 201, 196, 64, 64, 64, 64, 64, 64, 64, 64, 64, 227, 153, 129, 149, 64, 196, 133, 163, 129, 137, 147, 162, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 227, 153, 129, 149, 64, 193, 148, 150, 164, 149, 163])
    (k17 : mem.read 3606 1 = [64])
    (k18 : mem.read 3656 1 = [91])
    (k19 : mem.read 3670 67 = [227, 150, 163, 129, 147, 64, 197, 231, 215, 122, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 91])
    (k20 : mem.read 3750 80 = [92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 197, 213, 196, 64, 214, 198, 64, 226, 227, 193, 227, 197, 212, 197, 213, 227, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92])
    (k21 : mem.read 3930 34 = [76, 136, 243, 110, 226, 163, 129, 163, 133, 148, 133, 149, 163, 64, 134, 150, 153, 64, 193, 131, 131, 150, 164, 149, 163, 64, 213, 164, 148, 130, 133, 153, 122, 64])
    (k22 : mem.read 3984 5 = [76, 97, 136, 243, 110])
    (k23 : mem.read 3989 26 = [76, 151, 64, 162, 163, 168, 147, 133, 126, 127, 134, 150, 149, 163, 96, 162, 137, 169, 133, 122, 241, 246, 151, 167, 127, 110])
    (hacc : mem.read 1388 6 =
      encodeNum {} { digits := 11, scale := 2, signed := true, usage := .packed } 0) (fuel : Nat)
    (o l : Nat) (ho : 3656 ≤ o) (hl : o + l ≤ 3657) :
    (p4st env m fuel ⟨mem, idx, [], [], [], out, inp,
          [(1, { mode := some .output, recs := r1 }), (2, { mode := some .output, recs := r2 }),
           (3, f3), (4, f4), (5, f5), (6, f6)], clockN⟩).mem.read o l = mem.read o l :=
  (p4_frame env m mem hm idx out inp clockN r1 r2 f3 f4 f5 f6 gs hcr m0 htbl hS X hX hXl k01 k02 k03 k04 k05 k06 k07 k08 k09 k10 k11 k12 k13 k14 k15 k16 k17 k18 k19 k20 k21 k22 k23 hacc fuel).2.2.2.2.1 o l ho hl

theorem p4_read6 (env : Env) (m : Nat) (mem : Mem) (hm : mem.size = 178495)
    (idx : List (Nat × Int)) (out : List Event) (inp : List (Nat × List (List UInt8))) (clockN : Nat)
    (r1 r2 : List (List UInt8)) (f3 f4 f5 f6 : FileSt)
    (gs : List (List (List UInt8)))
    (hcr : mem.read 1380 2 = encodeNum {} { digits := 4, signed := true, usage := .binary }
      (gs.length : Int))
    (m0 : Mem) (htbl : mem.read 4365 171258 = m0.read 4365 171258) (hS : P4Static m gs m0)
    (X : List UInt8) (hX : mem.read 530 16 = X) (hXl : X.length = 16)
    (k01 : mem.read 2470 80 = [92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 226, 227, 193, 217, 227, 64, 214, 198, 64, 226, 227, 193, 227, 197, 212, 197, 213, 227, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92])
    (k02 : mem.read 2625 5 = [64, 64, 64, 64, 64])
    (k03 : mem.read 2680 30 = [64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64])
    (k04 : mem.read 2760 30 = [64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64])
    (k05 : mem.read 2870 80 = [96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96])
    (k06 : mem.read 2950 80 = [64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 194, 129, 162, 137, 131, 64, 196, 133, 163, 129, 137, 147, 162, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64])
    (k07 : mem.read 3030 20 = [193, 131, 131, 150, 164, 149, 163, 64, 201, 196, 64, 64, 64, 64, 64, 64, 64, 64, 64, 122])
    (k08 : mem.read 3070 40 = [64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64])
    (k09 : mem.read 3110 20 = [195, 164, 153, 153, 133, 149, 163, 64, 194, 129, 147, 129, 149, 131, 133, 64, 64, 64, 64, 122])
    (k10 : mem.read 3143 47 = [64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64])
    (k11 : mem.read 3190 20 = [198, 201, 195, 214, 64, 226, 131, 150, 153, 133, 64, 64, 64, 64, 64, 64, 64, 64, 64, 122])
    (k12 : mem.read 3230 40 = [64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64])
    (k13 : mem.read 3270 80 = [96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96])
    (k14 : mem.read 3350 80 = [64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 227, 217, 193, 213, 226, 193, 195, 227, 201, 214, 213, 64, 226, 228, 212, 212, 193, 217, 232, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64])
    (k15 : mem.read 3430 80 = [96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96])
    (k16 : mem.read 3510 80 = [227, 153, 129, 149, 64, 201, 196, 64, 64, 64, 64, 64, 64, 64, 64, 64, 227, 153, 129, 149, 64, 196, 133, 163, 129, 137, 147, 162, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 227, 153, 129, 149, 64, 193, 148, 150, 164, 149, 163])
    (k17 : mem.read 3606 1 = [64])
    (k18 : mem.read 3656 1 = [91])
    (k19 : mem.read 3670 67 = [227, 150, 163, 129, 147, 64, 197, 231, 215, 122, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 91])
    (k20 : mem.read 3750 80 = [92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 197, 213, 196, 64, 214, 198, 64, 226, 227, 193, 227, 197, 212, 197, 213, 227, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92])
    (k21 : mem.read 3930 34 = [76, 136, 243, 110, 226, 163, 129, 163, 133, 148, 133, 149, 163, 64, 134, 150, 153, 64, 193, 131, 131, 150, 164, 149, 163, 64, 213, 164, 148, 130, 133, 153, 122, 64])
    (k22 : mem.read 3984 5 = [76, 97, 136, 243, 110])
    (k23 : mem.read 3989 26 = [76, 151, 64, 162, 163, 168, 147, 133, 126, 127, 134, 150, 149, 163, 96, 162, 137, 169, 133, 122, 241, 246, 151, 167, 127, 110])
    (hacc : mem.read 1388 6 =
      encodeNum {} { digits := 11, scale := 2, signed := true, usage := .packed } 0) (fuel : Nat)
    (o l : Nat) (ho : 3670 ≤ o) (hl : o + l ≤ 3737) :
    (p4st env m fuel ⟨mem, idx, [], [], [], out, inp,
          [(1, { mode := some .output, recs := r1 }), (2, { mode := some .output, recs := r2 }),
           (3, f3), (4, f4), (5, f5), (6, f6)], clockN⟩).mem.read o l = mem.read o l :=
  (p4_frame env m mem hm idx out inp clockN r1 r2 f3 f4 f5 f6 gs hcr m0 htbl hS X hX hXl k01 k02 k03 k04 k05 k06 k07 k08 k09 k10 k11 k12 k13 k14 k15 k16 k17 k18 k19 k20 k21 k22 k23 hacc fuel).2.2.2.2.2.1 o l ho hl

theorem p4_read7 (env : Env) (m : Nat) (mem : Mem) (hm : mem.size = 178495)
    (idx : List (Nat × Int)) (out : List Event) (inp : List (Nat × List (List UInt8))) (clockN : Nat)
    (r1 r2 : List (List UInt8)) (f3 f4 f5 f6 : FileSt)
    (gs : List (List (List UInt8)))
    (hcr : mem.read 1380 2 = encodeNum {} { digits := 4, signed := true, usage := .binary }
      (gs.length : Int))
    (m0 : Mem) (htbl : mem.read 4365 171258 = m0.read 4365 171258) (hS : P4Static m gs m0)
    (X : List UInt8) (hX : mem.read 530 16 = X) (hXl : X.length = 16)
    (k01 : mem.read 2470 80 = [92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 226, 227, 193, 217, 227, 64, 214, 198, 64, 226, 227, 193, 227, 197, 212, 197, 213, 227, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92])
    (k02 : mem.read 2625 5 = [64, 64, 64, 64, 64])
    (k03 : mem.read 2680 30 = [64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64])
    (k04 : mem.read 2760 30 = [64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64])
    (k05 : mem.read 2870 80 = [96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96])
    (k06 : mem.read 2950 80 = [64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 194, 129, 162, 137, 131, 64, 196, 133, 163, 129, 137, 147, 162, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64])
    (k07 : mem.read 3030 20 = [193, 131, 131, 150, 164, 149, 163, 64, 201, 196, 64, 64, 64, 64, 64, 64, 64, 64, 64, 122])
    (k08 : mem.read 3070 40 = [64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64])
    (k09 : mem.read 3110 20 = [195, 164, 153, 153, 133, 149, 163, 64, 194, 129, 147, 129, 149, 131, 133, 64, 64, 64, 64, 122])
    (k10 : mem.read 3143 47 = [64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64])
    (k11 : mem.read 3190 20 = [198, 201, 195, 214, 64, 226, 131, 150, 153, 133, 64, 64, 64, 64, 64, 64, 64, 64, 64, 122])
    (k12 : mem.read 3230 40 = [64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64])
    (k13 : mem.read 3270 80 = [96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96])
    (k14 : mem.read 3350 80 = [64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 227, 217, 193, 213, 226, 193, 195, 227, 201, 214, 213, 64, 226, 228, 212, 212, 193, 217, 232, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64])
    (k15 : mem.read 3430 80 = [96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96])
    (k16 : mem.read 3510 80 = [227, 153, 129, 149, 64, 201, 196, 64, 64, 64, 64, 64, 64, 64, 64, 64, 227, 153, 129, 149, 64, 196, 133, 163, 129, 137, 147, 162, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 227, 153, 129, 149, 64, 193, 148, 150, 164, 149, 163])
    (k17 : mem.read 3606 1 = [64])
    (k18 : mem.read 3656 1 = [91])
    (k19 : mem.read 3670 67 = [227, 150, 163, 129, 147, 64, 197, 231, 215, 122, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 91])
    (k20 : mem.read 3750 80 = [92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 197, 213, 196, 64, 214, 198, 64, 226, 227, 193, 227, 197, 212, 197, 213, 227, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92])
    (k21 : mem.read 3930 34 = [76, 136, 243, 110, 226, 163, 129, 163, 133, 148, 133, 149, 163, 64, 134, 150, 153, 64, 193, 131, 131, 150, 164, 149, 163, 64, 213, 164, 148, 130, 133, 153, 122, 64])
    (k22 : mem.read 3984 5 = [76, 97, 136, 243, 110])
    (k23 : mem.read 3989 26 = [76, 151, 64, 162, 163, 168, 147, 133, 126, 127, 134, 150, 149, 163, 96, 162, 137, 169, 133, 122, 241, 246, 151, 167, 127, 110])
    (hacc : mem.read 1388 6 =
      encodeNum {} { digits := 11, scale := 2, signed := true, usage := .packed } 0) (fuel : Nat)
    (o l : Nat) (ho : 3750 ≤ o) (hl : o + l ≤ 3830) :
    (p4st env m fuel ⟨mem, idx, [], [], [], out, inp,
          [(1, { mode := some .output, recs := r1 }), (2, { mode := some .output, recs := r2 }),
           (3, f3), (4, f4), (5, f5), (6, f6)], clockN⟩).mem.read o l = mem.read o l :=
  (p4_frame env m mem hm idx out inp clockN r1 r2 f3 f4 f5 f6 gs hcr m0 htbl hS X hX hXl k01 k02 k03 k04 k05 k06 k07 k08 k09 k10 k11 k12 k13 k14 k15 k16 k17 k18 k19 k20 k21 k22 k23 hacc fuel).2.2.2.2.2.2.1 o l ho hl

theorem p4_read8 (env : Env) (m : Nat) (mem : Mem) (hm : mem.size = 178495)
    (idx : List (Nat × Int)) (out : List Event) (inp : List (Nat × List (List UInt8))) (clockN : Nat)
    (r1 r2 : List (List UInt8)) (f3 f4 f5 f6 : FileSt)
    (gs : List (List (List UInt8)))
    (hcr : mem.read 1380 2 = encodeNum {} { digits := 4, signed := true, usage := .binary }
      (gs.length : Int))
    (m0 : Mem) (htbl : mem.read 4365 171258 = m0.read 4365 171258) (hS : P4Static m gs m0)
    (X : List UInt8) (hX : mem.read 530 16 = X) (hXl : X.length = 16)
    (k01 : mem.read 2470 80 = [92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 226, 227, 193, 217, 227, 64, 214, 198, 64, 226, 227, 193, 227, 197, 212, 197, 213, 227, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92])
    (k02 : mem.read 2625 5 = [64, 64, 64, 64, 64])
    (k03 : mem.read 2680 30 = [64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64])
    (k04 : mem.read 2760 30 = [64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64])
    (k05 : mem.read 2870 80 = [96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96])
    (k06 : mem.read 2950 80 = [64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 194, 129, 162, 137, 131, 64, 196, 133, 163, 129, 137, 147, 162, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64])
    (k07 : mem.read 3030 20 = [193, 131, 131, 150, 164, 149, 163, 64, 201, 196, 64, 64, 64, 64, 64, 64, 64, 64, 64, 122])
    (k08 : mem.read 3070 40 = [64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64])
    (k09 : mem.read 3110 20 = [195, 164, 153, 153, 133, 149, 163, 64, 194, 129, 147, 129, 149, 131, 133, 64, 64, 64, 64, 122])
    (k10 : mem.read 3143 47 = [64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64])
    (k11 : mem.read 3190 20 = [198, 201, 195, 214, 64, 226, 131, 150, 153, 133, 64, 64, 64, 64, 64, 64, 64, 64, 64, 122])
    (k12 : mem.read 3230 40 = [64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64])
    (k13 : mem.read 3270 80 = [96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96])
    (k14 : mem.read 3350 80 = [64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 227, 217, 193, 213, 226, 193, 195, 227, 201, 214, 213, 64, 226, 228, 212, 212, 193, 217, 232, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64])
    (k15 : mem.read 3430 80 = [96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96])
    (k16 : mem.read 3510 80 = [227, 153, 129, 149, 64, 201, 196, 64, 64, 64, 64, 64, 64, 64, 64, 64, 227, 153, 129, 149, 64, 196, 133, 163, 129, 137, 147, 162, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 227, 153, 129, 149, 64, 193, 148, 150, 164, 149, 163])
    (k17 : mem.read 3606 1 = [64])
    (k18 : mem.read 3656 1 = [91])
    (k19 : mem.read 3670 67 = [227, 150, 163, 129, 147, 64, 197, 231, 215, 122, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 91])
    (k20 : mem.read 3750 80 = [92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 197, 213, 196, 64, 214, 198, 64, 226, 227, 193, 227, 197, 212, 197, 213, 227, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92])
    (k21 : mem.read 3930 34 = [76, 136, 243, 110, 226, 163, 129, 163, 133, 148, 133, 149, 163, 64, 134, 150, 153, 64, 193, 131, 131, 150, 164, 149, 163, 64, 213, 164, 148, 130, 133, 153, 122, 64])
    (k22 : mem.read 3984 5 = [76, 97, 136, 243, 110])
    (k23 : mem.read 3989 26 = [76, 151, 64, 162, 163, 168, 147, 133, 126, 127, 134, 150, 149, 163, 96, 162, 137, 169, 133, 122, 241, 246, 151, 167, 127, 110])
    (hacc : mem.read 1388 6 =
      encodeNum {} { digits := 11, scale := 2, signed := true, usage := .packed } 0) (fuel : Nat)
    (o l : Nat) (ho : 3930 ≤ o) (hl : o + l ≤ 4265) :
    (p4st env m fuel ⟨mem, idx, [], [], [], out, inp,
          [(1, { mode := some .output, recs := r1 }), (2, { mode := some .output, recs := r2 }),
           (3, f3), (4, f4), (5, f5), (6, f6)], clockN⟩).mem.read o l = mem.read o l :=
  (p4_frame env m mem hm idx out inp clockN r1 r2 f3 f4 f5 f6 gs hcr m0 htbl hS X hX hXl k01 k02 k03 k04 k05 k06 k07 k08 k09 k10 k11 k12 k13 k14 k15 k16 k17 k18 k19 k20 k21 k22 k23 hacc fuel).2.2.2.2.2.2.2.1 o l ho hl

theorem p4_read9 (env : Env) (m : Nat) (mem : Mem) (hm : mem.size = 178495)
    (idx : List (Nat × Int)) (out : List Event) (inp : List (Nat × List (List UInt8))) (clockN : Nat)
    (r1 r2 : List (List UInt8)) (f3 f4 f5 f6 : FileSt)
    (gs : List (List (List UInt8)))
    (hcr : mem.read 1380 2 = encodeNum {} { digits := 4, signed := true, usage := .binary }
      (gs.length : Int))
    (m0 : Mem) (htbl : mem.read 4365 171258 = m0.read 4365 171258) (hS : P4Static m gs m0)
    (X : List UInt8) (hX : mem.read 530 16 = X) (hXl : X.length = 16)
    (k01 : mem.read 2470 80 = [92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 226, 227, 193, 217, 227, 64, 214, 198, 64, 226, 227, 193, 227, 197, 212, 197, 213, 227, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92])
    (k02 : mem.read 2625 5 = [64, 64, 64, 64, 64])
    (k03 : mem.read 2680 30 = [64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64])
    (k04 : mem.read 2760 30 = [64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64])
    (k05 : mem.read 2870 80 = [96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96])
    (k06 : mem.read 2950 80 = [64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 194, 129, 162, 137, 131, 64, 196, 133, 163, 129, 137, 147, 162, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64])
    (k07 : mem.read 3030 20 = [193, 131, 131, 150, 164, 149, 163, 64, 201, 196, 64, 64, 64, 64, 64, 64, 64, 64, 64, 122])
    (k08 : mem.read 3070 40 = [64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64])
    (k09 : mem.read 3110 20 = [195, 164, 153, 153, 133, 149, 163, 64, 194, 129, 147, 129, 149, 131, 133, 64, 64, 64, 64, 122])
    (k10 : mem.read 3143 47 = [64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64])
    (k11 : mem.read 3190 20 = [198, 201, 195, 214, 64, 226, 131, 150, 153, 133, 64, 64, 64, 64, 64, 64, 64, 64, 64, 122])
    (k12 : mem.read 3230 40 = [64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64])
    (k13 : mem.read 3270 80 = [96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96])
    (k14 : mem.read 3350 80 = [64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 227, 217, 193, 213, 226, 193, 195, 227, 201, 214, 213, 64, 226, 228, 212, 212, 193, 217, 232, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64])
    (k15 : mem.read 3430 80 = [96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96])
    (k16 : mem.read 3510 80 = [227, 153, 129, 149, 64, 201, 196, 64, 64, 64, 64, 64, 64, 64, 64, 64, 227, 153, 129, 149, 64, 196, 133, 163, 129, 137, 147, 162, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 227, 153, 129, 149, 64, 193, 148, 150, 164, 149, 163])
    (k17 : mem.read 3606 1 = [64])
    (k18 : mem.read 3656 1 = [91])
    (k19 : mem.read 3670 67 = [227, 150, 163, 129, 147, 64, 197, 231, 215, 122, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 91])
    (k20 : mem.read 3750 80 = [92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 197, 213, 196, 64, 214, 198, 64, 226, 227, 193, 227, 197, 212, 197, 213, 227, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92, 92])
    (k21 : mem.read 3930 34 = [76, 136, 243, 110, 226, 163, 129, 163, 133, 148, 133, 149, 163, 64, 134, 150, 153, 64, 193, 131, 131, 150, 164, 149, 163, 64, 213, 164, 148, 130, 133, 153, 122, 64])
    (k22 : mem.read 3984 5 = [76, 97, 136, 243, 110])
    (k23 : mem.read 3989 26 = [76, 151, 64, 162, 163, 168, 147, 133, 126, 127, 134, 150, 149, 163, 96, 162, 137, 169, 133, 122, 241, 246, 151, 167, 127, 110])
    (hacc : mem.read 1388 6 =
      encodeNum {} { digits := 11, scale := 2, signed := true, usage := .packed } 0) (fuel : Nat)
    (o l : Nat) (ho : 4365 ≤ o) :
    (p4st env m fuel ⟨mem, idx, [], [], [], out, inp,
          [(1, { mode := some .output, recs := r1 }), (2, { mode := some .output, recs := r2 }),
           (3, f3), (4, f4), (5, f5), (6, f6)], clockN⟩).mem.read o l = mem.read o l :=
  (p4_frame env m mem hm idx out inp clockN r1 r2 f3 f4 f5 f6 gs hcr m0 htbl hS X hX hXl k01 k02 k03 k04 k05 k06 k07 k08 k09 k10 k11 k12 k13 k14 k15 k16 k17 k18 k19 k20 k21 k22 k23 hacc fuel).2.2.2.2.2.2.2.2 o l ho

end Cobol.StmCore
