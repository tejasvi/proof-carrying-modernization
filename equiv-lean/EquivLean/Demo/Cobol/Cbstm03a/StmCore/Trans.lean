/-
# Phase 6 of `CBSTM03AB`: `6000-WRITE-TRANS` and `4000-TRNXFILE-GET`

`4000-TRNXFILE-GET` (paragraph 7) scans the table entries in order (`PERFORM VARYING CR-JMP`)
until the last entry or the first card above the cross-reference's card; the entry with that
card has its transactions written (`PERFORM VARYING TR-JMP`, `6000-WRITE-TRANS`: one
`STMT-FILE` record `tranStmt`, eleven `HTML-FILE` records `tranHtml`) and their amounts added to
`WS-TOTAL-AMT`; then the total and the statement's closing records are written.
-/
import EquivLean.Demo.Cobol.Cbstm03a.StmCore.Create
import EquivLean.Demo.Cobol.Cbstm03a.StmCore.Load
import EquivLean.Demo.Cobol.Cbstm03a.StmCore.Loop2
import EquivLean.Demo.Cobol.Cbstm03a.StmCore.EditLen

open Cobol Cobol.Stm

namespace Cobol.StmCore

/-- The `STMT-FILE` record of a transaction (`ST-LINE14`): id, details (the first 49 bytes of
`TRNX-DESC`), edited amount. -/
def tranStmt (tid desc amtT : List UInt8) : List UInt8 := tid ++ c3606 ++ desc.take 49 ++ c3656 ++ amtT

/-- The eleven `HTML-FILE` records of a transaction. -/
def tranHtml (tid desc amtT : List UInt8) : List (List UInt8) :=
  [hLTRS, hL58, hfield tP (tokB 92 tid) tEndP, hLTDE, hL61, hfield tP (tokB 92 (desc.take 49)) tEndP,
   hLTDE, hL64, hfield tP (tokB 92 amtT) tEndP, hLTDE, hLTRE]

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 50000 in
/-- `6000-WRITE-TRANS`. -/
stm_summary html6000 (env : Env) (rec : Nat → State → Sem.Res) (fuel : Nat) (mem : Mem)
    (hm : mem.size = 178495)
    (idx : List (Nat × Int)) (slots : List (ExitPt × Nat)) (saves : List (Nat × Nat))
    (active : List Nat) (out : List Event) (inp : List (Nat × List (List UInt8))) (clockN : Nat)
    (r1 r2 : List (List UInt8)) (f3 f4 f5 f6 : FileSt)
    (hf1 : mem.read 3606 1 = [64]) (hf2 : mem.read 3656 1 = [91])
    (tid desc : List UInt8) (htid : mem.read 196 16 = tid) (htidl : tid.length = 16)
    (hdesc : mem.read 228 100 = desc) (hdescl : desc.length = 100)
    (amt : Int) (hamt : decodeNum {} { digits := 11, scale := 2, signed := true } (mem.read 328 11) = some amt)
    (amtT : List UInt8)
    (hed : Edit.edit {} [.z, .z, .z, .z, .z, .z, .z, .z, .z, .dot, .nine, .nine, .minus] false amt 2 =
      some amtT) (hamtl : amtT.length = 13) :
    Sem.execSentences Stm env rec fuel Stm.«6000-WRITE-TRANS».body
      ⟨mem, idx, slots, saves, active, out, inp,
        [(1, { mode := some .output, recs := r1 }), (2, { mode := some .output, recs := r2 }),
         (3, f3), (4, f4), (5, f5), (6, f6)], clockN⟩
  using [strPiece_match_single, strPiece_match_double, tokB_cons, tokB_nil, length_ovw, strRun_one,
    List.mapM_cons, List.mapM_nil, Option.mapM_some, Option.mapM_none]

/-- `TRNX-DESC` of a transaction record (through `TRNX-REST`). -/
def tDesc (r : List UInt8) : List UInt8 := ((tRest r).drop 16).take 100

/-- `TRNX-AMT` of a transaction record (`PIC S9(9)V99`, through `TRNX-REST`); 0 if invalid. -/
def tAmt (r : List UInt8) : Int :=
  (decodeNum {} { digits := 11, scale := 2, signed := true } (((tRest r).drop 116).take 11)).getD 0

/-- The amount of the record is a valid number. -/
def AmtOk (r : List UInt8) : Prop :=
  decodeNum {} { digits := 11, scale := 2, signed := true } (((tRest r).drop 116).take 11) = some (tAmt r)

def tranStmtR (r : List UInt8) : List UInt8 := tranStmt (tId r) (tDesc r) (editZ (tAmt r))
def tranHtmlR (r : List UInt8) : List (List UInt8) := tranHtml (tId r) (tDesc r) (editZ (tAmt r))

/-- The output events of one transaction, in program order. -/
def tranEvents (r : List UInt8) : List Event := .write 1 (tranStmtR r) :: (tranHtmlR r).map (.write 2)

/-- `ADD TRNX-AMT TO WS-TOTAL-AMT` (`PIC S9(9)V99 COMP-3`: high-order truncation). -/
def addAmt (acc : Int) (r : List UInt8) : Int :=
  (Sem.fitNum {} { digits := 11, scale := 2, signed := true, usage := .packed } (acc + tAmt r)).2

attribute [local cobol_eval high] html6000

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 50000 in
/-- One pass of the transaction loop's body: transaction `j` of entry `k` to `TRNX-ID` /
`TRNX-REST`, `6000-WRITE-TRANS`, the amount added. -/
stm_summary inbody (env : Env) (m fuel : Nat) (mem : Mem) (hm : mem.size = 178495)
    (idx : List (Nat × Int)) (out : List Event) (inp : List (Nat × List (List UInt8))) (clockN : Nat)
    (r1 r2 : List (List UInt8)) (f3 f4 f5 f6 : FileSt)
    (hf1 : mem.read 3606 1 = [64]) (hf2 : mem.read 3656 1 = [91])
    (k j : Int) (hka : k.natAbs < 51) (hk1 : 1 ≤ k) (hk2 : k ≤ 50)
    (hja : j.natAbs < 11) (hj1 : 1 ≤ j) (hj2 : j ≤ 10)
    (hck : mem.read 1384 2 = encodeNum {} { digits := 4, signed := true, usage := .binary } k)
    (htj : mem.read 1386 2 = encodeNum {} { digits := 4, signed := true, usage := .binary } j)
    (r : List UInt8) (hrl : r.length = 350) (hidl : (tId r).length = 16) (hrsl : (tRest r).length = 318)
    (hnum : mem.read (4381 + (k.toNat - 1) * 3356 + (j.toNat - 1) * 334) 16 = tId r)
    (hrest : mem.read (4397 + (k.toNat - 1) * 3356 + (j.toNat - 1) * 334) 318 = tRest r)
    (amt : Int) (hamt : decodeNum {} { digits := 11, scale := 2, signed := true } (((tRest r).drop 116).take 11) = some amt)
    (amtT : List UInt8)
    (hed : Edit.edit {} [.z, .z, .z, .z, .z, .z, .z, .z, .z, .dot, .nine, .nine, .minus] false amt 2 = some amtT) (hamtl : amtT.length = 13)
    (acc : Int) (hacc1 : acc.natAbs < 100000000000) (hacc2 : -100000000000 < acc)
    (hacc : mem.read 1388 6 = encodeNum {} { digits := 11, scale := 2, signed := true, usage := .packed } acc) :
    Sem.execStmts Stm env (Sem.runFrom Stm env (m + 1)) fuel
      [Stm.«4000-TRNXFILE-GET».s5, Stm.«4000-TRNXFILE-GET».s6, Stm.«4000-TRNXFILE-GET».s7, Stm.«4000-TRNXFILE-GET».s8]
      ⟨mem, idx, [(.para 7, 4)], [], [4], out, inp,
        [(1, { mode := some .output, recs := r1 }), (2, { mode := some .output, recs := r2 }),
         (3, f3), (4, f4), (5, f5), (6, f6)], clockN⟩
  using [Int.toNat_natCast]

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 50000 in
/-- The step of the transaction loop: `ADD 1 TO TR-JMP`. -/
stm_summary instep (env : Env) (rec : Nat → State → Sem.Res) (fuel : Nat) (mem : Mem)
    (hm : mem.size = 178495) (st : State)
    (j : Int) (hja : j.natAbs < 11) (hj1 : 1 ≤ j) (hj2 : j ≤ 10)
    (htj : mem.read 1386 2 = encodeNum {} { digits := 4, signed := true, usage := .binary } j) :
    Sem.execStmts Stm env rec fuel [Stm.«4000-TRNXFILE-GET».s4]
      ⟨mem, st.idx, st.slots, st.saves, st.active, st.out, st.inp, st.files, st.clockN⟩

theorem addAmt_lt (acc : Int) (r : List UInt8) : (addAmt acc r).natAbs < 100000000000 := by
  have h := fitDec_lt 11 (acc + tAmt r)
  simp only [addAmt, Sem.fitNum]
  exact h

theorem foldl_addAmt_lt (acc0 : Int) (h0 : acc0.natAbs < 100000000000) :
    ∀ rs : List (List UInt8), (rs.foldl addAmt acc0).natAbs < 100000000000
  | [] => h0
  | r :: rs => by
    rw [List.foldl_cons]
    exact foldl_addAmt_lt (addAmt acc0 r) (addAmt_lt acc0 r) rs

/-- Storage the transaction loop does not write, region by region: between the record areas and
`TRNX-ID`, between `TRNX-REST` and `TR-JMP`, from `END-OF-FILE` to `ST-LINE14`, its two
constant bytes, from `ST-LINE14A` to `HTML-FIXED-LN`, from `HTML-L11` to `HTML-TRAN-LN`, the
table and above.  `m` agrees with `m0` there. -/
def InnerFrame (m0 m : Mem) : Prop :=
  (∀ o l, 180 ≤ o → o + l ≤ 196 → m.read o l = m0.read o l) ∧
  (∀ o l, 530 ≤ o → o + l ≤ 1386 → m.read o l = m0.read o l) ∧
  (∀ o l, 1394 ≤ o → o + l ≤ 3590 → m.read o l = m0.read o l) ∧
  (∀ o l, 3606 ≤ o → o + l ≤ 3607 → m.read o l = m0.read o l) ∧
  (∀ o l, 3656 ≤ o → o + l ≤ 3657 → m.read o l = m0.read o l) ∧
  (∀ o l, 3670 ≤ o → o + l ≤ 3830 → m.read o l = m0.read o l) ∧
  (∀ o l, 3930 ≤ o → o + l ≤ 4265 → m.read o l = m0.read o l) ∧
  (∀ o l, 4365 ≤ o → m.read o l = m0.read o l)

/-- Invariant of the transaction loop of entry `k` (records `g`), indexed by the records left. -/
def InnerInv (k : Int) (g : List (List UInt8)) (mem0 : Mem) (idx : List (Nat × Int))
    (out : List Event) (inp : List (Nat × List (List UInt8))) (clockN : Nat)
    (r1 r2 : List (List UInt8)) (f3 f4 f5 f6 : FileSt) (acc0 : Int) (rest : List (List UInt8))
    (st : State) : Prop :=
  ∃ done, g = done ++ rest ∧
    st.idx = idx ∧ st.slots = [(.para 7, 4)] ∧ st.saves = [] ∧ st.active = [4] ∧ st.inp = inp ∧
    st.clockN = clockN ∧
    st.out = (done.flatMap tranEvents).reverse ++ out ∧
    st.files = [(1, { mode := some .output, recs := r1 ++ done.map tranStmtR }),
      (2, { mode := some .output, recs := r2 ++ done.flatMap tranHtmlR }), (3, f3), (4, f4), (5, f5),
      (6, f6)] ∧
    st.mem.size = 178495 ∧
    st.mem.read 1386 2 = encodeNum {} { digits := 4, signed := true, usage := .binary }
      ((done.length : Int) + 1) ∧
    st.mem.read 1388 6 = encodeNum {} { digits := 11, scale := 2, signed := true, usage := .packed }
      (done.foldl addAmt acc0) ∧
    InnerFrame mem0 st.mem

theorem cmp_gt_false {a b : Int} (h : a ≤ b) : (compare a b == Ordering.gt) = false := by
  simp only [compare, compareOfLessAndEq]
  by_cases h1 : a < b
  · simp [h1]
  · have h2 : a = b := by omega
    simp [h2]

theorem cmp_succ_gt (c : Int) : (compare (c + 1) c == Ordering.gt) = true := by
  simp only [compare, compareOfLessAndEq]
  have h1 : ¬ (c + 1 < c) := by omega
  have h2 : ¬ (c + 1 = c) := by omega
  simp [h1, h2]

/-- Split an `InnerFrame` goal into its eight regions. -/
macro "frame_tac" : tactic => `(tactic| refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)

theorem res_eq_of_fst {r : Sem.Res} (h : r.1 = .normal) : r = (.normal, r.2) := Prod.ext h rfl

/-- A run that ends normally in a state satisfying `I`. -/
def NormalAnd (I : State → Prop) (r : Sem.Res) : Prop := r.1 = .normal ∧ I r.2

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 50000 in
/-- **The transaction loop of one table entry** (`PERFORM VARYING TR-JMP`, statement 9 of
`4000-TRNXFILE-GET`): entry `k` holds the records `g`; every record is written by
`6000-WRITE-TRANS` and its amount added to `WS-TOTAL-AMT`. -/
theorem inner_ok (env : Env) (m : Nat) (hm10 : 10 ≤ m) (mem0 : Mem) (hm : mem0.size = 178495)
    (idx : List (Nat × Int)) (out : List Event) (inp : List (Nat × List (List UInt8))) (clockN : Nat)
    (r1 r2 : List (List UInt8)) (f3 f4 f5 f6 : FileSt)
    (k : Int) (hka : k.natAbs < 51) (hk1 : 1 ≤ k) (hk2 : k ≤ 50)
    (hck : mem0.read 1384 2 = encodeNum {} { digits := 4, signed := true, usage := .binary } k)
    (g : List (List UInt8)) (hgl : g.length ≤ 10)
    (hrecs : ∀ r ∈ g, r.length = 350 ∧ AmtOk r)
    (htrct : mem0.read (175521 + (k.toNat - 1) * 2) 2 =
      encodeNum {} { digits := 4, signed := true, usage := .binary } (g.length : Int))
    (hent : ∀ j, j < g.length →
      mem0.read (4381 + (k.toNat - 1) * 3356 + j * 334) 16 = tId (g.getD j []) ∧
      mem0.read (4397 + (k.toNat - 1) * 3356 + j * 334) 318 = tRest (g.getD j []))
    (hf1 : mem0.read 3606 1 = [64]) (hf2 : mem0.read 3656 1 = [91])
    (acc0 : Int) (hacc0 : acc0.natAbs < 100000000000)
    (hacc : mem0.read 1388 6 =
      encodeNum {} { digits := 11, scale := 2, signed := true, usage := .packed } acc0) :
    NormalAnd (InnerInv k g mem0 idx out inp clockN r1 r2 f3 f4 f5 f6 acc0 [])
      (Sem.execStmt Stm env (Sem.runFrom Stm env (m + 1)) (m + 1) Stm.«4000-TRNXFILE-GET».s9
        ⟨mem0, idx, [(.para 7, 4)], [], [4], out, inp,
          [(1, { mode := some .output, recs := r1 }), (2, { mode := some .output, recs := r2 }),
           (3, f3), (4, f4), (5, f5), (6, f6)], clockN⟩) := by
  unfold NormalAnd
  stm_auto
  cobol_loop_step (InnerInv k g mem0 idx out inp clockN r1 r2 f3 f4 f5 f6 acc0) g
  · exact ⟨rfl, hloopInv⟩
  · -- before the loop: `TR-JMP = 1`, nothing written yet
    refine ⟨[], by simp, rfl, rfl, rfl, rfl, rfl, rfl, by simp, by simp, by simp [hm],
      by (stm_auto) <;> rfl, by stm_auto, ?_⟩
    frame_tac <;> intros <;> stm_auto
  · omega
  · -- no record left: `TR-JMP = count + 1 > WS-TRCT (k)`
    rintro ⟨mem, idx', slots', saves', active', out', inp', files', clockN'⟩
      ⟨done, hg, -, -, -, -, -, -, -, -, hsz, htj, -, hfr⟩
    simp only [List.append_nil] at hg
    subst hg
    dsimp only at hsz htj hfr
    have ht := hfr.2.2.2.2.2.2.2 (175521 + (k.toNat - 1) * 2) 2 (by omega)
    rw [htrct] at ht
    have hck' := hfr.2.1 1384 2 (by omega) (by omega)
    rw [hck] at hck'
    have hb0 : (0 : Int) ≤ (g.length : Int) := by omega
    have hb1 : (g.length : Int) ≤ 10 := by omega
    have hba : (g.length : Int).natAbs < 11 := by omega
    generalize (g.length : Int) = c at *
    (stm_auto) <;> omega
  · -- one record: `TRNX-ID` / `TRNX-REST` from the table, `6000-WRITE-TRANS`, the amount added
    rintro x xs ⟨mem, idx', slots', saves', active', out', inp', files', clockN'⟩
      ⟨done, hg, hidx, hsl, hsv, hac, hinp, hclk, hout, hfiles, hsz, htj, htot, hfr⟩
    dsimp only at hidx hsl hsv hac hinp hclk hout hfiles hsz htj htot hfr
    subst idx' slots' saves' active' inp' clockN' out' files'
    have hj : done.length < g.length := by rw [hg]; simp
    have hx : g.getD done.length [] = x := by
      rw [hg, getD_append_right' _ _ _ _ (Nat.le_refl _)]; simp
    obtain ⟨hxl, hxa⟩ := hrecs x (by rw [hg]; simp)
    obtain ⟨hn, hr⟩ := hent done.length hj
    rw [hx] at hn hr
    have hn' := (hfr.2.2.2.2.2.2.2 _ 16 (by omega)).trans hn
    have hr' := (hfr.2.2.2.2.2.2.2 _ 318 (by omega)).trans hr
    have hck' := (hfr.2.1 1384 2 (by omega) (by omega)).trans hck
    have hf1' := (hfr.2.2.2.1 3606 1 (by omega) (by omega)).trans hf1
    have hf2' := (hfr.2.2.2.2.1 3656 1 (by omega) (by omega)).trans hf2
    have ht := (hfr.2.2.2.2.2.2.2 (175521 + (k.toNat - 1) * 2) 2 (by omega)).trans htrct
    have hidl : (tId x).length = 16 := by simp [tId, hxl]
    have hrsl : (tRest x).length = 318 := by simp [tRest, hxl]
    have hedZ : Edit.edit {} [.z, .z, .z, .z, .z, .z, .z, .z, .z, .dot, .nine, .nine, .minus] false
        (tAmt x) 2 = some (editZ (tAmt x)) := editZ_eq (tAmt x)
    have hn'' : mem.read (4381 + (k.toNat - 1) * 3356 + (((done.length : Int) + 1).toNat - 1) * 334) 16
        = tId x := by simpa using hn'
    have hr'' : mem.read (4397 + (k.toNat - 1) * 3356 + (((done.length : Int) + 1).toNat - 1) * 334) 318
        = tRest x := by simpa using hr'
    have hacc1 := foldl_addAmt_lt acc0 hacc0 done
    have hacc2 : -100000000000 < done.foldl addAmt acc0 := by omega
    have hda0 : (done.length : Int).natAbs < 10 := by omega
    have hdb0 : (0 : Int) ≤ (done.length : Int) := by omega
    have hja : ((done.length : Int) + 1).natAbs < 11 := by omega
    have hj1 : (1 : Int) ≤ (done.length : Int) + 1 := by omega
    have hj2 : (done.length : Int) + 1 ≤ 10 := by omega
    have hbody := inbody env m (m + 1) mem hsz idx ((done.flatMap tranEvents).reverse ++ out) inp clockN
      (r1 ++ done.map tranStmtR) (r2 ++ done.flatMap tranHtmlR) f3 f4 f5 f6 hf1' hf2' k
      ((done.length : Int) + 1) hka hk1 hk2 hja hj1 hj2 hck' htj x hxl hidl hrsl hn'' hr'' (tAmt x) hxa
      (editZ (tAmt x)) hedZ (length_editZ _) (done.foldl addAmt acc0) hacc1 hacc2 htot
    refine ⟨?_, ?_, ?_, ?_⟩
    · have hda : (done.length : Int).natAbs < 10 := by omega
      have hb0 : (0 : Int) ≤ (done.length : Int) := by omega
      have hba : (g.length : Int).natAbs < 11 := by omega
      have hb2 : (0 : Int) ≤ (g.length : Int) := by omega
      have hb1 : (done.length : Int) + 1 ≤ (g.length : Int) := by omega
      (stm_auto) <;> exact cmp_gt_false hb1
    · rw [hbody]
    · have hel : (editZ (tAmt x)).length = 13 := length_editZ _
      have hdl : (List.take 49 (List.take 100 (List.drop 16 (tRest x)))).length = 49 := by simp [hrsl]
      rw [hbody]; stm_auto
    · have hel : (editZ (tAmt x)).length = 13 := length_editZ _
      have hdl : (List.take 49 (List.take 100 (List.drop 16 (tRest x)))).length = 49 := by simp [hrsl]
      rw [hbody]
      obtain ⟨F1, F2, F3, F4, F5, F6, F7, F8⟩ := hfr
      refine ⟨done ++ [x], by simp [hg], by stm_auto, by stm_auto, by stm_auto, by stm_auto,
        by stm_auto, by stm_auto, ?_, ?_, by stm_auto, ?_, ?_, ?_⟩
      · stm_auto [tranEvents, tranStmtR, tranHtmlR, tranStmt, tranHtml, hfield, tDesc,
          List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.reverse_append,
          List.reverse_cons, List.reverse_nil, List.map_cons, List.map_nil, List.append_assoc,
          List.cons_append, List.nil_append, List.singleton_append, hLTRS_lit, hL58_lit, hLTDE_lit,
          hL61_lit, hL64_lit, hLTRE_lit, tP_lit, tEndP_lit, sp, List.replicate_succ,
          List.replicate_zero, c3606_lit, c3656_lit]
      · stm_auto [tranStmtR, tranHtmlR, tranStmt, tranHtml, hfield, tDesc,
          List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.map_append, List.map_cons,
          List.map_nil, List.append_assoc, List.cons_append, List.nil_append, List.singleton_append,
          hLTRS_lit, hL58_lit, hLTDE_lit, hL61_lit, hL64_lit, hLTRE_lit, tP_lit, tEndP_lit, sp,
          List.replicate_succ, List.replicate_zero, c3606_lit, c3656_lit]
      · stm_auto [List.length_append, List.length_singleton, Int.natCast_add, Int.natCast_one]
      · stm_auto [List.foldl_append, List.foldl_cons, List.foldl_nil, addAmt]
      · frame_tac
        · intro o l h1 h2; have := F1 o l h1 h2; stm_auto
        · intro o l h1 h2; have := F2 o l h1 h2; stm_auto
        · intro o l h1 h2; have := F3 o l h1 h2; stm_auto
        · intro o l h1 h2; have := F4 o l h1 h2; stm_auto
        · intro o l h1 h2; have := F5 o l h1 h2; stm_auto
        · intro o l h1 h2; have := F6 o l h1 h2; stm_auto
        · intro o l h1 h2; have := F7 o l h1 h2; stm_auto [length_ovw]
        · intro o l h1; have := F8 o l h1; stm_auto [length_ovw]

/-! ## The scan of the table entries -/

/-- The table entries the scan for card `X` visits: up to the first card above `X`. -/
def vis (X : List UInt8) (gs : List (List (List UInt8))) : List (List (List UInt8)) :=
  gs.takeWhile (fun g => Sem.cmpBytes (gCard g) X != .gt)

/-- What an entry contributes: its records if it has the card `X`. -/
def matchStmt (X : List UInt8) (g : List (List UInt8)) : List (List UInt8) :=
  if gCard g = X then g.map tranStmtR else []

def matchHtml (X : List UInt8) (g : List (List UInt8)) : List (List UInt8) :=
  if gCard g = X then g.flatMap tranHtmlR else []

def matchEvents (X : List UInt8) (g : List (List UInt8)) : List Event :=
  if gCard g = X then g.flatMap tranEvents else []

def accStep (X : List UInt8) (acc : Int) (g : List (List UInt8)) : Int :=
  if gCard g = X then g.foldl addAmt acc else acc

theorem mem_takeWhile {α : Type _} (p : α → Bool) :
    ∀ (l : List α) (a : α), a ∈ l.takeWhile p → p a = true
  | [], _, h => by simp at h
  | x :: xs, a, h => by
    simp only [List.takeWhile_cons] at h
    split at h
    · rename_i hx
      rcases List.mem_cons.mp h with rfl | h
      · exact hx
      · exact mem_takeWhile p xs a h
    · simp at h

theorem vis_cons (X : List UInt8) (gs : List (List (List UInt8))) (doneG : List (List (List UInt8)))
    (g : List (List UInt8)) (rest : List (List (List UInt8))) (h : vis X gs = doneG ++ g :: rest) :
    gs.getD doneG.length [] = g ∧ Sem.cmpBytes (gCard g) X ≠ .gt ∧ doneG.length < gs.length := by
  have hsplit : gs = vis X gs ++ gs.dropWhile (fun g => Sem.cmpBytes (gCard g) X != .gt) :=
    (List.takeWhile_append_dropWhile).symm
  have hlt : doneG.length < (vis X gs).length := by rw [h]; simp
  have hlen : (vis X gs).length ≤ gs.length := by
    conv => rhs; rw [hsplit]
    simp
  refine ⟨?_, ?_, by omega⟩
  · rw [hsplit, getD_append_left' _ _ _ _ hlt, h, getD_append_right' _ _ _ _ (Nat.le_refl _)]
    simp
  · have hm : g ∈ vis X gs := by rw [h]; simp
    have := mem_takeWhile _ gs g hm
    simpa using this

theorem vis_end (X : List UInt8) (gs : List (List (List UInt8))) :
    (vis X gs).length = gs.length ∨
      ((vis X gs).length < gs.length ∧ Sem.cmpBytes (gCard (gs.getD (vis X gs).length [])) X = .gt) := by
  have hsplit : gs = vis X gs ++ gs.dropWhile (fun g => Sem.cmpBytes (gCard g) X != .gt) :=
    (List.takeWhile_append_dropWhile).symm
  cases hd : gs.dropWhile (fun g => Sem.cmpBytes (gCard g) X != .gt) with
  | nil =>
    left
    conv => rhs; rw [hsplit, hd]
    simp
  | cons d ds =>
    right
    have hhead := List.head_dropWhile_not (fun g => Sem.cmpBytes (gCard g) X != .gt) (l := gs)
      (by rw [hd]; simp)
    simp only [hd, List.head_cons] at hhead
    refine ⟨?_, ?_⟩
    · conv => rhs; rw [hsplit, hd]
      simp
    · generalize hV : vis X gs = V at hsplit ⊢
      rw [hsplit, hd, getD_append_right' _ _ _ _ (Nat.le_refl _)]
      simpa using hhead

/-- Storage the table scan does not write (`InnerFrame` without `TRNX-CARD-NUM` and `CR-JMP`). -/
def OuterFrame (m0 m : Mem) : Prop :=
  (∀ o l, 530 ≤ o → o + l ≤ 1384 → m.read o l = m0.read o l) ∧
  (∀ o l, 1394 ≤ o → o + l ≤ 3590 → m.read o l = m0.read o l) ∧
  (∀ o l, 3606 ≤ o → o + l ≤ 3607 → m.read o l = m0.read o l) ∧
  (∀ o l, 3656 ≤ o → o + l ≤ 3657 → m.read o l = m0.read o l) ∧
  (∀ o l, 3670 ≤ o → o + l ≤ 3830 → m.read o l = m0.read o l) ∧
  (∀ o l, 3930 ≤ o → o + l ≤ 4265 → m.read o l = m0.read o l) ∧
  (∀ o l, 4365 ≤ o → m.read o l = m0.read o l)

/-- Invariant of the table scan for card `X`, indexed by the entries still to visit. -/
def OuterInv (X : List UInt8) (gs : List (List (List UInt8))) (mem0 : Mem)
    (idx : List (Nat × Int)) (out : List Event) (inp : List (Nat × List (List UInt8)))
    (clockN : Nat) (r1 r2 : List (List UInt8)) (f3 f4 f5 f6 : FileSt)
    (rest : List (List (List UInt8))) (st : State) : Prop :=
  ∃ doneG, vis X gs = doneG ++ rest ∧
    st.idx = idx ∧ st.slots = [(.para 7, 4)] ∧ st.saves = [] ∧ st.active = [4] ∧ st.inp = inp ∧
    st.clockN = clockN ∧
    st.out = (doneG.flatMap (matchEvents X)).reverse ++ out ∧
    st.files = [(1, { mode := some .output, recs := r1 ++ doneG.flatMap (matchStmt X) }),
      (2, { mode := some .output, recs := r2 ++ doneG.flatMap (matchHtml X) }), (3, f3), (4, f4),
      (5, f5), (6, f6)] ∧
    st.mem.size = 178495 ∧
    st.mem.read 1384 2 = encodeNum {} { digits := 4, signed := true, usage := .binary }
      ((doneG.length : Int) + 1) ∧
    st.mem.read 1388 6 = encodeNum {} { digits := 11, scale := 2, signed := true, usage := .packed }
      (doneG.foldl (accStep X) 0) ∧
    OuterFrame mem0 st.mem

theorem foldl_accStep_lt (X : List UInt8) :
    ∀ (gs : List (List (List UInt8))) (acc : Int), acc.natAbs < 100000000000 →
      (gs.foldl (accStep X) acc).natAbs < 100000000000
  | [], _, h => h
  | g :: gs, acc, h => by
    rw [List.foldl_cons]
    apply foldl_accStep_lt X gs
    unfold accStep
    split
    · exact foldl_addAmt_lt acc h g
    · exact h

/-- Storage `4000-TRNXFILE-GET` does not write. -/
def TrnxFrame (m0 m : Mem) : Prop :=
  (∀ o l, 530 ≤ o → o + l ≤ 1384 → m.read o l = m0.read o l) ∧
  (∀ o l, 1394 ≤ o → o + l ≤ 1402 → m.read o l = m0.read o l) ∧
  (∀ o l, 1413 ≤ o → o + l ≤ 3590 → m.read o l = m0.read o l) ∧
  (∀ o l, 3606 ≤ o → o + l ≤ 3607 → m.read o l = m0.read o l) ∧
  (∀ o l, 3656 ≤ o → o + l ≤ 3657 → m.read o l = m0.read o l) ∧
  (∀ o l, 3670 ≤ o → o + l ≤ 3737 → m.read o l = m0.read o l) ∧
  (∀ o l, 3750 ≤ o → o + l ≤ 3830 → m.read o l = m0.read o l) ∧
  (∀ o l, 3930 ≤ o → o + l ≤ 4265 → m.read o l = m0.read o l) ∧
  (∀ o l, 4365 ≤ o → m.read o l = m0.read o l)

/-- The closing records of a statement (`4000-TRNXFILE-GET` after the scan): the total. -/
def tailStmt (total : Int) : List (List UInt8) := [c3430, c3670 ++ editZ total, c3750]

def tailHtml : List (List UInt8) := [hLTRS, hL10, hL75, hLTDE, hLTRE, hL78, hL79, hL80]

def tailEvents (total : Int) : List Event :=
  (tailStmt total).map (.write 1) ++ tailHtml.map (.write 2)

/-- The statement body for card `X`: the scan's records, the total, the closing records. -/
def trnxStmt (X : List UInt8) (gs : List (List (List UInt8))) : List (List UInt8) :=
  (vis X gs).flatMap (matchStmt X) ++ tailStmt ((vis X gs).foldl (accStep X) 0)

def trnxHtml (X : List UInt8) (gs : List (List (List UInt8))) : List (List UInt8) :=
  (vis X gs).flatMap (matchHtml X) ++ tailHtml

def trnxEvents (X : List UInt8) (gs : List (List (List UInt8))) : List Event :=
  (vis X gs).flatMap (matchEvents X) ++ tailEvents ((vis X gs).foldl (accStep X) 0)

/-- What `4000-TRNXFILE-GET` leaves. -/
def TrnxPost (X : List UInt8) (gs : List (List (List UInt8))) (mem0 : Mem)
    (idx : List (Nat × Int)) (out : List Event) (inp : List (Nat × List (List UInt8)))
    (clockN : Nat) (r1 r2 : List (List UInt8)) (f3 f4 f5 f6 : FileSt) (st : State) : Prop :=
  st.idx = idx ∧ st.slots = [(.para 7, 4)] ∧ st.saves = [] ∧ st.active = [4] ∧ st.inp = inp ∧
    st.clockN = clockN ∧
    st.out = (trnxEvents X gs).reverse ++ out ∧
    st.files = [(1, { mode := some .output, recs := r1 ++ trnxStmt X gs }),
      (2, { mode := some .output, recs := r2 ++ trnxHtml X gs }), (3, f3), (4, f4), (5, f5),
      (6, f6)] ∧
    st.mem.size = 178495 ∧ TrnxFrame mem0 st.mem

set_option maxHeartbeats 100000000 in
/-- The entry body when entry `k` has the card `X`: `MOVE WS-CARD-NUM (k) TO TRNX-CARD-NUM`, then the
transaction loop (statement 9, left folded). -/
theorem s10_match (env : Env) (m : Nat) (mem : Mem) (hm : mem.size = 178495)
    (idx : List (Nat × Int)) (out : List Event) (inp : List (Nat × List (List UInt8))) (clockN : Nat)
    (files : List (Nat × FileSt))
    (k : Int) (hka : k.natAbs < 51) (hk1 : 1 ≤ k) (hk2 : k ≤ 50)
    (hck : mem.read 1384 2 = encodeNum {} { digits := 4, signed := true, usage := .binary } k)
    (X : List UInt8) (hXl : X.length = 16) (hX : mem.read 530 16 = X)
    (hcard : mem.read (4365 + (k.toNat - 1) * 3356) 16 = X) :
    Sem.execStmts Stm env (Sem.runFrom Stm env (m + 1)) (m + 1) [Stm.«4000-TRNXFILE-GET».s10]
      ⟨mem, idx, [(.para 7, 4)], [], [4], out, inp, files, clockN⟩ =
    Sem.execStmt Stm env (Sem.runFrom Stm env (m + 1)) (m + 1) Stm.«4000-TRNXFILE-GET».s9
      ⟨mem.write 180 X, idx, [(.para 7, 4)], [], [4], out, inp, files, clockN⟩ := by
  have hs10 : Stm.«4000-TRNXFILE-GET».s10 =
      Stmt.ite _ [Stm.«4000-TRNXFILE-GET».s2, Stm.«4000-TRNXFILE-GET».s9] [] := rfl
  rw [hs10]
  generalize Stm.«4000-TRNXFILE-GET».s9 = S
  stm_auto
  rcases Sem.execStmt Stm env (Sem.runFrom Stm env (m + 1)) (m + 1) S
    ⟨mem.write 180 X, idx, [(.para 7, 4)], [], [4], out, inp, files, clockN⟩ with ⟨sig, st⟩
  cases sig <;> rfl

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 50000 in
/-- **Phase 6: `4000-TRNXFILE-GET`.** -/
theorem trnx_ok (env : Env) (m : Nat) (hm50 : 50 ≤ m) (mem0 : Mem) (hm : mem0.size = 178495)
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
      encodeNum {} { digits := 11, scale := 2, signed := true, usage := .packed } 0) :
    NormalAnd (TrnxPost X gs mem0 idx out inp clockN r1 r2 f3 f4 f5 f6)
      (Sem.execSentences Stm env (Sem.runFrom Stm env (m + 1)) (m + 1)
        Stm.«4000-TRNXFILE-GET».body
        ⟨mem0, idx, [(.para 7, 4)], [], [4], out, inp,
          [(1, { mode := some .output, recs := r1 }), (2, { mode := some .output, recs := r2 }),
           (3, f3), (4, f4), (5, f5), (6, f6)], clockN⟩) := by
  unfold NormalAnd
  stm_auto
  cobol_loop_step (OuterInv X gs mem0 idx out inp clockN r1 r2 f3 f4 f5 f6) (vis X gs)
  · -- after the scan: the total to `WS-TRN-AMT` and `ST-TOTAL-TRAMT`, the closing records
    obtain ⟨mem, idx', slots', saves', active', out', inp', files', clockN'⟩ := loopState
    obtain ⟨doneG, hv, hidx, hsl, hsv, hac, hinp, hclk, hout, hfiles, hsz, hcj, htot, hfr⟩ := hloopInv
    dsimp only at hidx hsl hsv hac hinp hclk hout hfiles hsz hcj htot hfr
    subst idx' slots' saves' active' inp' clockN' out' files'
    simp only [List.append_nil] at hv
    simp only [ConstsOk] at hc
    obtain ⟨k01, k02, k03, k04, k05, k06, k07, k08, k09, k10, k11, k12, k13, k14, k15, k16, k17, k18, k19, k20, k21, k22, k23⟩ := hc
    obtain ⟨F1, F2, F3, F4, F5, F6, F7⟩ := hfr
    have q1 := (F2 3430 80 (by omega) (by omega)).trans k15
    have q2 := (F5 3670 67 (by omega) (by omega)).trans k19
    have q3 := (F5 3750 80 (by omega) (by omega)).trans k20
    have htb := foldl_accStep_lt X doneG 0 (by decide)
    have htb2 : -100000000000 < doneG.foldl (accStep X) 0 := by omega
    have hedZ : Edit.edit {} [.z, .z, .z, .z, .z, .z, .z, .z, .z, .dot, .nine, .nine, .minus] false
        (doneG.foldl (accStep X) 0) 2 = some (editZ (doneG.foldl (accStep X) 0)) := editZ_eq _
    have hel := length_editZ (doneG.foldl (accStep X) 0)
    unfold TrnxPost trnxEvents trnxStmt trnxHtml
    rw [hv]
    refine ⟨by stm_auto, by stm_auto, by stm_auto, by stm_auto, by stm_auto, by stm_auto, by stm_auto,
      ?_, ?_, by stm_auto, ?_⟩
    · stm_auto [tailEvents, tailStmt, tailHtml, List.map_cons, List.map_nil, List.reverse_append,
        List.reverse_cons, List.reverse_nil, List.append_assoc, List.cons_append, List.nil_append,
        List.singleton_append, hLTRS_lit, hL10_lit, hL75_lit, hLTDE_lit, hLTRE_lit, hL78_lit, hL79_lit,
        hL80_lit, c3430_lit, c3670_lit, c3750_lit]
    · stm_auto [tailStmt, tailHtml, List.append_assoc, List.cons_append, List.nil_append,
        List.singleton_append, hLTRS_lit, hL10_lit, hL75_lit, hLTDE_lit, hLTRE_lit, hL78_lit, hL79_lit,
        hL80_lit, c3430_lit, c3670_lit, c3750_lit]
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro o l h1 h2; have := F1 o l h1 h2; stm_auto
      · intro o l h1 h2; have := F2 o l h1 (by omega); stm_auto
      · intro o l h1 h2; have := F2 o l (by omega) h2; stm_auto
      · intro o l h1 h2; have := F3 o l h1 h2; stm_auto
      · intro o l h1 h2; have := F4 o l h1 h2; stm_auto
      · intro o l h1 h2; have := F5 o l h1 (by omega); stm_auto
      · intro o l h1 h2; have := F5 o l (by omega) h2; stm_auto
      · intro o l h1 h2; have := F6 o l h1 h2; stm_auto
      · intro o l h1; have := F7 o l h1; stm_auto
  · -- before the scan: `CR-JMP = 1`
    refine ⟨[], by simp, rfl, rfl, rfl, rfl, rfl, rfl, by simp, by simp, by simp [hm],
      by (stm_auto) <;> rfl, by stm_auto, ?_⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intros <;> stm_auto
  · rcases vis_end X gs with h | ⟨h, -⟩ <;> omega
  · -- the scan ends: past the last entry, or at a card above `X`
    rintro ⟨mem, idx', slots', saves', active', out', inp', files', clockN'⟩
      ⟨doneG, hv, -, -, -, -, -, -, -, -, hsz, hcj, -, hfr⟩
    simp only [List.append_nil] at hv
    dsimp only at hsz hcj hfr
    obtain ⟨F1, F2, F3, F4, F5, F6, F7⟩ := hfr
    have hcr' := (F1 1380 2 (by omega) (by omega)).trans hcr
    have hX' := (F1 530 16 (by omega) (by omega)).trans hX
    have hvl : doneG.length ≤ gs.length := by
      rw [← hv]; rcases vis_end X gs with h | ⟨h, -⟩ <;> omega
    have hdb : (doneG.length : Int).natAbs < 51 := by omega
    have hd0 : (0 : Int) ≤ doneG.length := by omega
    have hGa : (gs.length : Int).natAbs < 51 := by omega
    have hG0 : (0 : Int) ≤ gs.length := by omega
    rcases vis_end X gs with hA | ⟨hB1, hB2⟩
    · rw [hv] at hA
      rw [hA] at hcj hdb hd0
      (stm_auto) <;> simp [cmp_succ_gt]
    · rw [hv] at hB1 hB2
      obtain ⟨hc1, -⟩ := htab (doneG.length + 1) (by omega) (by omega)
      have hcard := (F7 _ 16 (by omega)).trans hc1
      simp only [Nat.add_sub_cancel] at hcard
      have hgl : (gCard (gs.getD doneG.length [])).length = 16 := by
        have := congrArg List.length hcard; simpa using this.symm
      stm_auto [Int.toNat_natCast_add_one, Int.toNat_natCast]
  · -- one entry: another card (nothing) or the card `X` (its transactions); then `CR-JMP + 1`
    rintro g rest ⟨mem, idx', slots', saves', active', out', inp', files', clockN'⟩
      ⟨doneG, hv, hidx, hsl, hsv, hac, hinp, hclk, hout, hfiles, hsz, hcj, htot, hfr⟩
    dsimp only at hidx hsl hsv hac hinp hclk hout hfiles hsz hcj htot hfr
    subst idx' slots' saves' active' inp' clockN' out' files'
    obtain ⟨hgd, hgt, hlt⟩ := vis_cons X gs doneG g rest hv
    have hgm : g ∈ gs := by
      rw [← hgd, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some]
      exact List.getElem_mem _
    obtain ⟨F1, F2, F3, F4, F5, F6, F7⟩ := hfr
    have hcr' := (F1 1380 2 (by omega) (by omega)).trans hcr
    have hX' := (F1 530 16 (by omega) (by omega)).trans hX
    obtain ⟨hc1, hc2⟩ := htab (doneG.length + 1) (by omega) (by omega)
    simp only [Nat.add_sub_cancel] at hc1 hc2
    rw [hgd] at hc1 hc2
    have hcard := (F7 _ 16 (by omega)).trans hc1
    have hgl : (gCard g).length = 16 := by
      have := congrArg List.length hcard; simpa using this.symm
    have hdb : (doneG.length : Int).natAbs < 50 := by omega
    have hd0 : (0 : Int) ≤ doneG.length := by omega
    have hGa : (gs.length : Int).natAbs < 51 := by omega
    have hG0 : (0 : Int) ≤ gs.length := by omega
    have hacb := foldl_accStep_lt X doneG 0 (by decide)
    have hacb2 : -100000000000 < doneG.foldl (accStep X) 0 := by omega
    have hcf : (compare ((doneG.length : Int) + 1) (gs.length : Int) == Ordering.gt) = false :=
      cmp_gt_false (by omega)
    have hgt' : (Sem.cmpBytes (gCard g) X == Ordering.gt) = false := by simpa using hgt
    by_cases hm : gCard g = X
    · -- the card `X`: `TRNX-CARD-NUM`, then the transaction loop of the entry
      subst hm
      simp only [ConstsOk] at hc
      obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, k17, k18, -, -, -, -, -⟩ := hc
      have e1 : (mem.write 180 (gCard g)).size = 178495 := by simp [hsz]
      have e2 : (mem.write 180 (gCard g)).read 1384 2 =
          encodeNum {} { digits := 4, signed := true, usage := .binary } ((doneG.length : Int) + 1) := by
        stm_auto
      have e3 : (mem.write 180 (gCard g)).read (175521 + (((doneG.length : Int) + 1).toNat - 1) * 2) 2 =
          encodeNum {} { digits := 4, signed := true, usage := .binary } (g.length : Int) := by
        have h := htrct (doneG.length + 1) (by omega) (by omega)
        simp only [Nat.add_sub_cancel] at h
        rw [hgd] at h
        have h2 := (F7 _ 2 (by omega)).trans h
        stm_auto [Int.toNat_natCast_add_one]
      have e4 : ∀ j, j < g.length →
          (mem.write 180 (gCard g)).read (4381 + (((doneG.length : Int) + 1).toNat - 1) * 3356 + j * 334) 16
            = tId (g.getD j []) ∧
          (mem.write 180 (gCard g)).read (4397 + (((doneG.length : Int) + 1).toNat - 1) * 3356 + j * 334) 318
            = tRest (g.getD j []) := by
        intro j hj
        obtain ⟨a, b⟩ := hc2 (j + 1) (by omega) (by omega)
        simp only [Nat.add_sub_cancel] at a b
        have a2 := (F7 _ 16 (by omega)).trans a
        have b2 := (F7 _ 318 (by omega)).trans b
        exact ⟨by stm_auto [Int.toNat_natCast_add_one], by stm_auto [Int.toNat_natCast_add_one]⟩
      have e5 : (mem.write 180 (gCard g)).read 3606 1 = [64] := by
        have h := (F3 3606 1 (by omega) (by omega)).trans k17; stm_auto
      have e6 : (mem.write 180 (gCard g)).read 3656 1 = [91] := by
        have h := (F4 3656 1 (by omega) (by omega)).trans k18; stm_auto
      have e7 : (mem.write 180 (gCard g)).read 1388 6 =
          encodeNum {} { digits := 11, scale := 2, signed := true, usage := .packed }
            (doneG.foldl (accStep (gCard g)) 0) := by stm_auto
      obtain ⟨hn, hi⟩ := inner_ok env m (by omega) (mem.write 180 (gCard g)) e1 idx
        ((doneG.flatMap (matchEvents (gCard g))).reverse ++ out) inp clockN
        (r1 ++ doneG.flatMap (matchStmt (gCard g))) (r2 ++ doneG.flatMap (matchHtml (gCard g)))
        f3 f4 f5 f6 ((doneG.length : Int) + 1) (by omega) (by omega) (by omega) e2 g (hT g hgm)
        (hrecs g hgm) e3 e4 e5 e6 (doneG.foldl (accStep (gCard g)) 0) hacb e7
      rw [s10_match env m mem hsz idx _ inp clockN _ ((doneG.length : Int) + 1) (by omega) (by omega)
        (by omega) hcj (gCard g) hgl hX' (by simpa using hcard)]
      rw [res_eq_of_fst hn]
      obtain ⟨done, hgdone, h3idx, h3sl, h3sv, h3ac, h3inp, h3clk, h3out, h3files, h3sz, h3tj, h3tot,
        h3fr⟩ := hi
      simp only [List.append_nil] at hgdone
      subst hgdone
      generalize (Sem.execStmt Stm env (Sem.runFrom Stm env (m + 1)) (m + 1) Stm.«4000-TRNXFILE-GET».s9
        ⟨mem.write 180 (gCard g), idx, [(.para 7, 4)], [], [4],
          (doneG.flatMap (matchEvents (gCard g))).reverse ++ out, inp,
          [(1, { mode := some .output, recs := r1 ++ doneG.flatMap (matchStmt (gCard g)) }),
           (2, { mode := some .output, recs := r2 ++ doneG.flatMap (matchHtml (gCard g)) }),
           (3, f3), (4, f4), (5, f5), (6, f6)], clockN⟩).2 = st3 at *
      obtain ⟨m3, idx3, slots3, saves3, active3, out3, inp3, files3, clockN3⟩ := st3
      dsimp only at h3idx h3sl h3sv h3ac h3inp h3clk h3out h3files h3sz h3tj h3tot h3fr
      subst idx3 slots3 saves3 active3 inp3 clockN3 out3 files3
      obtain ⟨G1, G2, G3, G4, G5, G6, G7, G8⟩ := h3fr
      have hcj3 := (G2 1384 2 (by omega) (by omega)).trans e2
      refine ⟨by stm_auto [Int.toNat_natCast_add_one, Int.toNat_natCast], rfl, by stm_auto, ?_⟩
      refine ⟨doneG ++ [g], by rw [hv]; simp, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      all_goals try (stm_auto [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, matchEvents,
        matchStmt, matchHtml, List.append_nil, List.foldl_append, List.foldl_cons, List.foldl_nil,
        accStep, List.length_append, List.length_singleton, Int.natCast_add, Int.natCast_one,
        List.reverse_append, List.append_assoc, List.map_append]; done)
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro o l h1 h2; have := G2 o l h1 (by omega); have := F1 o l h1 h2; stm_auto
      · intro o l h1 h2; have := G3 o l h1 h2; have := F2 o l h1 h2; stm_auto
      · intro o l h1 h2; have := G4 o l h1 h2; have := F3 o l h1 h2; stm_auto
      · intro o l h1 h2; have := G5 o l h1 h2; have := F4 o l h1 h2; stm_auto
      · intro o l h1 h2; have := G6 o l h1 h2; have := F5 o l h1 h2; stm_auto
      · intro o l h1 h2; have := G7 o l h1 h2; have := F6 o l h1 h2; stm_auto
      · intro o l h1; have := G8 o l h1; have := F7 o l h1; stm_auto
    · -- another card: the `IF` is false, nothing written
      have hne : X ≠ gCard g := fun h => hm h.symm
      refine ⟨by stm_auto [Int.toNat_natCast_add_one, Int.toNat_natCast],
        by stm_auto [Int.toNat_natCast_add_one, Int.toNat_natCast],
        by stm_auto [Int.toNat_natCast_add_one, Int.toNat_natCast], ?_⟩
      refine ⟨doneG ++ [g], by rw [hv]; simp, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      all_goals try (stm_auto [Int.toNat_natCast_add_one, Int.toNat_natCast, List.flatMap_append,
        List.flatMap_cons, List.flatMap_nil, matchEvents, matchStmt, matchHtml, hm, List.append_nil,
        List.foldl_append, List.foldl_cons, List.foldl_nil, accStep, List.length_append,
        List.length_singleton, Int.natCast_add, Int.natCast_one]; done)
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro o l h1 h2; have := F1 o l h1 h2; stm_auto [Int.toNat_natCast_add_one, Int.toNat_natCast]
      · intro o l h1 h2; have := F2 o l h1 h2; stm_auto [Int.toNat_natCast_add_one, Int.toNat_natCast]
      · intro o l h1 h2; have := F3 o l h1 h2; stm_auto [Int.toNat_natCast_add_one, Int.toNat_natCast]
      · intro o l h1 h2; have := F4 o l h1 h2; stm_auto [Int.toNat_natCast_add_one, Int.toNat_natCast]
      · intro o l h1 h2; have := F5 o l h1 h2; stm_auto [Int.toNat_natCast_add_one, Int.toNat_natCast]
      · intro o l h1 h2; have := F6 o l h1 h2; stm_auto [Int.toNat_natCast_add_one, Int.toNat_natCast]
      · intro o l h1; have := F7 o l h1; stm_auto [Int.toNat_natCast_add_one, Int.toNat_natCast]

end Cobol.StmCore
