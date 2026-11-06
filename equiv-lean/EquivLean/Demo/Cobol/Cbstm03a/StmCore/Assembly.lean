/-
# The whole run of `CBSTM03AB`

From the initial state (storage `m0` overwritten by the `VALUE` clauses, the four input files)
the program walks the `PSA`/`TCB`/`TIOT` blocks (`execSentences_walk`, a black box), opens
`STMT-FILE` and `HTML-FILE`, initialises the transaction table (`execStmts_init`), opens the
transaction file and reads its first record through `CBSTM03B` (`pre_load_eq`), loads the table
(`phase3`), opens the cross-reference, customer and account files (`post_load_eq`) and runs
`1000-MAINLINE` (`mainline_ok`).

The steps between paragraphs are separate lemmas, one paragraph run each (`run0`, `start_trnx`,
`open_trnx`, …): symbolic execution stops in front of the next paragraph because the run
equations of the paragraphs it must not enter are erased in the lemma's section.  Two lessons:
* the first paragraph's 1141 statements must never be unfolded in a definitional check: the
  summary `para0_sum` is stated at the exact fuel of its call site (an offset form `fuel + 9`
  made the kernel evaluate the paragraph to compare the two);
* `INITIALIZE`'s 171156 spaces stay a constant (`spTbl`): `cobol_eval` spells out
  `List.replicate`.
-/
import EquivLean.Demo.Cobol.Cbstm03a.StmCore.Mainline2
import EquivLean.Demo.Cobol.Cbstm03a.StmCore.Init

open Cobol Cobol.Stm

namespace Cobol.StmCore

/-! ## The first paragraph -/

/-- The first paragraph: the walk (`execSentences_walk`), then `OPEN` and `INITIALIZE`. -/
theorem para0_run (env : Env) (hEnv : env.addrSpace = asp) (rec : Nat → State → Sem.Res)
    (fuel : Nat) (st : State) (hm : st.mem.size = 178495)
    (hp : st.mem.read 175623 4 = [0, 0, 0, 0]) :
    Sem.execSentences Stm env rec (fuel + 9) Stm.para0.body st =
      Sem.execSentences Stm env rec (fuel + 9) [[Stm.para0.s17, Stm.para0.s18], initSentence]
        { st with mem := walkMem st.mem, out := walkDisplays ++ st.out } := by
  have hb : Stm.para0.body = [[Stm.para0.s0], [Stm.para0.s1], [Stm.para0.s2], [Stm.para0.s3],
      [Stm.para0.s4], [Stm.para0.s5], [Stm.para0.s6], [Stm.para0.s7], [Stm.para0.s13],
      [Stm.para0.s16]] ++ [[Stm.para0.s17, Stm.para0.s18], initSentence] := rfl
  rw [hb]
  exact execSentences_append _ _ _ _ _ _ _ _ (execSentences_walk env hEnv rec fuel st hm hp)

theorem walkMem_size (m : Mem) : (walkMem m).size = m.size := by simp [walkMem]

/-- The walk writes only 175627 … 176242. -/
theorem walkMem_read_lo (m : Mem) (o l : Nat) (h : o + l ≤ 175627) :
    (walkMem m).read o l = m.read o l := by
  unfold walkMem
  rw [Mem.read_write_disjoint, Mem.read_write_disjoint, Mem.read_write_disjoint,
    Mem.read_write_disjoint, Mem.read_write_disjoint] <;> (left; omega)

theorem walkMem_read_hi (m : Mem) (o l : Nat) (h : 176243 ≤ o) :
    (walkMem m).read o l = m.read o l := by
  have h4 : (encodeNum {} { digits := 8, signed := true, usage := Usage.binary } 8376).length = 4 := by
    decide
  unfold walkMem
  rw [Mem.read_write_disjoint, Mem.read_write_disjoint, Mem.read_write_disjoint,
    Mem.read_write_disjoint, Mem.read_write_disjoint] <;>
    (right; simp only [List.length_map, List.length_range, h4]; omega)

/-- `INITIALIZE`'s spaces over `WS-TRNX-TABLE` and zeros over `WS-TRN-TBL-CNTR`, as constants
(`cobol_eval` would spell the lists out). -/
def spTbl : List UInt8 := List.replicate 171156 64
def zTrct : List UInt8 := List.replicate 102 0

theorem length_spTbl : spTbl.length = 171156 := by rw [spTbl, List.length_replicate]
theorem length_zTrct : zTrct.length = 102 := by rw [zTrct, List.length_replicate]

/-- `execStmts_init` with the constants. -/
theorem init_run (env : Env) (rec : Nat → State → Sem.Res) (fuel : Nat) (st : State)
    (hm : st.mem.size = 178495) :
    Sem.execStmts Stm env rec fuel initSentence st =
      (.normal, { st with mem := (st.mem.write 4365 spTbl).write 175521 zTrct }) :=
  execStmts_init env rec fuel st hm

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 50000 in
/-- The first paragraph's body from the initial state shape, at the fuel of `run0`'s call. -/
stm_summary para0_sum (env : Env) (hEnv : env.addrSpace = asp)
    (ho1 : env.openError 1 .output = none) (ho2 : env.openError 2 .output = none) (n : Nat)
    (mem : Mem) (hm : mem.size = 178495) (hp : mem.read 175623 4 = [0, 0, 0, 0])
    (inp : List (Nat × List (List UInt8))) :
    Sem.execSentences Stm env (Sem.runFrom Stm env (n + 54)) (n + 54) Stm.para0.body
      ⟨mem, [], [], [], [], [], inp, [], 0⟩
  using [↓para0_run, ↓init_run, hEnv, ho1, ho2, walkMem_size, length_spTbl, length_zTrct]

/-! ## Paragraph runs, each up to the next paragraph -/

section
attribute [-cobol_eval] Cobol.runFrom_succ
attribute [-stm_flow] Stm.runFrom_1

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 50000 in
/-- The first paragraph, then on to `0000-START`. -/
stm_summary run0 (env : Env) (hEnv : env.addrSpace = asp)
    (ho1 : env.openError 1 .output = none) (ho2 : env.openError 2 .output = none)
    (mem : Mem) (hm : mem.size = 178495) (hp : mem.read 175623 4 = [0, 0, 0, 0])
    (inp : List (Nat × List (List UInt8))) (n : Nat) :
    Sem.runFrom Stm env (n + 55) 0 ⟨mem, [], [], [], [], [], inp, [], 0⟩
  with_pre (rewrite [Stm.runFrom_0, para0_sum env hEnv ho1 ho2 n mem hm hp inp])

end

section
attribute [-cobol_eval] Cobol.runFrom_succ
attribute [-stm_flow] Stm.runFrom_15

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 50000 in
/-- `0000-START` with `WS-FL-DD = 'TRNXFILE'`: `ALTER`, then `8100-FILE-OPEN` goes on to
`8100-TRNXFILE-OPEN`. -/
stm_summary start_trnx (env : Env) (n : Nat) (mem : Mem) (hm : mem.size = 178495)
    (idx : List (Nat × Int)) (out : List Event) (inp : List (Nat × List (List UInt8)))
    (files : List (Nat × FileSt)) (clockN : Nat)
    (hfl : mem.read 1394 8 = [227, 217, 213, 231, 198, 201, 211, 197]) :
    Sem.runFrom Stm env (n + 10) 1 ⟨mem, idx, [], [], [], out, inp, files, clockN⟩

end

section
attribute [-cobol_eval] Cobol.runFrom_succ
attribute [-stm_flow] Stm.runFrom_1

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 50000 in
/-- `8100-TRNXFILE-OPEN`: `OPEN` and the first `READ` of the transaction file through
`CBSTM03B`; `CR-CNT := 1`, `TR-CNT := 0`, `WS-FL-DD := 'READTRNX'`, back to `0000-START`. -/
stm_summary open_trnx (env : Env) (ho3 : env.openError 3 .input = none) (n : Nat) (mem : Mem)
    (hm : mem.size = 178495) (idx : List (Nat × Int)) (out : List Event)
    (xrefs custs accts : List (List UInt8)) (cur : List UInt8) (rest : List (List UInt8))
    (hcur : cur.length = 350) (f1 f2 : FileSt) (clockN : Nat) :
    Sem.runFrom Stm env (n + 10) 15 ⟨mem, idx, [], [], [], out,
      [(3, cur :: rest), (4, xrefs), (5, custs), (6, accts)], [(1, f1), (2, f2)], clockN⟩
  using [ho3]

end

section
attribute [-cobol_eval] Cobol.runFrom_succ
attribute [-stm_flow] Stm.runFrom_19

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 50000 in
/-- `0000-START` with `WS-FL-DD = 'READTRNX'`: on to `8500-READTRNX-READ`. -/
stm_summary start_read (env : Env) (n : Nat) (mem : Mem) (hm : mem.size = 178495)
    (idx : List (Nat × Int)) (out : List Event) (inp : List (Nat × List (List UInt8)))
    (files : List (Nat × FileSt)) (clockN : Nat)
    (hfl : mem.read 1394 8 = [217, 197, 193, 196, 227, 217, 213, 231]) :
    Sem.runFrom Stm env (n + 10) 1 ⟨mem, idx, [], [], [], out, inp, files, clockN⟩

end

section
attribute [-cobol_eval] Cobol.runFrom_succ
attribute [-stm_flow] Stm.runFrom_16

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 50000 in
/-- `0000-START` with `WS-FL-DD = 'XREFFILE'`: on to `8200-XREFFILE-OPEN`. -/
stm_summary start_xref (env : Env) (n : Nat) (mem : Mem) (hm : mem.size = 178495)
    (idx : List (Nat × Int)) (out : List Event) (inp : List (Nat × List (List UInt8)))
    (files : List (Nat × FileSt)) (clockN : Nat)
    (hfl : mem.read 1394 8 = [231, 217, 197, 198, 198, 201, 211, 197]) :
    Sem.runFrom Stm env (n + 10) 1 ⟨mem, idx, [], [], [], out, inp, files, clockN⟩

end

section
attribute [-cobol_eval] Cobol.runFrom_succ
attribute [-stm_flow] Stm.runFrom_17

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 50000 in
/-- `0000-START` with `WS-FL-DD = 'CUSTFILE'`: on to `8300-CUSTFILE-OPEN`. -/
stm_summary start_cust (env : Env) (n : Nat) (mem : Mem) (hm : mem.size = 178495)
    (idx : List (Nat × Int)) (out : List Event) (inp : List (Nat × List (List UInt8)))
    (files : List (Nat × FileSt)) (clockN : Nat)
    (hfl : mem.read 1394 8 = [195, 228, 226, 227, 198, 201, 211, 197]) :
    Sem.runFrom Stm env (n + 10) 1 ⟨mem, idx, [], [], [], out, inp, files, clockN⟩

end

section
attribute [-cobol_eval] Cobol.runFrom_succ
attribute [-stm_flow] Stm.runFrom_18

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 50000 in
/-- `0000-START` with `WS-FL-DD = 'ACCTFILE'`: on to `8400-ACCTFILE-OPEN`. -/
stm_summary start_acct (env : Env) (n : Nat) (mem : Mem) (hm : mem.size = 178495)
    (idx : List (Nat × Int)) (out : List Event) (inp : List (Nat × List (List UInt8)))
    (files : List (Nat × FileSt)) (clockN : Nat)
    (hfl : mem.read 1394 8 = [193, 195, 195, 227, 198, 201, 211, 197]) :
    Sem.runFrom Stm env (n + 10) 1 ⟨mem, idx, [], [], [], out, inp, files, clockN⟩

end

section
attribute [-cobol_eval] Cobol.runFrom_succ
attribute [-stm_flow] Stm.runFrom_1

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 50000 in
/-- `8200-XREFFILE-OPEN`: `OPEN` of the cross-reference file through `CBSTM03B`. -/
stm_summary open_xref (env : Env) (hop : env.openError 4 .input = none) (n : Nat) (mem : Mem)
    (hm : mem.size = 178495) (idx : List (Nat × Int)) (out : List Event)
    (trs xrefs custs accts : List (List UInt8)) (f1 f2 f3 : FileSt) (clockN : Nat) :
    Sem.runFrom Stm env (n + 10) 16 ⟨mem, idx, [], [], [], out,
      [(3, trs), (4, xrefs), (5, custs), (6, accts)], [(1, f1), (2, f2), (3, f3)], clockN⟩
  using [hop]

end

section
attribute [-cobol_eval] Cobol.runFrom_succ
attribute [-stm_flow] Stm.runFrom_1

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 50000 in
/-- `8300-CUSTFILE-OPEN`: `OPEN` of the customer file through `CBSTM03B`. -/
stm_summary open_cust (env : Env) (hop : env.openError 5 .input = none) (n : Nat) (mem : Mem)
    (hm : mem.size = 178495) (idx : List (Nat × Int)) (out : List Event)
    (trs xrefs custs accts : List (List UInt8)) (f1 f2 f3 f4 : FileSt) (clockN : Nat) :
    Sem.runFrom Stm env (n + 10) 17 ⟨mem, idx, [], [], [], out,
      [(3, trs), (4, xrefs), (5, custs), (6, accts)], [(1, f1), (2, f2), (3, f3), (4, f4)], clockN⟩
  using [hop]

end

section
attribute [-cobol_eval] Cobol.runFrom_succ
attribute [-stm_flow] Stm.runFrom_2

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 50000 in
/-- `8400-ACCTFILE-OPEN`: `OPEN` of the account file through `CBSTM03B`, then `GO TO
1000-MAINLINE`. -/
stm_summary open_acct (env : Env) (hop : env.openError 6 .input = none) (n : Nat) (mem : Mem)
    (hm : mem.size = 178495) (idx : List (Nat × Int)) (out : List Event)
    (trs xrefs custs accts : List (List UInt8)) (f1 f2 f3 f4 f5 : FileSt) (clockN : Nat) :
    Sem.runFrom Stm env (n + 10) 18 ⟨mem, idx, [], [], [], out,
      [(3, trs), (4, xrefs), (5, custs), (6, accts)], [(1, f1), (2, f2), (3, f3), (4, f4), (5, f5)],
      clockN⟩
  using [hop]

end

/-! ## Before and after the load -/

section
attribute [-cobol_eval] Cobol.runFrom_succ
attribute [-stm_flow] Stm.runFrom_0 Stm.runFrom_1 Stm.runFrom_14 Stm.runFrom_15 Stm.runFrom_19

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 50000 in
/-- From the initial state to `8500-READTRNX-READ`: the walk, `OPEN` of the two output files,
`INITIALIZE`, `OPEN` and first `READ` of the transaction file. -/
stm_summary pre_load_eq (env : Env) (hEnv : env.addrSpace = asp)
    (ho1 : env.openError 1 .output = none) (ho2 : env.openError 2 .output = none)
    (ho3 : env.openError 3 .input = none)
    (m0 : Mem) (hm0 : m0.size = 178495) (hpsa : m0.read 175623 4 = [0, 0, 0, 0])
    (xrefs custs accts : List (List UInt8)) (cur : List UInt8) (rest : List (List UInt8))
    (hcur : cur.length = 350) (n : Nat) :
    Sem.runFrom Stm env (n + 55) 0
      (Stm.initState m0 [(3, cur :: rest), (4, xrefs), (5, custs), (6, accts)])
  using [↓run0, ↓start_trnx, ↓open_trnx, ↓start_read, hEnv, ho1, ho2, ho3, walkMem_size,
    walkMem_read_lo, walkMem_read_hi, length_spTbl, length_zTrct]

end

section
attribute [-cobol_eval] Cobol.runFrom_succ
attribute [-stm_flow] Stm.runFrom_1 Stm.runFrom_14 Stm.runFrom_16 Stm.runFrom_17 Stm.runFrom_18
  Stm.runFrom_2

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 50000 in
/-- From `0000-START` after the load (`WS-FL-DD = 'XREFFILE'`) to `1000-MAINLINE`: `OPEN` of the
cross-reference, customer and account files. -/
stm_summary post_load_eq (env : Env) (ho4 : env.openError 4 .input = none)
    (ho5 : env.openError 5 .input = none) (ho6 : env.openError 6 .input = none)
    (mem : Mem) (hm : mem.size = 178495)
    (hfl : mem.read 1394 8 = [231, 217, 197, 198, 198, 201, 211, 197])
    (idx : List (Nat × Int)) (out : List Event) (trs xrefs custs accts : List (List UInt8))
    (f1 f2 f3 : FileSt) (clockN : Nat) (n : Nat) :
    Sem.runFrom Stm env (n + 40) 1 ⟨mem, idx, [], [], [], out,
      [(3, trs), (4, xrefs), (5, custs), (6, accts)], [(1, f1), (2, f2), (3, f3)], clockN⟩
  using [↓start_xref, ↓open_xref, ↓start_cust, ↓open_cust, ↓start_acct, ↓open_acct, ho4, ho5, ho6]

end

/-! ## The states before and after the load -/

/-- The records of a group are records of the file. -/
theorem mem_of_mem_grp (rs : List (List UInt8)) : ∀ g ∈ grp rs, ∀ r ∈ g, r ∈ rs := by
  induction rs using list_snoc_ind with
  | nil => simp [grp_nil]
  | snoc l a ih =>
    intro g hg r hr
    rw [grp_snoc] at hg
    unfold grpSnoc at hg
    split at hg
    · rename_i g0 hlast
      have hg0 : g0 ∈ grp l := List.mem_of_getLast? hlast
      split at hg
      · rcases List.mem_append.mp hg with h | h
        · exact List.mem_append_left _ (ih g (List.dropLast_subset _ h) r hr)
        · simp only [List.mem_singleton] at h
          subst h
          rcases List.mem_append.mp hr with h' | h'
          · exact List.mem_append_left _ (ih g0 hg0 r h')
          · simp only [List.mem_singleton] at h'
            subst h'
            simp
      · rcases List.mem_append.mp hg with h | h
        · exact List.mem_append_left _ (ih g h r hr)
        · simp only [List.mem_singleton] at h
          subst h
          simp only [List.mem_singleton] at hr
          subst hr
          simp
    · simp only [List.mem_singleton] at hg
      subst hg
      simp only [List.mem_singleton] at hr
      subst hr
      simp

/-- The constant texts of a storage that agrees with `m'` on `STATEMENT-LINES` and
`HTML-LINES`. -/
theorem ConstsOk_of_region {m m' : Mem} (h : m.read 2470 1895 = m'.read 2470 1895)
    (hc : ConstsOk m') : ConstsOk m := by
  simp only [ConstsOk] at hc ⊢
  obtain ⟨k01, k02, k03, k04, k05, k06, k07, k08, k09, k10, k11, k12, k13, k14, k15, k16, k17, k18,
    k19, k20, k21, k22, k23⟩ := hc
  exact ⟨(read_eq_of_region h (by omega) (by omega)).trans k01,
    (read_eq_of_region h (by omega) (by omega)).trans k02,
    (read_eq_of_region h (by omega) (by omega)).trans k03,
    (read_eq_of_region h (by omega) (by omega)).trans k04,
    (read_eq_of_region h (by omega) (by omega)).trans k05,
    (read_eq_of_region h (by omega) (by omega)).trans k06,
    (read_eq_of_region h (by omega) (by omega)).trans k07,
    (read_eq_of_region h (by omega) (by omega)).trans k08,
    (read_eq_of_region h (by omega) (by omega)).trans k09,
    (read_eq_of_region h (by omega) (by omega)).trans k10,
    (read_eq_of_region h (by omega) (by omega)).trans k11,
    (read_eq_of_region h (by omega) (by omega)).trans k12,
    (read_eq_of_region h (by omega) (by omega)).trans k13,
    (read_eq_of_region h (by omega) (by omega)).trans k14,
    (read_eq_of_region h (by omega) (by omega)).trans k15,
    (read_eq_of_region h (by omega) (by omega)).trans k16,
    (read_eq_of_region h (by omega) (by omega)).trans k17,
    (read_eq_of_region h (by omega) (by omega)).trans k18,
    (read_eq_of_region h (by omega) (by omega)).trans k19,
    (read_eq_of_region h (by omega) (by omega)).trans k20,
    (read_eq_of_region h (by omega) (by omega)).trans k21,
    (read_eq_of_region h (by omega) (by omega)).trans k22,
    (read_eq_of_region h (by omega) (by omega)).trans k23⟩

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 50000 in
/-- `pre_load_eq` with the load invariant of the state at `8500-READTRNX-READ` (first pass: no
group yet, the first record read) and what the rest of the run needs of it. -/
theorem pre_load (env : Env) (hEnv : env.addrSpace = asp)
    (ho1 : env.openError 1 .output = none) (ho2 : env.openError 2 .output = none)
    (ho3 : env.openError 3 .input = none)
    (m0 : Mem) (hm0 : m0.size = 178495) (hpsa : m0.read 175623 4 = [0, 0, 0, 0])
    (xrefs custs accts : List (List UInt8)) (cur : List UInt8) (rest : List (List UInt8))
    (hcur : cur.length = 350) (n : Nat) :
    ∃ S, Sem.runFrom Stm env (n + 55) 0
        (Stm.initState m0 [(3, cur :: rest), (4, xrefs), (5, custs), (6, accts)]) =
        Sem.runFrom Stm env (n + 41 + 9) 19 S ∧
      LoadInv S { mode := some .output } { mode := some .output } (cur :: rest) rest S ∧
      S.idx = [] ∧ S.slots = [] ∧ S.saves = [] ∧ S.active = [] ∧ S.out = walkDisplays ∧
      S.inp = [(3, cur :: rest), (4, xrefs), (5, custs), (6, accts)] ∧ S.clockN = 0 ∧
      ConstsOk S.mem ∧ S.mem.read 1429 1 = [213] := by
  refine ⟨_, pre_load_eq env hEnv ho1 ho2 ho3 m0 hm0 hpsa xrefs custs accts cur rest hcur n, ?_⟩
  refine ⟨⟨[], cur, by simp, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, rfl, rfl⟩, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩, rfl, rfl, rfl, rfl, ?_, rfl, rfl, ?_, ?_⟩
  · stm_auto [walkMem_size, length_spTbl, length_zTrct]
  · stm_auto [walkMem_size, walkMem_read_lo, length_spTbl, length_zTrct]
  · simp only [List.getLastD_nil, tCard]
    stm_auto [walkMem_size, walkMem_read_lo, length_spTbl, length_zTrct]
  · simp only [grp_nil, List.length_nil]
    (stm_auto [walkMem_size, walkMem_read_lo, length_spTbl, length_zTrct]) <;> rfl
  · simp only [grp_nil, List.getLastD_nil, List.length_nil]
    (stm_auto [walkMem_size, walkMem_read_lo, length_spTbl, length_zTrct]) <;> rfl
  · intro k h1 h2
    simp only [grp_nil, List.length_nil] at h2
    omega
  · intro k h1 h2
    simp only [grp_nil, List.length_nil] at h2
    omega
  · simp
  · rfl
  · simp only [ConstsOk]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_⟩ <;> stm_auto [walkMem_size, walkMem_read_lo, length_spTbl, length_zTrct]
  · stm_auto [walkMem_size, walkMem_read_lo, length_spTbl, length_zTrct]

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 50000 in
/-- `post_load_eq` with the invariant of `1000-MAINLINE` (nothing read yet) for the state it
reaches: the table region unchanged, the constant texts, `END-OF-FILE = 'N'`, the six files
open. -/
theorem post_load (env : Env) (ho4 : env.openError 4 .input = none)
    (ho5 : env.openError 5 .input = none) (ho6 : env.openError 6 .input = none)
    (mem : Mem) (hm : mem.size = 178495)
    (hfl : mem.read 1394 8 = [231, 217, 197, 198, 198, 201, 211, 197])
    (idx : List (Nat × Int)) (out : List Event) (trs xrefs custs accts : List (List UInt8))
    (f3 : FileSt) (clockN : Nat) (n : Nat) (gs : List (List (List UInt8)))
    (hcr : mem.read 1380 2 = encodeNum {} { digits := 4, signed := true, usage := .binary }
      (gs.length : Int))
    (hc : ConstsOk mem) (heof : mem.read 1429 1 = [213]) :
    ∃ S2, Sem.runFrom Stm env (n + 40) 1 ⟨mem, idx, [], [], [], out,
        [(3, trs), (4, xrefs), (5, custs), (6, accts)],
        [(1, { mode := some .output }), (2, { mode := some .output }), (3, f3)], clockN⟩ =
        Sem.runFrom Stm env (n + 22 + 9) 2 S2 ∧
      S2.mem.read 4365 171258 = mem.read 4365 171258 ∧
      MInv gs xrefs custs accts S2.mem idx [(3, trs), (4, xrefs), (5, custs), (6, accts)] clockN out
        [] [] f3 (xrefs.map some ++ [none]) S2 := by
  refine ⟨_, post_load_eq env ho4 ho5 ho6 mem hm hfl idx out trs xrefs custs accts _ _ f3 clockN n,
    ?_, ?_⟩
  · stm_auto
  · simp only [ConstsOk] at hc
    obtain ⟨k01, k02, k03, k04, k05, k06, k07, k08, k09, k10, k11, k12, k13, k14, k15, k16, k17, k18,
      k19, k20, k21, k22, k23⟩ := hc
    refine ⟨[], xrefs, by simp, rfl, rfl, rfl, rfl, rfl, rfl, by simp, by stm_auto, rfl, by stm_auto,
      ?_, 0, false, none, 0, false, none, none, Or.inl ⟨by simp, by stm_auto, by simp⟩⟩
    simp only [ConstsOk]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_⟩ <;> stm_auto

/-! ## The whole run -/

/-- A run that stops is the program's result. -/
theorem run_of_stop {P : Program} {env : Env} {F : Nat} {st : State} {k : StopKind}
    (h : (Sem.runFrom P env F 0 st).1 = .stop k) : P.run env F st = Sem.runFrom P env F 0 st := by
  unfold Program.run
  revert h
  cases Sem.runFrom P env F 0 st with
  | mk sig s => cases sig <;> intro h <;> first | rfl | cases h

set_option maxHeartbeats 4000000 in
/-- From the initial state to `1000-MAINLINE` (paragraph 2): the state there satisfies the loop
invariant with every cross-reference record still to read, the table holds the groups of the
transaction file. -/
theorem to_mainline (env : Env) (hEnv : env.addrSpace = asp)
    (hOpen : ∀ f md, env.openError f md = none)
    (m0 : Mem) (hm0 : m0.size = 178495) (hpsa : m0.read 175623 4 = [0, 0, 0, 0])
    (trs xrefs custs accts : List (List UInt8))
    (htl : ∀ r ∈ trs, r.length = 350 ∧ AmtOk r) (hne : trs ≠ [])
    (hG : (grp trs).length ≤ 50) (hT : ∀ g ∈ grp trs, g.length ≤ 10)
    (F : Nat) (hF : trs.length + xrefs.length + 100 ≤ F) :
    ∃ m S2, Sem.runFrom Stm env F 0
        (Stm.initState m0 [(3, trs), (4, xrefs), (5, custs), (6, accts)]) =
        Sem.runFrom Stm env (m + 11) 2 S2 ∧ xrefs.length + 1 < m + 10 ∧
      P4Static (m + 8) (grp trs) S2.mem ∧
      MInv (grp trs) xrefs custs accts S2.mem [] [(3, trs), (4, xrefs), (5, custs), (6, accts)] 0
        walkDisplays [] [] { mode := some .input, recs := trs, pos := trs.length, eof := true }
        (xrefs.map some ++ [none]) S2 := by
  obtain ⟨cur, rest, rfl⟩ : ∃ cur rest, trs = cur :: rest := by
    cases trs with
    | nil => exact absurd rfl hne
    | cons c r => exact ⟨c, r, rfl⟩
  have hcur : cur.length = 350 := (htl cur (by simp)).1
  obtain ⟨m, rfl, hm⟩ : ∃ m, F = m + rest.length + 55 ∧ xrefs.length + 40 ≤ m :=
    ⟨F - 55 - rest.length, by simp at hF; omega, by simp at hF; omega⟩
  obtain ⟨S, hS, hinv, hidx, hsl, hsv, hac, hout, hinp, hclk, hcS, heS⟩ :=
    pre_load env hEnv (hOpen 1 _) (hOpen 2 _) (hOpen 3 _) m0 hm0 hpsa xrefs custs accts cur rest
      hcur (m + rest.length)
  obtain ⟨st', h3, hP⟩ := phase3 env S _ _ (cur :: rest) (fun r hr => (htl r hr).1) hG hT hne rest
    S hinv (m + 8)
  obtain ⟨⟨hidx', hsl', hsv', hac', hout', hinp', hclk', hsz', hreg', heof'⟩, hcr', hT', hR', hfl',
    hfiles'⟩ := hP
  obtain ⟨mem', idx', slots', saves', active', out', inp', files', clockN'⟩ := st'
  dsimp only at hidx' hsl' hsv' hac' hout' hinp' hclk' hsz' hreg' heof' hcr' hT' hR' hfl' hfiles'
  rw [hidx] at hidx'
  rw [hsl] at hsl'
  rw [hsv] at hsv'
  rw [hac] at hac'
  rw [hout] at hout'
  rw [hinp] at hinp'
  rw [hclk] at hclk'
  subst hidx' hsl' hsv' hac' hout' hinp' hclk' hfiles'
  obtain ⟨S2, hS2, hreg2, hMI⟩ := post_load env (hOpen 4 _) (hOpen 5 _) (hOpen 6 _) mem' hsz' hfl'
    [] walkDisplays (cur :: rest) xrefs custs accts _ 0 (m + 8) (grp (cur :: rest)) hcr'
    (ConstsOk_of_region hreg' hcS) (heof'.trans heS)
  refine ⟨m + 28, S2, ?_, by omega, ⟨by omega, hG, hT, fun g hg r hr => htl r (mem_of_mem_grp _ g hg r hr),
    TableOk_of_region hT' hG hT hreg2, TrctOk_of_region hR' (by omega) hreg2⟩, hMI⟩
  rw [hS, show m + rest.length + 41 + 9 = m + 8 + 41 + rest.length + 1 by omega, h3, hS2,
    show m + 8 + 22 + 9 = m + 28 + 11 by omega]

set_option maxHeartbeats 4000000 in
/-- **`CBSTM03AB`, every input.**  On the constructed address space (`hEnv`, `PSAPTR` = 0), with
the files opening normally, a transaction file of 350-byte records with numeric amounts, at most
50 cards (consecutive groups `grp trs`) of at most 10 transactions each, and cross-reference
records whose customer and account are found with valid fields (`XOk`), the program ends with
`GOBACK`, its output (newest first) being the statement events of every cross-reference record
(`evsOf`) after the 11 walk `DISPLAY`s, `STMT-FILE` and `HTML-FILE` holding the records
`stmtOf` / `htmlOf` of every cross-reference record, all files closed. -/
theorem stm_run (env : Env) (hEnv : env.addrSpace = asp)
    (hOpen : ∀ f md, env.openError f md = none)
    (m0 : Mem) (hm0 : m0.size = 178495) (hpsa : m0.read 175623 4 = [0, 0, 0, 0])
    (trs xrefs custs accts : List (List UInt8))
    (htl : ∀ r ∈ trs, r.length = 350 ∧ AmtOk r) (hne : trs ≠ [])
    (hG : (grp trs).length ≤ 50) (hT : ∀ g ∈ grp trs, g.length ≤ 10)
    (hx : ∀ x ∈ xrefs, XOk custs accts x)
    (F : Nat) (hF : trs.length + xrefs.length + 100 ≤ F) :
    StopAnd (MainPost (grp trs) xrefs custs accts walkDisplays [] []
        { mode := some .input, recs := trs, pos := trs.length, eof := true })
      (Stm.run env F (Stm.initState m0 [(3, trs), (4, xrefs), (5, custs), (6, accts)])) := by
  obtain ⟨m, S2, hrun, hlen, hS4, hMI⟩ :=
    to_mainline env hEnv hOpen m0 hm0 hpsa trs xrefs custs accts htl hne hG hT F hF
  have hML := mainline_ok env m (grp trs) S2.mem hS4 xrefs custs accts hx hlen [] _ 0 walkDisplays
    [] [] _ rfl S2 hMI
  rw [run_of_stop (k := .goback) (by rw [hrun]; exact hML.1), hrun]
  exact hML

end Cobol.StmCore
