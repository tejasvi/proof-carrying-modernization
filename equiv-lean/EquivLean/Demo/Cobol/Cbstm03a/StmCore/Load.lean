/-
# Phase 3 of `CBSTM03AB`: the transaction table load

`8500-READTRNX-READ` (paragraph 19) is a `GO TO` loop: each pass stores the record in
`TRNX-RECORD` in `WS-TRNX-TABLE` and reads the next one through `CBSTM03B`, until the end of
the file (`GO TO 8599-EXIT`, paragraph 20).  `LoadInv` is the loop invariant, indexed by the
records not read yet: the records `done` before the current one `cur` are in the table as the
groups `grp done` (`TableOk`: card and transactions of every entry; `TrctOk`: the counts of the
entries before the last one, whose count is in `TR-CNT`), `CR-CNT` / `TR-CNT` count the groups
and the last group's transactions, `WS-SAVE-CARD` holds the card of the last record.
`load_loop` replaces the whole loop by its result (`runFrom_goto_loop`): at `8599-EXIT` the
table holds the groups of the whole file (`LoadDone`).
-/
import EquivLean.Demo.Cobol.Cbstm03a.StmCore.LoadPass
import EquivLean.Demo.Cobol.Cbstm03a.StmCore.Model
import EquivLean.Demo.Cobol.Cbstm03a.Stm.GotoLoop

open Cobol Cobol.Stm

namespace Cobol.StmCore

/-- Table entries `1 … gs.length` (`WS-CARD-NUM`, and `WS-TRAN-NUM` / `WS-TRAN-REST` of each
transaction of the entry). -/
def TableOk (m : Mem) (gs : List (List (List UInt8))) : Prop :=
  ∀ k, 1 ≤ k → k ≤ gs.length →
    m.read (4365 + (k - 1) * 3356) 16 = gCard (gs.getD (k - 1) []) ∧
    ∀ j, 1 ≤ j → j ≤ (gs.getD (k - 1) []).length →
      m.read (4381 + (k - 1) * 3356 + (j - 1) * 334) 16 = tId ((gs.getD (k - 1) []).getD (j - 1) []) ∧
      m.read (4397 + (k - 1) * 3356 + (j - 1) * 334) 318 = tRest ((gs.getD (k - 1) []).getD (j - 1) [])

/-- `WS-TRCT (1 … n)`: the transaction counts of the first `n` entries. -/
def TrctOk (m : Mem) (gs : List (List (List UInt8))) (n : Nat) : Prop :=
  ∀ k, 1 ≤ k → k ≤ n →
    m.read (175521 + (k - 1) * 2) 2 =
      encodeNum {} { digits := 4, signed := true, usage := .binary } ((gs.getD (k - 1) []).length : Int)

/-- The parts of the state the load does not change: everything but storage and files, the
storage size, `STATEMENT-LINES` and `HTML-LINES` (offsets 2470 … 4364), `END-OF-FILE` (1429). -/
def LoadFrame (st0 st : State) : Prop :=
  st.idx = st0.idx ∧ st.slots = st0.slots ∧ st.saves = st0.saves ∧ st.active = st0.active ∧
    st.out = st0.out ∧ st.inp = st0.inp ∧ st.clockN = st0.clockN ∧ st.mem.size = 178495 ∧
    st.mem.read 2470 1895 = st0.mem.read 2470 1895 ∧ st.mem.read 1429 1 = st0.mem.read 1429 1

/-- Loop invariant of `8500-READTRNX-READ`, indexed by the records not read yet. -/
def LoadInv (st0 : State) (f1 f2 : FileSt) (trs : List (List UInt8)) (rest : List (List UInt8))
    (st : State) : Prop :=
  ∃ done cur, trs = done ++ cur :: rest ∧ LoadFrame st0 st ∧
    st.mem.read 180 350 = cur ∧
    st.mem.read 1413 16 = tCard (done.getLastD cur) ∧
    st.mem.read 1380 2 = encodeNum {} { digits := 4, signed := true, usage := .binary }
      ((max 1 (grp done).length : Nat) : Int) ∧
    st.mem.read 1382 2 = encodeNum {} { digits := 4, signed := true, usage := .binary }
      (((grp done).getLastD []).length : Int) ∧
    TableOk st.mem (grp done) ∧ TrctOk st.mem (grp done) ((grp done).length - 1) ∧
    st.files = [(1, f1), (2, f2), (3,
      { mode := some .input, recs := trs, pos := done.length + 1, eof := false,
        cur := some done.length })]

/-- At `8599-EXIT`: the groups of the whole file in the table, the last count in `TR-CNT`. -/
def LoadDone (st0 : State) (f1 f2 : FileSt) (trs : List (List UInt8)) (st : State) : Prop :=
  LoadFrame st0 st ∧
    st.mem.read 1380 2 = encodeNum {} { digits := 4, signed := true, usage := .binary }
      ((grp trs).length : Int) ∧
    st.mem.read 1382 2 = encodeNum {} { digits := 4, signed := true, usage := .binary }
      (((grp trs).getLastD []).length : Int) ∧
    TableOk st.mem (grp trs) ∧ TrctOk st.mem (grp trs) ((grp trs).length - 1) ∧
    st.files = [(1, f1), (2, f2), (3,
      { mode := some .input, recs := trs, pos := trs.length, eof := true })]

/-- A pass result: `GO TO k` and the invariant `I` of the new state. -/
def PassOk (k : Nat) (I : State → Prop) (r : Sem.Res) : Prop := r.1 = .goto k ∧ I r.2

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 20000 in
/-- The first pass (no record stored yet): transaction 1 of card 1. -/
theorem step_first (env : Env) (st0 : State) (f1 f2 : FileSt) (trs : List (List UInt8))
    (htl : ∀ r ∈ trs, r.length = 350) (x : List UInt8) (xs : List (List UInt8)) (m' : Nat)
    (cur : List UInt8) (htrs : trs = [] ++ cur :: x :: xs)
    (mem : Mem) (hfr : LoadFrame st0 ⟨mem, st0.idx, st0.slots, st0.saves, st0.active, st0.out,
      st0.inp, [(1, f1), (2, f2), (3,
        { mode := some .input, recs := trs, pos := 1, eof := false, cur := some 0 })],
      st0.clockN⟩)
    (hcur : mem.read 180 350 = cur) (hsave : mem.read 1413 16 = tCard cur)
    (hcr : mem.read 1380 2 = encodeNum {} { digits := 4, signed := true, usage := .binary } 1)
    (htr : mem.read 1382 2 = encodeNum {} { digits := 4, signed := true, usage := .binary } 0) :
    PassOk 19 (LoadInv st0 f1 f2 trs xs) (Sem.execSentences Stm env (Sem.runFrom Stm env (m' + 40))
      (m' + 40) Stm.«8500-READTRNX-READ».body ⟨mem, st0.idx, st0.slots, st0.saves, st0.active,
      st0.out, st0.inp, [(1, f1), (2, f2), (3,
        { mode := some .input, recs := trs, pos := 1, eof := false, cur := some 0 })],
      st0.clockN⟩) := by
  obtain ⟨-, -, -, -, -, -, -, hsz, hR, hE⟩ := hfr
  dsimp only at hsz hR hE
  have hcl : cur.length = 350 := htl cur (by simp [htrs])
  have hxl : x.length = 350 := htl x (by simp [htrs])
  have hy : trs[1]? = some x := by simp [htrs]
  rw [PassOk, pass_same env m' mem hsz st0.idx st0.slots st0.saves st0.active st0.out
    st0.inp st0.clockN f1 f2 trs 1 (some 0) cur hcl hcur (by rw [hsave, tCard]) 1 0
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hcr htr x hy hxl]
  refine ⟨rfl, [cur], x, by simp [htrs], ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  · simp [hsz]
  · stm_auto
  · stm_auto
  · stm_auto
  · (stm_auto [tCard]) <;> rfl
  · rw [show grp [cur] = [[cur]] from rfl]; (stm_auto) <;> rfl
  · rw [show grp [cur] = [[cur]] from rfl]; (stm_auto) <;> rfl
  · intro k hk1 hk2
    have hg : grp [cur] = [[cur]] := rfl
    rw [hg] at hk2 ⊢
    obtain rfl : k = 1 := by simp at hk2; omega
    refine ⟨?_, fun j hj1 hj2 => ?_⟩
    · (stm_auto [gCard, tCard]) <;> rfl
    · obtain rfl : j = 1 := by simp at hj2; omega
      exact ⟨by stm_auto [tId], by stm_auto [tRest]⟩
  · intro k hk1 hk2
    simp [grp, grpSnoc] at hk2
    omega
  · rfl

theorem toNat_natCast_add_two (n : Nat) : ((n : Int) + 1 + 1).toNat = n + 1 + 1 := rfl

theorem getLastD_single {α : Type _} (a d : α) : [a].getLastD d = a := rfl

/-- `stm_auto` with the cast and model rewrites of the load proofs. -/
macro "load_auto" : tactic => `(tactic| stm_auto [Int.toNat_natCast, Int.toNat_natCast_add_one,
  toNat_natCast_add_two, getLastD_single,
  Int.natCast_add, Int.natCast_one, Nat.add_sub_cancel, gCard, tCard, tId, tRest, getLastD_snoc])

set_option maxHeartbeats 80000000 in
set_option maxRecDepth 20000 in
/-- A pass with the card of the current group: one more transaction of it. -/
theorem step_same (env : Env) (st0 : State) (f1 f2 : FileSt) (trs : List (List UInt8))
    (htl : ∀ r ∈ trs, r.length = 350) (hG : (grp trs).length ≤ 50)
    (hT : ∀ g ∈ grp trs, g.length ≤ 10) (x : List UInt8) (xs : List (List UInt8)) (m' : Nat)
    (done : List (List UInt8)) (cur : List UInt8) (htrs : trs = done ++ cur :: x :: xs)
    (gs0 : List (List (List UInt8))) (g : List (List UInt8)) (hgs : grp done = gs0 ++ [g])
    (hsame : gCard g = tCard cur)
    (mem : Mem) (hfr : LoadFrame st0 ⟨mem, st0.idx, st0.slots, st0.saves, st0.active, st0.out,
      st0.inp, [(1, f1), (2, f2), (3,
        { mode := some .input, recs := trs, pos := done.length + 1, eof := false,
          cur := some done.length })],
      st0.clockN⟩)
    (hcur : mem.read 180 350 = cur) (hsave : mem.read 1413 16 = gCard g)
    (hcr : mem.read 1380 2 = encodeNum {} { digits := 4, signed := true, usage := .binary }
      ((gs0.length + 1 : Nat) : Int))
    (htr : mem.read 1382 2 = encodeNum {} { digits := 4, signed := true, usage := .binary }
      (g.length : Int))
    (htab : TableOk mem (gs0 ++ [g])) (htrct : TrctOk mem (gs0 ++ [g]) gs0.length) :
    PassOk 19 (LoadInv st0 f1 f2 trs xs) (Sem.execSentences Stm env (Sem.runFrom Stm env (m' + 40))
      (m' + 40) Stm.«8500-READTRNX-READ».body ⟨mem, st0.idx, st0.slots, st0.saves, st0.active,
      st0.out, st0.inp, [(1, f1), (2, f2), (3,
        { mode := some .input, recs := trs, pos := done.length + 1, eof := false,
          cur := some done.length })],
      st0.clockN⟩) := by
  obtain ⟨-, -, -, -, -, -, -, hsz, hR, hE⟩ := hfr
  dsimp only at hsz hR hE
  have hcl : cur.length = 350 := htl cur (by simp [htrs])
  have hxl : x.length = 350 := htl x (by simp [htrs])
  have hy : trs[done.length + 1]? = some x := by
    rw [htrs, List.getElem?_append_right (by omega)]; simp
  have hgs' := grp_snoc_same done cur gs0 g hgs hsame
  have htrs' : trs = (done ++ [cur]) ++ x :: xs := by simp [htrs]
  obtain ⟨hb1, hb2⟩ := grp_bounds (done ++ [cur]) (x :: xs) (by rw [← htrs']; exact hG)
    (by rw [← htrs']; exact hT)
  rw [hgs'] at hb1 hb2
  have hgl : g.length + 1 ≤ 10 := by
    have := hb2 gs0.length (by simp); rw [getD_snoc_eq] at this; simpa using this
  simp only [List.length_append, List.length_singleton] at hb1
  rw [PassOk, pass_same env m' mem hsz st0.idx st0.slots st0.saves st0.active st0.out
    st0.inp st0.clockN f1 f2 trs (done.length + 1) (some done.length) cur hcl hcur
    (by rw [hsave, hsame, tCard]) ((gs0.length + 1 : Nat) : Int) (g.length : Int)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hcr htr x hy hxl]
  refine ⟨rfl, done ++ [cur], x, by simp [htrs], ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [hsz]
  · load_auto
  · load_auto
  · load_auto
  · load_auto
  · rw [hgs']; simp only [List.length_append, List.length_singleton]
    load_auto
  · rw [hgs', getLastD_snoc]
    load_auto
  · rw [hgs']
    intro k hk1 hk2
    simp only [List.length_append, List.length_singleton] at hk2
    have e1 : gs0.length + 1 - 1 = gs0.length := by omega
    by_cases hk : k = gs0.length + 1
    · subst hk
      rw [e1, getD_snoc_eq]
      refine ⟨by load_auto, fun j hj1 hj2 => ?_⟩
      simp only [List.length_append, List.length_singleton] at hj2
      by_cases hj : j = g.length + 1
      · subst hj
        have e2 : g.length + 1 - 1 = g.length := by omega
        rw [e2, getD_snoc_eq]
        exact ⟨by load_auto, by load_auto⟩
      · have hj' : j - 1 < g.length := by omega
        rw [getD_snoc_lt _ _ _ _ hj']
        obtain ⟨-, ho⟩ := htab (gs0.length + 1) (by omega) (by simp)
        rw [e1, getD_snoc_eq] at ho
        obtain ⟨ho1, ho2⟩ := ho j hj1 (by omega)
        exact ⟨by load_auto, by load_auto⟩
    · have hk' : k - 1 < gs0.length := by omega
      rw [getD_snoc_lt _ _ _ _ hk']
      obtain ⟨ho1, ho2⟩ := htab k hk1 (by simp; omega)
      rw [getD_snoc_lt _ _ _ _ hk'] at ho1 ho2
      refine ⟨by load_auto, fun j hj1 hj2 => ?_⟩
      obtain ⟨ho3, ho4⟩ := ho2 j hj1 hj2
      have hjl : j ≤ 10 := by
        have := hb2 (k - 1) (by simp; omega)
        rw [getD_snoc_lt _ _ _ _ hk'] at this
        omega
      exact ⟨by load_auto, by load_auto⟩
  · rw [hgs']
    intro k hk1 hk2
    simp only [List.length_append, List.length_singleton, Nat.add_sub_cancel] at hk2
    have hk' : k - 1 < gs0.length := by omega
    rw [getD_snoc_lt _ _ _ _ hk']
    have ho := htrct k hk1 hk2
    rw [getD_snoc_lt _ _ _ _ hk'] at ho
    load_auto
  · simp

set_option maxHeartbeats 80000000 in
set_option maxRecDepth 20000 in
/-- A pass with another card: the current group's count is stored, a new group begins. -/
theorem step_diff (env : Env) (st0 : State) (f1 f2 : FileSt) (trs : List (List UInt8))
    (htl : ∀ r ∈ trs, r.length = 350) (hG : (grp trs).length ≤ 50)
    (hT : ∀ g ∈ grp trs, g.length ≤ 10) (x : List UInt8) (xs : List (List UInt8)) (m' : Nat)
    (done : List (List UInt8)) (cur : List UInt8) (htrs : trs = done ++ cur :: x :: xs)
    (gs0 : List (List (List UInt8))) (g : List (List UInt8)) (hgs : grp done = gs0 ++ [g])
    (hdiff : gCard g ≠ tCard cur)
    (mem : Mem) (hfr : LoadFrame st0 ⟨mem, st0.idx, st0.slots, st0.saves, st0.active, st0.out,
      st0.inp, [(1, f1), (2, f2), (3,
        { mode := some .input, recs := trs, pos := done.length + 1, eof := false,
          cur := some done.length })],
      st0.clockN⟩)
    (hcur : mem.read 180 350 = cur) (hsave : mem.read 1413 16 = gCard g)
    (hcr : mem.read 1380 2 = encodeNum {} { digits := 4, signed := true, usage := .binary }
      ((gs0.length + 1 : Nat) : Int))
    (htr : mem.read 1382 2 = encodeNum {} { digits := 4, signed := true, usage := .binary }
      (g.length : Int))
    (htab : TableOk mem (gs0 ++ [g])) (htrct : TrctOk mem (gs0 ++ [g]) gs0.length) :
    PassOk 19 (LoadInv st0 f1 f2 trs xs) (Sem.execSentences Stm env (Sem.runFrom Stm env (m' + 40))
      (m' + 40) Stm.«8500-READTRNX-READ».body ⟨mem, st0.idx, st0.slots, st0.saves, st0.active,
      st0.out, st0.inp, [(1, f1), (2, f2), (3,
        { mode := some .input, recs := trs, pos := done.length + 1, eof := false,
          cur := some done.length })],
      st0.clockN⟩) := by
  obtain ⟨-, -, -, -, -, -, -, hsz, hR, hE⟩ := hfr
  dsimp only at hsz hR hE
  have hcl : cur.length = 350 := htl cur (by simp [htrs])
  have hxl : x.length = 350 := htl x (by simp [htrs])
  have hy : trs[done.length + 1]? = some x := by
    rw [htrs, List.getElem?_append_right (by omega)]; simp
  have hgs' := grp_snoc_diff done cur gs0 g hgs hdiff
  have htrs' : trs = (done ++ [cur]) ++ x :: xs := by simp [htrs]
  obtain ⟨hb1, hb2⟩ := grp_bounds (done ++ [cur]) (x :: xs) (by rw [← htrs']; exact hG)
    (by rw [← htrs']; exact hT)
  rw [hgs'] at hb1 hb2
  have hgl : g.length ≤ 10 := by
    have := hb2 gs0.length (by simp)
    rw [getD_snoc_lt _ _ _ _ (by simp), getD_snoc_eq] at this; exact this
  simp only [List.length_append, List.length_singleton] at hb1
  have hsl : (gCard g).length = 16 := by rw [← hsave]; simp
  have hne : gCard g ≠ cur.take 16 := by simpa [tCard] using hdiff
  rw [PassOk, pass_diff env m' mem hsz st0.idx st0.slots st0.saves st0.active st0.out
    st0.inp st0.clockN f1 f2 trs (done.length + 1) (some done.length) cur hcl hcur
    (gCard g) hsl hsave hne ((gs0.length + 1 : Nat) : Int) (g.length : Int)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hcr htr x hy hxl]
  refine ⟨rfl, done ++ [cur], x, by simp [htrs], ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [hsz]
  · load_auto
  · load_auto
  · load_auto
  · load_auto
  · rw [hgs']; simp only [List.length_append, List.length_singleton]
    load_auto
  · rw [hgs', getLastD_snoc]
    load_auto
  · rw [hgs']
    intro k hk1 hk2
    simp only [List.length_append, List.length_singleton] at hk2
    by_cases hk : k = gs0.length + 1 + 1
    · subst hk
      have e1 : gs0.length + 1 + 1 - 1 = (gs0 ++ [g]).length := by simp
      rw [e1, getD_snoc_eq]
      refine ⟨by load_auto, fun j hj1 hj2 => ?_⟩
      simp only [List.length_singleton] at hj2
      obtain rfl : j = 1 := by omega
      exact ⟨by load_auto, by load_auto⟩
    · have hk' : k - 1 < (gs0 ++ [g]).length := by simp; omega
      rw [getD_snoc_lt _ _ _ _ hk']
      obtain ⟨ho1, ho2⟩ := htab k hk1 (by simp; omega)
      refine ⟨by load_auto, fun j hj1 hj2 => ?_⟩
      obtain ⟨ho3, ho4⟩ := ho2 j hj1 hj2
      have hjl : j ≤ 10 := by
        have := hb2 (k - 1) (by simp; omega)
        rw [getD_snoc_lt _ _ _ _ hk'] at this
        omega
      exact ⟨by load_auto, by load_auto⟩
  · rw [hgs']
    intro k hk1 hk2
    simp only [List.length_append, List.length_singleton, Nat.add_sub_cancel] at hk2
    have hk' : k - 1 < (gs0 ++ [g]).length := by simp; omega
    rw [getD_snoc_lt _ _ _ _ hk']
    by_cases hk : k = gs0.length + 1
    · subst hk
      have e1 : gs0.length + 1 - 1 = gs0.length := by omega
      rw [e1, getD_snoc_eq]
      load_auto
    · have hk'' : k - 1 < gs0.length := by omega
      have ho := htrct k hk1 (by omega)
      rw [getD_snoc_lt _ _ _ _ hk''] at ho ⊢
      load_auto
  · simp

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 20000 in
/-- The last pass of a one-record file. -/
theorem last_first (env : Env) (st0 : State) (f1 f2 : FileSt) (trs : List (List UInt8))
    (htl : ∀ r ∈ trs, r.length = 350) (m' : Nat)
    (cur : List UInt8) (htrs : trs = [] ++ cur :: [])
    (mem : Mem) (hfr : LoadFrame st0 ⟨mem, st0.idx, st0.slots, st0.saves, st0.active, st0.out,
      st0.inp, [(1, f1), (2, f2), (3,
        { mode := some .input, recs := trs, pos := 1, eof := false, cur := some 0 })],
      st0.clockN⟩)
    (hcur : mem.read 180 350 = cur) (hsave : mem.read 1413 16 = tCard cur)
    (hcr : mem.read 1380 2 = encodeNum {} { digits := 4, signed := true, usage := .binary } 1)
    (htr : mem.read 1382 2 = encodeNum {} { digits := 4, signed := true, usage := .binary } 0) :
    PassOk 20 (LoadDone st0 f1 f2 trs) (Sem.execSentences Stm env (Sem.runFrom Stm env (m' + 40))
      (m' + 40) Stm.«8500-READTRNX-READ».body ⟨mem, st0.idx, st0.slots, st0.saves, st0.active,
      st0.out, st0.inp, [(1, f1), (2, f2), (3,
        { mode := some .input, recs := trs, pos := 1, eof := false, cur := some 0 })],
      st0.clockN⟩) := by
  obtain ⟨-, -, -, -, -, -, -, hsz, hR, hE⟩ := hfr
  dsimp only at hsz hR hE
  have hcl : cur.length = 350 := htl cur (by simp [htrs])
  have hy : trs[1]? = none := by simp [htrs]
  have hg : grp trs = [[cur]] := by rw [htrs]; rfl
  rw [PassOk, pass_same_eof env m' mem hsz st0.idx st0.slots st0.saves st0.active st0.out
    st0.inp st0.clockN f1 f2 trs 1 (some 0) cur hcl hcur (by rw [hsave, tCard]) 1 0
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hcr htr hy]
  refine ⟨rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · simp [hsz]
  · load_auto
  · load_auto
  · rw [hg]; (load_auto) <;> rfl
  · rw [hg]; (load_auto) <;> rfl
  · intro k hk1 hk2
    rw [hg] at hk2 ⊢
    obtain rfl : k = 1 := by simp at hk2; omega
    refine ⟨by (load_auto) <;> rfl, fun j hj1 hj2 => ?_⟩
    obtain rfl : j = 1 := by simp at hj2; omega
    exact ⟨by load_auto, by load_auto⟩
  · intro k hk1 hk2
    rw [hg] at hk2
    simp at hk2
    omega
  · simp [htrs]

set_option maxHeartbeats 80000000 in
set_option maxRecDepth 20000 in
/-- The last pass, with the card of the current group. -/
theorem last_same (env : Env) (st0 : State) (f1 f2 : FileSt) (trs : List (List UInt8))
    (htl : ∀ r ∈ trs, r.length = 350) (hG : (grp trs).length ≤ 50)
    (hT : ∀ g ∈ grp trs, g.length ≤ 10) (m' : Nat)
    (done : List (List UInt8)) (cur : List UInt8) (htrs : trs = done ++ cur :: [])
    (gs0 : List (List (List UInt8))) (g : List (List UInt8)) (hgs : grp done = gs0 ++ [g])
    (hsame : gCard g = tCard cur)
    (mem : Mem) (hfr : LoadFrame st0 ⟨mem, st0.idx, st0.slots, st0.saves, st0.active, st0.out,
      st0.inp, [(1, f1), (2, f2), (3,
        { mode := some .input, recs := trs, pos := done.length + 1, eof := false,
          cur := some done.length })],
      st0.clockN⟩)
    (hcur : mem.read 180 350 = cur) (hsave : mem.read 1413 16 = gCard g)
    (hcr : mem.read 1380 2 = encodeNum {} { digits := 4, signed := true, usage := .binary }
      ((gs0.length + 1 : Nat) : Int))
    (htr : mem.read 1382 2 = encodeNum {} { digits := 4, signed := true, usage := .binary }
      (g.length : Int))
    (htab : TableOk mem (gs0 ++ [g])) (htrct : TrctOk mem (gs0 ++ [g]) gs0.length) :
    PassOk 20 (LoadDone st0 f1 f2 trs) (Sem.execSentences Stm env (Sem.runFrom Stm env (m' + 40))
      (m' + 40) Stm.«8500-READTRNX-READ».body ⟨mem, st0.idx, st0.slots, st0.saves, st0.active,
      st0.out, st0.inp, [(1, f1), (2, f2), (3,
        { mode := some .input, recs := trs, pos := done.length + 1, eof := false,
          cur := some done.length })],
      st0.clockN⟩) := by
  obtain ⟨-, -, -, -, -, -, -, hsz, hR, hE⟩ := hfr
  dsimp only at hsz hR hE
  have hcl : cur.length = 350 := htl cur (by simp [htrs])
  have hy : trs[done.length + 1]? = none := by simp [htrs]
  have hgs' : grp trs = gs0 ++ [g ++ [cur]] := by
    rw [htrs]; exact grp_snoc_same done cur gs0 g hgs hsame
  have hb1 := hG
  rw [hgs'] at hb1 hT
  have hgl : g.length + 1 ≤ 10 := by
    have := hT (g ++ [cur]) (by simp); simpa using this
  simp only [List.length_append, List.length_singleton] at hb1
  rw [PassOk, pass_same_eof env m' mem hsz st0.idx st0.slots st0.saves st0.active st0.out
    st0.inp st0.clockN f1 f2 trs (done.length + 1) (some done.length) cur hcl hcur
    (by rw [hsave, hsame, tCard]) ((gs0.length + 1 : Nat) : Int) (g.length : Int)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hcr htr hy]
  refine ⟨rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · simp [hsz]
  · load_auto
  · load_auto
  · rw [hgs']; simp only [List.length_append, List.length_singleton]
    load_auto
  · rw [hgs', getLastD_snoc]
    load_auto
  · rw [hgs']
    intro k hk1 hk2
    simp only [List.length_append, List.length_singleton] at hk2
    have e1 : gs0.length + 1 - 1 = gs0.length := by omega
    by_cases hk : k = gs0.length + 1
    · subst hk
      rw [e1, getD_snoc_eq]
      refine ⟨by load_auto, fun j hj1 hj2 => ?_⟩
      simp only [List.length_append, List.length_singleton] at hj2
      by_cases hj : j = g.length + 1
      · subst hj
        have e2 : g.length + 1 - 1 = g.length := by omega
        rw [e2, getD_snoc_eq]
        exact ⟨by load_auto, by load_auto⟩
      · have hj' : j - 1 < g.length := by omega
        rw [getD_snoc_lt _ _ _ _ hj']
        obtain ⟨-, ho⟩ := htab (gs0.length + 1) (by omega) (by simp)
        rw [e1, getD_snoc_eq] at ho
        obtain ⟨ho1, ho2⟩ := ho j hj1 (by omega)
        exact ⟨by load_auto, by load_auto⟩
    · have hk' : k - 1 < gs0.length := by omega
      rw [getD_snoc_lt _ _ _ _ hk']
      obtain ⟨ho1, ho2⟩ := htab k hk1 (by simp; omega)
      rw [getD_snoc_lt _ _ _ _ hk'] at ho1 ho2
      refine ⟨by load_auto, fun j hj1 hj2 => ?_⟩
      obtain ⟨ho3, ho4⟩ := ho2 j hj1 hj2
      have hjl : j ≤ 10 := by
        have := hT (gs0.getD (k - 1) []) (by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk', Option.getD_some]
          exact List.mem_append_left _ (List.getElem_mem _))
        omega
      exact ⟨by load_auto, by load_auto⟩
  · rw [hgs']
    intro k hk1 hk2
    simp only [List.length_append, List.length_singleton, Nat.add_sub_cancel] at hk2
    have hk' : k - 1 < gs0.length := by omega
    rw [getD_snoc_lt _ _ _ _ hk']
    have ho := htrct k hk1 hk2
    rw [getD_snoc_lt _ _ _ _ hk'] at ho
    load_auto
  · simp [htrs]

set_option maxHeartbeats 80000000 in
set_option maxRecDepth 20000 in
/-- The last pass, with another card. -/
theorem last_diff (env : Env) (st0 : State) (f1 f2 : FileSt) (trs : List (List UInt8))
    (htl : ∀ r ∈ trs, r.length = 350) (hG : (grp trs).length ≤ 50)
    (hT : ∀ g ∈ grp trs, g.length ≤ 10) (m' : Nat)
    (done : List (List UInt8)) (cur : List UInt8) (htrs : trs = done ++ cur :: [])
    (gs0 : List (List (List UInt8))) (g : List (List UInt8)) (hgs : grp done = gs0 ++ [g])
    (hdiff : gCard g ≠ tCard cur)
    (mem : Mem) (hfr : LoadFrame st0 ⟨mem, st0.idx, st0.slots, st0.saves, st0.active, st0.out,
      st0.inp, [(1, f1), (2, f2), (3,
        { mode := some .input, recs := trs, pos := done.length + 1, eof := false,
          cur := some done.length })],
      st0.clockN⟩)
    (hcur : mem.read 180 350 = cur) (hsave : mem.read 1413 16 = gCard g)
    (hcr : mem.read 1380 2 = encodeNum {} { digits := 4, signed := true, usage := .binary }
      ((gs0.length + 1 : Nat) : Int))
    (htr : mem.read 1382 2 = encodeNum {} { digits := 4, signed := true, usage := .binary }
      (g.length : Int))
    (htab : TableOk mem (gs0 ++ [g])) (htrct : TrctOk mem (gs0 ++ [g]) gs0.length) :
    PassOk 20 (LoadDone st0 f1 f2 trs) (Sem.execSentences Stm env (Sem.runFrom Stm env (m' + 40))
      (m' + 40) Stm.«8500-READTRNX-READ».body ⟨mem, st0.idx, st0.slots, st0.saves, st0.active,
      st0.out, st0.inp, [(1, f1), (2, f2), (3,
        { mode := some .input, recs := trs, pos := done.length + 1, eof := false,
          cur := some done.length })],
      st0.clockN⟩) := by
  obtain ⟨-, -, -, -, -, -, -, hsz, hR, hE⟩ := hfr
  dsimp only at hsz hR hE
  have hcl : cur.length = 350 := htl cur (by simp [htrs])
  have hy : trs[done.length + 1]? = none := by simp [htrs]
  have hgs' : grp trs = gs0 ++ [g] ++ [[cur]] := by
    rw [htrs]; exact grp_snoc_diff done cur gs0 g hgs hdiff
  have hb1 := hG
  rw [hgs'] at hb1 hT
  have hgl : g.length ≤ 10 := hT g (by simp)
  simp only [List.length_append, List.length_singleton] at hb1
  have hsl : (gCard g).length = 16 := by rw [← hsave]; simp
  have hne : gCard g ≠ cur.take 16 := by simpa [tCard] using hdiff
  rw [PassOk, pass_diff_eof env m' mem hsz st0.idx st0.slots st0.saves st0.active st0.out
    st0.inp st0.clockN f1 f2 trs (done.length + 1) (some done.length) cur hcl hcur
    (gCard g) hsl hsave hne ((gs0.length + 1 : Nat) : Int) (g.length : Int)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hcr htr hy]
  refine ⟨rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · simp [hsz]
  · load_auto
  · load_auto
  · rw [hgs']; simp only [List.length_append, List.length_singleton]
    load_auto
  · rw [hgs', getLastD_snoc]
    load_auto
  · rw [hgs']
    intro k hk1 hk2
    simp only [List.length_append, List.length_singleton] at hk2
    by_cases hk : k = gs0.length + 1 + 1
    · subst hk
      have e1 : gs0.length + 1 + 1 - 1 = (gs0 ++ [g]).length := by simp
      rw [e1, getD_snoc_eq]
      refine ⟨by load_auto, fun j hj1 hj2 => ?_⟩
      simp only [List.length_singleton] at hj2
      obtain rfl : j = 1 := by omega
      exact ⟨by load_auto, by load_auto⟩
    · have hk' : k - 1 < (gs0 ++ [g]).length := by simp; omega
      rw [getD_snoc_lt _ _ _ _ hk']
      obtain ⟨ho1, ho2⟩ := htab k hk1 (by simp; omega)
      refine ⟨by load_auto, fun j hj1 hj2 => ?_⟩
      obtain ⟨ho3, ho4⟩ := ho2 j hj1 hj2
      have hjl : j ≤ 10 := by
        have := hT ((gs0 ++ [g]).getD (k - 1) []) (by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk', Option.getD_some]
          exact List.mem_append_left _ (List.getElem_mem _))
        omega
      exact ⟨by load_auto, by load_auto⟩
  · rw [hgs']
    intro k hk1 hk2
    simp only [List.length_append, List.length_singleton, Nat.add_sub_cancel] at hk2
    have hk' : k - 1 < (gs0 ++ [g]).length := by simp; omega
    rw [getD_snoc_lt _ _ _ _ hk']
    by_cases hk : k = gs0.length + 1
    · subst hk
      have e1 : gs0.length + 1 - 1 = gs0.length := by omega
      rw [e1, getD_snoc_eq]
      load_auto
    · have hk'' : k - 1 < gs0.length := by omega
      have ho := htrct k hk1 (by omega)
      rw [getD_snoc_lt _ _ _ _ hk''] at ho ⊢
      load_auto
  · simp [htrs]

theorem getLastD_ne_nil {α : Type _} (l : List α) (h : l ≠ []) (a b : α) :
    l.getLastD a = l.getLastD b := by
  simp [List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast h]

/-- One pass from the invariant with records left: `GO TO 8500-READTRNX-READ`, invariant. -/
theorem load_hstep (env : Env) (st0 : State) (f1 f2 : FileSt) (trs : List (List UInt8))
    (htl : ∀ r ∈ trs, r.length = 350) (hG : (grp trs).length ≤ 50)
    (hT : ∀ g ∈ grp trs, g.length ≤ 10) :
    ∀ x xs st m, 40 ≤ m → LoadInv st0 f1 f2 trs (x :: xs) st →
      (Sem.execSentences Stm env (Sem.runFrom Stm env m) m Stm.«8500-READTRNX-READ».body st).1 =
        .goto 19 ∧
      LoadInv st0 f1 f2 trs xs
        (Sem.execSentences Stm env (Sem.runFrom Stm env m) m Stm.«8500-READTRNX-READ».body st).2 := by
  intro x xs st m hm hinv
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 40 := ⟨m - 40, by omega⟩
  obtain ⟨done, cur, htrs, hfr, hcur, hsave, hcr, htr, htab, htrct, hfiles⟩ := hinv
  obtain ⟨mem, idx, slots, saves, active, out, inp, files, clockN⟩ := st
  obtain ⟨hidx, hsl, hsv, hact, hout, hinp, hclk, -, -, -⟩ := id hfr
  dsimp only at hidx hsl hsv hact hout hinp hclk hfiles hcur hsave hcr htr htab htrct
  subst hidx hsl hsv hact hout hinp hclk hfiles
  show PassOk 19 _ _
  by_cases hd : done = []
  · subst hd
    exact step_first env st0 f1 f2 trs htl x xs m' cur htrs mem hfr hcur hsave
      (by rw [hcr]; rfl) (by rw [htr]; rfl)
  · obtain ⟨gs0, g, hgs, hgc⟩ := grp_snoc_form done hd
    rw [hgs] at hcr htr htab htrct
    have hsave' : mem.read 1413 16 = gCard g := by
      rw [hsave, hgc, getLastD_ne_nil done hd cur []]
    have hcr' : mem.read 1380 2 = encodeNum {} { digits := 4, signed := true, usage := .binary }
        ((gs0.length + 1 : Nat) : Int) := by
      rw [hcr]; congr 2; simp
    have htr' : mem.read 1382 2 = encodeNum {} { digits := 4, signed := true, usage := .binary }
        (g.length : Int) := by rw [htr, getLastD_snoc]
    have htrct' : TrctOk mem (gs0 ++ [g]) gs0.length := by simpa using htrct
    by_cases hs : gCard g = tCard cur
    · exact step_same env st0 f1 f2 trs htl hG hT x xs m' done cur htrs gs0 g hgs hs mem hfr hcur
        hsave' hcr' htr' htab htrct'
    · exact step_diff env st0 f1 f2 trs htl hG hT x xs m' done cur htrs gs0 g hgs hs mem hfr hcur
        hsave' hcr' htr' htab htrct'

/-- The pass from the invariant with no record left: `GO TO 8599-EXIT`, `LoadDone`. -/
theorem load_hlast (env : Env) (st0 : State) (f1 f2 : FileSt) (trs : List (List UInt8))
    (htl : ∀ r ∈ trs, r.length = 350) (hG : (grp trs).length ≤ 50)
    (hT : ∀ g ∈ grp trs, g.length ≤ 10) :
    ∀ st m, 40 ≤ m → LoadInv st0 f1 f2 trs [] st →
      (Sem.execSentences Stm env (Sem.runFrom Stm env m) m Stm.«8500-READTRNX-READ».body st).1 =
        .goto 20 ∧
      LoadDone st0 f1 f2 trs
        (Sem.execSentences Stm env (Sem.runFrom Stm env m) m Stm.«8500-READTRNX-READ».body st).2 := by
  intro st m hm hinv
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 40 := ⟨m - 40, by omega⟩
  obtain ⟨done, cur, htrs, hfr, hcur, hsave, hcr, htr, htab, htrct, hfiles⟩ := hinv
  obtain ⟨mem, idx, slots, saves, active, out, inp, files, clockN⟩ := st
  obtain ⟨hidx, hsl, hsv, hact, hout, hinp, hclk, -, -, -⟩ := id hfr
  dsimp only at hidx hsl hsv hact hout hinp hclk hfiles hcur hsave hcr htr htab htrct
  subst hidx hsl hsv hact hout hinp hclk hfiles
  show PassOk 20 _ _
  by_cases hd : done = []
  · subst hd
    exact last_first env st0 f1 f2 trs htl m' cur htrs mem hfr hcur hsave
      (by rw [hcr]; rfl) (by rw [htr]; rfl)
  · obtain ⟨gs0, g, hgs, hgc⟩ := grp_snoc_form done hd
    rw [hgs] at hcr htr htab htrct
    have hsave' : mem.read 1413 16 = gCard g := by
      rw [hsave, hgc, getLastD_ne_nil done hd cur []]
    have hcr' : mem.read 1380 2 = encodeNum {} { digits := 4, signed := true, usage := .binary }
        ((gs0.length + 1 : Nat) : Int) := by
      rw [hcr]; congr 2; simp
    have htr' : mem.read 1382 2 = encodeNum {} { digits := 4, signed := true, usage := .binary }
        (g.length : Int) := by rw [htr, getLastD_snoc]
    have htrct' : TrctOk mem (gs0 ++ [g]) gs0.length := by simpa using htrct
    by_cases hs : gCard g = tCard cur
    · exact last_same env st0 f1 f2 trs htl hG hT m' done cur htrs gs0 g hgs hs mem hfr hcur
        hsave' hcr' htr' htab htrct'
    · exact last_diff env st0 f1 f2 trs htl hG hT m' done cur htrs gs0 g hgs hs mem hfr hcur
        hsave' hcr' htr' htab htrct'

/-- **The table load loop.** From the invariant with records `rest` still to read, the `GO TO`
loop of `8500-READTRNX-READ` ends at `8599-EXIT` with the groups of the whole file in the
table. -/
theorem load_loop (env : Env) (st0 : State) (f1 f2 : FileSt) (trs : List (List UInt8))
    (htl : ∀ r ∈ trs, r.length = 350) (hG : (grp trs).length ≤ 50)
    (hT : ∀ g ∈ grp trs, g.length ≤ 10) (rest : List (List UInt8)) (st : State)
    (hinv : LoadInv st0 f1 f2 trs rest st) (m : Nat) :
    ∃ st', Sem.runFrom Stm env (m + 40 + rest.length + 1) 19 st = Sem.runFrom Stm env (m + 40) 20 st' ∧
      LoadDone st0 f1 f2 trs st' :=
  runFrom_goto_loop Stm.paras_19 40 (LoadInv st0 f1 f2 trs) (LoadDone st0 f1 f2 trs)
    (load_hstep env st0 f1 f2 trs htl hG hT) (load_hlast env st0 f1 f2 trs htl hG hT)
    rest st (m + 40) (by omega) hinv

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 20000 in
/-- `8599-EXIT`: the last count to `WS-TRCT (CR-CNT)`, `'XREFFILE'` to `WS-FL-DD`,
`GO TO 0000-START`. -/
stm_summary exit8599 (env : Env) (m : Nat) (mem : Mem) (hm : mem.size = 178495)
    (idx : List (Nat × Int)) (slots : List (ExitPt × Nat)) (saves : List (Nat × Nat))
    (active : List Nat) (out : List Event) (inp : List (Nat × List (List UInt8))) (clockN : Nat)
    (files : List (Nat × FileSt))
    (c t : Int) (hca : c.natAbs < 52) (hc1 : 1 ≤ c) (hc2 : c ≤ 51)
    (hta : t.natAbs < 11) (ht1 : 0 ≤ t) (ht2 : t ≤ 10)
    (hc : mem.read 1380 2 = encodeNum {} { digits := 4, signed := true, usage := .binary } c)
    (ht : mem.read 1382 2 = encodeNum {} { digits := 4, signed := true, usage := .binary } t) :
    Sem.runFrom Stm env (m + 1) 20 ⟨mem, idx, slots, saves, active, out, inp, files, clockN⟩

/-- After `8599-EXIT` (at `0000-START`): the groups of the file in the table with all their
counts, `CR-CNT` = the number of groups, `WS-FL-DD = 'XREFFILE'`. -/
def Phase3Done (st0 : State) (f1 f2 : FileSt) (trs : List (List UInt8)) (st : State) : Prop :=
  LoadFrame st0 st ∧
    st.mem.read 1380 2 = encodeNum {} { digits := 4, signed := true, usage := .binary }
      ((grp trs).length : Int) ∧
    TableOk st.mem (grp trs) ∧ TrctOk st.mem (grp trs) (grp trs).length ∧
    st.mem.read 1394 8 = [231, 217, 197, 198, 198, 201, 211, 197] ∧
    st.files = [(1, f1), (2, f2), (3,
      { mode := some .input, recs := trs, pos := trs.length, eof := true })]

theorem getLastD_eq_getD {α : Type _} (l : List α) (d : α) :
    l.getLastD d = l.getD (l.length - 1) d := by
  cases l with
  | nil => rfl
  | cons a l => simp [List.getLastD_eq_getLast?, List.getLast?_eq_getElem?, List.getD_eq_getElem?_getD]

/-- **Phase 3: the transaction table load.** From the invariant at `8500-READTRNX-READ`
(paragraph 19) with the records `rest` still to read (for the first pass: `CR-CNT = 1`,
`TR-CNT = 0`, `WS-SAVE-CARD` = the card of the first record, which is in `TRNX-RECORD`), the
program reaches `0000-START` (paragraph 1) with the consecutive same-card groups `grp trs` of the
transaction file in `WS-TRNX-TABLE` (cards, transaction ids and data, counts in `WS-TRCT`),
`CR-CNT` = their number, `WS-FL-DD = 'XREFFILE'`, the transaction file at its end and the rest of
the state as before (no output events).  Assumptions: 350-byte records, at most 50 cards (the
table has 51 entries; `4000-TRNXFILE-GET` reads the entry after the last), at most 10
transactions per card. -/
theorem phase3 (env : Env) (st0 : State) (f1 f2 : FileSt) (trs : List (List UInt8))
    (htl : ∀ r ∈ trs, r.length = 350) (hG : (grp trs).length ≤ 50)
    (hT : ∀ g ∈ grp trs, g.length ≤ 10) (hne : trs ≠ []) (rest : List (List UInt8)) (st : State)
    (hinv : LoadInv st0 f1 f2 trs rest st) (m : Nat) :
    ∃ st', Sem.runFrom Stm env (m + 41 + rest.length + 1) 19 st = Sem.runFrom Stm env (m + 40) 1 st' ∧
      Phase3Done st0 f1 f2 trs st' := by
  obtain ⟨st1, h1, hd⟩ := load_loop env st0 f1 f2 trs htl hG hT rest st hinv (m + 1)
  rw [show m + 41 + rest.length + 1 = m + 1 + 40 + rest.length + 1 by omega, h1,
    show m + 1 + 40 = (m + 40) + 1 by omega]
  obtain ⟨⟨hidx, hsl, hsv, hact, hout, hinp, hclk, hsz, hR, hE⟩, hcr, htr, htab, htrct, hfiles⟩ := hd
  obtain ⟨mem, idx, slots, saves, active, out, inp, files, clockN⟩ := st1
  dsimp only at hidx hsl hsv hact hout hinp hclk hsz hR hE hcr htr htab htrct hfiles
  have hgne : grp trs ≠ [] := fun h => hne ((grp_eq_nil trs).mp h)
  have hGpos : 1 ≤ (grp trs).length := List.length_pos_iff.mpr hgne
  have hTl : ((grp trs).getLastD []).length ≤ 10 := by
    apply hT
    rw [List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast hgne]
    exact List.getLast_mem hgne
  rw [exit8599 env (m + 40) mem hsz idx slots saves active out inp clockN files
    ((grp trs).length : Int) (((grp trs).getLastD []).length : Int)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hcr htr]
  refine ⟨_, rfl, ⟨hidx, hsl, hsv, hact, hout, hinp, hclk, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, hfiles⟩
  · simp [hsz]
  · load_auto
  · load_auto
  · load_auto
  · intro k hk1 hk2
    obtain ⟨ho1, ho2⟩ := htab k hk1 hk2
    refine ⟨by load_auto, fun j hj1 hj2 => ?_⟩
    obtain ⟨ho3, ho4⟩ := ho2 j hj1 hj2
    have hjl : j ≤ 10 := by
      have := hT ((grp trs).getD (k - 1) []) (by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
        exact List.getElem_mem _)
      omega
    exact ⟨by load_auto, by load_auto⟩
  · intro k hk1 hk2
    by_cases hk : k = (grp trs).length
    · subst hk
      rw [getLastD_eq_getD] at htr ⊢
      load_auto
    · have ho := htrct k hk1 (by omega)
      load_auto
  · load_auto

end Cobol.StmCore
