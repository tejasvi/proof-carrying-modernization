/-
# `INITIALIZE WS-TRNX-TABLE WS-TRN-TBL-CNTR` as two writes

The last sentence of `CBSTM03AB`'s first paragraph (`para0`, sentence 11) initializes the
171 KB transaction table and its counters.  The front end lowers it to 1122 `MOVE`s with literal
subscripts: `SPACE` to the 51 `WS-CARD-NUM (i)`, the 510 `WS-TRAN-NUM (i, j)` and the 510
`WS-TRAN-REST (i, j)` (in that order), `ZERO` to the 51 binary `WS-TRCT (i)`.  Symbolic execution
of 1122 statements on the table would build a chain of 1122 writes; instead:

* `fillSpec` reads such a statement as the write it performs, `(offset, length, byte)`, and
  `execStmts_fills` runs a list of them as the fold of those writes (`execStmt_fill`);
* the kernel checks that the sentence's statements are exactly `initWrites` (`init_fillSpec`,
  `decide +kernel`);
* `foldl_initWrites` merges the fold: the writes of one byte cover `4365 … 175520` (the table)
  and `175521 … 175622` (the counters) exactly (`any_tbl`, `any_ctr`), so the fold is one write
  of 171156 spaces and one of 102 zero bytes (`get_foldl_const`, `Mem.ext_get`).
-/
import EquivLean.Demo.Cobol.Cbstm03a.Stm.WalkSummary

open Cobol Cobol.Stm

namespace Cobol.StmCore

/-- The offset a list of literal subscripts selects (`none`: not literal, or out of range). -/
def litOff : List Subscript → Nat → Option Nat
  | [], off => some off
  | ⟨.lit k, stride, max⟩ :: ss, off =>
    if 1 ≤ k ∧ k ≤ (max : Int) then litOff ss (off + (k.toNat - 1) * stride) else none
  | _ :: _, _ => none

/-- The binary format of `WS-TRCT` (`PIC S9(4) COMP`). -/
def trctFmt : NumFmt := { digits := 4, signed := true, usage := .binary }

/-- The write a `MOVE SPACE` to an alphanumeric item / `MOVE ZERO` to a `PIC S9(4) COMP` item
with literal subscripts performs: offset, length, byte. -/
def fillSpec : Stmt → Option (Nat × Nat × UInt8)
  | .move (.fig .space) [⟨_, ⟨off, len, .alnum false⟩, subs, none⟩] =>
    (litOff subs off).map fun o => (o, len, 64)
  | .move (.fig .zero) [⟨_, ⟨off, len, .num f⟩, subs, none⟩] =>
    if len = 2 ∧ f = trctFmt then (litOff subs off).map fun o => (o, 2, 0) else none
  | _ => none

/-- The fold of the writes. -/
def fillWrites (m : Mem) (ws : List (Nat × Nat × UInt8)) : Mem :=
  ws.foldl (fun m w => m.write w.1 (List.replicate w.2.1 w.2.2)) m

theorem subsOff_of_litOff (c : Config) (st : State) :
    ∀ (subs : List Subscript) (off o : Nat), litOff subs off = some o →
      Sem.subsOff c st subs off = .ok o
  | [], off, o, h => by simp [litOff] at h; subst h; rfl
  | ⟨.lit k, stride, max⟩ :: ss, off, o, h => by
    unfold litOff at h
    split at h
    · rename_i hk
      simp only [Sem.subsOff, Sem.evalSub, hk, and_self, ↓reduceIte]
      exact subsOff_of_litOff c st ss _ o h
    · simp at h
  | ⟨.ref _ _, _, _⟩ :: _, _, _, h => by simp [litOff] at h
  | ⟨.idx _ _, _, _⟩ :: _, _, _, h => by simp [litOff] at h

theorem fillPattern_space (n : Nat) : Sem.fillPattern [64] n = List.replicate n 64 := by
  apply List.ext_getElem
  · simp [Sem.fillPattern]
  · intro i h1 h2
    simp [Sem.fillPattern, Nat.mod_one]

theorem resolve_of_litOff (c : Config) (st : State) (item off len : Nat) (k : FieldKind)
    (subs : List Subscript) (o : Nat) (h : litOff subs off = some o) :
    Sem.resolve c st ⟨item, ⟨off, len, k⟩, subs, none⟩ = .ok ⟨o, len, k⟩ := by
  cases subs with
  | nil => simp [litOff] at h; subst h; rfl
  | cons s ss => simp only [Sem.resolve, subsOff_of_litOff c st (s :: ss) off o h]

theorem space_default : ({} : Config).space = 64 := by decide

theorem fitNum_trct : Sem.fitNum {} trctFmt 0 = (false, 0) := by decide

theorem encode_trct_zero : encodeNum {} trctFmt 0 = [0, 0] := by decide

/-- One statement read by `fillSpec` performs its write. -/
theorem execStmt_fill (P : Program) (hcfg : P.cfg = {}) (env : Env) (rec : Nat → State → Sem.Res)
    (fuel : Nat) (s : Stmt) (st : State) (o len : Nat) (b : UInt8)
    (h : fillSpec s = some (o, len, b)) :
    Sem.execStmt P env rec fuel s st = (.normal, { st with mem := st.mem.write o (List.replicate len b) }) := by
  unfold fillSpec at h
  split at h
  · rename_i item off len' subs
    obtain ⟨o', ho', he⟩ := Option.map_eq_some_iff.mp h
    simp only [Prod.mk.injEq] at he; obtain ⟨rfl, rfl, rfl⟩ := he
    rw [Sem.execStmt]
    simp only [Sem.move, Sem.srcVal, Sem.moveList, resolve_of_litOff {} st item off len' _ subs o' ho',
      Sem.moveInto, Sem.lift, Sem.writeBytes, hcfg, Sem.figBytes, space_default, fillPattern_space]
  · rename_i item off len' f subs
    split at h
    · rename_i hf
      obtain ⟨rfl, rfl⟩ := hf
      obtain ⟨o', ho', he⟩ := Option.map_eq_some_iff.mp h
      simp only [Prod.mk.injEq] at he; obtain ⟨rfl, rfl, rfl⟩ := he
      rw [Sem.execStmt]
      simp only [Sem.move, Sem.srcVal, Sem.moveList, resolve_of_litOff {} st item off 2 _ subs o' ho',
        Sem.moveInto, Sem.lift, Sem.writeBytes, Sem.storeMove, hcfg, fitNum_trct, encode_trct_zero]
      rfl
    · simp at h
  · simp at h

/-- A list of statements read by `fillSpec` performs the fold of their writes. -/
theorem execStmts_fills (P : Program) (hcfg : P.cfg = {}) (env : Env)
    (rec : Nat → State → Sem.Res) (fuel : Nat) :
    ∀ (ss : List Stmt) (ws : List (Nat × Nat × UInt8)) (st : State), ss.map fillSpec = ws.map some →
      Sem.execStmts P env rec fuel ss st = (.normal, { st with mem := fillWrites st.mem ws })
  | [], [], st, _ => rfl
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h
  | s :: ss, (o, len, b) :: ws, st, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [Sem.execStmts, execStmt_fill P hcfg env rec fuel s st o len b h.1]
    simp only
    rw [execStmts_fills P hcfg env rec fuel ss ws _ h.2]
    rfl

/-- The writes of the `INITIALIZE`: spaces on the 51 cards, the 510 transaction ids, the 510
transaction data, then zero bytes on the 51 counters. -/
def tblWrites : List (Nat × Nat × UInt8) :=
  (List.range 51).map (fun i => (4365 + i * 3356, 16, 64)) ++
  (List.range 51).flatMap (fun i => (List.range 10).map (fun j => (4381 + i * 3356 + j * 334, 16, 64))) ++
  (List.range 51).flatMap (fun i => (List.range 10).map (fun j => (4397 + i * 3356 + j * 334, 318, 64)))

def ctrWrites : List (Nat × Nat × UInt8) := (List.range 51).map (fun i => (175521 + i * 2, 2, 0))

/-- The `INITIALIZE` sentence (sentence 11 of `para0`). -/
def initSentence : List Stmt := Stm.para0.body.getD 11 []

theorem stm_cfg : Stm.cfg = {} := by decide

set_option maxRecDepth 100000 in
/-- The kernel reads the 1122 statements of the sentence. -/
theorem init_fillSpec : initSentence.map fillSpec = (tblWrites ++ ctrWrites).map some := by
  decide +kernel

theorem getD_replicate' (n k : Nat) (b d : UInt8) :
    (List.replicate n b).getD k d = if k < n then b else d := by
  by_cases h : k < n <;> simp [List.getD_eq_getElem?_getD, h]

theorem size_fillWrites : ∀ (m : Mem) (ws : List (Nat × Nat × UInt8)), (fillWrites m ws).size = m.size
  | _, [] => rfl
  | m, w :: ws => by
    simp only [fillWrites, List.foldl_cons]
    rw [← fillWrites, size_fillWrites]; simp

/-- A fold of writes of one byte `b`: `b` where some write covers the address, else the old
byte. -/
theorem get_fillWrites_const (b : UInt8) :
    ∀ (ws : List (Nat × Nat × UInt8)) (m : Mem) (i : Nat), (∀ w ∈ ws, w.2.2 = b) →
      (fillWrites m ws).get i =
        if ws.any (fun w => decide (w.1 ≤ i ∧ i < w.1 + w.2.1)) = true ∧ i < m.size then b
        else m.get i
  | [], m, i, _ => by simp [fillWrites]
  | w :: ws, m, i, hb => by
    have ih := get_fillWrites_const b ws (m.write w.1 (List.replicate w.2.1 w.2.2)) i
      (fun w' h => hb w' (List.mem_cons_of_mem _ h))
    have hw : w.2.2 = b := hb w (List.mem_cons_self ..)
    simp only [fillWrites, List.foldl_cons] at ih ⊢
    rw [ih, Mem.get_write, Mem.size_write, getD_replicate', List.length_replicate, List.any_cons, hw]
    by_cases h2 : w.1 ≤ i ∧ i < w.1 + w.2.1
    · have h2' : decide (w.1 ≤ i ∧ i < w.1 + w.2.1) = true := by simp [h2]
      have h4 : i - w.1 < w.2.1 := by omega
      by_cases h3 : i < m.size
      · simp [h2, h3, h4]
      · simp [h3]
    · have h2' : decide (w.1 ≤ i ∧ i < w.1 + w.2.1) = false := by simp [h2]
      simp only [h2', Bool.false_or]
      by_cases h3 : i < m.size
      · have h5 : ¬ (w.1 ≤ i ∧ i < w.1 + w.2.1 ∧ i < m.size) := by omega
        simp [h5]
      · simp [h3]

/-- The table writes cover exactly `4365 … 175520`. -/
theorem any_tbl (i : Nat) :
    tblWrites.any (fun w => decide (w.1 ≤ i ∧ i < w.1 + w.2.1)) =
      decide (4365 ≤ i ∧ i < 175521) := by
  rw [Bool.eq_iff_iff]
  simp only [tblWrites, List.any_append, List.any_map, List.any_flatMap, Bool.or_eq_true,
    List.any_eq_true, List.mem_range, Function.comp_apply, decide_eq_true_eq]
  constructor
  · rintro ((⟨a, ha, h⟩ | ⟨a, ha, b, hb, h⟩) | ⟨a, ha, b, hb, h⟩) <;> omega
  · intro h
    by_cases hr : (i - 4365) % 3356 < 16
    · exact Or.inl (Or.inl ⟨(i - 4365) / 3356, by omega, by omega⟩)
    · by_cases hs : ((i - 4365) % 3356 - 16) % 334 < 16
      · exact Or.inl (Or.inr ⟨(i - 4365) / 3356, by omega, ((i - 4365) % 3356 - 16) / 334,
          by omega, by omega⟩)
      · exact Or.inr ⟨(i - 4365) / 3356, by omega, ((i - 4365) % 3356 - 16) / 334,
          by omega, by omega⟩

/-- The counter writes cover exactly `175521 … 175622`. -/
theorem any_ctr (i : Nat) :
    ctrWrites.any (fun w => decide (w.1 ≤ i ∧ i < w.1 + w.2.1)) =
      decide (175521 ≤ i ∧ i < 175623) := by
  rw [Bool.eq_iff_iff]
  simp only [ctrWrites, List.any_map, List.any_eq_true, List.mem_range, Function.comp_apply,
    decide_eq_true_eq]
  constructor
  · rintro ⟨a, ha, h⟩; omega
  · intro h; exact ⟨(i - 175521) / 2, by omega, by omega⟩

/-- The fold of the 1122 writes is one write of spaces on the table and one of zero bytes on
the counters. -/
theorem fillWrites_init (m : Mem) (hm : m.size = 178495) :
    fillWrites m (tblWrites ++ ctrWrites) =
      (m.write 4365 (List.replicate 171156 64)).write 175521 (List.replicate 102 0) := by
  have hsplit : fillWrites m (tblWrites ++ ctrWrites) = fillWrites (fillWrites m tblWrites) ctrWrites := by
    simp [fillWrites, List.foldl_append]
  have hsz : (fillWrites m tblWrites).size = m.size := size_fillWrites _ _
  rw [hsplit]
  apply Mem.ext_get
  · simp only [Mem.size_write, size_fillWrites]
  · intro i hi
    have hc : ∀ w ∈ ctrWrites, w.2.2 = 0 := by decide +kernel
    have ht : ∀ w ∈ tblWrites, w.2.2 = 64 := by decide +kernel
    simp only [size_fillWrites] at hi
    rw [get_fillWrites_const 0 ctrWrites _ i hc, get_fillWrites_const 64 tblWrites m i ht, any_ctr,
      any_tbl, hsz, Mem.get_write, Mem.get_write, Mem.size_write, getD_replicate', getD_replicate']
    simp only [List.length_replicate, decide_eq_true_eq]
    rw [hm] at hi ⊢
    by_cases h1 : 175521 ≤ i ∧ i < 175623
    · have h1' : i - 175521 < 102 := by omega
      have h1c : 175521 ≤ i ∧ i < 175521 + 102 ∧ i < 178495 := by omega
      simp only [h1, hi, and_self, ↓reduceIte, h1']
    · have h1n : ¬(175521 ≤ i ∧ i < 175521 + 102 ∧ i < 178495) := by omega
      by_cases h2 : 4365 ≤ i ∧ i < 175521
      · have h2' : i - 4365 < 171156 := by omega
        have h1n' : ¬(175521 ≤ i ∧ i < 175521 + 102) := by omega
        simp only [h1, hi, h2, and_self, ↓reduceIte, h2', and_true]
      · have h2n : ¬(4365 ≤ i ∧ i < 4365 + 171156 ∧ i < 178495) := by omega
        simp only [h1, h2, h1n, h2n, false_and, ↓reduceIte]

/-- **`INITIALIZE WS-TRNX-TABLE WS-TRN-TBL-CNTR`** (sentence 11 of `para0`): spaces on the
171156-byte table, zero bytes on the 102-byte counter table, nothing else. -/
theorem execStmts_init (env : Env) (rec : Nat → State → Sem.Res) (fuel : Nat) (st : State)
    (hm : st.mem.size = 178495) :
    Sem.execStmts Stm env rec fuel initSentence st =
      (.normal, { st with
        mem := (st.mem.write 4365 (List.replicate 171156 64)).write 175521 (List.replicate 102 0) }) := by
  rw [execStmts_fills Stm stm_cfg env rec fuel initSentence _ st init_fillSpec, fillWrites_init _ hm]

end Cobol.StmCore
