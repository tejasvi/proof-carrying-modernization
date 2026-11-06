import EquivLean.Modernize.Cbtrn02c.Model

/-!
# CBTRN02C on any input: repeated transaction ids

`Model.run` assumes distinct transaction ids. On any input, the translations do what the COBOL
program does at `2900-WRITE-TRANSACTION-FILE` (Rust `lib.rs`, Java `Cbtrn02c.run`): the
transaction file is opened `OUTPUT`, so it holds the transaction records written so far in this
run (rejected transactions are never written). A posted transaction whose id is the id of one of
those records cannot be written (`INVALID KEY`, status 22): the program displays
`ERROR WRITING TO TRANSACTION FILE`, the file status and `ABENDING PROGRAM`, and abends. The
account and the category balance of that transaction are already updated; its transaction record
is not written; nothing follows (no counts, RETURN-CODE stays 0).

`runX_of_nodup`: without repeated ids, `runX` is `run`, and the program does not abend.
-/

open Cobol EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbtrn02c.Model

/-- The lines of the failed `WRITE` of a transaction record: the error line, the file status
(`9910-DISPLAY-IO-STATUS` for status 22), the abend message (`9999-ABEND-PROGRAM`). -/
def dupLines : List (List Nat) :=
  [txt "ERROR WRITING TO TRANSACTION FILE", txt "FILE STATUS IS: NNNN0022",
    txt "ABENDING PROGRAM"]

/-- The state between two transactions, and whether the program has abended. -/
structure StX where
  s : St
  stop : Bool

/-- One daily transaction: `step`, except that a transaction posted (`step` counts it) with the
id of a transaction record already written abends instead of writing its record. Nothing after
the abend. -/
def stepX (xrefs : List (List FVal)) (clk : List UInt8) (x : StX) (t : List FVal) : StX :=
  if x.stop then x
  else
    let s' := step xrefs clk x.s t
    if s'.posted = x.s.posted + 1 ∧ tId t ∈ x.s.tranW.map tId then
      ⟨{ s' with tranW := x.s.tranW, disp := s'.disp ++ dupLines }, true⟩
    else ⟨s', false⟩

/-- The outputs, and whether the program abended. -/
structure OutX extends Out where
  abended : Bool

/-- **What CBTRN02C outputs on any input**, for the daily transactions `trans`, cross-references
`xrefs`, accounts `accts`, category balances `cats` and the clock reading `clk`. -/
def runX (trans xrefs accts cats : List (List FVal)) (clk : List UInt8) : OutX :=
  let x := trans.foldl (stepX xrefs clk) ⟨init accts cats, false⟩
  if x.stop then
    { disp := x.s.disp, tranW := x.s.tranW, rejW := x.s.rejW, catW := x.s.catW,
      acctRW := x.s.acctRW, catRW := x.s.catRW, rc := 0, abended := true }
  else
    { disp := x.s.disp ++ [txt "TRANSACTIONS PROCESSED :" ++ zpad 9 trans.length,
        txt "TRANSACTIONS REJECTED  :" ++ zpad 9 x.s.rejects,
        txt "END OF EXECUTION OF PROGRAM CBTRN02C"],
      tranW := x.s.tranW, rejW := x.s.rejW, catW := x.s.catW, acctRW := x.s.acctRW,
      catRW := x.s.catRW, rc := if 0 < x.s.rejects then 4 else 0, abended := false }

/-! ## Without repeated ids -/

/-- `step` writes no transaction record, or that of `t`. -/
theorem step_tranW (xrefs : List (List FVal)) (clk : List UInt8) (s : St) (t : List FVal) :
    (step xrefs clk s t).tranW = s.tranW ∨
      (step xrefs clk s t).tranW = s.tranW ++ [tranVals t clk] := by
  unfold step
  split
  · exact .inl rfl
  · split
    · exact .inl rfl
    · split
      · exact .inl rfl
      · split
        · exact .inl rfl
        · right
          unfold St.post
          split <;> rfl

theorem tId_tranVals (t : List FVal) (clk : List UInt8) (h : t ≠ []) :
    tId (tranVals t clk) = tId t := by
  cases t with
  | nil => exact absurd rfl h
  | cons a l => rfl

/-- Without a repeated id, `stepX` is `step`. -/
theorem foldl_stepX_of_nodup (xrefs : List (List FVal)) (clk : List UInt8) :
    ∀ (ts : List (List FVal)) (s : St), (∀ t ∈ ts, t ≠ []) → (ts.map tId).Nodup →
      (∀ t ∈ ts, tId t ∉ s.tranW.map tId) →
      ts.foldl (stepX xrefs clk) ⟨s, false⟩ = ⟨ts.foldl (step xrefs clk) s, false⟩
  | [], _, _, _, _ => rfl
  | t :: ts, s, hne, hd, hw => by
    have ht : tId t ∉ s.tranW.map tId := hw t (by simp)
    have hstep : stepX xrefs clk ⟨s, false⟩ t = ⟨step xrefs clk s t, false⟩ := by
      simp only [stepX, Bool.false_eq_true, ↓reduceIte, ht, and_false]
    rw [List.foldl_cons, List.foldl_cons, hstep]
    refine foldl_stepX_of_nodup xrefs clk ts _ (fun t' h => hne t' (by simp [h]))
      (List.nodup_cons.1 hd).2 ?_
    intro t' ht' hmem
    rcases step_tranW xrefs clk s t with h | h
    · rw [h] at hmem
      exact hw t' (by simp [ht']) hmem
    · rw [h, List.map_append, List.mem_append] at hmem
      rcases hmem with hmem | hmem
      · exact hw t' (by simp [ht']) hmem
      · rw [List.map_cons, List.map_nil, List.mem_singleton,
          tId_tranVals t clk (hne t (by simp))] at hmem
        exact (List.nodup_cons.1 hd).1 (hmem ▸ List.mem_map_of_mem ht')

/-- **Without repeated transaction ids, `runX` is `run`**, and the program does not abend. -/
theorem runX_of_nodup (trans xrefs accts cats : List (List FVal)) (clk : List UInt8)
    (hne : ∀ t ∈ trans, t ≠ []) (hd : (trans.map tId).Nodup) :
    runX trans xrefs accts cats clk = { toOut := run trans xrefs accts cats clk, abended := false } := by
  have h := foldl_stepX_of_nodup xrefs clk trans (init accts cats) hne hd (by simp [init])
  simp only [runX, h, Bool.false_eq_true, ↓reduceIte]
  rfl

end EquivLean.Modernize.Cbtrn02c.Model
