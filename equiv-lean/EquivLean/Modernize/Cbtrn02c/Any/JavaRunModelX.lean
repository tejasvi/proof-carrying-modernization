import EquivLean.Modernize.Cbtrn02c.Any.JavaRunML
import EquivLean.Modernize.Cbtrn02c.ModelAny

/-!
# CBTRN02C → Java: the any-input model state along the daily transactions

`G.stx k` is `Model.runX`'s state after `k` transactions: `⟨G.st k, false⟩` until a posted
transaction repeats a written id; then it stops, and the outputs are those of the stopped state.
-/

open EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbtrn02c.Java

/-- The any-input model state after the first `n` daily transactions. -/
def G.stx (g : G) (n : Nat) : Model.StX :=
  (g.trans.take n).foldl (Model.stepX g.xrefs g.clk) ⟨Model.init g.accts g.cats, false⟩

/-- What the model outputs on any input. -/
def G.outX (g : G) : Model.OutX := Model.runX g.trans g.xrefs g.accts g.cats g.clk

theorem G.stx_zero (g : G) : g.stx 0 = ⟨g.st 0, false⟩ := by
  simp [G.stx, G.st]

theorem G.stx_succ (g : G) {k : Nat} (hk : k < g.trans.length) :
    g.stx (k + 1) = Model.stepX g.xrefs g.clk (g.stx k) (g.trec k) := by
  simp only [G.stx, G.trec]
  rw [List.take_add_one, List.getElem?_eq_getElem hk, Option.toList_some, List.foldl_append,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
  rfl

/-- A transaction that is rejected, or posted with a new id: one more `step`. -/
theorem G.stx_succ_ok (g : G) {k : Nat} (hk : k < g.trans.length) (h : g.stx k = ⟨g.st k, false⟩)
    (hn : ¬((g.step (g.st k) (g.trec k)).posted = (g.st k).posted + 1 ∧
      Model.tId (g.trec k) ∈ (g.st k).tranW.map Model.tId)) :
    g.stx (k + 1) = ⟨g.st (k + 1), false⟩ := by
  rw [G.stx_succ g hk, h, G.st_succ g hk]
  simp only [G.step] at hn ⊢
  simp only [Model.stepX, Bool.false_eq_true, ↓reduceIte, if_neg hn]

/-- A posted transaction with a written id: the run stops. -/
theorem G.stx_succ_dup (g : G) {k : Nat} (hk : k < g.trans.length) (h : g.stx k = ⟨g.st k, false⟩)
    (hp : (g.step (g.st k) (g.trec k)).posted = (g.st k).posted + 1)
    (hd : Model.tId (g.trec k) ∈ (g.st k).tranW.map Model.tId) :
    g.stx (k + 1) = ⟨{ g.step (g.st k) (g.trec k) with
        tranW := (g.st k).tranW, disp := (g.step (g.st k) (g.trec k)).disp ++ Model.dupLines }, true⟩ := by
  rw [G.stx_succ g hk, h]
  simp only [G.step] at hp hd ⊢
  simp only [Model.stepX, Bool.false_eq_true, ↓reduceIte, if_pos (And.intro hp hd)]

theorem foldl_stepX_stop (xrefs : List (List FVal)) (clk : List UInt8) :
    ∀ (ts : List (List FVal)) (x : Model.StX), x.stop = true →
      ts.foldl (Model.stepX xrefs clk) x = x
  | [], _, _ => rfl
  | t :: ts, x, h => by
    rw [List.foldl_cons]
    have e : Model.stepX xrefs clk x t = x := by simp [Model.stepX, h]
    rw [e]
    exact foldl_stepX_stop xrefs clk ts x h

/-- The outputs after a stop at transaction `k`. -/
theorem G.outX_stop (g : G) {k : Nat} (hk : k < g.trans.length) {s : Model.St}
    (hx : g.stx (k + 1) = ⟨s, true⟩) :
    g.outX = {
        disp := s.disp, tranW := s.tranW, rejW := s.rejW, catW := s.catW,
        acctRW := s.acctRW, catRW := s.catRW, rc := 0, abended := true } := by
  have hall : g.trans.foldl (Model.stepX g.xrefs g.clk) ⟨Model.init g.accts g.cats, false⟩ =
      ⟨s, true⟩ := by
    rw [← List.take_append_drop (k + 1) g.trans, List.foldl_append]
    have e : (g.trans.take (k + 1)).foldl (Model.stepX g.xrefs g.clk)
        ⟨Model.init g.accts g.cats, false⟩ = ⟨s, true⟩ := hx
    rw [e]
    exact foldl_stepX_stop _ _ _ _ rfl
  simp only [G.outX, Model.runX, hall, ↓reduceIte]

/-- The outputs when no transaction stopped the run: those of `Model.run`. -/
theorem G.outX_exit (g : G) (h : g.stx g.trans.length = ⟨g.st g.trans.length, false⟩) :
    g.outX = { toOut := g.out, abended := false } := by
  have hall : g.trans.foldl (Model.stepX g.xrefs g.clk) ⟨Model.init g.accts g.cats, false⟩ =
      ⟨g.trans.foldl (Model.step g.xrefs g.clk) (Model.init g.accts g.cats), false⟩ := by
    have e := h
    simp only [G.stx, G.st, G.step, List.take_length] at e
    exact e
  simp only [G.outX, G.out, Model.runX, hall, Bool.false_eq_true, ↓reduceIte]
  rfl

/-- The text of a written id determines the id. -/
theorem tidJ_mem_iff {t : List FVal} {clk : List UInt8} (ht : t ≠ []) (ws : List (List FVal)) :
    tidJ (Model.tranVals t clk) ∈ ws.map tidJ ↔ Model.tId t ∈ ws.map Model.tId := by
  have e : ∀ r, tidJ r = cp037Str (Model.tId r) := fun r => rfl
  rw [← Model.tId_tranVals t clk ht]
  constructor
  · intro hm
    obtain ⟨r, hr, hre⟩ := List.mem_map.1 hm
    rw [e, e] at hre
    exact List.mem_map.2 ⟨r, hr, cp037Str_inj hre⟩
  · intro hm
    obtain ⟨r, hr, hre⟩ := List.mem_map.1 hm
    exact List.mem_map.2 ⟨r, hr, by rw [e, e, hre]⟩

end EquivLean.Modernize.Cbtrn02c.Java
