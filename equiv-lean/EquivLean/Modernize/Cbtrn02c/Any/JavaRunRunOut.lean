import EquivLean.Modernize.Cbtrn02c.Any.JavaRunRunX

/-!
# CBTRN02C → Java: `run`'s outputs at its two returns

`post_abend`: after the abend of `postTransaction` on transaction `k` (the model has stopped), the
`Result` holds `Model.runX`'s outputs (`WAb` of the stopped state).
-/

open Jimple EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbtrn02c.Java

theorem listOf_of_lrec {σ : State} {fs : List (FieldKey × Value)} {f : String} {l : Addr}
    {s : Schema} {cls : ClassName} {ws : List Addr} {vals : List (List EquivLean.Cobol.Rec.FVal)}
    (hf : Fields.get fs ("Cbtrn02c$Result", f) = some (.ref l)) (h : LRec σ l s cls ws vals) :
    ListOf σ fs f s cls vals := by
  obtain ⟨xs, m, hl, hfs, -, -⟩ := h
  exact ⟨l, .arrayList, xs, m, hf, hl, hfs⟩

/-- **The outputs at the abend return.** -/
theorem post_abend {g : G} {σ' : State} {A : Addrs} {k : Nat} {s1 s2 : Model.St}
    (hk : k < g.trans.length) (hstx : g.stx (k + 1) = ⟨s2, true⟩) (hW : WAb σ' A s1)
    (e1 : s2.disp = s1.disp) (e2 : s2.tranW = s1.tranW) (e3 : s2.rejW = s1.rejW)
    (e4 : s2.catW = s1.catW) (e5 : s2.acctRW = s1.acctRW) (e6 : s2.catRW = s1.catRW) :
    RunPostGX g (some (.ref A.r)) σ' := by
  have ho := G.outX_stop g hk hstx
  obtain ⟨⟨fs, hR, r1, r2, r3, r4, r5, r6, r7, r8⟩, ⟨xs, m, hl, hfs, -⟩, hT, hRj, hCW, hAR, hCR⟩ := hW
  refine ⟨A.r, fs, A.lD, .arrayList, xs, m, rfl, hR, r1, hl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    rw [ho] <;> dsimp only
  · rw [e1]; exact hfs
  · rw [e2]; exact listOf_of_lrec r2 hT
  · rw [e3]; exact listOf_of_lrec r3 hRj
  · rw [e4]; exact listOf_of_lrec r4 hCW
  · rw [e5]; exact listOf_of_lrec r5 hAR
  · rw [e6]; exact listOf_of_lrec r6 hCR
  · rw [r7]; rfl
  · rw [r8]; rfl

/-- The stopped model state and `dupSt` have the same outputs. -/
theorem dup_fields {s : Model.St} {t x a : List EquivLean.Cobol.Rec.FVal} {clk : List UInt8} :
    let s2 : Model.St := { Model.St.post clk s t x a with
      tranW := s.tranW, disp := (Model.St.post clk s t x a).disp ++ Model.dupLines }
    s2.disp = (dupSt s t x a).disp ∧ s2.tranW = (dupSt s t x a).tranW ∧
      s2.rejW = (dupSt s t x a).rejW ∧ s2.catW = (dupSt s t x a).catW ∧
      s2.acctRW = (dupSt s t x a).acctRW ∧ s2.catRW = (dupSt s t x a).catRW := by
  intro s2
  simp [s2, dupSt, post_eq, postTr, postAcc_postCat_tranW]

end EquivLean.Modernize.Cbtrn02c.Java
