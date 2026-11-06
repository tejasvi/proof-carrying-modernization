import EquivLean.Modernize.Cbtrn02c.Any.JavaRunVtPre
import EquivLean.Modernize.Cbtrn02c.Any.JavaRunDet
import EquivLean.Modernize.Cbtrn02c.Any.JavaRunRunOut

/-!
# CBTRN02C → Java: facts for the main loop's segments

`vreason_zero_of`/`vreason_ne_of`: the reject reason from `validateTran`'s `int`; `ptFacts_of`:
`postTransaction`'s precondition at statement 76 from the loop's invariant and the inputs.
-/

open Jimple EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbtrn02c.Java

theorem vreason_zero_of {xr ac : List (List EquivLean.Cobol.Rec.FVal)} {t : List EquivLean.Cobol.Rec.FVal}
    (h : BitVec.ofInt 32 (vreason xr ac t) = 0#32) : vreason xr ac t = 0 := by
  rcases vreason_cases xr ac t with h0 | h0 | h0 | h0 | h0 <;> rw [h0] at h ⊢ <;> revert h <;> decide

theorem vreason_ne_of {xr ac : List (List EquivLean.Cobol.Rec.FVal)} {t : List EquivLean.Cobol.Rec.FVal}
    (h : ¬BitVec.ofInt 32 (vreason xr ac t) = 0#32) : vreason xr ac t ≠ 0 := by
  intro h0; rw [h0] at h; exact h rfl

/-- The `k`-th daily transaction record in the heap (the input array is unchanged since the entry). -/
theorem trec_at {g : G} {σ0 σ : State} {k : Nat} {et : JType} {xsD : List Value} {d : Addr}
    (hin : Any.Java.RunIn g.args σ0 g.trans g.xrefs g.accts g.cats g.clk) (hg : Grows σ0 σ)
    (ha1 : σ.heap g.a1 = some (.array et xsD)) (hxk : xsD[k]? = some (.ref d)) (hk : k < g.trans.length) :
    JRecAt DalytranRecord dalCls σ (.ref d) (g.trec k) ∧ DalytranRecord.Valid (g.trec k) := by
  obtain ⟨a1, a2, a3, a4, cs, hargs, ⟨et1, xs1, h1, -, hf1⟩, -, -, -, -, -, hv1, -⟩ := hin
  simp only [G.args, List.cons.injEq, Value.ref.injEq, and_true] at hargs
  obtain ⟨rfl, -, -, -, -⟩ := hargs
  have h1' := heap_of_grows hg h1
  rw [ha1] at h1'
  simp only [Option.some.injEq, Obj.array.injEq] at h1'
  obtain ⟨-, rfl⟩ := h1'
  have hl := forall2_length hf1
  have hkx : k < xsD.length := by omega
  have hr := forall2_get hf1 k hkx hk
  rw [List.getElem?_eq_getElem hkx] at hxk
  simp only [Option.some.injEq] at hxk
  rw [hxk] at hr
  have etr : g.trec k = g.trans[k] := by
    simp only [G.trec, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]
  rw [etr]
  exact ⟨jrecAt_grows hr hg, hv1 _ (List.getElem_mem hk)⟩

/-- **`postTransaction`'s precondition** at statement 76 of `run`. -/
theorem ptFacts_of {g : G} {σ0 σ : State} {A : Addrs} {k : Nat} {d : Addr}
    {x a : List EquivLean.Cobol.Rec.FVal}
    (hin : Any.Java.RunIn g.args σ0 g.trans g.xrefs g.accts g.cats g.clk) (hg : Grows σ0 σ)
    (hW : W σ A (g.st k)) (hMV : MV (g.st k)) (hAd : AdEt σ A.aD) (hk : k < g.trans.length)
    (hd : JRecAt DalytranRecord dalCls σ (.ref d) (g.trec k)) (htv : DalytranRecord.Valid (g.trec k))
    (hx : Model.findXref g.xrefs (Model.tCard (g.trec k)) = some x)
    (ha : Model.findAcct (g.st k).accts (Model.xAcct x) = some a)
    (hxj : JRecAt CardXrefRecord xrCls σ (.ref A.wX) x) (haj : JRecAt AccountRecord acCls σ (.ref A.wA) a)
    (hI : Inits σ) :
    PtFacts σ ⟨A, g.st k, g.trec k, x, a, g.clk, d, g.cs⟩ := by
  have hin0 := hin
  obtain ⟨a1, a2, a3, a4, cs, hargs, -, -, -, -, hcs, hcd, -, hv2, -, -, -, hbound⟩ := hin0
  simp only [G.args, List.cons.injEq, Value.ref.injEq, and_true] at hargs
  obtain ⟨-, -, -, -, rfl⟩ := hargs
  have hlb := G.lb g (Nat.le_of_lt hk)
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8⟩ := hlb
  refine ⟨hW, hMV, hd, htv, hxj, hv2 x (List.mem_of_find?_eq_some hx), haj, ha,
    jstrAt_grows hcs hg, hcd, ?_, hI, hAd⟩
  show PtLen (g.st k)
  exact ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩

end EquivLean.Modernize.Cbtrn02c.Java
