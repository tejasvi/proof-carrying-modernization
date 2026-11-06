import EquivLean.Modernize.Cbtrn02c.Any.JavaRunRunX

/-!
# CBTRN02C → Java: `validateTran`'s precondition in the main loop

`vtd_of`: the daily transaction record as `validateTran` reads it; `vtin_of`: the cross-reference
file (the input array, unchanged since the entry) and the account table (`W`) as `validateTran`
searches them; `vtPre_of`: the precondition of the call at statement 74.
-/

open Jimple EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbtrn02c.Java

theorem keysOf_xref' : keysOf CardXrefRecord xrCls = xrKeys := by decide

theorem vtd_of {σ : State} {d : Addr} {t : List EquivLean.Cobol.Rec.FVal}
    (hd : JRecAt DalytranRecord dalCls σ (.ref d) t) (htv : DalytranRecord.Valid t) : VtD σ d t := by
  have htv0 := htv
  obtain ⟨⟨a, fsd, s0, s1, s3, s4, s7, s8, s9, s10, s11, s12, s13, hae, hdo, g0, t0, g1, t1, g2, g3,
    t3, g4, t4, g5, g6, g7, t7, g8, t8, g9, t9, g10, t10, g11, t11, g12, t12, g13, t13⟩, b0, b1, n2,
    b3, b4, n5, n6, b7, b8, b9, b10, b11, b12, b13, rfl, h2, h5, h6⟩ := dalobj_of_rec hd htv
  cases hae
  obtain ⟨-, -, -, -, -, -, hamt, -, -, -, -, -, -, horig, -⟩ := Glue.tranOf_valid htv0
  exact ⟨fsd, s10, s11, hdo, g10, t10, g5, g11, t11, horig, hamt⟩

theorem vtin_of {g : G} {σ0 σ : State} {A : Addrs} {s : Model.St}
    (hin : Any.Java.RunIn g.args σ0 g.trans g.xrefs g.accts g.cats g.clk) (hg : Grows σ0 σ)
    (hW : W σ A s) (hMV : MV s) (hFr : Fresh σ0 A) :
    VtIn σ g.a2 A.aD A.wX A.wA g.xrefs s.accts := by
  obtain ⟨a1, a2, a3, a4, cs, hargs, -, ⟨etX, xsX, hxa, hlX, hfX⟩, -, -, -, -, -, hv2, -, -, -⟩ := hin
  simp only [G.args, List.cons.injEq, Value.ref.injEq, and_true] at hargs
  obtain ⟨-, rfl, -, -, -⟩ := hargs
  obtain ⟨-, -, -, -, -, -, -, ⟨etA, xsA, haD, hfA, hwsA, hlA⟩, -⟩ := hW
  have hfX1 := forall2_imp (fun _ _ h => jrecAt_grows h hg) hfX
  have hwX : σ0.next ≤ A.wX := hFr A.wX (by simp)
  refine ⟨etX, xsX, etA, xsA, heap_of_grows hg hxa, hlX, ?_, hfX1, hv2, ?_, haD, hlA, ?_, hfA,
    hMV.1, ?_⟩
  · intro v hv
    obtain ⟨x, hx, hr⟩ := forall2_ex_mem hfX1 v hv
    exact ⟨x, hx, (xobj_of_rec hr (hv2 x hx)).1⟩
  · intro v hv he
    obtain ⟨x, -, hr⟩ := forall2_ex_mem hfX v hv
    obtain ⟨y, fs, hy, hyo, -⟩ := hr
    rw [he] at hy
    cases hy
    have := State.lt_next_of_heap hyo
    jomega
  · intro v hv
    obtain ⟨x, hx, hr⟩ := forall2_ex_mem hfA v hv
    exact ⟨x, hx, (acctobj_of_rec hr (hMV.1 x hx)).1⟩
  · intro v hv
    exact hwsA v hv A.wA (by simp [Addrs.ws])

/-- **`validateTran`'s precondition** at statement 74 of `run`. -/
theorem vtPre_of {g : G} {σ0 σ : State} {A : Addrs} {s : Model.St} {d : Addr}
    {t : List EquivLean.Cobol.Rec.FVal}
    (hin : Any.Java.RunIn g.args σ0 g.trans g.xrefs g.accts g.cats g.clk) (hg : Grows σ0 σ)
    (hW : W σ A s) (hMV : MV s) (hFr : Fresh σ0 A) (hI : σ.initOf "Cbtrn02c" = .done)
    (hd : JRecAt DalytranRecord dalCls σ (.ref d) t) (htv : DalytranRecord.Valid t) :
    validateTranSpec.pre [.ref d, .ref g.a2, .ref A.aD, .ref A.wX, .ref A.wA] σ := by
  have hW0 := hW
  obtain ⟨-, -, -, -, -, -, -, -, -, -, ⟨fsX, hwX, hkX⟩, ⟨fsA, hwA, hkA⟩, -⟩ := hW0
  refine ⟨d, g.a2, A.aD, A.wX, A.wA, t, g.xrefs, s.accts, fsX, fsA, rfl, vtd_of hd htv,
    vtin_of hin hg hW hMV hFr, hwX, ?_, hwA, ?_, hI⟩
  · rw [← keysOf_xref']; exact hkX
  · rw [← keysOf_acct'']; exact hkA

end EquivLean.Modernize.Cbtrn02c.Java
