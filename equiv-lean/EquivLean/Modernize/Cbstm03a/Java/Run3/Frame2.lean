import EquivLean.Modernize.Cbstm03a.Java.Run3.Frame

/-!
# CBSTM03A → Java, `run`'s segments 117, 140, 153: frames that only change locals, record facts, the model's step
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows Keeps fixStr zpadStr argText StrOk space GrowsK grows_split
  growsK_elim forall2_imp keeps_refl keeps_alloc)
open EquivLean.Modernize.Cbstm03a.Java

namespace EquivLean.Modernize.Cbstm03a.Java.Seg3

/-- The loop state with other locals changed. -/
theorem xctx_frame {g : RunG} {σ0 : State} {fr fr' : Frame} {σ : State} {res ld ls lh : Addr} {o : JOut}
    {L : LdSt} {j : Nat} (hX : XCtx g σ0 fr σ res ld ls lh o L j)
    (hfr : ∀ k, k ∈ xLocals → fr'.get k = fr.get k) : XCtx g σ0 fr' σ res ld ls lh o L j := by
  obtain ⟨t1, t2, t3k, t3, t4, mem, trct, st2, -, -, -, h2, hst2, -⟩ := id hX
  exact xctx_keeps_st2 hX h2 (keeps_refl _ _) hst2 hfr rfl rfl

/-- The loop state after an allocation, other locals changed. -/
theorem xctx_alloc {g : RunG} {σ0 : State} {fr fr' : Frame} {σ : State} {res ld ls lh : Addr} {o : JOut}
    {L : LdSt} {j : Nat} {ob : Obj} (hX : XCtx g σ0 fr σ res ld ls lh o L j)
    (hfr : ∀ k, k ∈ xLocals → fr'.get k = fr.get k) : XCtx g σ0 fr' (σ.alloc ob).2 res ld ls lh o L j := by
  obtain ⟨t1, t2, t3k, t3, t4, mem, trct, st2, -, -, -, h2, hst2, -⟩ := id hX
  exact xctx_keeps_st2 hX h2 (keeps_alloc _ _ _) (heap_alloc_eq (State.lt_next_of_heap hst2) hst2) hfr rfl rfl

theorem xrecLocs_frame {σ : State} {fr fr' : Frame} {x : JStr} (h : XrecLocs σ fr x)
    (h32 : fr'.get 32 = fr.get 32) (h34 : fr'.get 34 = fr.get 34) (h33 : fr'.get 33 = fr.get 33) :
    XrecLocs σ fr' x := by
  obtain ⟨⟨a, ha, ha'⟩, ⟨b, hb, hb'⟩, ⟨c, hc, hc'⟩⟩ := h
  exact ⟨⟨a, h32.trans ha, ha'⟩, ⟨b, h34.trans hb, hb'⟩, ⟨c, h33.trans hc, hc'⟩⟩

theorem xrecLocs_alloc {σ : State} {fr fr' : Frame} {x : JStr} {ob : Obj} (h : XrecLocs σ fr x)
    (h32 : fr'.get 32 = fr.get 32) (h34 : fr'.get 34 = fr.get 34) (h33 : fr'.get 33 = fr.get 33) :
    XrecLocs (σ.alloc ob).2 fr' x := by
  obtain ⟨⟨a, ha, ha'⟩, ⟨b, hb, hb'⟩, ⟨c, hc, hc'⟩⟩ := h
  exact ⟨⟨a, h32.trans ha, heap_alloc_eq (State.lt_next_of_heap ha') ha'⟩,
    ⟨b, h34.trans hb, heap_alloc_eq (State.lt_next_of_heap hb') hb'⟩,
    ⟨c, h33.trans hc, heap_alloc_eq (State.lt_next_of_heap hc') hc'⟩⟩

theorem resAtL_alloc {σ : State} {ob : Obj} {res ld ls lh : Addr} {d s h : List JStr} {ab : Bool}
    (hr : ResAtL σ res ld ls lh d s h ab) : ResAtL (σ.alloc ob).2 res ld ls lh d s h ab :=
  resAtL_on (P := fun _ => True) ⟨by rw [State.next_alloc]; exact Nat.le_succ _,
    fun y o hy _ => heap_alloc_eq (State.lt_next_of_heap hy) hy⟩ (fun _ => trivial) (fun _ _ => trivial)
    (fun _ => trivial) hr

theorem resAtL_disp {σ : State} {res ld ls lh : Addr} {d d' s h : List JStr} {ab : Bool}
    (hr : ResAtL σ res ld ls lh d s h ab) (hd : d = d') : ResAtL σ res ld ls lh d' s h ab := hd ▸ hr

theorem toInt_add_one32 {i : I32} (h0 : 0 ≤ i.toInt) (h : i.toInt < 2147483647) :
    (i + 1).toInt = i.toInt + 1 := by
  have h1 : (1 : BitVec 32).toInt = 1 := by decide
  rw [BitVec.toInt_add, h1]
  exact Int.bmod_eq_of_le (by simp only [Nat.reducePow, Nat.cast_ofNat]; omega)
    (by simp only [Nat.reducePow, Nat.cast_ofNat]; omega)

theorem crs_len_lt {g : RunG} {args : List Value} {σ0 : State} (hpre : RunPre g args σ0) :
    g.crs.length < 2147483648 := by
  obtain ⟨-, -, -, hR3, -⟩ := hpre
  exact recsAt_len hR3

theorem ars_len_lt {g : RunG} {args : List Value} {σ0 : State} (hpre : RunPre g args σ0) :
    g.ars.length < 2147483648 := by
  obtain ⟨-, -, -, -, hR4, -⟩ := hpre
  exact recsAt_len hR4

/-! ## The model's step for record `j` -/

theorem model_cust_none {g : RunG} {L : LdSt} {o : JOut} {j : Nat} (hj : j < g.T2.length)
    (hm : xrefAll g.K3 g.T3 g.T4 L o (g.T2.drop j) = g.F)
    (hc : custFind g.K3 g.T3 (sub (fixStr (g.T2.getD j []) 1000) 16 25) = none) :
    g.F = o.abend (jl "ERROR READING CUSTFILE") (jl "23") := by
  rw [← hm, drop_getD_cons [] hj]
  simp only [xrefAll, xrefStep, hc]

theorem model_acct_none {g : RunG} {L : LdSt} {o : JOut} {j : Nat} {crec : JStr} (hj : j < g.T2.length)
    (hm : xrefAll g.K3 g.T3 g.T4 L o (g.T2.drop j) = g.F)
    (hc : custFind g.K3 g.T3 (sub (fixStr (g.T2.getD j []) 1000) 16 25) = some crec)
    (ha : acctFind g.T4 (sub (fixStr (g.T2.getD j []) 1000) 25 36) = none) :
    g.F = o.abend (jl "ERROR READING ACCTFILE") (jl "23") := by
  rw [← hm, drop_getD_cons [] hj]
  simp only [xrefAll, xrefStep, hc, ha]

theorem argText_lit1 (σ : State) (s1 s2 : JStr) :
    argText ((σ.alloc (.str s1)).2.alloc (.str s2)).2 (.ref σ.next) = s1 := by
  simp [argText, strOf, State.heap_alloc, State.next_alloc]

theorem argText_lit2 (σ : State) (s1 s2 : JStr) :
    argText ((σ.alloc (.str s1)).2.alloc (.str s2)).2 (.ref (σ.next + 1)) = s2 := by
  simp [argText, strOf, State.heap_alloc, State.next_alloc]

theorem initC_of {g : RunG} {args : List Value} {σ0 σ : State} (hpre : RunPre g args σ0)
    (h : σ.inits = σ0.inits) : σ.initOf "Cbstm03a" = .done := by
  obtain ⟨-, -, -, -, -, hcp, -⟩ := hpre
  rw [State.initOf_eq_of_inits h]; exact hcp.1

end EquivLean.Modernize.Cbstm03a.Java.Seg3
