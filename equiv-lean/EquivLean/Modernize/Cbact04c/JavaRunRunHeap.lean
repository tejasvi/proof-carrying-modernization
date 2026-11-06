import EquivLean.Modernize.Cbact04c.JavaRunRunLemmas

/-!
# CBACT04C → Java: the loop's heap invariant along the statements of an iteration

`CoreHeap` and `LoopHeap` are kept by the heap growing (`Grows`: allocations, callees) and
updated by the writes of `run`: a line added to the display list, a record added to the write or
rewrite list, an account stored into the table copy, a field of the current account or of the
transaction object set.
-/

open Jimple EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbact04c.Java

/-! ## Distinct objects -/

theorem ne_of_heap_list_plain {σ : State} {a b : Addr} {k : ListKind} {xs : List Value} {m : Nat}
    {c : ClassName} {fs : List (FieldKey × Value)} (ha : σ.heap a = some (.list k xs m))
    (hb : σ.heap b = some (.plain c fs)) : b ≠ a := by
  intro e; subst e; rw [ha] at hb; cases hb

theorem noStr_list {σ : State} {l : Addr} {k : ListKind} {xs : List Value} {m : Nat}
    (hl : σ.heap l = some (.list k xs m)) : NoStr σ [l] := by
  intro w hw s hs
  rw [List.mem_singleton] at hw; subst hw
  rw [hl] at hs; cases hs

/-! ## The heap grows -/

theorem jstrAt_grows {σ σ' : State} {v : Value} {s : JStr} (hg : Grows σ σ') (h : JStrAt σ v s) :
    JStrAt σ' v s := jstrAt_agree h (agree_of_grows [] hg) (fun _ h => absurd h List.not_mem_nil)

theorem jrecAt_grows {s : Schema} {cls : ClassName} {σ σ' : State} {v : Value}
    {vals : List FV} (hg : Grows σ σ') (h : JRecAt s cls σ v vals) : JRecAt s cls σ' v vals := by
  have h' := h
  obtain ⟨x, fs, rfl, -⟩ := h'
  exact jrecAt_agree h (agree_of_grows [] hg) (fun _ h => absurd h List.not_mem_nil) List.not_mem_nil

theorem tranOk_grows {σ σ' : State} {T : Addr} (hg : Grows σ σ') (h : TranOk σ T) : TranOk σ' T := by
  obtain ⟨fs, h1, h2, ⟨d, s, h3, h4, h5, h6⟩, ⟨f, h7, h8⟩⟩ := h
  exact ⟨fs, heap_of_grows hg h1, h2, ⟨d, s, h3, heap_of_grows hg h4, h5, h6⟩,
    ⟨f, h7, heap_of_grows hg h8⟩⟩

theorem inits_of_eq {σ σ' : State} (h : σ'.inits = σ.inits) (hi : Inits σ) : Inits σ' := by
  unfold Inits State.initOf at *
  rw [h]
  exact hi

theorem coreHeap_grows {g : G} {σ0 σ σ' : State} {h : Hp} {s : Model.St} {M : List Addr}
    (hc : CoreHeap g σ0 σ h s M) (hg : Grows σ σ') (hi : σ'.inits = σ.inits) :
    CoreHeap g σ0 σ' h s M := by
  obtain ⟨hg0, hin, hfr, hres, hdisp, hw, hr, ht, htr, hp, hcl⟩ := hc
  have ha := agree_of_grows ([] : List Addr) hg
  have hn : NoStr σ [] := fun _ h => absurd h List.not_mem_nil
  refine ⟨grows_trans hg0 hg, ?_, hfr, resAt_agree hres ha List.not_mem_nil,
    dispAt_agree hdisp ha hn List.not_mem_nil,
    recsAt_agree hw ha hn List.not_mem_nil (fun _ h => absurd h List.not_mem_nil),
    recsAt_agree hr ha hn List.not_mem_nil (fun _ h => absurd h List.not_mem_nil),
    tableAt_agree ht ha hn List.not_mem_nil (fun _ h => absurd h List.not_mem_nil),
    tranOk_grows hg htr, jstrAt_grows hg hp, jstrAt_grows hg hcl⟩
  exact inits_of_eq hi hin

theorem loopHeap_grows {g : G} {σ0 σ σ' : State} {h : Hp} {s : Model.St} {acctV xrefV lastV : Value}
    (hL : LoopHeap g σ0 σ h s acctV xrefV lastV) (hg : Grows σ σ') (hi : σ'.inits = σ.inits) :
    LoopHeap g σ0 σ' h s acctV xrefV lastV := by
  obtain ⟨hc, ha, hx, hl, hf⟩ := hL
  exact ⟨coreHeap_grows hc hg hi, fun h' => jrecAt_grows hg (ha h'), fun h' => jrecAt_grows hg (hx h'),
    jstrAt_grows hg hl, hf⟩

/-! ## A write to one of the lists -/

/-- Writing the list object `l` (no string, no record object) keeps the facts about the other
objects. -/
theorem jrecAt_setObj_list {s : Schema} {cls : ClassName} {σ : State} {l : Addr} {k : ListKind}
    {xs : List Value} {m : Nat} {o : Obj} {v : Value} {vals : List FV}
    (hl : σ.heap l = some (.list k xs m)) (h : JRecAt s cls σ v vals) :
    JRecAt s cls (σ.setObj l o) v vals := by
  have h' := h
  obtain ⟨x, fs, rfl, hx, -⟩ := h'
  exact jrecAt_agree h (agree_setObj_mem (agree_refl σ [l]) (List.mem_singleton_self l) o)
    (noStr_list hl) (by rw [List.mem_singleton]; exact ne_of_heap_list_plain hl hx)

theorem jstrAt_setObj_list {σ : State} {l : Addr} {k : ListKind} {xs : List Value} {m : Nat}
    {o : Obj} {v : Value} {str : JStr} (hl : σ.heap l = some (.list k xs m)) (h : JStrAt σ v str) :
    JStrAt (σ.setObj l o) v str :=
  jstrAt_agree h (agree_setObj_mem (agree_refl σ [l]) (List.mem_singleton_self l) o) (noStr_list hl)

theorem heap_setObj_other {σ : State} {l x : Addr} {o : Obj} (h : x ≠ l) :
    (σ.setObj l o).heap x = σ.heap x := by
  rw [State.heap_setObj, ite_eq_right h]

theorem heap_setObj_self' {σ : State} {l : Addr} {o o' : Obj} (h : σ.heap l = some o') :
    (σ.setObj l o).heap l = some o := by
  rw [State.heap_setObj, if_pos rfl, if_pos (State.lt_next_of_heap h)]

theorem recsAt_setObj_list {s : Schema} {cls : ClassName} {σ : State} {l l' : Addr} {k : ListKind}
    {xs : List Value} {m : Nat} {o : Obj} {vals : List (List FV)} {M : List Addr}
    (hl : σ.heap l = some (.list k xs m)) (hne : l' ≠ l) (h : RecsAt s cls σ l' vals M) :
    RecsAt s cls (σ.setObj l o) l' vals M := by
  obtain ⟨ys, n, h1, h2, h3⟩ := h
  refine ⟨ys, n, by rw [heap_setObj_other hne, h1], ?_, h3⟩
  exact forall2_mono (fun _ _ h => jrecAt_setObj_list hl h) h2

theorem tableAt_setObj_list {σ : State} {l A : Addr} {k : ListKind} {xs : List Value} {m : Nat}
    {o : Obj} {accts : List (List FV)} {M : List Addr} (hl : σ.heap l = some (.list k xs m))
    (h : TableAt σ A accts M) : TableAt (σ.setObj l o) A accts M := by
  obtain ⟨ys, h1, h2, h3⟩ := h
  have hne : A ≠ l := by intro e; subst e; rw [hl] at h1; cases h1
  exact ⟨ys, by rw [heap_setObj_other hne, h1], forall2_mono (fun _ _ h => jrecAt_setObj_list hl h) h2, h3⟩

theorem tranOk_setObj_list {σ : State} {l T : Addr} {k : ListKind} {xs : List Value} {m : Nat}
    {o : Obj} (hl : σ.heap l = some (.list k xs m)) (h : TranOk σ T) : TranOk (σ.setObj l o) T := by
  obtain ⟨fs, h1, h2, ⟨d, str, h3, h4, h5, h6⟩, ⟨f, h7, h8⟩⟩ := h
  have hT : T ≠ l := ne_of_heap_list_plain hl h1
  have hd : d ≠ l := by intro e; subst e; rw [hl] at h4; cases h4
  have hf : f ≠ l := by intro e; subst e; rw [hl] at h8; cases h8
  exact ⟨fs, by rw [heap_setObj_other hT, h1], h2, ⟨d, str, h3, by rw [heap_setObj_other hd, h4], h5, h6⟩,
    ⟨f, h7, by rw [heap_setObj_other hf, h8]⟩⟩

theorem resAt_setObj_list {σ : State} {l : Addr} {k : ListKind} {xs : List Value} {m : Nat}
    {o : Obj} {h : Hp} (hl : σ.heap l = some (.list k xs m)) (hr : ResAt σ h) : ResAt (σ.setObj l o) h := by
  obtain ⟨fs, h1, h2⟩ := hr
  exact ⟨fs, by rw [heap_setObj_other (ne_of_heap_list_plain hl h1), h1], h2⟩

/-- A line added to the display list. -/
theorem loopHeap_disp_add {g : G} {σ0 σ σ1 : State} {h : Hp} {s : Model.St}
    {acctV xrefV lastV v : Value} {xs : List Value} {m : Nat} {line : List Nat}
    (hL : LoopHeap g σ0 σ h s acctV xrefV lastV) (hld : σ.heap h.ld = some (.list .arrayList xs m))
    (hg : Grows σ σ1) (hi : σ1.inits = σ.inits) (hv : JStrAt σ1 v (jline line)) :
    LoopHeap g σ0 (σ1.setObj h.ld (.list .arrayList (xs ++ [v]) (m + 1))) h
      { s with disp := s.disp ++ [line] } acctV xrefV lastV := by
  obtain ⟨⟨hg0, hin, hfr, hres, hdisp, hw, hr, ht, htr, hp, hcl⟩, ha, hx, hla, hfa⟩ :=
    loopHeap_grows hL hg hi
  have hld1 : σ1.heap h.ld = some (.list .arrayList xs m) := heap_of_grows hg hld
  obtain ⟨xs', m', hld', hxs'⟩ := hdisp
  rw [hld1] at hld'
  simp only [Option.some.injEq, Obj.list.injEq, true_and] at hld'
  obtain ⟨rfl, rfl⟩ := hld'
  obtain ⟨h0r, h0d, h0w, h0l, h0A, h0T, hdw, hdl, hwl⟩ := hfr
  refine ⟨⟨grows_setObj hg0 h0d, inits_of_eq rfl hin, ⟨h0r, h0d, h0w, h0l, h0A, h0T, hdw, hdl, hwl⟩,
    resAt_setObj_list hld1 hres, ⟨xs ++ [v], m + 1, heap_setObj_self' hld1, ?_⟩,
    recsAt_setObj_list hld1 (Ne.symm hdw) hw, recsAt_setObj_list hld1 (Ne.symm hdl) hr,
    tableAt_setObj_list hld1 ht, tranOk_setObj_list hld1 htr, jstrAt_setObj_list hld1 hp,
    jstrAt_setObj_list hld1 hcl⟩,
    fun h' => jrecAt_setObj_list hld1 (ha h'), fun h' => jrecAt_setObj_list hld1 (hx h'),
    jstrAt_setObj_list hld1 hla, hfa⟩
  simp only [List.map_append, List.map_cons, List.map_nil]
  exact forall2_append (jstrAt_setObj_list hld1 hv)
    (forall2_mono (fun _ _ h => jstrAt_setObj_list hld1 h) hxs')

/-! ## The exit: the end line, the `Result` -/

theorem jstrAt_alloc {σ : State} {o : Obj} {v : Value} {str : JStr} (h : JStrAt σ v str) :
    JStrAt (σ.alloc o).2 v str := jstrAt_grows (grows_alloc σ o) h

theorem jrecAt_alloc {s : Schema} {cls : ClassName} {σ : State} {o : Obj} {v : Value}
    {vals : List FV} (h : JRecAt s cls σ v vals) : JRecAt s cls (σ.alloc o).2 v vals :=
  jrecAt_grows (grows_alloc σ o) h

/-- **The postcondition**, after the last record: the end line added to the display list. -/
theorem runPost_exit {g : G} {σ0 σ : State} {h : Hp} {acctV xrefV lastV : Value} {dxs : List Value}
    {dm : Nat} {es : JStr}
    (hL : LoopHeap g σ0 σ h (g.st g.tcat.length) acctV xrefV lastV)
    (hld : σ.heap h.ld = some (.list .arrayList dxs dm))
    (hes : es = jline (Model.txt "END OF EXECUTION OF PROGRAM CBACT04C")) :
    RunPostG g (some (.ref h.res))
      (((σ.alloc (.str es)).2).setObj h.ld (.list .arrayList (dxs ++ [.ref σ.next]) (dm + 1))) := by
  obtain ⟨⟨hg0, hin, hfr, ⟨fsR, hR, hRd, hRw, hRr, hRa⟩, hdisp, ⟨wxs, wm, hlw, hw, -⟩,
    ⟨rxs, rm, hlr, hr, -⟩, -⟩, -⟩ := hL
  obtain ⟨xs', m', hld', hxs'⟩ := hdisp
  rw [hld] at hld'
  simp only [Option.some.injEq, Obj.list.injEq, true_and] at hld'
  obtain ⟨rfl, rfl⟩ := hld'
  obtain ⟨-, -, -, -, -, -, hdw, hdl, -⟩ := hfr
  have hld1 : (σ.alloc (.str es)).2.heap h.ld = some (.list .arrayList dxs dm) := by
    rw [State.heap_alloc, ite_eq_right (State.ne_next_of_heap hld)]; exact hld
  have hR1 : (σ.alloc (.str es)).2.heap h.res = some (.plain "Cbact04c$Result" fsR) := by
    rw [State.heap_alloc, ite_eq_right (State.ne_next_of_heap hR)]; exact hR
  have hlw1 : (σ.alloc (.str es)).2.heap h.lw = some (.list .arrayList wxs wm) := by
    rw [State.heap_alloc, ite_eq_right (State.ne_next_of_heap hlw)]; exact hlw
  have hlr1 : (σ.alloc (.str es)).2.heap h.lr = some (.list .arrayList rxs rm) := by
    rw [State.heap_alloc, ite_eq_right (State.ne_next_of_heap hlr)]; exact hlr
  refine ⟨h.res, fsR, h.ld, .arrayList, dxs ++ [.ref σ.next], dm + 1, h.lw, .arrayList, wxs, wm,
    h.lr, .arrayList, rxs, rm, rfl, ?_, hRd, heap_setObj_self' hld1, ?_, hRw, ?_, ?_, hRr, ?_, ?_,
    hRa⟩
  · rw [heap_setObj_other (ne_of_heap_list_plain hld1 hR1)]; exact hR1
  · rw [G.out_eq]
    simp only [List.map_append, List.map_cons, List.map_nil]
    refine forall2_append ⟨σ.next, rfl, ?_⟩
      (forall2_mono (fun _ _ hh => jstrAt_setObj_list hld1 (jstrAt_alloc hh)) hxs')
    rw [heap_setObj_other (State.ne_next_of_heap hld).symm, State.heap_alloc, if_pos rfl, hes]
  · rw [heap_setObj_other (Ne.symm hdw)]; exact hlw1
  · rw [G.out_eq]
    exact forall2_mono (fun _ _ hh => jrecAt_setObj_list hld1 (jrecAt_alloc hh)) hw
  · rw [heap_setObj_other (Ne.symm hdl)]; exact hlr1
  · rw [G.out_eq]
    exact forall2_mono (fun _ _ hh => jrecAt_setObj_list hld1 (jrecAt_alloc hh)) hr

end EquivLean.Modernize.Cbact04c.Java
