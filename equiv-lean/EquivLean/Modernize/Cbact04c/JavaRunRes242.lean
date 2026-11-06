import EquivLean.Modernize.Cbact04c.JavaRunRes232

/-!
# CBACT04C → Java, `run`: closing the loop at 85 after a transaction write
-/

open Jimple EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbact04c.Java

/-- The model state after a record with a nonzero rate: the transaction is written. -/
theorem st_succ_write {g : G} {n : Nat} (hn : n < g.tcat.length) (hr : rateOf g n ≠ 0) :
    g.st (n + 1) =
      { (sel g n) with total := totOf g n, k := kOf g n, writes := (sel g n).writes ++ [tvals g n] } := by
  rw [st_succ_eq g hn]
  have hr' : Model.dRate (discOf g (stSel g.xrefs (g.st n) (g.trec n)) (g.trec n)) ≠ 0 := hr
  unfold stFin
  rw [if_neg hr']
  rfl

/-- One more transaction record in the write list (after a callee that grew the heap). -/
theorem loopHeap_writes_add {g : G} {σ0 σ σ1 : State} {h : Hp} {s : Model.St}
    {acctV xrefV lastV v : Value} {xs : List Value} {m : Nat} {p : List FV} (t' : Int) (k' : Nat)
    (hL : LoopHeap g σ0 σ h s acctV xrefV lastV) (hlw : σ.heap h.lw = some (.list .arrayList xs m))
    (hg : Grows σ σ1) (hi : σ1.inits = σ.inits)
    (hv : JRecAt TranRecord "Cbact04c$TranRecord" σ1 v p) (hvT : ∀ a, v = .ref a → a ∉ [h.T]) :
    LoopHeap g σ0 (σ1.setObj h.lw (.list .arrayList (xs ++ [v]) (m + 1))) h
      { s with total := t', k := k', writes := s.writes ++ [p] } acctV xrefV lastV := by
  obtain ⟨⟨hg0, hin, hfr, hres, hdisp, hw, hr, ht, htr, hp, hcl⟩, ha, hx, hla, hfa⟩ :=
    loopHeap_grows hL hg hi
  have hlw1 : σ1.heap h.lw = some (.list .arrayList xs m) := heap_of_grows hg hlw
  obtain ⟨xs', m', hlw', hxs', hT'⟩ := hw
  rw [hlw1] at hlw'
  simp only [Option.some.injEq, Obj.list.injEq, true_and] at hlw'
  obtain ⟨rfl, rfl⟩ := hlw'
  obtain ⟨h0r, h0d, h0w, h0l, h0A, h0T, hdw, hdl, hwl⟩ := hfr
  refine ⟨⟨grows_setObj hg0 h0w, inits_of_eq rfl hin, ⟨h0r, h0d, h0w, h0l, h0A, h0T, hdw, hdl, hwl⟩,
    resAt_setObj_list hlw1 hres, ?_, ⟨xs ++ [v], m + 1, heap_setObj_self' hlw1, ?_, ?_⟩,
    recsAt_setObj_list hlw1 (Ne.symm hwl) hr,
    tableAt_setObj_list hlw1 ht, tranOk_setObj_list hlw1 htr, jstrAt_setObj_list hlw1 hp,
    jstrAt_setObj_list hlw1 hcl⟩,
    fun h' => jrecAt_setObj_list hlw1 (ha h'), fun h' => jrecAt_setObj_list hlw1 (hx h'),
    jstrAt_setObj_list hlw1 hla, hfa⟩
  · obtain ⟨dxs, dm, hld, hdd⟩ := hdisp
    exact ⟨dxs, dm, by rw [heap_setObj_other hdw, hld],
      forall2_mono (fun _ _ hh => jstrAt_setObj_list hlw1 hh) hdd⟩
  · exact forall2_append (jrecAt_setObj_list hlw1 hv)
      (forall2_mono (fun _ _ hh => jrecAt_setObj_list hlw1 hh) hxs')
  · intro w hw' a ha'
    rcases List.mem_append.1 hw' with hm | hm
    · exact hT' w hm a ha'
    · rw [List.mem_singleton] at hm
      subst hm
      exact hvT a ha'

/-- The copy of `T` holds the transaction record. -/
theorem tvals_rec {g : G} {σ σ1 : State} {T y : Addr} {fsT fs' : List (FieldKey × Value)} {n : Nat}
    (hset : TranSet σ T 13 (tvals g n)) (hT : σ.heap T = some (.plain "Cbact04c$TranRecord" fsT))
    (htr : TranOk σ T) (hg : Grows σ σ1) (hy : σ1.heap y = some (.plain "Cbact04c$TranRecord" fs'))
    (hk : ∀ k ∈ keysRC, Fields.get fs' ("Cbact04c$TranRecord", k) =
      Fields.get (fieldsOf σ T) ("Cbact04c$TranRecord", k)) :
    JRecAt TranRecord "Cbact04c$TranRecord" σ1 (.ref y) (tvals g n) := by
  obtain ⟨fs0, h1, -, -, ⟨f, h7, h8⟩⟩ := htr
  rw [hT] at h1
  cases h1
  have hl := tvals_length g n
  have h14 := tranSet_extend hset hT (by decide) hl (by
    refine ⟨.ref f, h7, f, rfl, ?_⟩
    try simp only [tvals, Model.tranVals, List.getD_cons_succ, List.getD_cons_zero]
    rw [cp037Str_sp]
    exact h8)
  obtain ⟨fs1, h1', h2'⟩ := h14
  rw [hT] at h1'
  cases h1'
  have hfl : TranRecord.fields.length = 14 := by decide
  rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega)] at h2'
  have hmap : TranRecord.fields.map (·.jname) = keysRC := by decide
  refine ⟨y, fs', rfl, hy, forall2_jfield_copy (strKeep_of_grows hg) h2' (fun f hf => ?_)⟩
  have hm : f.jname ∈ keysRC := by rw [← hmap]; exact List.mem_map_of_mem hf
  rw [hk f.jname hm, fieldsOf_eq hT]

/-- The cut at 85 for the next record, after the transaction of record `i` was written. -/
theorem j85_of_write {g : G} {σ0 σ σ1 : State} {fr' : Frame} {i : I32} {hp : Hp}
    {acctV xrefV lastV : Value} {fsT fs' : List (FieldKey × Value)} {y : Addr}
    {wxs : List Value} {wm : Nat}
    (hn : i.toInt.toNat < g.tcat.length) (hi0 : 0 ≤ i.toInt) (hlen : g.tcat.length < 2147483647)
    (hheap : Hide (LoopHeap g σ0 σ hp (sel g i.toInt.toNat) acctV xrefV lastV))
    (hrate : rateOf g i.toInt.toNat ≠ 0)
    (hset : Hide (TranSet σ hp.T 13 (tvals g i.toInt.toNat)))
    (hT : σ.heap hp.T = some (.plain "Cbact04c$TranRecord" fsT))
    (hlw : σ.heap hp.lw = some (.list .arrayList wxs wm))
    (hy0 : σ.next ≤ y) (hy : σ1.heap y = some (.plain "Cbact04c$TranRecord" fs'))
    (hk : ∀ k ∈ keysRC, Fields.get fs' ("Cbact04c$TranRecord", k) =
      Fields.get (fieldsOf σ hp.T) ("Cbact04c$TranRecord", k))
    (hg : Grows σ σ1) (hi : σ1.inits = σ.inits)
    (hlocs : Locs g hp fr')
    (f22 : fr'.get 22 = some (.int (i + 1#32)))
    (f12 : fr'.get 12 = some (.long (BitVec.ofInt 64 (totOf g i.toInt.toNat))))
    (f3 : fr'.get 3 = some (.int 0#32))
    (f14 : fr'.get 14 = some (.long (BitVec.ofNat 64 (kOf g i.toInt.toNat))))
    (f25 : fr'.get 25 = some lastV) (f16 : fr'.get 16 = some acctV)
    (f17 : fr'.get 17 = some xrefV) (f4 : fr'.get 4 = some (.int 0#32))
    (f5 : fr'.get 5 = some (.int 0#32)) :
    J85 g g.args σ0 fr' (σ1.setObj hp.lw (.list .arrayList (wxs ++ [.ref y]) (wm + 1))) := by
  have hL := Hide.elim hheap
  obtain ⟨-, -, -, -, -, -, -, -, htr, -⟩ := hL.1
  have hE := st_succ_write hn hrate
  have hsome : (g.st (i.toInt.toNat + 1)).lastId.isSome := by
    rw [hE]
    show (sel g i.toInt.toNat).lastId.isSome
    rw [sel, stSel_lastId]
    rfl
  have hrec := tvals_rec (Hide.elim hset) hT htr hg hy hk
  have hTn := State.lt_next_of_heap hT
  have hL2 := loopHeap_writes_add (totOf g i.toInt.toNat) (kOf g i.toInt.toNat) hL hlw hg hi hrec
    (fun a ha hm => by
      cases ha
      rw [List.mem_singleton] at hm
      subst hm
      jomega)
  refine j85_of hn hi0 hlen hlocs f22 ?_ f3 hsome ?_ f25 f16 f17 f4 f5 ?_
  · rw [hE]; exact f12
  · rw [hE]; exact f14
  · rw [hE]; exact Hide.intro hL2

end EquivLean.Modernize.Cbact04c.Java
