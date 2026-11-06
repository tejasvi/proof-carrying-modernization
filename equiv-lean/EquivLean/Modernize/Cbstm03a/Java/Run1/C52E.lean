import EquivLean.Modernize.Cbstm03a.Java.Run1.C52
import EquivLean.Modernize.Cbstm03a.Java.Run1.VCut

/-!
# CBSTM03A → Java `run`: the ACCTFILE loop's exit (cut point 52, statements 58 … 79) and `run_cut52_vc`

The exit is split at a virtual cut point (`bodyWP_vcut`) right after the first `seqRead` (statement 63,
assertion `a63`): `jvc` instantiates `seqRead`'s postcondition (heap premises at the call state, five binders) only
when the call state is a variable. Then either the first transaction is read (status `00`: `fix`, the record and
its card number, `inv80`) or there is none (status `10`: `abend`, `run`'s result).
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows Keeps fixStr zpadStr argText StrOk space grows_refl grows_trans
  grows_split fixStr_length keeps_alloc keeps_setObj keeps_trans GrowsK growsK_elim heap_grows)

namespace EquivLean.Modernize.Cbstm03a.Java.Seg1

/-! ## Frames -/

theorem runBase_grows {g : RunG} {σ0 σ σ' : State} {fr fr' : Frame} {res ld ls lh : Addr}
    (hb : RunBase g σ0 fr σ res ld ls lh JOut.init) (hg : Grows σ σ') (hi : σ'.inits = σ.inits)
    (hs : σ'.statics = σ.statics)
    (f10 : fr'.get 10 = fr.get 10) (f23 : fr'.get 23 = fr.get 23)
    (f9 : fr'.get 9 = fr.get 9) (f6 : fr'.get 6 = fr.get 6) (f7 : fr'.get 7 = fr.get 7) :
    RunBase g σ0 fr' σ' res ld ls lh JOut.init := by
  obtain ⟨g10, g23, g9, g6, g7, hR, r0, l0, s0, h0, hg0, hi0, hs0⟩ := hb
  have hR' := hR
  obtain ⟨fs, hr, -, -, -, -, -, -, -, ⟨xd, md, hd, -⟩, ⟨xs', ms, hls, -⟩, ⟨xh, mh, hlh, -⟩⟩ := hR'
  exact ⟨f10.trans g10, f23.trans g23, f9.trans g9, f6.trans g6, f7.trans g7,
    resAtL_init_of_heap hR (hg.2 _ (State.lt_next_of_heap hr)) (hg.2 _ (State.lt_next_of_heap hd))
      (hg.2 _ (State.lt_next_of_heap hls)) (hg.2 _ (State.lt_next_of_heap hlh)), r0, l0, s0, h0,
    grows_trans hg0 hg, hi.trans hi0, hs.trans hs0⟩

theorem textsAt_grows {σ σ' : State} {a : Addr} {ts : List JStr} {n : Nat} (h : TextsAt σ a ts n)
    (hg : Grows σ σ') : TextsAt σ' a ts n := by
  obtain ⟨xs, hx, hf⟩ := h
  exact ⟨xs, by rw [hg.2 a (State.lt_next_of_heap hx)]; exact hx, forall2_jstr_mono hf (strMono_of_grows hg)⟩

theorem runTexts_grows {g : RunG} {σ0 σ σ' : State} {fr fr' : Frame} {t1 t2 t3k t3 t4 : Addr}
    (h : RunTexts g σ0 fr σ t1 t2 t3k t3 t4) (hg : Grows σ σ')
    (f11 : fr'.get 11 = fr.get 11) (f12 : fr'.get 12 = fr.get 12) (f13 : fr'.get 13 = fr.get 13)
    (f14 : fr'.get 14 = fr.get 14) (f15 : fr'.get 15 = fr.get 15) (f27 : fr'.get 27 = fr.get 27)
    (f28 : fr'.get 28 = fr.get 28) : RunTexts g σ0 fr' σ' t1 t2 t3k t3 t4 := by
  obtain ⟨g11, g12, g13, g14, g15, ⟨n3, g27, hn3⟩, ⟨n4, g28, hn4⟩, h1, h2, h3, h4, h5, o1, o2, o3, o4, o5⟩ := h
  exact ⟨f11.trans g11, f12.trans g12, f13.trans g13, f14.trans g14, f15.trans g15, ⟨n3, f27.trans g27, hn3⟩,
    ⟨n4, f28.trans g28, hn4⟩, textsAt_grows h1 hg, textsAt_grows h2 hg, textsAt_grows h3 hg, textsAt_grows h4 hg,
    textsAt_grows h5 hg, o1, o2, o3, o4, o5⟩

theorem addr_lt1 (a : Addr) : a < a + 1 := Nat.lt_succ_self a
theorem addr_lt2 (a : Addr) : a < a + 1 + 1 := Nat.lt_succ_of_lt (Nat.lt_succ_self a)
theorem addr_lt3 (a : Addr) : a < a + 1 + 1 + 1 := Nat.lt_succ_of_lt (Nat.lt_succ_of_lt (Nat.lt_succ_self a))
theorem addr_le3 (a : Addr) : a ≤ a + 1 + 1 + 1 := Nat.le_of_lt (addr_lt3 a)

theorem alloc3_next {σ : State} {A B C : Obj} :
    (((σ.alloc A).2.alloc B).2.alloc C).2.next = σ.next + 1 + 1 + 1 := by
  simp only [State.next_alloc]

theorem alloc3_lt {σ : State} {A B C : Obj} {y : Addr} (hy : y < σ.next) :
    (((σ.alloc A).2.alloc B).2.alloc C).2.heap y = σ.heap y := by
  have h1 : y < (σ.alloc A).2.next := by rw [State.next_alloc]; exact Nat.lt_succ_of_lt hy
  have h2 : y < ((σ.alloc A).2.alloc B).2.next := by rw [State.next_alloc]; exact Nat.lt_succ_of_lt h1
  rw [State.heap_alloc_of_lt h2, State.heap_alloc_of_lt h1, State.heap_alloc_of_lt hy]

theorem alloc3_0 {σ : State} {A B C : Obj} : (((σ.alloc A).2.alloc B).2.alloc C).2.heap σ.next = some A := by
  have h1 : σ.next < (σ.alloc A).2.next := by rw [State.next_alloc]; exact Nat.lt_succ_self _
  have h2 : σ.next < ((σ.alloc A).2.alloc B).2.next := by rw [State.next_alloc]; exact Nat.lt_succ_of_lt h1
  rw [State.heap_alloc_of_lt h2, State.heap_alloc_of_lt h1, State.heap_alloc, if_pos rfl]

theorem alloc3_1 {σ : State} {A B C : Obj} :
    (((σ.alloc A).2.alloc B).2.alloc C).2.heap (σ.next + 1) = some B := by
  have h2 : σ.next + 1 < ((σ.alloc A).2.alloc B).2.next := by
    rw [State.next_alloc, State.next_alloc]; exact Nat.lt_succ_self _
  rw [State.heap_alloc_of_lt h2, State.heap_alloc, State.next_alloc, if_pos rfl]

theorem alloc3_2 {σ : State} {A B C : Obj} :
    (((σ.alloc A).2.alloc B).2.alloc C).2.heap (σ.next + 1 + 1) = some C := by
  rw [State.heap_alloc, State.next_alloc, State.next_alloc, if_pos rfl]

theorem slotsAt_nulls {σ : State} {a : Addr}
    (h : σ.heap a = some (.array (.cls "java.lang.String") (List.replicate 561 .null))) : SlotsAt σ a mem0 :=
  ⟨_, h, List.length_replicate, fun i hi => Or.inl ⟨by rw [List.getElem?_replicate, if_pos hi], fun _ _ => rfl⟩⟩

/-! ## Statement 63 (virtual) -/


/-- Statement 63 (virtual): the first `seqRead` done (`trnxSt` and the status string `x` as it leaves them). -/
def a63 (g : RunG) (σ0 : State) (fr : Frame) (σ : State) : Prop :=
  ∃ (res ld ls lh t1 t2 t3k t3 t4 mem trct st x : Addr),
    RunBase g σ0 fr σ res ld ls lh JOut.init ∧ RunTexts g σ0 fr σ t1 t2 t3k t3 t4 ∧
    fr.get 16 = some (.ref mem) ∧ fr.get 24 = some (.ref trct) ∧ fr.get 1 = some (.ref st) ∧
    fr.get 32 = some (.ref x) ∧
    σ.heap mem = some (.array (.cls "java.lang.String") (List.replicate 561 .null)) ∧
    σ.heap trct = some (.array (.prim .long) (List.replicate 51 (.long 0))) ∧
    σ.heap st = some (.array (.prim .int) (seqStArr 0 0 g.trs.length)) ∧
    σ.heap x = some (.str (seqCode 0 0 g.trs.length)) ∧
    t4 < mem ∧ mem < trct ∧ trct < st ∧ st < x

/-- Statements 58 … 62 end in `a63`: the arrays new, `spaces(1000)`, the first `seqRead`. -/
theorem c52_63_close {g : RunG} {σ0 σ σ1 σf : State} {fr : Frame}
    {res ld ls lh t1 t2 t3k t3 t4 w : Addr} {xs : List Value} {v : Option Value}
    (hb : RunBase g σ0 fr σ res ld ls lh JOut.init) (hRT : RunTexts g σ0 fr σ t1 t2 t3k t3 t4)
    (ht1 : σ.heap t1 = some (.array (.cls "java.lang.String") xs)) (hl1 : xs.length < 2147483648)
    (hxl : xs.length = g.trs.length) (ht4lt : t4 < σ.next)
    {LA LB LC : List Value} (hg1 : GrowsK (((σ.alloc (.array (.cls "java.lang.String") LA)).2.alloc
      (.array (.prim .long) LB)).2.alloc (.array (.prim .int) LC)).2 σ1)
    (hA : LA = List.replicate 561 .null) (hB : LB = List.replicate 51 (.long 0)) (hC : LC = [.int 0, .int 0])
    (hS : ∀ (a b : Addr) (txs : List Value) (i e : I32), t1 = a → σ.next + 1 + 1 = b →
        σ1.heap a = some (.array (.cls "java.lang.String") txs) → txs.length < 2147483648 →
        σ1.heap b = some (.array (.prim .int) [.int i, .int e]) →
        ∃ x, v = some (.ref x) ∧ σ1.next ≤ x ∧ σf.heap x = some (.str (seqCode i e txs.length)) ∧
          σf.heap b = some (.array (.prim .int) (seqStArr i e txs.length)) ∧
          Keeps (fun x => x = b) σ1 σf ∧ σf.inits = σ.inits ∧ σf.statics = σ.statics) :
    a63 g σ0 (((((fr.setLocal 16 (.ref σ.next)).setLocal 24 (.ref (σ.next + 1))).setLocal 1
        (.ref (σ.next + 1 + 1))).setLocal 33 (.ref w)).setLocal 32 (v.getD .null)) σf := by
  subst hA hB hC
  have hg1' := growsK_elim hg1
  have hlt1 : t1 < σ.next := State.lt_next_of_heap ht1
  have h2n := alloc3_next (σ := σ) (A := .array (.cls "java.lang.String") (List.replicate 561 .null))
    (B := .array (.prim .long) (List.replicate 51 (.long 0))) (C := .array (.prim .int) [.int 0, .int 0])
  have h3 : ∀ y, y < σ.next →
      y < (((σ.alloc (.array (.cls "java.lang.String") (List.replicate 561 .null))).2.alloc
        (.array (.prim .long) (List.replicate 51 (.long 0)))).2.alloc (.array (.prim .int) [.int 0, .int 0])).2.next :=
    fun y hy => by rw [h2n]; exact Nat.lt_trans hy (addr_lt3 _)
  have hσ1t1 : σ1.heap t1 = some (.array (.cls "java.lang.String") xs) := by
    rw [hg1'.2 t1 (h3 t1 hlt1), alloc3_lt hlt1, ht1]
  have hσ1st : σ1.heap (σ.next + 1 + 1) = some (.array (.prim .int) [.int 0, .int 0]) := by
    rw [hg1'.2 _ (by rw [h2n]; exact Nat.lt_succ_self _), alloc3_2]
  obtain ⟨x, hv, hxn, hx, hstf, hK, hinf, hstf'⟩ := hS t1 _ xs 0 0 rfl rfl hσ1t1 hl1 hσ1st
  have h1n : σ.next + 1 + 1 + 1 ≤ σ1.next := h2n ▸ hg1'.1
  have h0n : σ.next ≤ σ1.next := Nat.le_trans (addr_le3 _) h1n
  have hgr : Grows σ σf := ⟨Nat.le_trans h0n hK.1, fun y hy => by
    have hy1 : y < σ1.next := Nat.lt_of_lt_of_le hy h0n
    have hy2 : ¬ y = σ.next + 1 + 1 := fun e => absurd (e ▸ hy) (Nat.not_lt.mpr (Nat.le_of_lt (addr_lt2 _)))
    rw [hK.2 y hy1 hy2, hg1'.2 y (h3 y hy), alloc3_lt hy]⟩
  have hmem : σf.heap σ.next = some (.array (.cls "java.lang.String") (List.replicate 561 .null)) := by
    rw [hK.2 _ (Nat.lt_of_lt_of_le (addr_lt3 _) h1n) (Nat.ne_of_lt (addr_lt2 _)),
      hg1'.2 _ (by rw [h2n]; exact addr_lt3 _), alloc3_0]
  have htrct : σf.heap (σ.next + 1) = some (.array (.prim .long) (List.replicate 51 (.long 0))) := by
    rw [hK.2 _ (Nat.lt_of_lt_of_le (addr_lt2 _) h1n) (Nat.ne_of_lt (addr_lt1 _)),
      hg1'.2 _ (by rw [h2n]; exact addr_lt2 _), alloc3_1]
  have hstx : σ.next + 1 + 1 < x := Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (addr_lt1 _) h1n) hxn
  have hstf2 : σf.heap (σ.next + 1 + 1) = some (.array (.prim .int) (seqStArr 0 0 g.trs.length)) := by
    rw [← hxl]; exact hstf
  have hx2 : σf.heap x = some (.str (seqCode 0 0 g.trs.length)) := by rw [← hxl]; exact hx
  refine ⟨res, ld, ls, lh, t1, t2, t3k, t3, t4, σ.next, σ.next + 1, σ.next + 1 + 1, x,
    runBase_grows hb hgr hinf hstf' ?_ ?_ ?_ ?_ ?_, runTexts_grows hRT hgr ?_ ?_ ?_ ?_ ?_ ?_ ?_, ?_, ?_, ?_, ?_,
    hmem, htrct, hstf2, hx2, ht4lt, addr_lt1 _, addr_lt1 _, hstx⟩
  all_goals simp [Frame.get_setLocal, hv]

/-! ## From statement 63: the first transaction read -/

/-- `inv80` at the load loop's first record. -/
theorem c63B_close {g : RunG} {args : List Value} {σ0 σ σc : State} {fr : Frame}
    {res ld ls lh t1 t2 t3k t3 t4 mem trct st x0 w : Addr} {t0s : JStr}
    (hb : RunBase g σ0 fr σ res ld ls lh JOut.init) (hRT : RunTexts g σ0 fr σ t1 t2 t3k t3 t4)
    (h16 : fr.get 16 = some (.ref mem)) (h24 : fr.get 24 = some (.ref trct)) (h1 : fr.get 1 = some (.ref st))
    (hmem : σ.heap mem = some (.array (.cls "java.lang.String") (List.replicate 561 .null)))
    (htrct : σ.heap trct = some (.array (.prim .long) (List.replicate 51 (.long 0))))
    (hst : σ.heap st = some (.array (.prim .int) [.int 1, .int 0]))
    (o1 : t4 < mem) (o2 : mem < trct) (o3 : trct < st) (hne : g.trs ≠ [])
    (ht0 : t0s = g.T1.getD 0 [])
    (hg : GrowsK (σ.alloc (.str (JStr.ofString "00"))).2 σc) (hin : σc.inits = σ.inits)
    (hstc : σc.statics = σ.statics) (hw : σc.heap w = some (.str (fixStr t0s 1000))) :
    inv80 g args σ0
      (((((((((((fr.setLocal 3 (.int 1)).setLocal 26 (.int 1)).setLocal 26 (.int 0)).setLocal 33 (.ref x0)).setLocal
        33 (.ref w)).setLocal 3 (.int 1)).setLocal 32 (.ref (σc.next + 1))).setLocal 33 (.ref (σc.next + 1))).setLocal
        32 (.ref (σc.next + 1 + 1))).setLocal 18 (.long 1)).setLocal 17 (.long 0))
      (((σc.alloc (.str (JStr.ofString "00"))).2.alloc (.str (List.take 350 (fixStr t0s 1000)))).2.alloc
        (.str (List.take 16 (List.take 350 (fixStr t0s 1000))))).2 := by
  have hg' := growsK_elim hg
  have hgσ : Grows σ σc := grows_trans (grows_alloc_r (grows_refl σ) _) hg'
  have hgr : Grows σ (((σc.alloc (.str (JStr.ofString "00"))).2.alloc
      (.str (List.take 350 (fixStr t0s 1000)))).2.alloc (.str (List.take 16 (List.take 350 (fixStr t0s 1000))))).2 :=
    grows_alloc_r (grows_alloc_r (grows_alloc_r hgσ _) _) _
  obtain ⟨t0, ts, hc⟩ : ∃ t0 ts, g.trs = t0 :: ts := List.exists_cons_of_ne_nil hne
  have hR1 : g.R1.getD 0 [] = recOf t0s 350 := by
    rw [ht0]; simp [RunG.R1, RunG.T1, hc]
  have hmem' := hgr.2 _ (State.lt_next_of_heap hmem)
  have htrct' := hgr.2 _ (State.lt_next_of_heap htrct)
  have hst' := hgr.2 _ (State.lt_next_of_heap hst)
  rw [hmem] at hmem'
  rw [htrct] at htrct'
  rw [hst] at hst'
  refine ⟨res, ld, ls, lh, t1, t2, t3k, t3, t4, mem, trct, st, ld0 (g.R1.getD 0 []), 0,
    runBase_grows hb hgr (by simp only [State.alloc_inits]; exact hin)
      (by simp only [State.alloc_statics]; exact hstc) ?_ ?_ ?_ ?_ ?_,
    runTexts_grows hRT hgr ?_ ?_ ?_ ?_ ?_ ?_ ?_, ⟨?_, ?_, slotsAt_nulls hmem', htrct', rfl⟩, ?_,
    hst', o1, o2, o3, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (simp [Frame.get_setLocal, h16, h24, h1]; done)
    | skip
  · simp only [RunG.R1, RunG.T1, hc, List.map_cons, List.length_cons]; omega
  · refine ⟨σc.next + 1, by simp [Frame.get_setLocal], ?_⟩
    rw [hR1]
    simp [State.heap_alloc, State.next_alloc, recOf, sub]
  · refine ⟨σc.next + 1 + 1, by simp [Frame.get_setLocal], ?_⟩
    rw [hR1]
    simp [State.heap_alloc, State.next_alloc, ld0, recOf, sub]
  · simp [Frame.get_setLocal, ld0]
  · simp [Frame.get_setLocal, ld0]
  · refine ⟨by simp [ld0], by simp [ld0], by simp [ld0], by simp [ld0], fun v hv => ?_⟩
    simp only [ld0, trct0, List.mem_replicate] at hv
    exact ⟨0, hv.2, by decide, by decide⟩
  · simp [RunG.F, jRunR, jRunT, RunG.K3, RunG.T3, RunG.R1, RunG.T1, RunG.T2, RunG.T4, hc, ld0]

end EquivLean.Modernize.Cbstm03a.Java.Seg1
