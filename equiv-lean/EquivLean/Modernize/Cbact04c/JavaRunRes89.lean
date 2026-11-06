import EquivLean.Modernize.Cbact04c.JavaRunRunHeap
import EquivLean.Modernize.Cbact04c.JavaRunGlue04

/-!
# CBACT04C → Java, `run`: the cut point after record `i` is displayed (statements 90–96)
-/

open Jimple EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbact04c.Java

theorem trec_valid {g : G} {args : List Value} {σ0 : State} (hpre : RunPreG g args σ0) {n : Nat}
    (hn : n < g.tcat.length) : TranCatBalRecord.Valid (g.trec n) := by
  obtain ⟨-, ⟨b1, b2, b3, b4, q1, c1, -, -, -, -, -, -, -, -, hv1, -⟩, -⟩ := hpre
  have : g.trec n = g.tcat[n] := by
    simp [G.trec, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hn]
  rw [this]
  exact hv1 _ (List.getElem_mem _)

/-- The line `displayTcb` returns for the record object of record `t` is the record's text. -/
theorem tcbLineOf_text {σ : State} {y : Addr} {t : List FV}
    (h : JRecAt TranCatBalRecord "Cbact04c$TranCatBalRecord" σ (.ref y) t)
    (hv : TranCatBalRecord.Valid t) : tcbLineOf σ y = jline (TranCatBalRecord.textS t) := by
  obtain ⟨fsy, tyA, fiA, hyh, ht0, ht1, htyA, ht2, ht3, ht4, hfiA, hr0, hr1, hr2, hr3, hr4, hr5,
    -, -⟩ := tcb_facts h hv
  rw [tcbLineOf_eq hyh ht0 ht1 htyA ht2 ht3 ht4 hfiA,
    tcbLine_eq hv (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]

/-- The loop's fixed locals survive writes to the other locals. -/
theorem locs_setLocal {g : G} {hp : Hp} {fr : Frame} (h : Locs g hp fr) {n : Nat} (v : Value)
    (hn : n ∉ [1, 36, 40, 8, 37, 10, 19, 20, 21, 41, 38, 26, 24]) : Locs g hp (fr.setLocal n v) := by
  obtain ⟨f1, f36, f40, f8, f37, f10, f19, f20, f21, f41, f38, f26, f24⟩ := h
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
  obtain ⟨n1, n36, n40, n8, n37, n10, n19, n20, n21, n41, n38, n26, n24⟩ := hn
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [Frame.get_setLocal, Ne.symm n1, Ne.symm n36, Ne.symm n40, Ne.symm n8, Ne.symm n37,
      Ne.symm n10, Ne.symm n19, Ne.symm n20, Ne.symm n21, Ne.symm n41, Ne.symm n38, Ne.symm n26,
      Ne.symm n24, ite_false, *]

/-- `Locs` of a frame built by writes to other locals, from a hidden `Locs` of the old frame. -/
macro "locs_tac" : tactic => `(tactic| repeat (first
  | refine locs_setLocal ?_ _ (by decide)
  | exact Hide.elim ‹Hide (Locs _ _ _)›))

/-- **Record `i` displayed** (`displayTcb`'s line added to the display list): the cut point 97. -/
theorem j97_of_disp {g : G} {σ0 σ σ1 : State} {fr : Frame} {i : I32} {hp : Hp} {y : Addr}
    {acctV xrefV lastV : Value} {y' : Addr} {dxs : List Value} {dm : Nat}
    (hn : i.toInt.toNat < g.tcat.length) (hi0 : 0 ≤ i.toInt) (hlocs : Locs g hp fr)
    (f22 : fr.get 22 = some (.int (i + 1#32))) (f6 : fr.get 6 = some (.ref y))
    (f4 : fr.get 4 = some (.int 0#32)) (f5 : fr.get 5 = some (.int 0#32))
    (f12 : fr.get 12 = some (.long (BitVec.ofInt 64 (g.st i.toInt.toNat).total)))
    (f3 : fr.get 3 = some (.int (if (g.st i.toInt.toNat).lastId.isSome then 0#32 else 1#32)))
    (f14 : fr.get 14 = some (.long (BitVec.ofNat 64 (g.st i.toInt.toNat).k)))
    (f25 : fr.get 25 = some lastV) (f16 : fr.get 16 = some acctV) (f17 : fr.get 17 = some xrefV)
    (htcb : Hide (JRecAt TranCatBalRecord "Cbact04c$TranCatBalRecord" σ (.ref y)
      (g.trec i.toInt.toNat)))
    (hvt : Hide (TranCatBalRecord.Valid (g.trec i.toInt.toNat)))
    (hheap : Hide (LoopHeap g σ0 σ hp (g.st i.toInt.toNat) acctV xrefV lastV))
    (hld : σ.heap hp.ld = some (.list .arrayList dxs dm))
    (hg : Grows σ σ1) (hi : σ1.inits = σ.inits)
    (hy' : σ1.heap y' = some (.str (tcbLineOf σ y))) :
    J97 g g.args σ0 ((fr.setLocal 9 (.ref hp.ld)).setLocal 27 (.ref y'))
      (σ1.setObj hp.ld (.list .arrayList (dxs ++ [.ref y']) (dm + 1))) := by
  have hrec := Hide.elim htcb
  have hv : JStrAt σ1 (.ref y') (jline (TranCatBalRecord.textS (g.trec i.toInt.toNat))) :=
    ⟨y', rfl, by rw [hy', tcbLineOf_text hrec (Hide.elim hvt)]⟩
  have hL' := loopHeap_disp_add (Hide.elim hheap) hld hg hi hv
  have hld1 : σ1.heap hp.ld = some (.list .arrayList dxs dm) := heap_of_grows hg hld
  obtain ⟨f1, f36, f40, f8, f37, f10, f19, f20, f21, f41, f38, f26, f24⟩ := hlocs
  refine ⟨i, hp, .ref y, acctV, xrefV, lastV, ⟨hn, hi0, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (frame_simp [f1, f36, f40, f8, f37, f10, f19, f20, f21, f41, f38, f26, f24, f12, f3, f14, f25,
        f16, f17, f4, f5, f22, f6]; done)
    | skip
  · exact Hide.intro (jrecAt_setObj_list hld1 (jrecAt_grows hg hrec))
  · exact Hide.intro hL'

end EquivLean.Modernize.Cbact04c.Java
