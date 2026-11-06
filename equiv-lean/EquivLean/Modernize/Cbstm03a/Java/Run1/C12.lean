import EquivLean.Modernize.Cbstm03a.Java.Run1.Entry

/-!
# CBSTM03A → Java `run`: the TRNXFILE texts loop (cut point 12)

From `inv12`: while `i < n` the body (statements 13 … 17: `trnxText(trnxFile[i])` stored into `trnxTexts[i]`)
returns to 12 with one more text; otherwise the exit (18 … 23: `xrefTexts = new String[xrefFile.length]`,
`i#9 = 0`) reaches `inv24`.
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows Keeps fixStr zpadStr argText StrOk space grows_refl grows_split
  keeps_alloc GrowsK growsK_elim heap_grows)

namespace EquivLean.Modernize.Cbstm03a.Java.Seg1

/-- The body's end: text `i` stored, `i + 1`. -/
theorem c12_loop_close {g : RunG} {args : List Value} {σ0 σ σ' : State} {fr : Frame}
    {res ld ls lh t1 x w : Addr} {n i : I32} {xs : List Value} {tr : TrnxR} {c : Nat}
    (hb : RunBase g σ0 fr σ res ld ls lh JOut.init) (h11 : fr.get 11 = some (.ref t1))
    (h27 : fr.get 27 = some (.int n)) (hn : n.toInt = g.trs.length) (hi0 : 0 ≤ i.toInt)
    (hlt : i.toInt < n.toInt) (hxs : Forall2 (JStrAt σ) xs (g.T1.take i.toInt.toNat))
    (hc : c = g.trs.length - i.toInt.toNat)
    (ht1 : σ.heap t1 = some (.array (.cls "java.lang.String") (xs ++ List.replicate c .null)))
    (h0t1 : σ0.next ≤ t1) (hk : i.toInt.toNat < g.trs.length) (htr : tr = g.trs[i.toInt.toNat]'hk)
    (hg : GrowsK σ σ') (hwn : σ.next ≤ w) (hw : σ'.heap w = some (.str (trnxTextO (some tr))))
    (hin : σ'.inits = σ.inits) (hst : σ'.statics = σ.statics) :
    inv12 g args σ0 (((fr.setLocal 31 (.ref x)).setLocal 32 (.ref w)).setLocal 28 (.int (i + 1)))
      (σ'.setObj t1 (.array (.cls "java.lang.String") (xs ++ (List.replicate c .null).set 0 (.ref w)))) := by
  have hg' := growsK_elim hg
  have hK := keeps_setObj_grows (t := t1) hg'
    (.array (.cls "java.lang.String") (xs ++ (List.replicate c .null).set 0 (.ref w)))
  have ht1lt : t1 < σ.next := State.lt_next_of_heap ht1
  have ht1lt' : t1 < σ'.next := Nat.lt_of_lt_of_le ht1lt hg'.1
  have hwt : w ≠ t1 := fun e => Nat.lt_irrefl t1 (Nat.lt_of_lt_of_le ht1lt (e ▸ hwn))
  have hadd := i32_toInt_add_one hlt
  refine ⟨res, ld, ls, lh, t1, n, i + 1, runBase_keeps hb hK ht1 h0t1 hin hst ?_ ?_ ?_ ?_ ?_, ?_, ?_, ?_, hn,
    ?_, ?_, ?_, h0t1⟩
  · simp [Frame.get_setLocal]
  · simp [Frame.get_setLocal]
  · simp [Frame.get_setLocal]
  · simp [Frame.get_setLocal]
  · simp [Frame.get_setLocal]
  · simp [Frame.get_setLocal, h11]
  · simp [Frame.get_setLocal, h27]
  · simp [Frame.get_setLocal]
  · rw [hadd]; omega
  · rw [hadd]; omega
  · have he : (i + 1).toInt.toNat = i.toInt.toNat + 1 := by rw [hadd]; omega
    have hc' : g.trs.length - (i.toInt.toNat + 1) = c - 1 := by rw [hc]; omega
    rw [he, hc']
    refine textsAt_store0 (y := w) (s := trnxTextO (some tr)) hxs (by simp [RunG.T1]; exact hk) (by omega)
      (strMono_of_keeps hK ht1) ?_ ?_ ?_
    · rw [State.heap_setObj_of_lt ht1lt', if_pos rfl]
    · rw [State.heap_setObj_of_lt ht1lt', if_neg hwt]; exact hw
    · simp [RunG.T1, htr, trnxTextO]

/-- The exit: all texts stored, the XREFFILE array new. -/
theorem c12_exit_close {g : RunG} {args : List Value} {σ0 σ : State} {fr : Frame} {res ld ls lh t1 : Addr}
    {n i : I32} {xs xs2 : List Value}
    (hb : RunBase g σ0 fr σ res ld ls lh JOut.init) (h11 : fr.get 11 = some (.ref t1))
    (hn : n.toInt = g.trs.length) (hge : ¬ i.toInt < n.toInt) (hin : i.toInt ≤ n.toInt) (hi0 : 0 ≤ i.toInt)
    (hxs : Forall2 (JStrAt σ) xs (g.T1.take i.toInt.toNat))
    (ht1 : σ.heap t1 = some (.array (.cls "java.lang.String")
      (xs ++ List.replicate (g.trs.length - i.toInt.toNat) .null)))
    (h0t1 : σ0.next ≤ t1) (hl2 : xs2.length < 2147483648) (hlen2 : xs2.length = g.xrs.length) :
    inv24 g args σ0
      (((fr.setLocal 27 (.int (BitVec.ofNat 32 xs2.length))).setLocal 12 (.ref σ.next)).setLocal 29 (.int 0))
      (σ.alloc (.array (.cls "java.lang.String") (List.replicate xs2.length .null))).2 := by
  have hT : TextsAt σ t1 g.T1 0 := textsAt_full hxs (by simp [RunG.T1]) (by omega) ht1
  refine ⟨res, ld, ls, lh, t1, σ.next, BitVec.ofNat 32 xs2.length, 0, runBase_alloc hb _ ?_ ?_ ?_ ?_ ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, textsAt_alloc hT _, ?_, h0t1, State.lt_next_of_heap ht1⟩
  · simp [Frame.get_setLocal]
  · simp [Frame.get_setLocal]
  · simp [Frame.get_setLocal]
  · simp [Frame.get_setLocal]
  · simp [Frame.get_setLocal]
  · simp [Frame.get_setLocal, h11]
  · simp [Frame.get_setLocal]
  · simp [Frame.get_setLocal]
  · simp [Frame.get_setLocal]
  · rw [bv32_toInt_ofNat_of_lt hl2, hlen2]
  · simp [i32_zero_toInt]
  · rw [i32_zero_toInt, bv32_toInt_ofNat_of_lt hl2]; omega
  · rw [i32_zero_toInt]
    simp only [Int.toNat_zero, List.take_zero, Nat.sub_zero]
    rw [← hlen2]
    exact textsAt_new (by simp [State.heap_alloc])

section paths

attribute [local irreducible] TrnxAtN trnxTextO

set_option jimple.modelContracts true in
set_option maxRecDepth 8000 in
set_option maxHeartbeats 400000 in
/-- Statements 13 … 17 back to 12. -/
theorem c12_loop (g : RunG) (σ0 : State) (fr : Frame) (σ : State) (res ld ls lh t1 x : Addr) (n i : I32)
    (et1 : JType) (xs1 xs : List Value) (tr : TrnxR) (c : Nat)
    (hb : RunBase g σ0 fr σ res ld ls lh JOut.init) (hxs : Forall2 (JStrAt σ) xs (g.T1.take i.toInt.toNat))
    (hn : n.toInt = g.trs.length) (h0t1 : σ0.next ≤ t1) (hc : c = g.trs.length - i.toInt.toNat)
    (htrE : ∃ hk : i.toInt.toNat < g.trs.length, tr = g.trs[i.toInt.toNat]'hk)
    (h10 : fr.get 10 = some (.ref g.a1)) (h11 : fr.get 11 = some (.ref t1)) (h27 : fr.get 27 = some (.int n))
    (h28 : fr.get 28 = some (.int i)) (hha1 : σ.heap g.a1 = some (.array et1 xs1))
    (hn1 : n.toInt = xs1.length) (hi0 : 0 ≤ i.toInt) (hlt : i.toInt < n.toInt)
    (hk : i.toInt.toNat < xs1.length) (hel : xs1[i.toInt.toNat]'hk = .ref x)
    (htr : TrnxAtN σ (.ref x) (some tr)) (hci : σ.initOf "Cbstm03a" = .done)
    (ht1 : σ.heap t1 = some (.array (.cls "java.lang.String") (xs ++ List.replicate c .null)))
    (hxl : xs.length = i.toInt.toNat) (hc0 : 0 < c) (ht1lt : t1 < σ.next) :
    runWP g [.ref g.a1, .ref g.a2, .ref g.a3, .ref g.a4] σ0 12 fr σ := by
  have hH := hid_intro (And.intro hb (And.intro hxs (And.intro hn (And.intro h0t1 (And.intro hc htrE)))))
  clear hb hxs hn h0t1 hc htrE
  unfold runWP
  jvc [runCallees, runInv, grows_split]
  obtain ⟨hb, hxs, hn, h0t1, hc, hkT, htrE⟩ := hid_elim hH
  exact c12_loop_close hb h11 h27 hn hi0 hlt hxs hc ht1 h0t1 hkT htrE (by assumption) (by assumption)
    (by assumption) (by assumption) (by assumption)

set_option maxRecDepth 8000 in
set_option maxHeartbeats 400000 in
/-- Statements 18 … 23 to 24. -/
theorem c12_exit (g : RunG) (σ0 : State) (fr : Frame) (σ : State) (res ld ls lh t1 : Addr) (n i : I32)
    (et2 : JType) (xs xs2 : List Value)
    (hb : RunBase g σ0 fr σ res ld ls lh JOut.init) (h11 : fr.get 11 = some (.ref t1))
    (hn : n.toInt = g.trs.length) (hin : i.toInt ≤ n.toInt) (hi0 : 0 ≤ i.toInt)
    (hxs : Forall2 (JStrAt σ) xs (g.T1.take i.toInt.toNat))
    (ht1 : σ.heap t1 = some (.array (.cls "java.lang.String")
      (xs ++ List.replicate (g.trs.length - i.toInt.toNat) .null)))
    (h0t1 : σ0.next ≤ t1) (hlen2 : xs2.length = g.xrs.length)
    (h23 : fr.get 23 = some (.ref g.a2)) (h27 : fr.get 27 = some (.int n))
    (h28 : fr.get 28 = some (.int i)) (hha2 : σ.heap g.a2 = some (.array et2 xs2))
    (hl2 : xs2.length < 2147483648) (hge : ¬ i.toInt < n.toInt) :
    runWP g [.ref g.a1, .ref g.a2, .ref g.a3, .ref g.a4] σ0 12 fr σ := by
  have hH := hid_intro (And.intro hb (And.intro h11 (And.intro hn (And.intro hin (And.intro hi0
    (And.intro hxs (And.intro ht1 (And.intro h0t1 hlen2))))))))
  clear hb h11 hn hin hi0 hxs ht1 h0t1 hlen2
  unfold runWP
  jvc [runCallees, runInv, grows_split]
  obtain ⟨hb, h11, hn, hin, hi0, hxs, ht1, h0t1, hlen2⟩ := hid_elim hH
  exact c12_exit_close hb h11 hn hge hin hi0 hxs ht1 h0t1 hl2 hlen2

end paths

end EquivLean.Modernize.Cbstm03a.Java.Seg1

namespace EquivLean.Modernize.Cbstm03a.Java

open Seg1

theorem run_cut12_vc (g : RunG) : RunCutVC g 12 inv12 := by
  intro args σ0 hpre fr σ hI
  obtain ⟨hargs, ⟨et1, xs1, hh1, hl1, hf1⟩, ⟨et2, xs2, hh2, hl2, hf2⟩, -, -, ⟨hcpi, -⟩, -⟩ := hpre
  subst hargs
  obtain ⟨res, ld, ls, lh, t1, n, i, hb, h11, h27, h28, hn, hi0, hin, ⟨xs, ht1, hxs⟩, h0t1⟩ := hI
  have hb' := hb
  obtain ⟨h10, h23, -, -, -, -, -, -, -, -, hg, hinits, -⟩ := hb'
  by_cases hlt : i.toInt < n.toInt
  · have hlen1 := forall2_length hf1
    have hk : i.toInt.toNat < g.trs.length := by omega
    obtain ⟨hk1, x, hx, hat⟩ := recsAt_elem hf1 _ hk
    have hxl : xs.length = i.toInt.toNat := by
      rw [forall2_length hxs, List.length_take]; simp [RunG.T1]; omega
    exact c12_loop g σ0 fr σ res ld ls lh t1 x n i et1 xs1 xs _ _ hb hxs hn h0t1 rfl ⟨hk, rfl⟩ h10 h11 h27 h28
      (heap_grows hg hh1) (by rw [hn, hlen1]) hi0 hlt hk1 hx ⟨x, rfl, trnxAt_grows hat hg⟩
      (by rw [State.initOf_eq_of_inits hinits]; exact hcpi) ht1 hxl (by omega) (State.lt_next_of_heap ht1)
  · exact c12_exit g σ0 fr σ res ld ls lh t1 n i et2 xs xs2 hb h11 hn hin hi0 hxs ht1 h0t1 (forall2_length hf2)
      h23 h27 h28 (heap_grows hg hh2) hl2 hlt

end EquivLean.Modernize.Cbstm03a.Java

#print axioms EquivLean.Modernize.Cbstm03a.Java.run_cut12_vc
