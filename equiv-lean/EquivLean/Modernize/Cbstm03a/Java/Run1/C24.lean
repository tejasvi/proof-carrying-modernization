import EquivLean.Modernize.Cbstm03a.Java.Run1.C12

/-!
# CBSTM03A → Java `run`: the XREFFILE texts loop (cut point 24)

From `inv24`: while `i#9 < n` the body (statements 25 … 29: `xrefText(xrefFile[i#9])` stored into
`xrefTexts[i#9]`) returns to 24 with one more text; otherwise the exit (30 … 36: `custKeys` and `custTexts` new
arrays of `custFile.length` elements, `i#16 = 0`) reaches `inv37`.
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows Keeps fixStr zpadStr argText StrOk space grows_refl grows_split
  keeps_alloc GrowsK growsK_elim heap_grows)

namespace EquivLean.Modernize.Cbstm03a.Java.Seg1

/-- The body's end: text `i#9` stored, `i#9 + 1`. -/
theorem c24_loop_close {g : RunG} {args : List Value} {σ0 σ σ' : State} {fr : Frame}
    {res ld ls lh t1 t2 x w : Addr} {n i : I32} {xs : List Value} {tr : XrefR} {c : Nat}
    (hb : RunBase g σ0 fr σ res ld ls lh JOut.init) (h11 : fr.get 11 = some (.ref t1))
    (h12 : fr.get 12 = some (.ref t2)) (h27 : fr.get 27 = some (.int n)) (hn : n.toInt = g.xrs.length)
    (hi0 : 0 ≤ i.toInt) (hlt : i.toInt < n.toInt) (hT1 : TextsAt σ t1 g.T1 0)
    (hxs : Forall2 (JStrAt σ) xs (g.T2.take i.toInt.toNat)) (hc : c = g.xrs.length - i.toInt.toNat)
    (ht2 : σ.heap t2 = some (.array (.cls "java.lang.String") (xs ++ List.replicate c .null)))
    (h0t1 : σ0.next ≤ t1) (h12lt : t1 < t2) (hk : i.toInt.toNat < g.xrs.length)
    (htr : tr = g.xrs[i.toInt.toNat]'hk)
    (hg : GrowsK σ σ') (hwn : σ.next ≤ w) (hw : σ'.heap w = some (.str (xrefTextO (some tr))))
    (hin : σ'.inits = σ.inits) (hst : σ'.statics = σ.statics) :
    inv24 g args σ0 (((fr.setLocal 39 (.ref x)).setLocal 32 (.ref w)).setLocal 29 (.int (i + 1)))
      (σ'.setObj t2 (.array (.cls "java.lang.String") (xs ++ (List.replicate c .null).set 0 (.ref w)))) := by
  have hg' := growsK_elim hg
  have hK := keeps_setObj_grows (t := t2) hg'
    (.array (.cls "java.lang.String") (xs ++ (List.replicate c .null).set 0 (.ref w)))
  have ht2lt : t2 < σ.next := State.lt_next_of_heap ht2
  have ht2lt' : t2 < σ'.next := Nat.lt_of_lt_of_le ht2lt hg'.1
  have hwt : w ≠ t2 := fun e => Nat.lt_irrefl t2 (Nat.lt_of_lt_of_le ht2lt (e ▸ hwn))
  have h0t2 : σ0.next ≤ t2 := Nat.le_of_lt (Nat.lt_of_le_of_lt h0t1 h12lt)
  have hadd := i32_toInt_add_one hlt
  refine ⟨res, ld, ls, lh, t1, t2, n, i + 1, runBase_keeps hb hK ht2 h0t2 hin hst ?_ ?_ ?_ ?_ ?_, ?_, ?_, ?_,
    ?_, hn, ?_, ?_, textsAt_keeps hT1 hK ht2 (Nat.ne_of_lt h12lt), ?_, h0t1, h12lt⟩
  · simp [Frame.get_setLocal]
  · simp [Frame.get_setLocal]
  · simp [Frame.get_setLocal]
  · simp [Frame.get_setLocal]
  · simp [Frame.get_setLocal]
  · simp [Frame.get_setLocal, h11]
  · simp [Frame.get_setLocal, h12]
  · simp [Frame.get_setLocal, h27]
  · simp [Frame.get_setLocal]
  · rw [hadd]; omega
  · rw [hadd]; omega
  · have he : (i + 1).toInt.toNat = i.toInt.toNat + 1 := by rw [hadd]; omega
    have hc' : g.xrs.length - (i.toInt.toNat + 1) = c - 1 := by rw [hc]; omega
    rw [he, hc']
    refine textsAt_store0 (y := w) (s := xrefTextO (some tr)) hxs (by simp [RunG.T2]; exact hk) (by omega)
      (strMono_of_keeps hK ht2) ?_ ?_ ?_
    · rw [State.heap_setObj_of_lt ht2lt', if_pos rfl]
    · rw [State.heap_setObj_of_lt ht2lt', if_neg hwt]; exact hw
    · simp [RunG.T2, htr, xrefTextO]

/-- The exit: all texts stored, the customer key and text arrays new. -/
theorem c24_exit_close {g : RunG} {args : List Value} {σ0 σ : State} {fr : Frame} {res ld ls lh t1 t2 : Addr}
    {n i : I32} {xs xs3 : List Value}
    (hb : RunBase g σ0 fr σ res ld ls lh JOut.init) (h11 : fr.get 11 = some (.ref t1))
    (h12 : fr.get 12 = some (.ref t2))
    (hn : n.toInt = g.xrs.length) (hge : ¬ i.toInt < n.toInt) (hin : i.toInt ≤ n.toInt) (hi0 : 0 ≤ i.toInt)
    (hT1 : TextsAt σ t1 g.T1 0) (hxs : Forall2 (JStrAt σ) xs (g.T2.take i.toInt.toNat))
    (ht2 : σ.heap t2 = some (.array (.cls "java.lang.String")
      (xs ++ List.replicate (g.xrs.length - i.toInt.toNat) .null)))
    (h0t1 : σ0.next ≤ t1) (h12lt : t1 < t2) (hl3 : xs3.length < 2147483648) (hlen3 : xs3.length = g.crs.length) :
    inv37 g args σ0
      ((((fr.setLocal 27 (.int (BitVec.ofNat 32 xs3.length))).setLocal 13 (.ref σ.next)).setLocal 14
        (.ref (σ.next + 1))).setLocal 30 (.int 0))
      ((σ.alloc (.array (.cls "java.lang.String") (List.replicate xs3.length .null))).2.alloc
        (.array (.cls "java.lang.String") (List.replicate xs3.length .null))).2 := by
  have hT2 : TextsAt σ t2 g.T2 0 := textsAt_full hxs (by simp [RunG.T2]) (by omega) ht2
  have hK3 : g.K3.length = g.crs.length := by simp [RunG.K3, RunG.T3]
  have hT3 : g.T3.length = g.crs.length := by simp [RunG.T3]
  refine ⟨res, ld, ls, lh, t1, t2, σ.next, σ.next + 1, BitVec.ofNat 32 xs3.length, 0,
    runBase_alloc (runBase_alloc hb _ rfl rfl rfl rfl rfl) _ ?_ ?_ ?_ ?_ ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, textsAt_alloc (textsAt_alloc hT1 _) _,
    textsAt_alloc (textsAt_alloc hT2 _) _, ?_, ?_, h0t1, h12lt, State.lt_next_of_heap ht2,
    Nat.lt_succ_self _⟩
  · simp [Frame.get_setLocal]
  · simp [Frame.get_setLocal]
  · simp [Frame.get_setLocal]
  · simp [Frame.get_setLocal]
  · simp [Frame.get_setLocal]
  · simp [Frame.get_setLocal, h11]
  · simp [Frame.get_setLocal, h12]
  · simp [Frame.get_setLocal]
  · simp [Frame.get_setLocal]
  · simp [Frame.get_setLocal]
  · simp [Frame.get_setLocal]
  · rw [bv32_toInt_ofNat_of_lt hl3, hlen3]
  · simp [i32_zero_toInt]
  · rw [i32_zero_toInt, bv32_toInt_ofNat_of_lt hl3]; omega
  · rw [i32_zero_toInt]
    simp only [Int.toNat_zero, List.take_zero, Nat.sub_zero]
    rw [← hlen3]
    exact textsAt_new (by simp [State.heap_alloc, State.next_alloc])
  · rw [i32_zero_toInt]
    simp only [Int.toNat_zero, List.take_zero, Nat.sub_zero]
    rw [← hlen3]
    exact textsAt_new (by simp [State.heap_alloc, State.next_alloc])

section paths

attribute [local irreducible] XrefAtN xrefTextO

set_option jimple.modelContracts true in
set_option maxRecDepth 8000 in
set_option maxHeartbeats 400000 in
/-- Statements 25 … 29 back to 24. -/
theorem c24_loop (g : RunG) (σ0 : State) (fr : Frame) (σ : State) (res ld ls lh t1 t2 x : Addr) (n i : I32)
    (et2 : JType) (xs2 xs : List Value) (tr : XrefR) (c : Nat)
    (hb : RunBase g σ0 fr σ res ld ls lh JOut.init) (hT1 : TextsAt σ t1 g.T1 0)
    (hxs : Forall2 (JStrAt σ) xs (g.T2.take i.toInt.toNat))
    (hn : n.toInt = g.xrs.length) (h0t1 : σ0.next ≤ t1) (h12lt : t1 < t2) (hc : c = g.xrs.length - i.toInt.toNat)
    (htrE : ∃ hk : i.toInt.toNat < g.xrs.length, tr = g.xrs[i.toInt.toNat]'hk) (h11 : fr.get 11 = some (.ref t1))
    (h23 : fr.get 23 = some (.ref g.a2)) (h12 : fr.get 12 = some (.ref t2)) (h27 : fr.get 27 = some (.int n))
    (h29 : fr.get 29 = some (.int i)) (hha2 : σ.heap g.a2 = some (.array et2 xs2))
    (hn1 : n.toInt = xs2.length) (hi0 : 0 ≤ i.toInt) (hlt : i.toInt < n.toInt)
    (hk : i.toInt.toNat < xs2.length) (hel : xs2[i.toInt.toNat]'hk = .ref x)
    (htr : XrefAtN σ (.ref x) (some tr)) (hci : σ.initOf "Cbstm03a" = .done)
    (ht2 : σ.heap t2 = some (.array (.cls "java.lang.String") (xs ++ List.replicate c .null)))
    (hxl : xs.length = i.toInt.toNat) (hc0 : 0 < c) (ht2lt : t2 < σ.next) :
    runWP g [.ref g.a1, .ref g.a2, .ref g.a3, .ref g.a4] σ0 24 fr σ := by
  have hH := hid_intro (And.intro hb (And.intro hT1 (And.intro hxs (And.intro hn (And.intro h0t1
    (And.intro h12lt (And.intro hc (And.intro htrE h11))))))))
  clear hb hT1 hxs hn h0t1 h12lt hc htrE h11
  unfold runWP
  jvc [runCallees, runInv, grows_split]
  obtain ⟨hb, hT1, hxs, hn, h0t1, h12lt, hc, ⟨hkT, htrE⟩, h11⟩ := hid_elim hH
  exact c24_loop_close hb h11 h12 h27 hn hi0 hlt hT1 hxs hc ht2 h0t1 h12lt hkT htrE (by assumption)
    (by assumption) (by assumption) (by assumption) (by assumption)

set_option maxRecDepth 8000 in
set_option maxHeartbeats 400000 in
/-- Statements 30 … 36 to 37. -/
theorem c24_exit (g : RunG) (σ0 : State) (fr : Frame) (σ : State) (res ld ls lh t1 t2 : Addr) (n i : I32)
    (et3 : JType) (xs xs3 : List Value)
    (hb : RunBase g σ0 fr σ res ld ls lh JOut.init) (h11 : fr.get 11 = some (.ref t1))
    (h12 : fr.get 12 = some (.ref t2))
    (hn : n.toInt = g.xrs.length) (hin : i.toInt ≤ n.toInt) (hi0 : 0 ≤ i.toInt) (hT1 : TextsAt σ t1 g.T1 0)
    (hxs : Forall2 (JStrAt σ) xs (g.T2.take i.toInt.toNat))
    (ht2 : σ.heap t2 = some (.array (.cls "java.lang.String")
      (xs ++ List.replicate (g.xrs.length - i.toInt.toNat) .null)))
    (h0t1 : σ0.next ≤ t1) (h12lt : t1 < t2) (hlen3 : xs3.length = g.crs.length)
    (h9 : fr.get 9 = some (.ref g.a3)) (h27 : fr.get 27 = some (.int n))
    (h29 : fr.get 29 = some (.int i)) (hha3 : σ.heap g.a3 = some (.array et3 xs3))
    (hl3 : xs3.length < 2147483648) (hge : ¬ i.toInt < n.toInt) :
    runWP g [.ref g.a1, .ref g.a2, .ref g.a3, .ref g.a4] σ0 24 fr σ := by
  have hH := hid_intro (And.intro hb (And.intro h11 (And.intro h12 (And.intro hn (And.intro hin (And.intro hi0
    (And.intro hT1 (And.intro hxs (And.intro ht2 (And.intro h0t1 (And.intro h12lt hlen3)))))))))))
  clear hb h11 h12 hn hin hi0 hT1 hxs ht2 h0t1 h12lt hlen3
  unfold runWP
  jvc [runCallees, runInv, grows_split]
  obtain ⟨hb, h11, h12, hn, hin, hi0, hT1, hxs, ht2, h0t1, h12lt, hlen3⟩ := hid_elim hH
  exact c24_exit_close hb h11 h12 hn hge hin hi0 hT1 hxs ht2 h0t1 h12lt hl3 hlen3

end paths

end EquivLean.Modernize.Cbstm03a.Java.Seg1

namespace EquivLean.Modernize.Cbstm03a.Java

open Seg1

theorem run_cut24_vc (g : RunG) : RunCutVC g 24 inv24 := by
  intro args σ0 hpre fr σ hI
  obtain ⟨hargs, -, ⟨et2, xs2, hh2, hl2, hf2⟩, ⟨et3, xs3, hh3, hl3, hf3⟩, -, ⟨hcpi, -⟩, -⟩ := hpre
  subst hargs
  obtain ⟨res, ld, ls, lh, t1, t2, n, i, hb, h11, h12, h27, h29, hn, hi0, hin, hT1, ⟨xs, ht2, hxs⟩, h0t1,
    h12lt⟩ := hI
  have hb' := hb
  obtain ⟨-, h23, h9, -, -, -, -, -, -, -, hg, hinits, -⟩ := hb'
  by_cases hlt : i.toInt < n.toInt
  · have hlen2 := forall2_length hf2
    have hk : i.toInt.toNat < g.xrs.length := by omega
    obtain ⟨hk1, x, hx, hat⟩ := recsAt_elem hf2 _ hk
    have hxl : xs.length = i.toInt.toNat := by
      rw [forall2_length hxs, List.length_take]; simp [RunG.T2]; omega
    exact c24_loop g σ0 fr σ res ld ls lh t1 t2 x n i et2 xs2 xs _ _ hb hT1 hxs hn h0t1 h12lt rfl ⟨hk, rfl⟩ h11
      h23 h12 h27 h29 (heap_grows hg hh2) (by rw [hn, hlen2]) hi0 hlt hk1 hx ⟨x, rfl, xrefAt_grows hat hg⟩
      (by rw [State.initOf_eq_of_inits hinits]; exact hcpi) ht2 hxl (by omega) (State.lt_next_of_heap ht2)
  · exact c24_exit g σ0 fr σ res ld ls lh t1 t2 n i et3 xs xs3 hb h11 h12 hn hin hi0 hT1 hxs ht2 h0t1 h12lt
      (forall2_length hf3) h9 h27 h29 (heap_grows hg hh3) hl3 hlt

end EquivLean.Modernize.Cbstm03a.Java

#print axioms EquivLean.Modernize.Cbstm03a.Java.run_cut24_vc
