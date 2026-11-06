import EquivLean.Modernize.Cbstm03a.Java.Run1.C37

/-!
# CBSTM03A → Java `run`: the ACCTFILE loop (cut point 52)

From `inv52`: while `i#78 < i` the body (statements 53 … 57: `acctText(acctFile[i#78])` stored into
`acctTexts[i#78]`) returns to 52; otherwise the exit (58 … 79: the table memory, the counts, `trnxSt`,
`spaces(1000)`, the first `seqRead`) either abends (no transaction: status `10`, statements 69 … 74) or reads the
first record and reaches the load loop's invariant `inv80`.
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows Keeps fixStr zpadStr argText StrOk space grows_refl grows_split
  keeps_alloc keeps_setObj keeps_trans GrowsK growsK_elim heap_grows)

namespace EquivLean.Modernize.Cbstm03a.Java.Seg1

/-- The body's end: text `i#78` stored, `i#78 + 1`. -/
theorem c52_loop_close {g : RunG} {args : List Value} {σ0 σ σ' : State} {fr : Frame}
    {res ld ls lh t1 t2 t3k t3 t4 x w : Addr} {n3 n i : I32} {xs : List Value} {tr : AcctR} {c : Nat}
    (hb : RunBase g σ0 fr σ res ld ls lh JOut.init) (h11 : fr.get 11 = some (.ref t1))
    (h12 : fr.get 12 = some (.ref t2)) (h13 : fr.get 13 = some (.ref t3k)) (h14 : fr.get 14 = some (.ref t3))
    (h15 : fr.get 15 = some (.ref t4)) (h27 : fr.get 27 = some (.int n3)) (h28 : fr.get 28 = some (.int n))
    (hn3 : n3.toInt = g.crs.length) (hn : n.toInt = g.ars.length) (hi0 : 0 ≤ i.toInt) (hlt : i.toInt < n.toInt)
    (hT1 : TextsAt σ t1 g.T1 0) (hT2 : TextsAt σ t2 g.T2 0) (hK3 : TextsAt σ t3k g.K3 0)
    (hT3 : TextsAt σ t3 g.T3 0) (hxs : Forall2 (JStrAt σ) xs (g.T4.take i.toInt.toNat))
    (hc : c = g.ars.length - i.toInt.toNat)
    (ht4 : σ.heap t4 = some (.array (.cls "java.lang.String") (xs ++ List.replicate c .null)))
    (h0t1 : σ0.next ≤ t1) (h12lt : t1 < t2) (h23lt : t2 < t3k) (h34lt : t3k < t3) (h45lt : t3 < t4)
    (hk : i.toInt.toNat < g.ars.length) (htr : tr = g.ars[i.toInt.toNat]'hk)
    (hg : GrowsK σ σ') (hwn : σ.next ≤ w) (hw : σ'.heap w = some (.str (acctTextO (some tr))))
    (hin : σ'.inits = σ.inits) (hst : σ'.statics = σ.statics) :
    inv52 g args σ0 (((fr.setLocal 8 (.ref x)).setLocal 32 (.ref w)).setLocal 26 (.int (i + 1)))
      (σ'.setObj t4 (.array (.cls "java.lang.String") (xs ++ (List.replicate c .null).set 0 (.ref w)))) := by
  have hg' := growsK_elim hg
  have hK := keeps_setObj_grows (t := t4) hg'
    (.array (.cls "java.lang.String") (xs ++ (List.replicate c .null).set 0 (.ref w)))
  have ht4lt : t4 < σ.next := State.lt_next_of_heap ht4
  have ht4lt' : t4 < σ'.next := Nat.lt_of_lt_of_le ht4lt hg'.1
  have hwt : w ≠ t4 := fun e => Nat.lt_irrefl t4 (Nat.lt_of_lt_of_le ht4lt (e ▸ hwn))
  have h3 : t3 < t4 := h45lt
  have h2 : t3k < t4 := Nat.lt_trans h34lt h3
  have h1 : t2 < t4 := Nat.lt_trans h23lt h2
  have h0 : t1 < t4 := Nat.lt_trans h12lt h1
  have h0t4 : σ0.next ≤ t4 := Nat.le_of_lt (Nat.lt_of_le_of_lt h0t1 h0)
  have hadd := i32_toInt_add_one hlt
  refine ⟨res, ld, ls, lh, t1, t2, t3k, t3, t4, n3, n, i + 1,
    runBase_keeps hb hK ht4 h0t4 hin hst ?_ ?_ ?_ ?_ ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hn3, hn, ?_, ?_,
    textsAt_keeps hT1 hK ht4 (Nat.ne_of_lt h0), textsAt_keeps hT2 hK ht4 (Nat.ne_of_lt h1),
    textsAt_keeps hK3 hK ht4 (Nat.ne_of_lt h2), textsAt_keeps hT3 hK ht4 (Nat.ne_of_lt h3), ?_,
    h0t1, h12lt, h23lt, h34lt, h45lt⟩
  · simp [Frame.get_setLocal]
  · simp [Frame.get_setLocal]
  · simp [Frame.get_setLocal]
  · simp [Frame.get_setLocal]
  · simp [Frame.get_setLocal]
  · simp [Frame.get_setLocal, h11]
  · simp [Frame.get_setLocal, h12]
  · simp [Frame.get_setLocal, h13]
  · simp [Frame.get_setLocal, h14]
  · simp [Frame.get_setLocal, h15]
  · simp [Frame.get_setLocal, h27]
  · simp [Frame.get_setLocal, h28]
  · simp [Frame.get_setLocal]
  · rw [hadd]; omega
  · rw [hadd]; omega
  · have he : (i + 1).toInt.toNat = i.toInt.toNat + 1 := by rw [hadd]; omega
    have hc' : g.ars.length - (i.toInt.toNat + 1) = c - 1 := by rw [hc]; omega
    rw [he, hc']
    refine textsAt_store0 (y := w) (s := acctTextO (some tr)) hxs (by simp [RunG.T4]; exact hk) (by omega)
      (strMono_of_keeps hK ht4) ?_ ?_ ?_
    · rw [State.heap_setObj_of_lt ht4lt', if_pos rfl]
    · rw [State.heap_setObj_of_lt ht4lt', if_neg hwt]; exact hw
    · simp [RunG.T4, htr, acctTextO]

section paths

attribute [local irreducible] AcctAtN acctTextO

set_option jimple.modelContracts true in
set_option maxRecDepth 8000 in
set_option maxHeartbeats 400000 in
/-- Statements 53 … 57 back to 52. -/
theorem c52_loop (g : RunG) (σ0 : State) (fr : Frame) (σ : State) (res ld ls lh t1 t2 t3k t3 t4 x : Addr)
    (n3 n i : I32) (et4 : JType) (xs4 xs : List Value) (tr : AcctR) (c : Nat)
    (hb : RunBase g σ0 fr σ res ld ls lh JOut.init) (hT1 : TextsAt σ t1 g.T1 0) (hT2 : TextsAt σ t2 g.T2 0)
    (hK3 : TextsAt σ t3k g.K3 0) (hT3 : TextsAt σ t3 g.T3 0)
    (hxs : Forall2 (JStrAt σ) xs (g.T4.take i.toInt.toNat))
    (hn3 : n3.toInt = g.crs.length) (hn : n.toInt = g.ars.length) (h0t1 : σ0.next ≤ t1) (h12lt : t1 < t2)
    (h23lt : t2 < t3k) (h34lt : t3k < t3) (h45lt : t3 < t4) (hc : c = g.ars.length - i.toInt.toNat)
    (htrE : ∃ hk : i.toInt.toNat < g.ars.length, tr = g.ars[i.toInt.toNat]'hk)
    (h11 : fr.get 11 = some (.ref t1)) (h12 : fr.get 12 = some (.ref t2)) (h13 : fr.get 13 = some (.ref t3k))
    (h14 : fr.get 14 = some (.ref t3)) (h27 : fr.get 27 = some (.int n3))
    (h6 : fr.get 6 = some (.ref g.a4)) (h15 : fr.get 15 = some (.ref t4)) (h28 : fr.get 28 = some (.int n))
    (h26 : fr.get 26 = some (.int i)) (hha4 : σ.heap g.a4 = some (.array et4 xs4))
    (hn1 : n.toInt = xs4.length) (hi0 : 0 ≤ i.toInt) (hlt : i.toInt < n.toInt)
    (hk : i.toInt.toNat < xs4.length) (hel : xs4[i.toInt.toNat]'hk = .ref x)
    (htr : AcctAtN σ (.ref x) (some tr)) (hci : σ.initOf "Cbstm03a" = .done)
    (ht4 : σ.heap t4 = some (.array (.cls "java.lang.String") (xs ++ List.replicate c .null)))
    (hxl : xs.length = i.toInt.toNat) (hc0 : 0 < c) (ht4lt : t4 < σ.next) :
    runWP g [.ref g.a1, .ref g.a2, .ref g.a3, .ref g.a4] σ0 52 fr σ := by
  have hH := hid_intro (And.intro hb (And.intro hT1 (And.intro hT2 (And.intro hK3 (And.intro hT3 (And.intro hxs
    (And.intro hn3 (And.intro hn (And.intro h0t1 (And.intro h12lt (And.intro h23lt (And.intro h34lt
    (And.intro h45lt (And.intro hc (And.intro htrE (And.intro h11 (And.intro h12 (And.intro h13
    (And.intro h14 h27)))))))))))))))))))
  clear hb hT1 hT2 hK3 hT3 hxs hn3 hn h0t1 h12lt h23lt h34lt h45lt hc htrE h11 h12 h13 h14 h27
  unfold runWP
  jvc [runCallees, runInv, grows_split]
  obtain ⟨hb, hT1, hT2, hK3, hT3, hxs, hn3, hn, h0t1, h12lt, h23lt, h34lt, h45lt, hc, ⟨hkT, htrE⟩, h11, h12, h13,
    h14, h27⟩ := hid_elim hH
  exact c52_loop_close hb h11 h12 h13 h14 h15 h27 h28 hn3 hn hi0 hlt hT1 hT2 hK3 hT3 hxs hc ht4 h0t1 h12lt h23lt
    h34lt h45lt hkT htrE (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)

end paths

end EquivLean.Modernize.Cbstm03a.Java.Seg1
