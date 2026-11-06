import EquivLean.Modernize.Cbstm03a.Java.Run1.C24

/-!
# CBSTM03A → Java `run`: the CUSTFILE loop (cut point 37)

From `inv37`: while `i#16 < n` the body (statements 38 … 45: `custText(custFile[i#16])` stored into
`custTexts[i#16]`, read back, its first 9 characters stored into `custKeys[i#16]`) returns to 37; otherwise the
exit (46 … 51: `i = acctFile.length`, `acctTexts = new String[i]`, `i#78 = 0`) reaches `inv52`.
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows Keeps fixStr zpadStr argText StrOk space grows_refl grows_split
  keeps_alloc keeps_setObj keeps_trans GrowsK growsK_elim heap_grows zpadStr_length)

namespace EquivLean.Modernize.Cbstm03a.Java.Seg1

theorem custTextO_length (t : CustR) : (custTextO (some t)).length = 500 := by
  simp [custTextO, custTextR, zuI, zpadStr_length]

/-- The first 9 characters, as `jvc` spells them out. -/
theorem take9_explicit (s : JStr) (h0 : 0 < s.length) (h1 : 1 < s.length) (h2 : 2 < s.length)
    (h3 : 3 < s.length) (h4 : 4 < s.length) (h5 : 5 < s.length) (h6 : 6 < s.length) (h7 : 7 < s.length)
    (h8 : 8 < s.length) :
    [s[0], s[1], s[2], s[3], s[4], s[5], s[6], s[7], s[8]] = sub s 0 9 := by
  match s with
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ => rfl
  | [] => simp at h0
  | [_] => simp at h1
  | [_, _] => simp at h2
  | [_, _, _] => simp at h3
  | [_, _, _, _] => simp at h4
  | [_, _, _, _, _] => simp at h5
  | [_, _, _, _, _, _] => simp at h6
  | [_, _, _, _, _, _, _] => simp at h7
  | [_, _, _, _, _, _, _, _] => simp at h8

/-- The body's end: text `i#16` and its key stored, `i#16 + 1`. -/
theorem c37_loop_close {g : RunG} {args : List Value} {σ0 σ σ' : State} {fr : Frame}
    {res ld ls lh t1 t2 t3k t3 x w : Addr} {n i : I32} {xs xsk : List Value} {tr : CustR} {c : Nat}
    (hb : RunBase g σ0 fr σ res ld ls lh JOut.init) (h11 : fr.get 11 = some (.ref t1))
    (h12 : fr.get 12 = some (.ref t2)) (h13 : fr.get 13 = some (.ref t3k)) (h14 : fr.get 14 = some (.ref t3))
    (h27 : fr.get 27 = some (.int n)) (hn : n.toInt = g.crs.length) (hi0 : 0 ≤ i.toInt)
    (hlt : i.toInt < n.toInt) (hT1 : TextsAt σ t1 g.T1 0) (hT2 : TextsAt σ t2 g.T2 0)
    (hxs : Forall2 (JStrAt σ) xs (g.T3.take i.toInt.toNat))
    (hxsk : Forall2 (JStrAt σ) xsk (g.K3.take i.toInt.toNat)) (hc : c = g.crs.length - i.toInt.toNat)
    (ht3 : σ.heap t3 = some (.array (.cls "java.lang.String") (xs ++ List.replicate c .null)))
    (ht3k : σ.heap t3k = some (.array (.cls "java.lang.String") (xsk ++ List.replicate c .null)))
    (h0t1 : σ0.next ≤ t1) (h12lt : t1 < t2) (h23lt : t2 < t3k) (h34lt : t3k < t3)
    (hk : i.toInt.toNat < g.crs.length) (htr : tr = g.crs[i.toInt.toNat]'hk)
    (hg : GrowsK σ σ') (hwn : σ.next ≤ w) (hw : σ'.heap w = some (.str (custTextO (some tr))))
    (hin : σ'.inits = σ.inits) (hst : σ'.statics = σ.statics) :
    inv37 g args σ0
      (((((fr.setLocal 25 (.ref x)).setLocal 32 (.ref w)).setLocal 32 (.ref w)).setLocal 32 (.ref σ'.next)).setLocal
        30 (.int (i + 1)))
      (((σ'.setObj t3 (.array (.cls "java.lang.String") (xs ++ (List.replicate c .null).set 0 (.ref w)))).alloc
        (.str [(custTextO (some tr))[0]'(by rw [custTextO_length]; decide),
          (custTextO (some tr))[1]'(by rw [custTextO_length]; decide),
          (custTextO (some tr))[2]'(by rw [custTextO_length]; decide),
          (custTextO (some tr))[3]'(by rw [custTextO_length]; decide),
          (custTextO (some tr))[4]'(by rw [custTextO_length]; decide),
          (custTextO (some tr))[5]'(by rw [custTextO_length]; decide),
          (custTextO (some tr))[6]'(by rw [custTextO_length]; decide),
          (custTextO (some tr))[7]'(by rw [custTextO_length]; decide),
          (custTextO (some tr))[8]'(by rw [custTextO_length]; decide)])).2.setObj t3k
        (.array (.cls "java.lang.String") (xsk ++ (List.replicate c .null).set 0 (.ref σ'.next)))) := by
  have hg' := growsK_elim hg
  have hK1 := keeps_setObj_grows (t := t3) hg'
    (.array (.cls "java.lang.String") (xs ++ (List.replicate c .null).set 0 (.ref w)))
  have ht3lt : t3 < σ.next := State.lt_next_of_heap ht3
  have ht3klt : t3k < σ.next := State.lt_next_of_heap ht3k
  have ht3lt' : t3 < σ'.next := Nat.lt_of_lt_of_le ht3lt hg'.1
  have ht3klt' : t3k < σ'.next := Nat.lt_of_lt_of_le ht3klt hg'.1
  have hwt : w ≠ t3 := fun e => Nat.lt_irrefl t3 (Nat.lt_of_lt_of_le ht3lt (e ▸ hwn))
  have h0t3k : σ0.next ≤ t3k := Nat.le_of_lt (Nat.lt_of_le_of_lt h0t1 (Nat.lt_trans h12lt h23lt))
  have h0t3 : σ0.next ≤ t3 := Nat.le_of_lt (Nat.lt_of_le_of_lt h0t3k h34lt)
  have ht3k1 : (σ'.setObj t3 (.array (.cls "java.lang.String") (xs ++ (List.replicate c .null).set 0 (.ref w)))).heap
      t3k = some (.array (.cls "java.lang.String") (xsk ++ List.replicate c .null)) :=
    heap_keeps_ne hK1 ht3k (Nat.ne_of_lt h34lt)
  generalize hS : [(custTextO (some tr))[0]'(by rw [custTextO_length]; decide),
          (custTextO (some tr))[1]'(by rw [custTextO_length]; decide),
          (custTextO (some tr))[2]'(by rw [custTextO_length]; decide),
          (custTextO (some tr))[3]'(by rw [custTextO_length]; decide),
          (custTextO (some tr))[4]'(by rw [custTextO_length]; decide),
          (custTextO (some tr))[5]'(by rw [custTextO_length]; decide),
          (custTextO (some tr))[6]'(by rw [custTextO_length]; decide),
          (custTextO (some tr))[7]'(by rw [custTextO_length]; decide),
          (custTextO (some tr))[8]'(by rw [custTextO_length]; decide)] = K
  generalize hσ1 : σ'.setObj t3 (.array (.cls "java.lang.String") (xs ++ (List.replicate c .null).set 0 (.ref w)))
    = σ1 at hK1 ht3k1 ⊢
  have hn1 : σ1.next = σ'.next := by rw [← hσ1, State.next_setObj]
  have hK2 : Keeps (· = t3k) σ1 (((σ1.alloc (.str K)).2).setObj t3k
      (.array (.cls "java.lang.String") (xsk ++ (List.replicate c .null).set 0 (.ref σ'.next)))) :=
    keeps_trans (keeps_alloc _ σ1 _) (keeps_setObj _ rfl)
  have hb1 := runBase_keeps (fr' := fr) hb hK1 ht3 h0t3 (by rw [← hσ1]; exact hin) (by rw [← hσ1]; exact hst)
    rfl rfl rfl rfl rfl
  have hadd := i32_toInt_add_one hlt
  have he : (i + 1).toInt.toNat = i.toInt.toNat + 1 := by rw [hadd]; omega
  have hc' : g.crs.length - (i.toInt.toNat + 1) = c - 1 := by rw [hc]; omega
  have hT3len : i.toInt.toNat < g.T3.length := by simp [RunG.T3]; exact hk
  have hK3len : i.toInt.toNat < g.K3.length := by simp [RunG.K3, RunG.T3]; exact hk
  have hm1 : StrMono σ σ1 := strMono_of_keeps hK1 ht3
  have hm2 := strMono_of_keeps hK2 ht3k1
  have hst3 : TextsAt σ1 t3 (g.T3.take (i.toInt.toNat + 1)) (c - 1) := by
    refine textsAt_store0 (y := w) (s := custTextO (some tr)) hxs hT3len (by omega) hm1 ?_ ?_ ?_
    · rw [← hσ1, State.heap_setObj_of_lt ht3lt', if_pos rfl]
    · rw [← hσ1, State.heap_setObj_of_lt ht3lt', if_neg hwt]; exact hw
    · simp [RunG.T3, htr, custTextO]
  have hσ1lt : t3k < (σ1.alloc (.str K)).2.next := by
    rw [State.next_alloc, hn1]; exact Nat.lt_succ_of_lt ht3klt'
  refine ⟨res, ld, ls, lh, t1, t2, t3k, t3, n, i + 1, runBase_keeps hb1 hK2 ht3k1 h0t3k rfl rfl ?_ ?_ ?_ ?_ ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, hn, ?_, ?_, ?_, ?_, ?_, ?_, h0t1, h12lt, h23lt, h34lt⟩
  · simp [Frame.get_setLocal]
  · simp [Frame.get_setLocal]
  · simp [Frame.get_setLocal]
  · simp [Frame.get_setLocal]
  · simp [Frame.get_setLocal]
  · simp [Frame.get_setLocal, h11]
  · simp [Frame.get_setLocal, h12]
  · simp [Frame.get_setLocal, h13]
  · simp [Frame.get_setLocal, h14]
  · simp [Frame.get_setLocal, h27]
  · simp [Frame.get_setLocal]
  · rw [hadd]; omega
  · rw [hadd]; omega
  · exact textsAt_keeps (textsAt_keeps hT1 hK1 ht3 (Nat.ne_of_lt (Nat.lt_trans h12lt (Nat.lt_trans h23lt h34lt))))
      hK2 ht3k1 (Nat.ne_of_lt (Nat.lt_trans h12lt h23lt))
  · exact textsAt_keeps (textsAt_keeps hT2 hK1 ht3 (Nat.ne_of_lt (Nat.lt_trans h23lt h34lt)))
      hK2 ht3k1 (Nat.ne_of_lt h23lt)
  · rw [he, hc']
    refine textsAt_store0 (y := σ'.next) (s := K) hxsk hK3len (by omega) (strMono_trans hm1 hm2) ?_ ?_ ?_
    · rw [State.heap_setObj_of_lt hσ1lt, if_pos rfl]
    · have hne : σ'.next ≠ t3k := fun e => Nat.lt_irrefl t3k (e ▸ ht3klt')
      rw [State.heap_setObj_of_lt hσ1lt, if_neg hne, State.heap_alloc, if_pos hn1.symm]
    · rw [← hS, take9_explicit]
      simp [RunG.K3, RunG.T3, htr, custTextO]
  · rw [he, hc']
    exact textsAt_keeps hst3 hK2 ht3k1 (Nat.ne_of_gt h34lt)

/-- The exit: all customer texts and keys stored, the ACCTFILE array new. -/
theorem c37_exit_close {g : RunG} {args : List Value} {σ0 σ : State} {fr : Frame}
    {res ld ls lh t1 t2 t3k t3 : Addr} {n i : I32} {xs xsk xs4 : List Value}
    (hb : RunBase g σ0 fr σ res ld ls lh JOut.init) (h11 : fr.get 11 = some (.ref t1))
    (h12 : fr.get 12 = some (.ref t2)) (h13 : fr.get 13 = some (.ref t3k)) (h14 : fr.get 14 = some (.ref t3))
    (h27 : fr.get 27 = some (.int n))
    (hn : n.toInt = g.crs.length) (hge : ¬ i.toInt < n.toInt) (hin : i.toInt ≤ n.toInt) (hi0 : 0 ≤ i.toInt)
    (hT1 : TextsAt σ t1 g.T1 0) (hT2 : TextsAt σ t2 g.T2 0)
    (hxs : Forall2 (JStrAt σ) xs (g.T3.take i.toInt.toNat))
    (hxsk : Forall2 (JStrAt σ) xsk (g.K3.take i.toInt.toNat))
    (ht3 : σ.heap t3 = some (.array (.cls "java.lang.String")
      (xs ++ List.replicate (g.crs.length - i.toInt.toNat) .null)))
    (ht3k : σ.heap t3k = some (.array (.cls "java.lang.String")
      (xsk ++ List.replicate (g.crs.length - i.toInt.toNat) .null)))
    (h0t1 : σ0.next ≤ t1) (h12lt : t1 < t2) (h23lt : t2 < t3k) (h34lt : t3k < t3)
    (hl4 : xs4.length < 2147483648) (hlen4 : xs4.length = g.ars.length) :
    inv52 g args σ0
      (((fr.setLocal 28 (.int (BitVec.ofNat 32 xs4.length))).setLocal 15 (.ref σ.next)).setLocal 26 (.int 0))
      (σ.alloc (.array (.cls "java.lang.String") (List.replicate xs4.length .null))).2 := by
  have hT3 : TextsAt σ t3 g.T3 0 := textsAt_full hxs (by simp [RunG.T3]) (by omega) ht3
  have hK3 : TextsAt σ t3k g.K3 0 := textsAt_full hxsk (by simp [RunG.K3, RunG.T3]) (by omega) ht3k
  refine ⟨res, ld, ls, lh, t1, t2, t3k, t3, σ.next, n, BitVec.ofNat 32 xs4.length, 0,
    runBase_alloc hb _ ?_ ?_ ?_ ?_ ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hn, ?_, ?_, ?_,
    textsAt_alloc hT1 _, textsAt_alloc hT2 _, textsAt_alloc hK3 _, textsAt_alloc hT3 _, ?_, h0t1, h12lt, h23lt,
    h34lt, State.lt_next_of_heap ht3⟩
  · simp [Frame.get_setLocal]
  · simp [Frame.get_setLocal]
  · simp [Frame.get_setLocal]
  · simp [Frame.get_setLocal]
  · simp [Frame.get_setLocal]
  · simp [Frame.get_setLocal, h11]
  · simp [Frame.get_setLocal, h12]
  · simp [Frame.get_setLocal, h13]
  · simp [Frame.get_setLocal, h14]
  · simp [Frame.get_setLocal]
  · simp [Frame.get_setLocal, h27]
  · simp [Frame.get_setLocal]
  · simp [Frame.get_setLocal]
  · rw [bv32_toInt_ofNat_of_lt hl4, hlen4]
  · simp [i32_zero_toInt]
  · rw [i32_zero_toInt, bv32_toInt_ofNat_of_lt hl4]; omega
  · rw [i32_zero_toInt]
    simp only [Int.toNat_zero, List.take_zero, Nat.sub_zero]
    rw [← hlen4]
    exact textsAt_new (by simp [State.heap_alloc])

section paths

attribute [local irreducible] CustAtN custTextO

set_option jimple.modelContracts true in
set_option maxRecDepth 8000 in
set_option maxHeartbeats 400000 in
/-- Statements 38 … 45 back to 37. -/
theorem c37_loop (g : RunG) (σ0 : State) (fr : Frame) (σ : State) (res ld ls lh t1 t2 t3k t3 x : Addr)
    (n i : I32) (et3 : JType) (xs3 xsk xs : List Value) (tr : CustR) (c : Nat)
    (hb : RunBase g σ0 fr σ res ld ls lh JOut.init) (hT1 : TextsAt σ t1 g.T1 0) (hT2 : TextsAt σ t2 g.T2 0)
    (hxs : Forall2 (JStrAt σ) xs (g.T3.take i.toInt.toNat))
    (hxsk : Forall2 (JStrAt σ) xsk (g.K3.take i.toInt.toNat))
    (hn : n.toInt = g.crs.length) (h0t1 : σ0.next ≤ t1) (h12lt : t1 < t2) (h23lt : t2 < t3k) (h34lt : t3k < t3)
    (hc : c = g.crs.length - i.toInt.toNat)
    (htrE : ∃ hk : i.toInt.toNat < g.crs.length, tr = g.crs[i.toInt.toNat]'hk) (h11 : fr.get 11 = some (.ref t1))
    (h12 : fr.get 12 = some (.ref t2))
    (h9 : fr.get 9 = some (.ref g.a3)) (h13 : fr.get 13 = some (.ref t3k)) (h14 : fr.get 14 = some (.ref t3))
    (h27 : fr.get 27 = some (.int n))
    (h30 : fr.get 30 = some (.int i)) (hha3 : σ.heap g.a3 = some (.array et3 xs3))
    (hn1 : n.toInt = xs3.length) (hi0 : 0 ≤ i.toInt) (hlt : i.toInt < n.toInt)
    (hk : i.toInt.toNat < xs3.length) (hel : xs3[i.toInt.toNat]'hk = .ref x)
    (htr : CustAtN σ (.ref x) (some tr)) (hci : σ.initOf "Cbstm03a" = .done)
    (hlen : (custTextO (some tr)).length = 500)
    (ht3 : σ.heap t3 = some (.array (.cls "java.lang.String") (xs ++ List.replicate c .null)))
    (ht3k : σ.heap t3k = some (.array (.cls "java.lang.String") (xsk ++ List.replicate c .null)))
    (hxl : xs.length = i.toInt.toNat) (hxkl : xsk.length = i.toInt.toNat) (hc0 : 0 < c)
    (ht3lt : t3 < σ.next) (ht3klt : t3k < σ.next) (hne : t3k ≠ t3) (hne' : t3 ≠ t3k) :
    runWP g [.ref g.a1, .ref g.a2, .ref g.a3, .ref g.a4] σ0 37 fr σ := by
  have hH := hid_intro (And.intro hb (And.intro hT1 (And.intro hT2 (And.intro hxs (And.intro hxsk (And.intro hn
    (And.intro h0t1 (And.intro h12lt (And.intro h23lt (And.intro h34lt (And.intro hc (And.intro htrE
    (And.intro h11 h12)))))))))))))
  clear hb hT1 hT2 hxs hxsk hn h0t1 h12lt h23lt h34lt hc htrE h11 h12
  unfold runWP
  jvc [runCallees, runInv, grows_split, getElem?_append_set0, getElem_append_set0]
  obtain ⟨hb, hT1, hT2, hxs, hxsk, hn, h0t1, h12lt, h23lt, h34lt, hc, ⟨hkT, htrE⟩, h11, h12⟩ := hid_elim hH
  exact c37_loop_close hb h11 h12 h13 h14 h27 hn hi0 hlt hT1 hT2 hxs hxsk hc ht3 ht3k h0t1 h12lt h23lt h34lt
    hkT htrE (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)

set_option maxRecDepth 8000 in
set_option maxHeartbeats 400000 in
/-- Statements 46 … 51 to 52. -/
theorem c37_exit (g : RunG) (σ0 : State) (fr : Frame) (σ : State) (res ld ls lh t1 t2 t3k t3 : Addr)
    (n i : I32) (et4 : JType) (xs xsk xs4 : List Value)
    (hb : RunBase g σ0 fr σ res ld ls lh JOut.init) (h11 : fr.get 11 = some (.ref t1))
    (h12 : fr.get 12 = some (.ref t2)) (h13 : fr.get 13 = some (.ref t3k)) (h14 : fr.get 14 = some (.ref t3))
    (hn : n.toInt = g.crs.length) (hin : i.toInt ≤ n.toInt) (hi0 : 0 ≤ i.toInt)
    (hT1 : TextsAt σ t1 g.T1 0) (hT2 : TextsAt σ t2 g.T2 0)
    (hxs : Forall2 (JStrAt σ) xs (g.T3.take i.toInt.toNat))
    (hxsk : Forall2 (JStrAt σ) xsk (g.K3.take i.toInt.toNat))
    (ht3 : σ.heap t3 = some (.array (.cls "java.lang.String")
      (xs ++ List.replicate (g.crs.length - i.toInt.toNat) .null)))
    (ht3k : σ.heap t3k = some (.array (.cls "java.lang.String")
      (xsk ++ List.replicate (g.crs.length - i.toInt.toNat) .null)))
    (h0t1 : σ0.next ≤ t1) (h12lt : t1 < t2) (h23lt : t2 < t3k) (h34lt : t3k < t3)
    (hlen4 : xs4.length = g.ars.length)
    (h6 : fr.get 6 = some (.ref g.a4)) (h27 : fr.get 27 = some (.int n))
    (h30 : fr.get 30 = some (.int i)) (hha4 : σ.heap g.a4 = some (.array et4 xs4))
    (hl4 : xs4.length < 2147483648) (hge : ¬ i.toInt < n.toInt) :
    runWP g [.ref g.a1, .ref g.a2, .ref g.a3, .ref g.a4] σ0 37 fr σ := by
  have hH := hid_intro (And.intro hb (And.intro h11 (And.intro h12 (And.intro h13 (And.intro h14 (And.intro hn
    (And.intro hin (And.intro hi0 (And.intro hT1 (And.intro hT2 (And.intro hxs (And.intro hxsk (And.intro ht3
    (And.intro ht3k (And.intro h0t1 (And.intro h12lt (And.intro h23lt (And.intro h34lt hlen4))))))))))))))))))
  clear hb h11 h12 h13 h14 hn hin hi0 hT1 hT2 hxs hxsk ht3 ht3k h0t1 h12lt h23lt h34lt hlen4
  unfold runWP
  jvc [runCallees, runInv, grows_split]
  obtain ⟨hb, h11, h12, h13, h14, hn, hin, hi0, hT1, hT2, hxs, hxsk, ht3, ht3k, h0t1, h12lt, h23lt, h34lt,
    hlen4⟩ := hid_elim hH
  exact c37_exit_close hb h11 h12 h13 h14 h27 hn hge hin hi0 hT1 hT2 hxs hxsk ht3 ht3k h0t1 h12lt h23lt h34lt
    hl4 hlen4

end paths

end EquivLean.Modernize.Cbstm03a.Java.Seg1

namespace EquivLean.Modernize.Cbstm03a.Java

open Seg1

theorem run_cut37_vc (g : RunG) : RunCutVC g 37 inv37 := by
  intro args σ0 hpre fr σ hI
  obtain ⟨hargs, -, -, ⟨et3, xs3, hh3, hl3, hf3⟩, ⟨et4, xs4, hh4, hl4, hf4⟩, ⟨hcpi, -⟩, -⟩ := hpre
  subst hargs
  obtain ⟨res, ld, ls, lh, t1, t2, t3k, t3, n, i, hb, h11, h12, h13, h14, h27, h30, hn, hi0, hin, hT1, hT2,
    ⟨xsk, ht3k, hxsk⟩, ⟨xs, ht3, hxs⟩, h0t1, h12lt, h23lt, h34lt⟩ := hI
  have hb' := hb
  obtain ⟨-, -, h9, h6, -, -, -, -, -, -, hg, hinits, -⟩ := hb'
  by_cases hlt : i.toInt < n.toInt
  · have hlen3 := forall2_length hf3
    have hk : i.toInt.toNat < g.crs.length := by omega
    obtain ⟨hk1, x, hx, hat⟩ := recsAt_elem hf3 _ hk
    have hxl : xs.length = i.toInt.toNat := by
      rw [forall2_length hxs, List.length_take]; simp [RunG.T3]; omega
    have hxkl : xsk.length = i.toInt.toNat := by
      rw [forall2_length hxsk, List.length_take]; simp [RunG.K3, RunG.T3]; omega
    exact c37_loop g σ0 fr σ res ld ls lh t1 t2 t3k t3 x n i et3 xs3 xsk xs _ _ hb hT1 hT2 hxs hxsk hn h0t1
      h12lt h23lt h34lt rfl ⟨hk, rfl⟩ h11 h12 h9 h13 h14 h27 h30 (heap_grows hg hh3) (by rw [hn, hlen3]) hi0 hlt
      hk1 hx ⟨x, rfl, custAt_grows hat hg⟩ (by rw [State.initOf_eq_of_inits hinits]; exact hcpi)
      (custTextO_length _) ht3 ht3k hxl hxkl (by omega) (State.lt_next_of_heap ht3) (State.lt_next_of_heap ht3k)
      (Nat.ne_of_lt h34lt) (Nat.ne_of_gt h34lt)
  · exact c37_exit g σ0 fr σ res ld ls lh t1 t2 t3k t3 n i et4 xs xsk xs4 hb h11 h12 h13 h14 hn hin hi0 hT1 hT2
      hxs hxsk ht3 ht3k h0t1 h12lt h23lt h34lt (forall2_length hf4) h6 h27 h30 (heap_grows hg hh4) hl4 hlt

end EquivLean.Modernize.Cbstm03a.Java

#print axioms EquivLean.Modernize.Cbstm03a.Java.run_cut37_vc
