import EquivLean.Modernize.Cbstm03a.Java.Run2.Frame

/-!
# CBSTM03A → Java `run`, the load loop: the target invariants from the facts of a path's end

The paths from statement 80 update in place only the table memory, the counts array and `trnxSt` (`Upd3`, all
three arrays allocated after the text arrays); everything else of the loop head's facts carries over a
`Keeps (Upd3 …)`. `close80` (back at the loop head) and `close117` (the load done) take the new values.
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows Keeps fixStr argText space GrowsK)

namespace EquivLean.Modernize.Cbstm03a.Java.Seg2

/-- The three objects the load loop updates in place. -/
abbrev Upd3 (mem trct st1 : Addr) : Addr → Prop := fun y => y = mem ∨ y = trct ∨ y = st1

theorem arrOnly3 {σ : State} {mem trct st1 : Addr} {e1 e2 e3 : JType} {v1 v2 v3 : List Value}
    (h1 : σ.heap mem = some (.array e1 v1)) (h2 : σ.heap trct = some (.array e2 v2))
    (h3 : σ.heap st1 = some (.array e3 v3)) : ArrOnly (Upd3 mem trct st1) σ := by
  rintro y (rfl | rfl | rfl)
  · exact ⟨_, _, h1⟩
  · exact ⟨_, _, h2⟩
  · exact ⟨_, _, h3⟩

theorem not_upd3 {mem trct st1 t : Addr} (h1 : t < mem) (h2 : mem < trct) (h3 : trct < st1) :
    ¬ Upd3 mem trct st1 t := by
  rintro (rfl | rfl | rfl)
  · exact Nat.lt_irrefl _ h1
  · exact Nat.lt_irrefl _ (Nat.lt_trans h1 h2)
  · exact Nat.lt_irrefl _ (Nat.lt_trans (Nat.lt_trans h1 h2) h3)

/-- The locals the invariants read and the paths do not write. -/
def SameLocs (fr fr' : Frame) : Prop :=
  ∀ i, i = 10 ∨ i = 23 ∨ i = 9 ∨ i = 6 ∨ i = 7 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 27 ∨
    i = 28 ∨ i = 16 ∨ i = 24 ∨ i = 1 → fr'.get i = fr.get i

/-- The loop head's facts that every path carries over. -/
theorem carry {g : RunG} {σ0 : State} {fr : Frame} {σ : State}
    {res ld ls lh t1 t2 t3k t3 t4 mem trct st1 : Addr} {fr' : Frame} {σ' : State}
    (hbase : RunBase g σ0 fr σ res ld ls lh JOut.init) (htexts : RunTexts g σ0 fr σ t1 t2 t3k t3 t4)
    {e1 e2 e3 : JType} {v1 v2 v3 : List Value}
    (hm : σ.heap mem = some (.array e1 v1)) (ht : σ.heap trct = some (.array e2 v2))
    (hs : σ.heap st1 = some (.array e3 v3))
    (o1 : t4 < mem) (o2 : mem < trct) (o3 : trct < st1)
    (hk : Keeps (Upd3 mem trct st1) σ σ') (hinit : σ'.inits = σ.inits) (hstat : σ'.statics = σ.statics)
    (hf : SameLocs fr fr') :
    RunBase g σ0 fr' σ' res ld ls lh JOut.init ∧ RunTexts g σ0 fr' σ' t1 t2 t3k t3 t4 := by
  obtain ⟨b10, b23, b9, b6, b7, bres, bn1, bn2, bn3, bn4, bg, bi, bs⟩ := hbase
  obtain ⟨x11, x12, x13, x14, x15, ⟨n3, x27, hn3⟩, ⟨n4, x28, hn4⟩, T1, T2, T3k, T3, T4, q0, q1, q2, q3, q4⟩ :=
    htexts
  have hA := arrOnly3 hm ht hs
  have l4 : t4 < mem := o1
  have l3 : t3 < mem := Nat.lt_trans q4 l4
  have l3k : t3k < mem := Nat.lt_trans q3 l3
  have l2 : t2 < mem := Nat.lt_trans q2 l3k
  have l1 : t1 < mem := Nat.lt_trans q1 l2
  have c1 : σ0.next < mem := Nat.lt_of_le_of_lt q0 l1
  have hA0 : ∀ y, Upd3 mem trct st1 y → σ0.next ≤ y := by
    rintro y (rfl | rfl | rfl)
    · exact Nat.le_of_lt c1
    · exact Nat.le_of_lt (Nat.lt_trans c1 o2)
    · exact Nat.le_of_lt (Nat.lt_trans (Nat.lt_trans c1 o2) o3)
  refine ⟨?_, ?_⟩
  · unfold RunBase
    exact ⟨(hf 10 (by simp)).trans b10, (hf 23 (by simp)).trans b23, (hf 9 (by simp)).trans b9,
      (hf 6 (by simp)).trans b6, (hf 7 (by simp)).trans b7, resAtL_keeps hk hA bres, bn1, bn2, bn3, bn4,
      grows_keeps bg hk hA0, hinit.trans bi, hstat.trans bs⟩
  · unfold RunTexts
    exact ⟨(hf 11 (by simp)).trans x11, (hf 12 (by simp)).trans x12, (hf 13 (by simp)).trans x13,
      (hf 14 (by simp)).trans x14, (hf 15 (by simp)).trans x15, ⟨n3, (hf 27 (by simp)).trans x27, hn3⟩,
      ⟨n4, (hf 28 (by simp)).trans x28, hn4⟩, textsAt_keeps hk hA T1 (not_upd3 l1 o2 o3),
      textsAt_keeps hk hA T2 (not_upd3 l2 o2 o3), textsAt_keeps hk hA T3k (not_upd3 l3k o2 o3),
      textsAt_keeps hk hA T3 (not_upd3 l3 o2 o3), textsAt_keeps hk hA T4 (not_upd3 l4 o2 o3), q0, q1, q2, q3, q4⟩

/-- Back at the loop head with record `k'` and the load state `s'`. -/
theorem close80 {g : RunG} {args : List Value} {σ0 : State} {fr : Frame} {σ : State}
    {res ld ls lh t1 t2 t3k t3 t4 mem trct st1 : Addr} {fr' : Frame} {σ' : State}
    (hbase : RunBase g σ0 fr σ res ld ls lh JOut.init) (htexts : RunTexts g σ0 fr σ t1 t2 t3k t3 t4)
    (h16 : fr.get 16 = some (.ref mem)) (h24 : fr.get 24 = some (.ref trct)) (h1 : fr.get 1 = some (.ref st1))
    {e1 e2 e3 : JType} {v1 v2 v3 : List Value}
    (hm : σ.heap mem = some (.array e1 v1)) (ht : σ.heap trct = some (.array e2 v2))
    (hs : σ.heap st1 = some (.array e3 v3))
    (o1 : t4 < mem) (o2 : mem < trct) (o3 : trct < st1)
    (hk : Keeps (Upd3 mem trct st1) σ σ') (hinit : σ'.inits = σ.inits) (hstat : σ'.statics = σ.statics)
    (hf : SameLocs fr fr') (s' : LdSt) (k' : Nat)
    (hslots' : SlotsAt σ' mem s'.m) (htr' : σ'.heap trct = some (.array (.prim .long) s'.trct))
    (htl' : s'.trct.length = 51)
    (hst1' : σ'.heap st1 = some (.array (.prim .int) [.int (BitVec.ofNat 32 (k' + 1)), .int 0]))
    (hk' : k' < g.R1.length) (h33 : StrLoc σ' fr' 33 (g.R1.getD k' [])) (h32 : StrLoc σ' fr' 32 s'.save)
    (h18 : fr'.get 18 = some (.long s'.cr)) (h17 : fr'.get 17 = some (.long s'.tr)) (hb : LdBounded s')
    (heq : xrefAll g.K3 g.T3 g.T4 (ldFin (ldAll s' (g.R1.drop k'))) JOut.init g.T2 = g.F) :
    inv80 g args σ0 fr' σ' := by
  obtain ⟨hb', ht'⟩ := carry hbase htexts hm ht hs o1 o2 o3 hk hinit hstat hf
  have hl : LoadAt σ' fr' mem trct s' := by
    unfold LoadAt
    exact ⟨(hf 16 (by simp)).trans h16, (hf 24 (by simp)).trans h24, hslots', htr', htl'⟩
  exact ⟨res, ld, ls, lh, t1, t2, t3k, t3, t4, mem, trct, st1, s', k', hb', ht', hl, (hf 1 (by simp)).trans h1,
    hst1', o1, o2, o3, hk', h33, h32, h18, h17, hb, heq⟩

/-- The load done: the cross-reference loop's head with the table `L`, no record read. -/
theorem close117 {g : RunG} {args : List Value} {σ0 : State} {fr : Frame} {σ : State}
    {res ld ls lh t1 t2 t3k t3 t4 mem trct st1 : Addr} {fr' : Frame} {σ' : State}
    (hbase : RunBase g σ0 fr σ res ld ls lh JOut.init) (htexts : RunTexts g σ0 fr σ t1 t2 t3k t3 t4)
    (h16 : fr.get 16 = some (.ref mem)) (h24 : fr.get 24 = some (.ref trct))
    {e1 e2 e3 : JType} {v1 v2 v3 : List Value}
    (hm : σ.heap mem = some (.array e1 v1)) (ht : σ.heap trct = some (.array e2 v2))
    (hs : σ.heap st1 = some (.array e3 v3))
    (o1 : t4 < mem) (o2 : mem < trct) (o3 : trct < st1)
    (hk : Keeps (Upd3 mem trct st1) σ σ') (hinit : σ'.inits = σ.inits) (hstat : σ'.statics = σ.statics)
    (hf : SameLocs fr fr') (L : LdSt) (st2 : Addr)
    (hslots' : SlotsAt σ' mem L.m) (htr' : σ'.heap trct = some (.array (.prim .long) L.trct))
    (htl' : L.trct.length = 51)
    (h2 : fr'.get 2 = some (.ref st2))
    (hst2 : σ'.heap st2 = some (.array (.prim .int) [.int (BitVec.ofNat 32 0), .int 0])) (hst2n : σ.next ≤ st2)
    (h5 : fr'.get 5 = some (.int 0)) (h3 : fr'.get 3 = some (.int 0)) (h18 : fr'.get 18 = some (.long L.cr))
    (hb : LdBounded L) (heq : xrefAll g.K3 g.T3 g.T4 L JOut.init g.T2 = g.F) :
    inv117 g args σ0 fr' σ' := by
  obtain ⟨hb', ht'⟩ := carry hbase htexts hm ht hs o1 o2 o3 hk hinit hstat hf
  have hl : LoadAt σ' fr' mem trct L := by
    unfold LoadAt
    exact ⟨(hf 16 (by simp)).trans h16, (hf 24 (by simp)).trans h24, hslots', htr', htl'⟩
  have hx : XCtx g σ0 fr' σ' res ld ls lh JOut.init L 0 := by
    unfold XCtx
    exact ⟨t1, t2, t3k, t3, t4, mem, trct, st2, hb', ht', hl, h2, hst2, o1, o2,
      Nat.lt_of_lt_of_le (State.lt_next_of_heap ht) hst2n, h5, h3, h18, hb⟩
  exact ⟨res, ld, ls, lh, L, JOut.init, 0, hx, Nat.zero_le _, heq⟩

theorem bv32_succ (n : Nat) : BitVec.ofNat 32 n + 1 = BitVec.ofNat 32 (n + 1) := by
  apply BitVec.eq_of_toNat_eq
  have h1 : (1 : BitVec 32).toNat = 1 := rfl
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, h1]
  omega

end EquivLean.Modernize.Cbstm03a.Java.Seg2
