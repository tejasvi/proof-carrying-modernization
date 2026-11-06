import EquivLean.Modernize.Cbstm03a.Java.Run2.Steps

/-!
# CBSTM03A → Java `run`, the load loop: the loop head's facts the target invariants need

`Orig`: what the loop head's invariant says about its own frame and state (the parts the closers rebuild in the
end state), bundled.
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows Keeps fixStr argText space GrowsK Kept)

namespace EquivLean.Modernize.Cbstm03a.Java.Seg2

/-- The loop head's facts at `p.fr`, `p.σ` for the target invariants. -/
def Orig (g : RunG) (σ0 : State) (p : LP) (res ld ls lh t2 t3k t3 t4 : Addr) : Prop :=
  RunBase g σ0 p.fr p.σ res ld ls lh JOut.init ∧ RunTexts g σ0 p.fr p.σ p.t1 t2 t3k t3 t4 ∧
    p.fr.get 16 = some (.ref p.mem) ∧ p.fr.get 24 = some (.ref p.trct) ∧ p.fr.get 1 = some (.ref p.st1) ∧
    (∃ vs, p.σ.heap p.mem = some (.array (.cls "java.lang.String") vs)) ∧
    p.σ.heap p.trct = some (.array (.prim .long) p.s.trct) ∧
    p.σ.heap p.st1 = some (.array (.prim .int) [.int (BitVec.ofNat 32 (p.k + 1)), .int 0]) ∧
    t4 < p.mem ∧ p.s.trct.length = 51 ∧ LdBounded p.s ∧ p.k < g.R1.length ∧ p.r = g.R1.getD p.k [] ∧
    xrefAll g.K3 g.T3 g.T4 (ldFin (ldAll p.s (g.R1.drop p.k))) JOut.init g.T2 = g.F

theorem sameLocs_ne11 (i : Nat) (hi : i = 10 ∨ i = 23 ∨ i = 9 ∨ i = 6 ∨ i = 7 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨
    i = 14 ∨ i = 15 ∨ i = 27 ∨ i = 28 ∨ i = 16 ∨ i = 24 ∨ i = 1) :
    i ≠ 33 ∧ i ≠ 3 ∧ i ≠ 26 ∧ i ≠ 2 ∧ i ≠ 5 ∧ i ≠ 19 ∧ i ≠ 32 ∧ i ≠ 17 ∧ i ≠ 18 ∧ i ≠ 36 ∧ i ≠ 34 := by
  omega

theorem sameLocs_step {fr fr1 fr2 : Frame} (h : SameLocs fr fr1)
    (hf : ∀ i, i ≠ 33 → i ≠ 3 → i ≠ 26 → i ≠ 2 → i ≠ 5 → i ≠ 19 → i ≠ 32 → i ≠ 17 → i ≠ 18 → i ≠ 36 →
      i ≠ 34 → fr2.get i = fr1.get i) : SameLocs fr fr2 := fun i hi => by
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11⟩ := sameLocs_ne11 i hi
  exact (hf i n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11).trans (h i hi)

/-- Back at the loop head, from the facts of the end state. -/
theorem close80' {g : RunG} {args : List Value} {σ0 : State} {p : LP} {res ld ls lh t2 t3k t3 t4 : Addr}
    (ho : Orig g σ0 p res ld ls lh t2 t3k t3 t4) (o2 : p.mem < p.trct) (o3 : p.trct < p.st1)
    {fr' : Frame} {σ' : State}
    (hk : Keeps (Upd3 p.mem p.trct p.st1) p.σ σ') (hinit : σ'.inits = p.σ.inits)
    (hstat : σ'.statics = p.σ.statics) (hf : SameLocs p.fr fr')
    (hslots' : SlotsAt σ' p.mem p.L.m) (htr' : σ'.heap p.trct = some (.array (.prim .long) p.L.trct))
    (hst1' : σ'.heap p.st1 = some (.array (.prim .int) [.int (BitVec.ofNat 32 (p.k + 1 + 1)), .int 0]))
    (hk' : p.k + 1 < g.R1.length) (h33 : StrLoc σ' fr' 33 (g.R1.getD (p.k + 1) []))
    (h32 : StrLoc σ' fr' 32 p.L.save)
    (h18 : fr'.get 18 = some (.long p.L.cr)) (h17 : fr'.get 17 = some (.long p.L.tr)) :
    inv80 g args σ0 fr' σ' := by
  obtain ⟨hbase, htexts, h16, h24, h1, ⟨vs, hm⟩, ht, hs, o1, htl, hb, hkR, hrec, heq⟩ := ho
  refine close80 hbase htexts h16 h24 h1 hm ht hs o1 o2 o3 hk hinit hstat hf p.L (p.k + 1) hslots' htr'
    ((ldStep_trct_length _ _).trans htl) hst1' hk' h33 h32 h18 h17 (ldStep_bounded _ hb) ?_
  rw [ldAll_drop_succ p.s g.R1 p.k hkR, ← hrec] at heq
  exact heq

/-- The load done, from the facts of the end state. -/
theorem close117' {g : RunG} {args : List Value} {σ0 : State} {p : LP} {res ld ls lh t2 t3k t3 t4 : Addr}
    (ho : Orig g σ0 p res ld ls lh t2 t3k t3 t4) (o2 : p.mem < p.trct) (o3 : p.trct < p.st1)
    (hlast : p.k + 1 = g.R1.length) {fr' : Frame} {σ' : State}
    (hk : Keeps (Upd3 p.mem p.trct p.st1) p.σ σ') (hinit : σ'.inits = p.σ.inits)
    (hstat : σ'.statics = p.σ.statics) (hf : SameLocs p.fr fr')
    (hslots' : SlotsAt σ' p.mem (ldFin p.L).m)
    (htr' : σ'.heap p.trct = some (.array (.prim .long) (ldFin p.L).trct))
    {st2 : Addr} (h2 : fr'.get 2 = some (.ref st2))
    (hst2 : σ'.heap st2 = some (.array (.prim .int) [.int (BitVec.ofNat 32 0), .int 0])) (hst2n : p.σ.next ≤ st2)
    (h5 : fr'.get 5 = some (.int 0)) (h3 : fr'.get 3 = some (.int 0))
    (h18 : fr'.get 18 = some (.long (ldFin p.L).cr)) :
    inv117 g args σ0 fr' σ' := by
  obtain ⟨hbase, htexts, h16, h24, h1, ⟨vs, hm⟩, ht, hs, o1, htl, hb, hkR, hrec, heq⟩ := ho
  refine close117 hbase htexts h16 h24 hm ht hs o1 o2 o3 hk hinit hstat hf (ldFin p.L) st2 hslots' htr'
    ?_ h2 hst2 hst2n h5 h3 h18 (ldFin_bounded (ldStep_bounded _ hb)) ?_
  · show (trctSet p.L.trct p.L.cr p.L.tr).length = 51
    rw [trctSet_lengthR, ldStep_trct_length]; exact htl
  · rw [ldAll_drop_last p.s g.R1 p.k hlast, ← hrec] at heq
    exact heq

end EquivLean.Modernize.Cbstm03a.Java.Seg2
