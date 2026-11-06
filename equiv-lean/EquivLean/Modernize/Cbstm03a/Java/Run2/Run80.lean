import EquivLean.Modernize.Cbstm03a.Java.Run2.S1
import EquivLean.Modernize.Cbstm03a.Java.Run2.S2
import EquivLean.Modernize.Cbstm03a.Java.Run2.S92
import EquivLean.Modernize.Cbstm03a.Java.Run2.S95
import EquivLean.Modernize.Cbstm03a.Java.Run2.S98
import EquivLean.Modernize.Cbstm03a.Java.Run2.S100L
import EquivLean.Modernize.Cbstm03a.Java.Run2.S100E
import EquivLean.Modernize.Cbstm03a.Java.Run2.S4

/-!
# CBSTM03A → Java `run`: the paths from the load loop's head (statement 80)

`run_cut80_vc`: from `inv80` (record `k` in `cn`, the table holding the load state `s`), the loop body
(`ldStep s (R1[k])`) and `seqRead` lead back to statement 80 with record `k + 1` (`inv80`) or, after the last
record, to the cross-reference loop's head with the table `ldFin` (`inv117`). The paths are cut at statements 88,
92, 95, 98, 100 and 113 (`Seg2.cuts…`, extra cut points introduced by `Seg2.cut_intro`), each segment proved by
`jvc` (`Seg2.seg…`).
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows Keeps fixStr argText StrOk space GrowsK Kept)

namespace EquivLean.Modernize.Cbstm03a.Java

namespace Seg2

theorem forall2_length {α β : Type} {R : α → β → Prop} :
    ∀ {xs : List α} {ys : List β}, Forall2 R xs ys → xs.length = ys.length
  | [], [], .nil => rfl
  | _ :: _, _ :: _, .cons _ h => by simp [forall2_length h]

theorem forall2_jstr_get {σ : State} :
    ∀ {xs : List Value} {ts : List JStr}, Forall2 (JStrAt σ) xs ts → ∀ i, i < ts.length →
      ∃ y, xs[i]? = some (.ref y) ∧ σ.heap y = some (.str (ts.getD i []))
  | [], [], .nil, _, hi => by simp at hi
  | _ :: _, _ :: _, .cons hx _, 0, _ => by
    obtain ⟨y, rfl, hy⟩ := hx
    exact ⟨y, rfl, hy⟩
  | _ :: _, _ :: _, .cons _ h, i + 1, hi => by
    simpa using forall2_jstr_get h i (by simpa using hi)

theorem bv32_toInt (n : Nat) (h : n < 2147483648) : (BitVec.ofNat 32 n).toInt = n := by
  rw [BitVec.toInt_eq_toNat_cond, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), if_pos (by omega)]

theorem bv32_toNat (n : Nat) (h : n < 2147483648) : (BitVec.ofNat 32 n).toNat = n := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- The paths from statement 80 for the loop head's values `p`, from the segments. -/
theorem run80_of_segs {g : RunG} {args : List Value} {σ0 : State} {p : LP}
    (h113 : ∀ fr σ, A113 p fr σ → segWP g args σ0 (cuts0 g args σ0) 40 113 fr σ)
    (h100 : ∀ fr σ, A100 p fr σ → segWP g args σ0 (cuts113 g args σ0 p) 40 100 fr σ)
    (h98 : ∀ fr σ, A98 p fr σ → segWP g args σ0 (cuts100 g args σ0 p) 40 98 fr σ)
    (h95 : ∀ fr σ, A95 p fr σ → segWP g args σ0 (cuts98 g args σ0 p) 40 95 fr σ)
    (h92 : ∀ fr σ, A92 p fr σ → segWP g args σ0 (cuts95 g args σ0 p) 40 92 fr σ)
    (h80 : segWP g args σ0 (cuts92 g args σ0 p) 80 80 p.fr p.σ) :
    segWP g args σ0 (cuts0 g args σ0) 300 80 p.fr p.σ := by
  have hH : HMono (callWP Gen.prog runCallees.env 1) := callWP_mono _ 1
  refine bodyWP_fuel_le hH (show 240 + 40 ≤ 300 by omega) ?_
  refine cut_intro hH runBodyA (cuts0 g args σ0) _ 113 (A113 p) rfl 40 h113 240 80 p.fr p.σ ?_
  refine cut_intro hH runBodyA (cuts113 g args σ0 p) _ 100 (A100 p) rfl 40 h100 200 80 p.fr p.σ ?_
  refine cut_intro hH runBodyA (cuts100 g args σ0 p) _ 98 (A98 p) rfl 40 h98 160 80 p.fr p.σ ?_
  refine cut_intro hH runBodyA (cuts98 g args σ0 p) _ 95 (A95 p) rfl 40 h95 120 80 p.fr p.σ ?_
  exact cut_intro hH runBodyA (cuts95 g args σ0 p) _ 92 (A92 p) rfl 40 h92 80 80 p.fr p.σ h80

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- The paths from statement 80 up to statement 92: both branches of the comparison. -/
theorem run80_head {g : RunG} {args : List Value} {σ0 : State} {p : LP}
    (o0 : p.t1 < p.mem) (o2 : p.mem < p.trct) (o3 : p.trct < p.st1)
    (hI0 : p.σ.initOf "Cbstm03a" = .done) {x33 x32 : Addr}
    (h33 : p.fr.get 33 = some (.ref x33)) (hx33 : p.σ.heap x33 = some (.str p.r)) (hrl : p.r.length = 350)
    (h32 : p.fr.get 32 = some (.ref x32)) (hx32 : p.σ.heap x32 = some (.str p.s.save))
    (h18 : p.fr.get 18 = some (.long p.s.cr)) (h17 : p.fr.get 17 = some (.long p.s.tr)) (hc : HeadAt p) :
    segWP g args σ0 (cuts92 g args σ0 p) 80 80 p.fr p.σ := by
  have hH : HMono (callWP Gen.prog runCallees.env 1) := callWP_mono _ 1
  by_cases hsv : List.take 16 p.r = p.s.save
  · exact bodyWP_fuel_le hH (show 40 ≤ 80 by omega)
      (seg1E g args σ0 p o0 o2 o3 hI0 x33 x32 h33 hx33 hrl h32 hx32 h18 h17 hsv (Kept.intro hc))
  · have hne : ¬ p.s.save = sub p.r 0 16 := fun e => hsv (by simp only [sub, List.drop_zero] at e; exact e.symm)
    refine cut_intro hH runBodyA (cuts92 g args σ0 p) _ 88 (A88 p) rfl 40
      (seg2 g args σ0 p o0 o2 o3 (Kept.intro hne)) 40 80 p.fr p.σ ?_
    exact seg1N g args σ0 p o0 o2 o3 hI0 x33 x32 h33 hx33 hrl h32 hx32 h18 h17 hsv (fun e => hsv e.symm)
      (Kept.intro hc)

end Seg2

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
open Seg2 in
/-- **The paths from the load loop's head (statement 80)**: back to statement 80 with the next record, or to the
cross-reference loop's head after the last one. -/
theorem run_cut80_vc (g : RunG) : RunCutVC g 80 inv80 := by
  intro args σ0 hpre fr σ hI
  obtain ⟨res, ld, ls, lh, t1, t2, t3k, t3, t4, mem, trct, st1, s, k, hbase, htexts, hload, h1, hst1, o1, o2, o3,
    hk, ⟨x33, h33, hx33⟩, ⟨x32, h32, hx32⟩, h18, h17, hb, heq⟩ := hI
  obtain ⟨h16, h24, hsl, htr, htl⟩ := hload
  obtain ⟨-, ⟨ea, xa, -, hxa, hfa⟩, -, -, -, ⟨hcp, -⟩, -⟩ := hpre
  have hbase' := hbase
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hinits, -⟩ := hbase'
  have htexts' := htexts
  obtain ⟨h11, -, -, -, -, -, -, ⟨xs, ht1, hxsF⟩, -, -, -, -, q0, q1, q2, q3, q4⟩ := htexts'
  have ht1' : σ.heap t1 = some (.array (.cls "java.lang.String") xs) := by simpa using ht1
  have hsl' := hsl
  obtain ⟨vs, hm, -⟩ := hsl'
  have hI0 : σ.initOf "Cbstm03a" = .done := (initOf_of_inits hinits _).trans hcp
  have htrs : g.trs.length < 2147483648 := by rw [← forall2_length hfa]; exact hxa
  have hxl : xs.length = g.R1.length := by rw [forall2_length hxsF, T1_length, R1_length]
  have hxl2 : g.R1.length < 2147483648 := by rw [R1_length]; exact htrs
  have o0 : t1 < mem := Nat.lt_trans q1 (Nat.lt_trans q2 (Nat.lt_trans q3 (Nat.lt_trans q4 o1)))
  have hrl : (g.R1.getD k []).length = 350 := R1_getD_length g hk
  obtain ⟨hl0, hl1, hl2⟩ := sub_length hrl
  have hk1i : (BitVec.ofNat 32 (k + 1)).toInt = (k + 1 : Int) := by
    rw [bv32_toInt _ (by omega)]; omega
  have hk1n : (BitVec.ofNat 32 (k + 1)).toNat = k + 1 := bv32_toNat _ (by omega)
  obtain ⟨lc0, lc1, lt0, lt1, -⟩ := ldStep_bounded (g.R1.getD k []) hb
  have hxl3 : xs.length < 2147483648 := by rw [hxl]; exact hxl2
  unfold runWP
  rcases Nat.lt_or_ge (k + 1) g.R1.length with hlt | hge
  · -- a record is left: back at statement 80
    have hlt1 : k + 1 < g.T1.length := by rw [T1_length, ← R1_length]; exact hlt
    obtain ⟨y, hy, hyh⟩ := forall2_jstr_get hxsF (k + 1) hlt1
    let p : LP := ⟨fr, σ, mem, trct, st1, t1, y, xs, k, g.T1.getD (k + 1) [], s, g.R1.getD k [], False⟩
    have horig : Orig g σ0 p res ld ls lh t2 t3k t3 t4 := by
      unfold Orig; exact ⟨hbase, htexts, h16, h24, h1, ⟨vs, hm⟩, htr, hst1, o1, htl, hb, hk, rfl, heq⟩
    have hhead : HeadAt p := by unfold HeadAt; exact ⟨h11, ht1', h16, h24, h1, hst1, hyh, ⟨vs, hm⟩, hsl, htr, htl⟩
    show segWP g args σ0 (cuts0 g args σ0) 300 80 p.fr p.σ
    exact run80_of_segs
      (seg4 g args σ0 p res ld ls lh t2 t3k t3 t4 (Kept.intro horig) o0 o2 o3 (Kept.intro (fun h => h.elim)))
      (seg100L g args σ0 p res ld ls lh t2 t3k t3 t4 (Kept.intro horig) o0 o2 o3 hxl hxl2 hy
        (T1_getD_length g hlt1) hlt hxl3 hk1i hk1n (Kept.intro rfl))
      (seg98 g args σ0 p o0 o2 o3 hl2 (tranOff16_lb lc0 lc1 lt0 lt1) lc0 lc1 lt0 lt1 (tranOff_range lc0 lc1 lt0 lt1).1
        (tranOff_range lc0 lc1 lt0 lt1).2) (seg95 g args σ0 p o0 o2 o3 hl1 (tranOff_lb lc0 lc1 lt0 lt1) lc0 lc1 lt0 lt1)
      (seg92 g args σ0 p o0 o2 o3 hl0 (cardOff_lb lc0 lc1) lc0 lc1 lt0 lt1)
      (run80_head o0 o2 o3 hI0 h33 hx33 hrl h32 hx32 h18 h17 hhead)
  · -- the last record: to the cross-reference loop
    have hlast : k + 1 = g.R1.length := by omega
    let p : LP := ⟨fr, σ, mem, trct, st1, t1, x33, xs, k, g.R1.getD k [], s, g.R1.getD k [],
      k + 1 = g.R1.length⟩
    have horig : Orig g σ0 p res ld ls lh t2 t3k t3 t4 := by
      unfold Orig; exact ⟨hbase, htexts, h16, h24, h1, ⟨vs, hm⟩, htr, hst1, o1, htl, hb, hk, rfl, heq⟩
    have hhead : HeadAt p := by unfold HeadAt; exact ⟨h11, ht1', h16, h24, h1, hst1, hx33, ⟨vs, hm⟩, hsl, htr, htl⟩
    show segWP g args σ0 (cuts0 g args σ0) 300 80 p.fr p.σ
    exact run80_of_segs
      (seg4 g args σ0 p res ld ls lh t2 t3k t3 t4 (Kept.intro horig) o0 o2 o3 (Kept.intro id))
      (seg100E g args σ0 p o0 o2 o3 hxl hxl3 hlast hk1i hlast)
      (seg98 g args σ0 p o0 o2 o3 hl2 (tranOff16_lb lc0 lc1 lt0 lt1) lc0 lc1 lt0 lt1 (tranOff_range lc0 lc1 lt0 lt1).1
        (tranOff_range lc0 lc1 lt0 lt1).2) (seg95 g args σ0 p o0 o2 o3 hl1 (tranOff_lb lc0 lc1 lt0 lt1) lc0 lc1 lt0 lt1)
      (seg92 g args σ0 p o0 o2 o3 hl0 (cardOff_lb lc0 lc1) lc0 lc1 lt0 lt1)
      (run80_head o0 o2 o3 hI0 h33 hx33 hrl h32 hx32 h18 h17 hhead)

end EquivLean.Modernize.Cbstm03a.Java

#print axioms EquivLean.Modernize.Cbstm03a.Java.run_cut80_vc
