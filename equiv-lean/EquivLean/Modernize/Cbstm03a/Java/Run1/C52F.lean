import EquivLean.Modernize.Cbstm03a.Java.Run1.C52E

/-!
# CBSTM03A → Java `run`: the paths of cut point 52 (`run_cut52_vc`)

The loop body (`c52_loop`), and the exit split at the virtual cut point 63: statements 58 … 62 (`c52_to63`), then
from 63 the first transaction read (`c63_B`, to `inv80`) or none (`c63_A`, `abend` and `run`'s result).
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows Keeps fixStr zpadStr argText StrOk space grows_refl grows_trans
  grows_split fixStr_length zpadStr_length keeps_alloc keeps_setObj keeps_trans GrowsK growsK_elim heap_grows)

namespace EquivLean.Modernize.Cbstm03a.Java.Seg1

theorem forall2_nil_cons {α β : Type} {R : α → β → Prop} {b : β} {bs : List β} (h : Forall2 R [] (b :: bs)) :
    False := by
  cases h

theorem forall2_head {α β : Type} {R : α → β → Prop} {a : α} {al : List α} {b : β} {bs : List β}
    (h : Forall2 R (a :: al) (b :: bs)) : R a b := by
  cases h with
  | cons h1 _ => exact h1

theorem trnxTextR_length (t : TrnxR) : (trnxTextR t).length = 350 := by
  simp [trnxTextR, zuI, zsI, zpadStr_length]

theorem seqStArr_pos {len : Nat} (h : 0 < len) : seqStArr 0 0 len = [.int 1, .int 0] := by
  have h0 : (0 : I32).toInt = 0 := by decide
  simp [seqStArr, h0, h]

theorem seqCode_pos {len : Nat} (h : 0 < len) : seqCode 0 0 len = JStr.ofString "00" := by
  have h0 : (0 : I32).toInt = 0 := by decide
  simp [seqCode, h0, h]

theorem seqCode_zero : seqCode 0 0 0 = JStr.ofString "10" := by
  have h0 : (0 : I32).toInt = 0 := by decide
  simp [seqCode, h0]

theorem runF_nil {g : RunG} (h : g.trs = []) :
    g.F = JOut.init.abend (jl "ERROR READING TRNXFILE") (jl "10") := by
  simp [RunG.F, jRunR, jRunT, h]

/-- Four strings allocated (the literals of statements 63 … 73). -/
abbrev alloc4 (σ : State) : State :=
  ((((σ.alloc (.str (JStr.ofString "00"))).2.alloc (.str (JStr.ofString "00"))).2.alloc
    (.str (JStr.ofString "04"))).2.alloc (.str (JStr.ofString "ERROR READING TRNXFILE"))).2

theorem alloc4_lt {σ : State} {y : Addr} (hy : y < σ.next) : (alloc4 σ).heap y = σ.heap y := by
  have h1 : y < (σ.alloc (.str (JStr.ofString "00"))).2.next := by rw [State.next_alloc]; exact Nat.lt_succ_of_lt hy
  have h2 : y < ((σ.alloc (.str (JStr.ofString "00"))).2.alloc (.str (JStr.ofString "00"))).2.next := by
    rw [State.next_alloc]; exact Nat.lt_succ_of_lt h1
  have h3 : y < (((σ.alloc (.str (JStr.ofString "00"))).2.alloc (.str (JStr.ofString "00"))).2.alloc
      (.str (JStr.ofString "04"))).2.next := by
    rw [State.next_alloc]; exact Nat.lt_succ_of_lt h2
  simp only [alloc4]
  rw [State.heap_alloc_of_lt h3, State.heap_alloc_of_lt h2, State.heap_alloc_of_lt h1, State.heap_alloc_of_lt hy]

theorem alloc4_3 {σ : State} :
    (alloc4 σ).heap (σ.next + 1 + 1 + 1) = some (.str (JStr.ofString "ERROR READING TRNXFILE")) := by
  simp only [alloc4]
  rw [State.heap_alloc, State.next_alloc, State.next_alloc, State.next_alloc, if_pos rfl]

theorem argText_of_heap {σ : State} {y : Addr} {s : JStr} (h : σ.heap y = some (.str s)) :
    argText σ (.ref y) = s := by
  simp [argText, strOf, h]

section paths

attribute [local irreducible] ResAtL

set_option jimple.modelContracts true in
set_option maxRecDepth 8000 in
set_option maxHeartbeats 400000 in
/-- From 63 with no transaction: `abend(res, "ERROR READING TRNXFILE", "10")`, `return res`. -/
theorem c63_A (g : RunG) (σ0 : State) (fr : Frame) (σ : State) (res ld ls lh x : Addr)
    (hRA : ResAtL (alloc4 σ) res ld ls lh [] [] [] false) (hnil : g.trs = []) (hxlt : x < σ.next)
    (h7 : fr.get 7 = some (.ref res)) (h32 : fr.get 32 = some (.ref x))
    (hR : ResAtL σ res ld ls lh [] [] [] false)
    (hx : σ.heap x = some (.str (JStr.ofString "10")))
    (hci : σ.initOf "Cbstm03a" = .done) :
    bodyWP Gen.prog (callWP Gen.prog runCallees.env 1) runBodyA
      ((runInv g).inst [.ref g.a1, .ref g.a2, .ref g.a3, .ref g.a4] σ0)
      ((runSpecG g).post [.ref g.a1, .ref g.a2, .ref g.a3, .ref g.a4] σ0) 290 63 fr σ := by
  have hH := hid_intro (And.intro hRA (And.intro hnil hxlt))
  clear hRA hnil hxlt
  jvc [runCallees, runInv, runSpecG]
  all_goals obtain ⟨hRA, hnil, hxlt⟩ := hid_elim hH
  all_goals first
    | exact ⟨ld, ls, lh, [], [], [], Or.inl hRA⟩
    | exact ⟨_, _, rfl, alloc4_3⟩
    | exact ⟨_, _, rfl, by rw [alloc4_lt hxlt]; exact hx⟩
    | skip
  rename_i v σ' hA
  obtain ⟨hv, hR', -⟩ := (hA res ld ls lh [] [] []).1 rfl hRA
  refine ⟨res, by rw [hv]; rfl, ld, ls, lh, ?_⟩
  rw [argText_of_heap alloc4_3, argText_of_heap (by rw [alloc4_lt hxlt]; exact hx)] at hR'
  rw [runF_nil hnil]
  exact hR'

end paths

section pathsB

attribute [-jsimp] List.take_succ

set_option jimple.modelContracts true in
set_option maxRecDepth 8000 in
set_option maxHeartbeats 400000 in
/-- From 63 with a first transaction: `fix`, the record, its card number, to `inv80`. -/
theorem c63_B (g : RunG) (σ0 : State) (fr : Frame) (σ : State) (res ld ls lh t1 t2 t3k t3 t4 mem trct st x x0 : Addr)
    (xs' : List Value) (t0s : JStr)
    (hb : RunBase g σ0 fr σ res ld ls lh JOut.init) (hRT : RunTexts g σ0 fr σ t1 t2 t3k t3 t4)
    (h16 : fr.get 16 = some (.ref mem)) (h24 : fr.get 24 = some (.ref trct))
    (hmem : σ.heap mem = some (.array (.cls "java.lang.String") (List.replicate 561 .null)))
    (htrct : σ.heap trct = some (.array (.prim .long) (List.replicate 51 (.long 0))))
    (o1 : t4 < mem) (o2 : mem < trct) (o3 : trct < st) (hne : g.trs ≠ []) (ht0 : t0s = g.T1.getD 0 [])
    (h11 : fr.get 11 = some (.ref t1)) (h1 : fr.get 1 = some (.ref st)) (h32 : fr.get 32 = some (.ref x))
    (ht1 : σ.heap t1 = some (.array (.cls "java.lang.String") (.ref x0 :: xs')))
    (hst : σ.heap st = some (.array (.prim .int) [.int 1, .int 0]))
    (hx : σ.heap x = some (.str (JStr.ofString "00")))
    (hx0 : σ.heap x0 = some (.str t0s)) (ht0l : t0s.length < 2147483648)
    (hci : σ.initOf "Cbstm03a" = .done) :
    bodyWP Gen.prog (callWP Gen.prog runCallees.env 1) runBodyA
      ((runInv g).inst [.ref g.a1, .ref g.a2, .ref g.a3, .ref g.a4] σ0)
      ((runSpecG g).post [.ref g.a1, .ref g.a2, .ref g.a3, .ref g.a4] σ0) 290 63 fr σ := by
  have hH := hid_intro (And.intro hb (And.intro hRT (And.intro h16 (And.intro h24 (And.intro hmem (And.intro htrct
    (And.intro o1 (And.intro o2 (And.intro o3 (And.intro hne ht0))))))))))
  clear hb hRT h16 h24 hmem htrct o1 o2 o3 hne ht0
  jvc [runCallees, runInv, grows_split, StrOk, argText, fixStr_length]
  obtain ⟨hb, hRT, h16, h24, hmem, htrct, o1, o2, o3, hne, ht0⟩ := hid_elim hH
  exact c63B_close hb hRT h16 h24 h1 hmem htrct hst o1 o2 o3 hne ht0 (by assumption) (by assumption)
    (by assumption) (by assumption)

end pathsB

section to63

attribute [local irreducible] a63

set_option linter.unusedVariables false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
/-- Statements 52 (exit), 58 … 62 to the virtual cut point 63. -/
theorem c52_to63 (g : RunG) (σ0 : State) (fr : Frame) (σ : State) (res ld ls lh t1 t2 t3k t3 t4 : Addr)
    (xs : List Value) (n i : I32)
    (hb : RunBase g σ0 fr σ res ld ls lh JOut.init) (hRT : RunTexts g σ0 fr σ t1 t2 t3k t3 t4)
    (hxl : xs.length = g.trs.length) (ht4lt : t4 < σ.next)
    (h11 : fr.get 11 = some (.ref t1))
    (ht1 : σ.heap t1 = some (.array (.cls "java.lang.String") xs)) (hl1 : xs.length < 2147483648)
    (ht1lt : t1 < σ.next)
    (h28 : fr.get 28 = some (.int n)) (h26 : fr.get 26 = some (.int i)) (hge : ¬ i.toInt < n.toInt)
    (hci : σ.initOf "Cbstm03a" = .done) :
    bodyWP Gen.prog (callWP Gen.prog runCallees.env 1) runBodyA
      ((63, a63 g σ0) :: (runInv g).inst [.ref g.a1, .ref g.a2, .ref g.a3, .ref g.a4] σ0)
      ((runSpecG g).post [.ref g.a1, .ref g.a2, .ref g.a3, .ref g.a4] σ0) 10 52 fr σ := by
  have hH := hid_intro (And.intro hb (And.intro hRT (And.intro hxl ht4lt)))
  clear hb hRT hxl ht4lt
  jvc [runCallees, runInv, grows_split]
  obtain ⟨hb, hRT, hxl, ht4lt⟩ := hid_elim hH
  rename_i σ1 _ _ hg1 _ _ _ _ _ _ _ v σf hS
  set_option maxHeartbeats 100000 in
  exact c52_63_close (σ1 := σ1) (σf := σf) (v := v) hb hRT ht1 hl1 hxl ht4lt hg1
    (by decide +kernel) (by decide +kernel) rfl hS

end to63

set_option maxRecDepth 8000 in
/-- From the virtual cut point 63. -/
theorem c63_paths (g : RunG) (σ0 : State) (hcpi : σ0.initOf "Cbstm03a" = .done) (fr : Frame) (σ : State)
    (h : a63 g σ0 fr σ) :
    bodyWP Gen.prog (callWP Gen.prog runCallees.env 1) runBodyA
      ((runInv g).inst [.ref g.a1, .ref g.a2, .ref g.a3, .ref g.a4] σ0)
      ((runSpecG g).post [.ref g.a1, .ref g.a2, .ref g.a3, .ref g.a4] σ0) 290 63 fr σ := by
  obtain ⟨res, ld, ls, lh, t1, t2, t3k, t3, t4, mem, trct, st, x, hb, hRT, h16, h24, h1, h32, hmem, htrct, hst,
    hx, o1, o2, o3, o4⟩ := h
  have hRT' := hRT
  obtain ⟨h11, -, -, -, -, -, -, ⟨xs, ht1, hxs⟩, -, -, -, -, -⟩ := hRT'
  have hb' := hb
  obtain ⟨-, -, -, -, h7, hR, -, -, -, -, hg, hinits, -⟩ := hb'
  have hci : σ.initOf "Cbstm03a" = .done := by rw [State.initOf_eq_of_inits hinits]; exact hcpi
  have hxlt : x < σ.next := State.lt_next_of_heap hx
  cases hc : g.trs with
  | nil =>
    rw [hc, List.length_nil, seqCode_zero] at hx
    have hRA : ResAtL (alloc4 σ) res ld ls lh [] [] [] false := by
      have hR' := hR
      obtain ⟨fs, hr, -, -, -, -, -, -, -, ⟨xd, md, hd, -⟩, ⟨xs2, ms, hls, -⟩, ⟨xh, mh, hlh, -⟩⟩ := hR'
      exact resAtL_init_of_heap hR (alloc4_lt (State.lt_next_of_heap hr)) (alloc4_lt (State.lt_next_of_heap hd))
        (alloc4_lt (State.lt_next_of_heap hls)) (alloc4_lt (State.lt_next_of_heap hlh))
    exact c63_A g σ0 fr σ res ld ls lh x hRA hc hxlt h7 h32 hR hx hci
  | cons t0 ts =>
    have hT1 : g.T1 = trnxTextR t0 :: ts.map trnxTextR := by simp [RunG.T1, hc]
    rw [hT1] at hxs
    obtain ⟨v0, xs', rfl⟩ : ∃ v0 xs', xs = v0 :: xs' := by
      cases xs with
      | nil => exact (forall2_nil_cons hxs).elim
      | cons v0 xs' => exact ⟨v0, xs', rfl⟩
    obtain ⟨x0, rfl, hx0⟩ : JStrAt σ v0 (trnxTextR t0) := forall2_head hxs
    have hpos : 0 < g.trs.length := by rw [hc]; exact Nat.succ_pos _
    rw [seqCode_pos hpos] at hx
    rw [seqStArr_pos hpos] at hst
    have hne : g.trs ≠ [] := by rw [hc]; exact List.cons_ne_nil _ _
    refine c63_B g σ0 fr σ res ld ls lh t1 t2 t3k t3 t4 mem trct st x x0 xs' (trnxTextR t0) hb hRT h16 h24 hmem htrct
      o1 o2 o3 hne (by rw [hT1]; rfl) h11 h1 h32 ?_ hst hx hx0 (by rw [trnxTextR_length]; decide) hci
    rw [ht1]; simp

set_option maxRecDepth 8000 in
/-- The exit of the ACCTFILE loop, split at the virtual cut point 63. -/
theorem c52_exit (g : RunG) (σ0 : State) (hcpi : σ0.initOf "Cbstm03a" = .done) (fr : Frame) (σ : State)
    (res ld ls lh t1 t2 t3k t3 t4 : Addr) (xs : List Value) (n i : I32)
    (hb : RunBase g σ0 fr σ res ld ls lh JOut.init) (hRT : RunTexts g σ0 fr σ t1 t2 t3k t3 t4)
    (hxl : xs.length = g.trs.length) (ht4lt : t4 < σ.next)
    (h11 : fr.get 11 = some (.ref t1))
    (ht1 : σ.heap t1 = some (.array (.cls "java.lang.String") xs)) (hl1 : xs.length < 2147483648)
    (h28 : fr.get 28 = some (.int n)) (h26 : fr.get 26 = some (.int i)) (hge : ¬ i.toInt < n.toInt)
    (hci : σ.initOf "Cbstm03a" = .done) :
    runWP g [.ref g.a1, .ref g.a2, .ref g.a3, .ref g.a4] σ0 52 fr σ := by
  unfold runWP
  have hI : ((runInv g).inst [.ref g.a1, .ref g.a2, .ref g.a3, .ref g.a4] σ0).lookup 63 = none := rfl
  exact bodyWP_vcut (callWP_mono Gen.prog runCallees.env 1) runBodyA _ _ 63 hI (a63 g σ0) 290
    (fun fr σ h => c63_paths g σ0 hcpi fr σ h) 10 52 fr σ
    (c52_to63 g σ0 fr σ res ld ls lh t1 t2 t3k t3 t4 xs n i hb hRT hxl ht4lt h11 ht1 hl1
      (State.lt_next_of_heap ht1) h28 h26 hge hci)

end EquivLean.Modernize.Cbstm03a.Java.Seg1

namespace EquivLean.Modernize.Cbstm03a.Java

open Seg1

set_option maxRecDepth 8000 in
theorem run_cut52_vc (g : RunG) : RunCutVC g 52 inv52 := by
  intro args σ0 hpre fr σ hI
  obtain ⟨hargs, ⟨et1, xs1, hh1, hl1, hf1⟩, -, -, ⟨et4, xs4, hh4, hl4, hf4⟩, ⟨hcpi, -⟩, -⟩ := hpre
  subst hargs
  obtain ⟨res, ld, ls, lh, t1, t2, t3k, t3, t4, n3, n, i, hb, h11, h12, h13, h14, h15, h27, h28, h26, hn3, hn,
    hi0, hin, hT1, hT2, hK3, hT3, ⟨xs, ht4, hxs⟩, h0t1, h12lt, h23lt, h34lt, h45lt⟩ := hI
  have hb' := hb
  obtain ⟨-, -, -, h6, -, -, -, -, -, -, hg, hinits, -⟩ := hb'
  have hci : σ.initOf "Cbstm03a" = .done := by rw [State.initOf_eq_of_inits hinits]; exact hcpi
  by_cases hlt : i.toInt < n.toInt
  · have hlen4 := forall2_length hf4
    have hk : i.toInt.toNat < g.ars.length := by omega
    obtain ⟨hk1, x, hx, hat⟩ := recsAt_elem hf4 _ hk
    have hxl : xs.length = i.toInt.toNat := by
      rw [forall2_length hxs, List.length_take]; simp [RunG.T4]; omega
    exact c52_loop g σ0 fr σ res ld ls lh t1 t2 t3k t3 t4 x n3 n i et4 xs4 xs _ _ hb hT1 hT2 hK3 hT3 hxs hn3 hn h0t1
      h12lt h23lt h34lt h45lt rfl ⟨hk, rfl⟩ h11 h12 h13 h14 h27 h6 h15 h28 h26 (heap_grows hg hh4)
      (by rw [hn, hlen4]) hi0 hlt hk1 hx ⟨x, rfl, acctAt_grows hat hg⟩ hci ht4 hxl (by omega)
      (State.lt_next_of_heap ht4)
  · have hT4 : TextsAt σ t4 g.T4 0 := textsAt_full hxs (by simp [RunG.T4]) (by omega) ht4
    have hRT : RunTexts g σ0 fr σ t1 t2 t3k t3 t4 :=
      ⟨h11, h12, h13, h14, h15, ⟨n3, h27, hn3⟩, ⟨n, h28, hn⟩, hT1, hT2, hK3, hT3, hT4, h0t1, h12lt, h23lt, h34lt,
        h45lt⟩
    obtain ⟨ys, hy1, hys⟩ := hT1
    have hylen : ys.length = g.trs.length := by rw [forall2_length hys]; simp [RunG.T1]
    have hlen1 := forall2_length hf1
    exact c52_exit g σ0 hcpi fr σ res ld ls lh t1 t2 t3k t3 t4 ys n i hb hRT hylen (State.lt_next_of_heap ht4) h11
      (by rw [hy1]; simp) (by omega) h28 h26 hlt hci

end EquivLean.Modernize.Cbstm03a.Java

#print axioms EquivLean.Modernize.Cbstm03a.Java.run_cut52_vc
