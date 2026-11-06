import EquivLean.Modernize.Cbtrn02c.Any.JavaRunRunOutX

/-!
# CBTRN02C → Java: `run`'s main loop head (statement 65)

From the loop head: the exit (statement 83), the next transaction (`validateTran`, to statement
75), or the end of the input (the flag set, back to 65).
-/

open Jimple EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbtrn02c.Java

/-- The `k`-th element of the input array is a reference. -/
theorem elem_ref {g : G} {σ0 σ : State} {k : Nat} {et : JType} {xsD : List Value}
    (hin : Any.Java.RunIn g.args σ0 g.trans g.xrefs g.accts g.cats g.clk) (hg : Grows σ0 σ)
    (ha1 : σ.heap g.a1 = some (.array et xsD)) (hk : k < g.trans.length) :
    ∃ d, xsD[k]? = some (.ref d) := by
  obtain ⟨a1, a2, a3, a4, cs, hargs, ⟨et1, xs1, h1, -, hf1⟩, -⟩ := hin
  simp only [G.args, List.cons.injEq, Value.ref.injEq, and_true] at hargs
  obtain ⟨rfl, -, -, -, -⟩ := hargs
  have h1' := heap_of_grows hg h1
  rw [ha1] at h1'
  simp only [Option.some.injEq, Obj.array.injEq] at h1'
  obtain ⟨-, rfl⟩ := h1'
  have hl := forall2_length hf1
  have hkx : k < xsD.length := by omega
  obtain ⟨y, fs, hy, -⟩ := forall2_get hf1 k hkx hk
  exact ⟨y, by rw [List.getElem?_eq_getElem hkx, hy]⟩

/-- `validateTran`'s precondition in the form the symbolic execution asks for. -/
theorem vtPre_shape {σ : State} {d xA aD wX wA : Addr}
    (h : validateTranSpec.pre [.ref d, .ref xA, .ref aD, .ref wX, .ref wA] σ) :
    (∃ x, VtD σ d x) ∧ (∃ x x_1, VtIn σ xA aD wX wA x x_1) ∧
      ∃ x, σ.heap wX = some (Obj.plain "Cbtrn02c$CardXrefRecord" x) ∧
        (∀ (a : ClassName) (b : String), (a, b) ∈ xrKeys → (Fields.get x (a, b)).isSome = true) ∧
        ∃ x, σ.heap wA = some (Obj.plain "Cbtrn02c$AccountRecord" x) ∧
          ∀ (a : ClassName) (b : String), (a, b) ∈ acKeys → (Fields.get x (a, b)).isSome = true := by
  obtain ⟨d', xA', aD', wX', wA', t, vals2, accts, fsX, fsA, hargs, hD, hIn, hX, hXk, hA, hAk, -⟩ := h
  simp only [List.cons.injEq, Value.ref.injEq, and_true] at hargs
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hargs
  exact ⟨⟨t, hD⟩, ⟨vals2, accts, hIn⟩, fsX, hX, fun a b h => hXk (a, b) h, fsA, hA,
    fun a b h => hAk (a, b) h⟩

/-- **After `validateTran`** (statement 75): the next transaction and its reject reason. -/
theorem l75x_after_vt {g : G} {σ0 σ σ1 : State} {fr : Frame} {A : Addrs} {k : Nat} {next c : I32}
    {et : JType} {xsD : List Value} {d : Addr} {fsX' fsA' : List (FieldKey × Value)}
    {u v30 w1 v15 : Value}
    (hpre : RunPreGX g g.args σ0) (hL : Locs65 g A fr) (f14 : fr.get 14 = some (.int next))
    (f4 : fr.get 4 = some (.int 0#32))
    (f10 : fr.get 10 = some (.long (BitVec.ofNat 64 ((g.st k).rejects % 1000000000))))
    (ha1 : σ.heap g.a1 = some (.array et xsD)) (hlenD : xsD.length = g.trans.length)
    (hxk : xsD[k]? = some (.ref d)) (hk : k < g.trans.length) (hnext : next.toInt = k)
    (hstx : g.stx k = ⟨g.st k, false⟩)
    (hW : W σ A (g.st k)) (hMV : MV (g.st k)) (hAd : AdEt σ A.aD) (hFr : Fresh σ0 A)
    (hg : Grows σ0 σ) (hf : FrameS σ σ1 [A.wX, A.wA])
    (hX' : σ1.heap A.wX = some (.plain "Cbtrn02c$CardXrefRecord" fsX'))
    (hXk' : ∀ (a : ClassName) (b : String), (a, b) ∈ xrKeys → (Fields.get fsX' (a, b)).isSome = true)
    (hA' : σ1.heap A.wA = some (.plain "Cbtrn02c$AccountRecord" fsA'))
    (hAk' : ∀ (a : ClassName) (b : String), (a, b) ∈ acKeys → (Fields.get fsA' (a, b)).isSome = true)
    (hceq : c = BitVec.ofInt 32 (vreason g.xrefs (g.st k).accts (g.trec k)))
    (hxa : vreason g.xrefs (g.st k).accts (g.trec k) = 0 →
      ∃ x, Model.findXref g.xrefs (Model.tCard (g.trec k)) = some x ∧
        ∃ x_1, Model.findAcct (g.st k).accts (Model.xAcct x) = some x_1 ∧
          JRecAt CardXrefRecord "Cbtrn02c$CardXrefRecord" σ1 (.ref A.wX) x ∧
          JRecAt AccountRecord "Cbtrn02c$AccountRecord" σ1 (.ref A.wA) x_1)
    (hi1 : σ1.inits = σ0.inits) (hs1 : σ1.statics = σ0.statics)
    (hv30 : v30 = .ref d) (hv15 : v15 = .int c) :
    L75X g g.args σ0
      ((((((fr.setLocal 15 u).setLocal 30 v30).setLocal 14 (.int (next + 1#32))).setLocal 9 w1).setLocal 9
        (.long (BitVec.srem (BitVec.ofNat 64 (k % 1000000000) + 1#64) 1000000000#64))).setLocal 15 v15)
      σ1 := by
  subst hv30 hv15
  have hb := (exit_facts hpre).2
  obtain ⟨-, hin, -⟩ := hpre
  have ha10 : g.a1 < σ0.next := by
    obtain ⟨a1, a2, a3, a4, cs, hargs, ⟨et1, xs1, h1', -⟩, -⟩ := hin
    simp only [G.args, List.cons.injEq, Value.ref.injEq, and_true] at hargs
    obtain ⟨rfl, -, -, -, -⟩ := hargs
    exact State.lt_next_of_heap h1'
  have hwX : σ0.next ≤ A.wX := hFr A.wX (by simp)
  have hwA : σ0.next ≤ A.wA := hFr A.wA (by simp)
  have hnot : ∀ z, z < σ0.next → z ∉ [A.wX, A.wA] := by
    intro z hz hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl
    · exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le hz hwX)
    · exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le hz hwA)
  have hW1 := W_vt hW hf
    ⟨fsX', hX', by rw [keysOf_xref']; exact fun key hkey => hXk' key.1 key.2 hkey⟩
    ⟨fsA', hA', by rw [keysOf_acct'']; exact fun key hkey => hAk' key.1 key.2 hkey⟩
  have hAd1 : AdEt σ1 A.aD := by
    obtain ⟨xs, hxs⟩ := hAd
    obtain ⟨-, -, -, -, -, -, -, -, -, -, ⟨fsX, hwXo, -⟩, ⟨fsA, hwAo, -⟩, -⟩ := hW
    refine ⟨xs, hf.heap hxs ?_⟩
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with h | h
    · rw [h, hwXo] at hxs; cases hxs
    · rw [h, hwAo] at hxs; cases hxs
  have hg1 : Grows σ0 σ1 := by
    refine ⟨Nat.le_trans hg.1 hf.1, fun z hz => ?_⟩
    rw [hf.2 z (Nat.lt_of_lt_of_le hz hg.1) (hnot z hz), hg.2 z hz]
  have hn1 : (next + 1#32).toInt = k + 1 := by
    rw [toInt_succ32 (by omega) (by omega), hnext]
  obtain ⟨l32, l0, l16, l31, l8, l11, l12, l6, l13, l29, l28⟩ := hL
  refine ⟨A, k, next + 1#32, c, BitVec.ofNat 64 ((k + 1) % 1000000000),
    BitVec.ofNat 64 ((g.st k).rejects % 1000000000), et, xsD, d,
    ⟨by frame_simp [l32], by frame_simp [l0], by frame_simp [l16], by frame_simp [l31],
      by frame_simp [l8], by frame_simp [l11], by frame_simp [l12], by frame_simp [l6],
      by frame_simp [l13], by frame_simp [l29], by frame_simp [l28]⟩,
    by frame_simp [], by frame_simp [cnt_succ], by frame_simp [f10], by frame_simp [],
    by frame_simp [], by frame_simp [f4], hf.heap ha1 (hnot _ ha10), hlenD, hxk, hk, hn1, rfl, rfl,
    hceq, hstx, Hide.intro ⟨hW1, hMV, hAd1, hFr, fun h0 => ?_⟩, hg1, hi1, hs1⟩
  obtain ⟨x, h1, a, h2, h3, h4⟩ := hxa h0
  exact ⟨x, a, h1, h2, h3, h4⟩

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
set_option pp.maxSteps 3000 in
set_option pp.deepTerms false in
theorem run_seg65 (g : G) (σ0 : State) (cuts : Cuts) (fr : Frame) (σ : State)
    (hpre : RunPreGX g g.args σ0) (h : L65X g g.args σ0 fr σ)
    (hc : ∀ k, 66 ≤ k → k ≤ 74 → cuts.lookup k = none)
    (c83 : cuts.lookup 83 = some (J83X g g.args σ0))
    (c75 : cuts.lookup 75 = some (L75X g g.args σ0)) (c65 : cuts.lookup 65 = some (L65X g g.args σ0)) :
    RunWPcX g σ0 cuts 65 fr σ := by
  obtain ⟨A, k, next, z, tx, rej, et, xsD, hL, f14, f4, f9, f10, ha1, hlenD, hnext, hk, hz, htx, hrej,
    hstx, hkeep, hg, hin, hst⟩ := h
  have hI : Inits σ := by
    obtain ⟨-, -, hI0⟩ := hpre
    obtain ⟨i1, i2, i3, i4, i5, i6, i7, i8⟩ := hI0
    have e := fun c => initOf_of_inits hin c
    exact ⟨by rw [e]; exact i1, by rw [e]; exact i2, by rw [e]; exact i3, by rw [e]; exact i4,
      by rw [e]; exact i5, by rw [e]; exact i6, by rw [e]; exact i7, by rw [e]; exact i8⟩
  have hkeepP := Hide.intro hpre
  have hkeepG := Hide.intro hg
  have hkeepI := Hide.intro hI
  clear hpre hg
  obtain ⟨f32, f0, f16, f31, f8, f11, f12, f6, f13, f29, f28⟩ := hL
  have c66 := hc 66 (by omega) (by omega)
  have c67 := hc 67 (by omega) (by omega)
  have c68 := hc 68 (by omega) (by omega)
  have c69 := hc 69 (by omega) (by omega)
  have c70 := hc 70 (by omega) (by omega)
  have c71 := hc 71 (by omega) (by omega)
  have c72 := hc 72 (by omega) (by omega)
  have c73 := hc 73 (by omega) (by omega)
  have c74 := hc 74 (by omega) (by omega)
  clear hc
  rcases hz with rfl | ⟨rfl, hkn⟩
  · unfold RunWPcX
    jvc [runCX, validateTranSig, validateTranSpec, Grows, narrow_long, narrow_cls, G.args]
    case isTrue.isTrue.left =>
      obtain ⟨hW, hMV, -, hFr⟩ := Hide.elim hkeep
      obtain ⟨-, hRin, -⟩ := Hide.elim hkeepP
      have hg := Hide.elim hkeepG
      obtain ⟨d, hxk⟩ := elem_ref hRin hg ha1 hcond
      obtain ⟨hd, htv⟩ := trec_at hRin hg ha1 hxk hcond
      obtain ⟨hlt, he⟩ := List.getElem?_eq_some_iff.1 hxk
      exact ⟨d, g.a2, A.aD, A.wX, A.wA, ⟨he, rfl, rfl, rfl, rfl⟩,
        vtPre_shape (vtPre_of hRin hg hW hMV hFr (Hide.elim hkeepI).1 hd htv)⟩
    case isTrue.isTrue.right.normal =>
      rename_i v σ1 hpost
      obtain ⟨hW, hMV, hAd, hFr⟩ := Hide.elim hkeep
      obtain ⟨-, hRin, -⟩ := Hide.elim hkeepP
      have hg := Hide.elim hkeepG
      obtain ⟨d, hxk⟩ := elem_ref hRin hg ha1 hcond
      obtain ⟨hd, htv⟩ := trec_at hRin hg ha1 hxk hcond
      obtain ⟨hlt, he⟩ := List.getElem?_eq_some_iff.1 hxk
      obtain ⟨hf, hi1, hs1, -, ⟨fsX', hX', hXk'⟩, ⟨fsA', hA', hAk'⟩, c, hv, hc⟩ :=
        hpost d g.a2 A.aD A.wX A.wA he rfl rfl rfl rfl
      obtain ⟨hceq, hxa⟩ := hc (g.trec k) g.xrefs (g.st k).accts (vtd_of hd htv)
        (vtin_of hRin hg hW hMV hFr)
      subst hv
      exact l75x_after_vt (Hide.elim hkeepP) ⟨f32, f0, f16, f31, f8, f11, f12, f6, f13, f29, f28⟩
        f14 f4 f10 ha1 hlenD hxk hcond hnext hstx hW hMV hAd hFr hg hf hX' hXk' hA' hAk' hceq hxa
        hi1 hs1 he rfl
    case isTrue.isFalse =>
      have hb : g.trans.length < 134217728 := (exit_facts (Hide.elim hkeepP)).2
      have h1 := ‹(k : Int) < (BitVec.ofNat 32 g.trans.length).toInt›
      rw [toInt_ofNat32 (by omega)] at h1
      exfalso
      omega
    case isFalse =>
      have hb : g.trans.length < 134217728 := (exit_facts (Hide.elim hkeepP)).2
      have hkn : k = g.trans.length := by
        rw [toInt_ofNat32 (by omega)] at hcond
        omega
      subst hkn
      exact ⟨A, g.trans.length, next, 1#32, BitVec.ofNat 64 (g.trans.length % 1000000000),
        BitVec.ofNat 64 ((g.st g.trans.length).rejects % 1000000000), et, xsD,
        ⟨by frame_simp [f32], by frame_simp [f0], by frame_simp [f16], by frame_simp [f31],
          by frame_simp [f8], by frame_simp [f11], by frame_simp [f12], by frame_simp [f6],
          by frame_simp [f13], by frame_simp [f29], by frame_simp [f28]⟩,
        by frame_simp [f14], by frame_simp [], by frame_simp [f9], by frame_simp [f10], ha1, hlenD,
        hnext, Nat.le_refl _, Or.inr ⟨rfl, rfl⟩, rfl, rfl, hstx, hkeep, Hide.elim hkeepG, hin, hst⟩
  · unfold RunWPcX
    jvc [runCX, validateTranSig, validateTranSpec, Grows, narrow_long, narrow_cls, G.args]
    obtain ⟨hW, hMV, -, hFr⟩ := Hide.elim hkeep
    exact ⟨A, _, _, ⟨f32, f0, f16, f31, f8, f11, f12, f6, f13, f29, f28⟩, f9, f10,
      Hide.intro ⟨rfl, rfl, hstx, hW, hMV, hFr⟩, Hide.elim hkeepG, hin, hst⟩

end EquivLean.Modernize.Cbtrn02c.Java
