import EquivLean.Modernize.Cbtrn02c.Any.JavaRunRunH2
import EquivLean.Modernize.Cbtrn02c.Any.JavaRunWR
import EquivLean.Modernize.Cbtrn02c.Any.JavaRunU

/-!
# CBTRN02C → Java: the main loop after `validateTran`, the facts of statement 75

`dalOk_line`: `dalytranText` reads the daily transaction object and builds the CP037 text of the
record's bytes; `trailer_of`: the trailer text of a reject reason; `wrPre_of`: `writeReject`'s
precondition; `seg75_valid`: a valid transaction's cross-reference, account and
`postTransaction`'s precondition; `l65x_reject`: the loop head after a rejected transaction.
-/

open Jimple EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbtrn02c.Java

set_option maxRecDepth 4000 in
theorem dalOk_line0 {σ : State} {d : Addr} {t : List EquivLean.Cobol.Rec.FVal}
    (hr : JRecAt DalytranRecord dalCls σ (.ref d) t) (hv : DalytranRecord.Valid t) :
    DalOk σ d ∧ dtLine σ d = jline (DalytranRecord.textS t) := by
  obtain ⟨x, fs, hxe, hx, hf⟩ := hr
  cases hxe
  have hl : t.length = 14 := (forall2_length hv).symm
  match t, hl, hv, hf with
  | [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13], _,
    .cons h0 (.cons h1 (.cons h2 (.cons h3 (.cons h4 (.cons h5 (.cons h6 (.cons h7 (.cons h8
      (.cons h9 (.cons h10 (.cons h11 (.cons h12 (.cons h13 .nil))))))))))))),
    .cons j0 (.cons j1 (.cons j2 (.cons j3 (.cons j4 (.cons j5 (.cons j6 (.cons j7 (.cons j8
      (.cons j9 (.cons j10 (.cons j11 (.cons j12 (.cons j13 .nil))))))))))))) =>
    obtain ⟨b0, y0, rfl, g0, s0, l0⟩ := str_field rfl h0 j0
    obtain ⟨b1, y1, rfl, g1, s1, l1⟩ := str_field rfl h1 j1
    obtain ⟨n2, rfl, g2, hh2, -, hd2⟩ := num_field rfl h2 j2
    obtain ⟨b3, y3, rfl, g3, s3, l3⟩ := str_field rfl h3 j3
    obtain ⟨b4, y4, rfl, g4, s4, l4⟩ := str_field rfl h4 j4
    obtain ⟨n5, rfl, g5, hh5, -, hd5⟩ := num_field rfl h5 j5
    obtain ⟨n6, rfl, g6, hh6, -, hd6⟩ := num_field rfl h6 j6
    obtain ⟨b7, y7, rfl, g7, s7, l7⟩ := str_field rfl h7 j7
    obtain ⟨b8, y8, rfl, g8, s8, l8⟩ := str_field rfl h8 j8
    obtain ⟨b9, y9, rfl, g9, s9, l9⟩ := str_field rfl h9 j9
    obtain ⟨b10, y10, rfl, g10, s10, l10⟩ := str_field rfl h10 j10
    obtain ⟨b11, y11, rfl, g11, s11, l11⟩ := str_field rfl h11 j11
    obtain ⟨b12, y12, rfl, g12, s12, l12⟩ := str_field rfl h12 j12
    obtain ⟨b13, y13, rfl, g13, s13, l13⟩ := str_field rfl h13 j13
    have a2 := natAbs_lt_of_holds rfl hh2 hd2
    have a5 := natAbs_lt_of_holds rfl hh5 hd5
    have a6 := natAbs_lt_of_holds rfl hh6 hd6
    dsimp only at g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 l0 l1 l3 l4 l7 l8 l9 l10 l11 l12 l13
    refine ⟨⟨fs, hx, ⟨y0, _, g0, s0, ?_⟩, ⟨y1, _, g1, s1, ?_⟩, ⟨_, g2, minval_lt a2⟩,
      ⟨y3, _, g3, s3, ?_⟩, ⟨y4, _, g4, s4, ?_⟩, ⟨_, g5, minval_lt a5⟩, ⟨_, g6, minval_lt a6⟩,
      ⟨y7, _, g7, s7, ?_⟩, ⟨y8, _, g8, s8, ?_⟩, ⟨y9, _, g9, s9, ?_⟩, ⟨y10, _, g10, s10, ?_⟩,
      ⟨y11, _, g11, s11, ?_⟩, ⟨y12, _, g12, s12, ?_⟩, ⟨y13, _, g13, s13, ?_⟩⟩, ?_⟩
    any_goals simp [cp037Str_length, *]
    have e2 : (BitVec.ofInt 64 n2).toInt = n2 := toInt_ofInt_of_natAbs a2
    have e6 : (BitVec.ofInt 64 n6).toInt = n6 := toInt_ofInt_of_natAbs a6
    simp only [dtLine, fieldOf, fieldLong, hx, dtCls, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10,
      g11, g12, g13, Option.getD_some, argText_of s0, argText_of s1, argText_of s3, argText_of s4,
      argText_of s7, argText_of s8, argText_of s9, argText_of s10, argText_of s11, argText_of s12,
      argText_of s13, e2, e6]
    simp only [fitJ_full _ _ (by simp [cp037Str_length, *] : (cp037Str b0).length = 16),
      fitJ_full _ _ (by simp [cp037Str_length, *] : (cp037Str b1).length = 2),
      fitJ_full _ _ (by simp [cp037Str_length, *] : (cp037Str b3).length = 10),
      fitJ_full _ _ (by simp [cp037Str_length, *] : (cp037Str b4).length = 100),
      fitJ_full _ _ (by simp [cp037Str_length, *] : (cp037Str b7).length = 50),
      fitJ_full _ _ (by simp [cp037Str_length, *] : (cp037Str b8).length = 50),
      fitJ_full _ _ (by simp [cp037Str_length, *] : (cp037Str b9).length = 10),
      fitJ_full _ _ (by simp [cp037Str_length, *] : (cp037Str b10).length = 16),
      fitJ_full _ _ (by simp [cp037Str_length, *] : (cp037Str b11).length = 26),
      fitJ_full _ _ (by simp [cp037Str_length, *] : (cp037Str b12).length = 26),
      fitJ_full _ _ (by simp [cp037Str_length, *] : (cp037Str b13).length = 20)]
    simp only [Schema.textS, List.zip_cons_cons, List.zip_nil_right,
      List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, fieldTextS,
      List.append_nil, jline_append, jline_cp037, jline_zpad, Bool.false_eq_true, ↓reduceIte,
      Nat.add_one_sub_one, List.append_assoc]
    rw [← szJ_of n5 a5]
    simp only [jline_append, List.append_assoc]
    rfl

/-- **The daily transaction object as `dalytranText` reads it**: its text is the CP037 text of the
record's bytes. -/
theorem dalOk_line {σ : State} {d : Addr} {t : List EquivLean.Cobol.Rec.FVal}
    (hr : JRecAt DalytranRecord dalCls σ (.ref d) t) (hv : DalytranRecord.Valid t) :
    DalOk σ d ∧ dtLine σ d = cp037Str (Model.DalytranRecord.encode t) := by
  obtain ⟨hD, he⟩ := dalOk_line0 hr hv
  refine ⟨hD, ?_⟩
  rw [he, Schema.textS_eq (by decide) hv, jline_cp037]

theorem vreason_ne_cases {xr ac : List (List EquivLean.Cobol.Rec.FVal)} {t : List EquivLean.Cobol.Rec.FVal}
    (h : vreason xr ac t ≠ 0) :
    vreason xr ac t = 100 ∨ vreason xr ac t = 101 ∨ vreason xr ac t = 102 ∨ vreason xr ac t = 103 := by
  rcases vreason_cases xr ac t with h0 | h0 | h0 | h0 | h0
  · exact absurd h0 h
  · exact Or.inl h0
  · exact Or.inr (Or.inl h0)
  · exact Or.inr (Or.inr (Or.inl h0))
  · exact Or.inr (Or.inr (Or.inr h0))

/-- The trailer text of a reject reason. -/
theorem trailer_of {c : Int} (h : c = 100 ∨ c = 101 ∨ c = 102 ∨ c = 103) :
    trailerJ (BitVec.ofInt 32 c) = cp037Str (CardDemo.Cbtrn02c.trailer c (descOf c)) := by
  rcases h with rfl | rfl | rfl | rfl
  · rw [show BitVec.ofInt 32 100 = 100#32 by decide, trailer_100]; rfl
  · rw [show BitVec.ofInt 32 101 = 101#32 by decide, trailer_101]; rfl
  · rw [show BitVec.ofInt 32 102 = 102#32 by decide, trailer_102]; rfl
  · rw [show BitVec.ofInt 32 103 = 103#32 by decide, trailer_103]; rfl

/-- **`writeReject`'s precondition** at statement 79 of `run`. -/
theorem wrPre_of {σ : State} {A : Addrs} {s : Model.St} {d : Addr} {c : Int}
    {t : List EquivLean.Cobol.Rec.FVal} (hW : W σ A s)
    (hd : JRecAt DalytranRecord dalCls σ (.ref d) t) (htv : DalytranRecord.Valid t)
    (hc : c = 100 ∨ c = 101 ∨ c = 102 ∨ c = 103) :
    ∃ d_1 k_1, (d = d_1 ∧ BitVec.ofInt 32 c = k_1) ∧
      (k_1 = 100#32 ∨ k_1 = 101#32 ∨ k_1 = 102#32 ∨ k_1 = 103#32) ∧
      ∃ x, σ.heap A.r = some (Obj.plain "Cbtrn02c$Result" x) ∧
        ∃ x_1, Fields.get x rejKey = some (Value.ref x_1) ∧
          (∃ x x_2, σ.heap x_1 = some (Obj.list ListKind.arrayList x x_2)) ∧ Hide (DalOk σ d_1) := by
  obtain ⟨fsR, hRh, -, -, hRj, -⟩ := hW.1
  obtain ⟨xs0, m0, hl0, -⟩ := hW.2.2.2.1
  refine ⟨d, _, ⟨rfl, rfl⟩, ?_, fsR, hRh, A.lR, hRj, ⟨xs0, m0, hl0⟩, Hide.intro (dalOk_line hd htv).1⟩
  rcases hc with rfl | rfl | rfl | rfl <;> decide

/-- **A valid transaction** at statement 76: its cross-reference and account, the input array
below the entry's `next`, and `postTransaction`'s precondition. -/
theorem seg75_valid {g : G} {σ0 σ : State} {A : Addrs} {k : Nat} {d : Addr} {et : JType}
    {xsD : List Value} (hpre : RunPreGX g g.args σ0) (hg : Grows σ0 σ) (hI : Inits σ)
    (hkeep : W σ A (g.st k) ∧ MV (g.st k) ∧ AdEt σ A.aD ∧ Fresh σ0 A ∧
      (vreason g.xrefs (g.st k).accts (g.trec k) = 0 → ∃ x a,
        Model.findXref g.xrefs (Model.tCard (g.trec k)) = some x ∧
        Model.findAcct (g.st k).accts (Model.xAcct x) = some a ∧
        JRecAt CardXrefRecord xrCls σ (.ref A.wX) x ∧
        JRecAt AccountRecord acCls σ (.ref A.wA) a))
    (ha1 : σ.heap g.a1 = some (.array et xsD)) (hxk : xsD[k]? = some (.ref d))
    (hk : k < g.trans.length)
    (hcond : BitVec.ofInt 32 (vreason g.xrefs (g.st k).accts (g.trec k)) = 0#32) :
    ∃ x a, vreason g.xrefs (g.st k).accts (g.trec k) = 0 ∧
      Model.findXref g.xrefs (Model.tCard (g.trec k)) = some x ∧
      Model.findAcct (g.st k).accts (Model.xAcct x) = some a ∧
      DalytranRecord.Valid (g.trec k) ∧ CardXrefRecord.Valid x ∧ AccountRecord.Valid a ∧
      g.a1 < σ0.next ∧ PtFacts σ ⟨A, g.st k, g.trec k, x, a, g.clk, d, g.cs⟩ := by
  obtain ⟨-, hin, -⟩ := hpre
  obtain ⟨hW, hMV, hAd, -, hxa⟩ := hkeep
  have hv0 := vreason_zero_of hcond
  obtain ⟨x, a, hfx, hfa, hxj, haj⟩ := hxa hv0
  obtain ⟨hd, htv⟩ := trec_at hin hg ha1 hxk hk
  have hPF := ptFacts_of hin hg hW hMV hAd hk hd htv hfx hfa hxj haj hI
  have hav : AccountRecord.Valid a := hMV.1 a (List.mem_of_find?_eq_some hfa)
  have ha10 : g.a1 < σ0.next := by
    obtain ⟨a1, a2, a3, a4, cs, hargs, ⟨et1, xs1, h1, -⟩, -⟩ := hin
    simp only [G.args, List.cons.injEq, Value.ref.injEq, and_true] at hargs
    obtain ⟨rfl, -, -, -, -⟩ := hargs
    exact State.lt_next_of_heap h1
  exact ⟨x, a, hv0, hfx, hfa, htv, hPF.2.2.2.2.2.1, hav, ha10, hPF⟩

/-- **The loop head after a rejected transaction** (`writeReject` added its reject record). -/
theorem l65x_reject {g : G} {σ0 σ σ1 : State} {fr : Frame} {A : Addrs} {k : Nat} {next : I32}
    {et : JType} {xsD : List Value} {d y t1 t2 : Addr} {fsy : List (FieldKey × Value)} {m' : Nat}
    (hpre : RunPreGX g g.args σ0)
    (hL : Locs65 g A fr) (f14 : fr.get 14 = some (.int next)) (f4 : fr.get 4 = some (.int 0#32))
    (f9 : fr.get 9 = some (.long (BitVec.ofNat 64 ((k + 1) % 1000000000))))
    (ha1 : σ.heap g.a1 = some (.array et xsD)) (hlenD : xsD.length = g.trans.length)
    (hxk : xsD[k]? = some (.ref d)) (hnext : next.toInt = k + 1) (hk : k < g.trans.length)
    (hstx : g.stx k = ⟨g.st k, false⟩) (hv : vreason g.xrefs (g.st k).accts (g.trec k) ≠ 0)
    (hW : W σ A (g.st k)) (hMV : MV (g.st k)) (hAd : AdEt σ A.aD) (hFr : Fresh σ0 A)
    (hg : Grows σ0 σ)
    (hl' : σ1.heap (refField σ A.r rejKey) =
      some (.list .arrayList (listOf σ (refField σ A.r rejKey) ++ [.ref y]) m'))
    (hy : σ.next ≤ y) (hyo : σ1.heap y = some (.plain "Cbtrn02c$RejectRecord" fsy))
    (h1 : Fields.get fsy ("Cbtrn02c$RejectRecord", "rejectTranData") = some (.ref t1))
    (ht1 : σ1.heap t1 = some (.str (dtLine σ d)))
    (h2 : Fields.get fsy ("Cbtrn02c$RejectRecord", "validationTrailer") = some (.ref t2))
    (ht2 : σ1.heap t2 =
      some (.str (trailerJ (BitVec.ofInt 32 (vreason g.xrefs (g.st k).accts (g.trec k))))))
    (hn1 : σ.next ≤ σ1.next) (hi : σ1.inits = σ0.inits) (hs : σ1.statics = σ0.statics)
    (hfr : ∀ z, z < σ.next → ¬z = refField σ A.r rejKey → σ1.heap z = σ.heap z) :
    L65X g g.args σ0
      ((fr.setLocal 10 (.long (BitVec.ofNat 64 ((g.st k).rejects % 1000000000) + 1#64))).setLocal 10
        (.long (BitVec.srem (BitVec.ofNat 64 ((g.st k).rejects % 1000000000) + 1#64) 1000000000#64)))
      σ1 := by
  obtain ⟨-, hin, -⟩ := hpre
  obtain ⟨hd, htv⟩ := trec_at hin hg ha1 hxk hk
  have hline := (dalOk_line hd htv).2
  have hc4 := vreason_ne_cases hv
  have hstep : g.step (g.st k) (g.trec k) = (g.st k).reject (g.trec k)
      (vreason g.xrefs (g.st k).accts (g.trec k)) (descOf (vreason g.xrefs (g.st k).accts (g.trec k))) :=
    step_reject g.xrefs g.clk (g.st k) (g.trec k) hv
  have hst : g.st (k + 1) = (g.st k).reject (g.trec k)
      (vreason g.xrefs (g.st k).accts (g.trec k)) (descOf (vreason g.xrefs (g.st k).accts (g.trec k))) := by
    rw [G.st_succ g hk, hstep]
  obtain ⟨fsR, hRh, -, -, hRj, -⟩ := hW.1
  have hrf : refField σ A.r rejKey = A.lR := refField_of hRh hRj
  obtain ⟨xs0, m0, hl0, -⟩ := hW.2.2.2.1
  rw [hrf, listOf_of hl0] at hl'
  rw [hrf] at hfr
  have hf : FrameS σ σ1 [A.lR] :=
    ⟨hn1, fun z hz hm => hfr z hz (fun he => hm (by simp [he]))⟩
  obtain ⟨-, lr, -⟩ := G.lb g (Nat.le_of_lt hk)
  have hbound : g.trans.length < 2 ^ 27 := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hb⟩ := hin
    omega
  have hW1 := W_reject hW hl0 hl' hy hyo h1 (by rw [ht1, hline]) h2
    (by rw [ht2, trailer_of hc4]) hf (by omega)
  have hlR : σ0.next ≤ A.lR := hFr A.lR (by simp)
  have ha10 : g.a1 < σ0.next := by
    obtain ⟨a1, a2, a3, a4, cs, hargs, ⟨et1, xs1, h1', -⟩, -⟩ := hin
    simp only [G.args, List.cons.injEq, Value.ref.injEq, and_true] at hargs
    obtain ⟨rfl, -, -, -, -⟩ := hargs
    exact State.lt_next_of_heap h1'
  have hnot : ∀ z, z < σ0.next → z ∉ [A.lR] := by
    intro z hz hm
    simp only [List.mem_singleton] at hm
    subst hm
    exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le hz hlR)
  have hAd1 : AdEt σ1 A.aD := by
    obtain ⟨xs, hxs⟩ := hAd
    refine ⟨xs, hf.heap hxs ?_⟩
    intro hm
    simp only [List.mem_singleton] at hm
    rw [hm, hl0] at hxs
    cases hxs
  have hg1 : Grows σ0 σ1 := by
    refine ⟨Nat.le_trans hg.1 hf.1, fun z hz => ?_⟩
    rw [hf.2 z (Nat.lt_of_lt_of_le hz hg.1) (hnot z hz), hg.2 z hz]
  have hstx1 : g.stx (k + 1) = ⟨g.st (k + 1), false⟩ := by
    refine G.stx_succ_ok g hk hstx ?_
    intro hh
    have hp := hh.1
    rw [hstep] at hp
    simp only [Model.St.reject] at hp
    omega
  have hrej : (g.st (k + 1)).rejects = (g.st k).rejects + 1 := by rw [hst]; rfl
  obtain ⟨l32, l0, l16, l31, l8, l11, l12, l6, l13, l29, l28⟩ := hL
  refine ⟨A, k + 1, next, 0#32, BitVec.ofNat 64 ((k + 1) % 1000000000),
    BitVec.ofNat 64 (((g.st k).rejects + 1) % 1000000000), et, xsD,
    ⟨by frame_simp [l32], by frame_simp [l0], by frame_simp [l16], by frame_simp [l31],
      by frame_simp [l8], by frame_simp [l11], by frame_simp [l12], by frame_simp [l6],
      by frame_simp [l13], by frame_simp [l29], by frame_simp [l28]⟩,
    by frame_simp [f14], by frame_simp [f4], by frame_simp [f9], by frame_simp [cnt_succ],
    hf.heap ha1 (hnot _ ha10), hlenD, by omega, by omega, Or.inl rfl, rfl, by rw [hrej], hstx1,
    Hide.intro ⟨by rw [hst]; exact hW1, by rw [hst]; exact hMV, hAd1, hFr⟩, hg1, hi, hs⟩

end EquivLean.Modernize.Cbtrn02c.Java
