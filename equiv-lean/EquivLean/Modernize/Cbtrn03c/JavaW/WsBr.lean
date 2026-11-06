import EquivLean.Modernize.Cbtrn03c.JavaW.TotDefs
import EquivLean.Modernize.Cbtrn03c.JavaW.Lines
import EquivLean.Modernize.Cbtrn03c.JavaW.Bridge

/-!
# CBTRN03C → Java: the working state's fields and the model state

The shared `WsRel` splits into the fields of the `Ws` object (`WsAt`) and how they hold the model
state (`VRel`).  A writer's contract on the fields gives its contract on the model once the
counter and the totals agree as machine numbers (`inc_lc`, `add11J_ofInt`) and the written lines'
record texts are the model's lines (`recLine_eq`: Latin-1 lines).
-/

open Jimple EquivLean.Cobol.Rec EquivLean.Jimple

namespace EquivLean.Modernize.Cbtrn03c.Java

/-! ## Machine arithmetic of the counter and the totals -/

theorem inc_lc (n : Nat) (h : n < 1000000000) :
    (BitVec.ofNat 64 n + 1#64).srem 1000000000#64 = BitVec.ofNat 64 ((n + 1) % 1000000000) := by
  have h1 : BitVec.ofNat 64 n + 1#64 = BitVec.ofNat 64 (n + 1) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  rw [h1]
  have h2 : 0 ≤ (BitVec.ofNat 64 (n + 1)).toInt := by
    rw [BitVec.toInt_eq_toNat_cond]; simp only [BitVec.toNat_ofNat]; split <;> omega
  have h3 : 0 ≤ (1000000000#64 : BitVec 64).toInt := by decide
  apply BitVec.eq_of_toNat_eq
  have e := srem_toNat_of_nonneg _ _ h2 h3
  have e1 : (BitVec.ofNat 64 (n + 1)).toNat = n + 1 := by simp only [BitVec.toNat_ofNat]; omega
  have e2 : (1000000000#64 : BitVec 64).toNat = 1000000000 := by decide
  have e3 : (BitVec.ofNat 64 ((n + 1) % 1000000000)).toNat = (n + 1) % 1000000000 := by
    simp only [BitVec.toNat_ofNat]; omega
  rw [e, e1, e2, e3]

theorem incL_ofNat (n : Nat) (h : n < 1000000000) :
    incL (BitVec.ofNat 64 n) = BitVec.ofNat 64 ((n + 1) % 1000000000) := inc_lc n h

theorem trunc11_small {x : Int} (h : x.natAbs < 200000000000) :
    (BitVec.ofInt 64 x).toInt = x := by
  rw [BitVec.toInt_ofInt, Int.bmod_def]
  have h2 : ((2 : Nat) ^ 64 : Nat) = 18446744073709551616 := by decide
  simp only [h2]
  split <;> omega

theorem trunc11_lt (x : Int) : (Model.trunc11 x).natAbs < 100000000000 := by
  unfold Model.trunc11
  have l1 := Int.tmod_lt_of_pos x (show (0 : Int) < 100000000000 by decide)
  have l2 := Int.lt_tmod_of_pos x (show (0 : Int) < 100000000000 by decide)
  omega

/-- `add11` on the totals: the model's `trunc11` of the sum. -/
theorem add11J_ofInt (a b : Int) (ha : a.natAbs < 100000000000) (hb : b.natAbs < 100000000000) :
    add11J (BitVec.ofInt 64 a) (BitVec.ofInt 64 b) = BitVec.ofInt 64 (Model.trunc11 (a + b)) := by
  unfold add11J
  apply BitVec.eq_of_toInt_eq
  rw [BitVec.toInt_srem]
  have h2 : ((2 : Nat) ^ 64 : Nat) = 18446744073709551616 := by decide
  have hab : (BitVec.ofInt 64 a + BitVec.ofInt 64 b).toInt = a + b := by
    rw [BitVec.toInt_add, trunc11_small (by omega), trunc11_small (by omega), Int.bmod_def]
    simp only [h2]
    split <;> omega
  have hc : (BitVec.ofInt 64 100000000000).toInt = 100000000000 := by decide
  have ht : (BitVec.ofInt 64 (Model.trunc11 (a + b))).toInt = (a + b).tmod 100000000000 :=
    trunc11_small (by have := trunc11_lt (a + b); omega)
  rw [hab, hc, ht]

/-! ## Latin-1 lines: a written line's record text is the line -/

/-- Every code point of `l` is a Latin-1 one (CP037 maps `0 ..= 255` onto the bytes). -/
def Latin1 (l : List Nat) : Prop := ∀ u ∈ l, u < 256

set_option maxRecDepth 100000 in
theorem ebc_unit_all : ∀ u : Fin 256, cp037Unit (Model.ebc u.val) = BitVec.ofNat 16 u.val := by
  decide +kernel

theorem recLine_eq {l : List Nat} (h : Latin1 l) : Top.recLine l = jline l := by
  simp only [Top.recLine, cp037Str, jline, List.map_map]
  apply List.map_congr_left
  intro u hu
  exact ebc_unit_all ⟨u, h u hu⟩

theorem latin1_append {a b : List Nat} (ha : Latin1 a) (hb : Latin1 b) : Latin1 (a ++ b) :=
  fun u hu => (List.mem_append.1 hu).elim (ha u) (hb u)

theorem latin1_cons {u : Nat} {l : List Nat} (hu : u < 256) (hl : Latin1 l) : Latin1 (u :: l) :=
  fun v hv => (List.mem_cons.1 hv).elim (fun h => h ▸ hu) (hl v)

theorem latin1_replicate {n u : Nat} (hu : u < 256) : Latin1 (List.replicate n u) := by
  intro v hv; rw [(List.mem_replicate.1 hv).2]; exact hu

theorem latin1_take {l : List Nat} (h : Latin1 l) (n : Nat) : Latin1 (l.take n) :=
  fun u hu => h u (List.mem_of_mem_take hu)

theorem latin1_pad {l : List Nat} (h : Latin1 l) (n : Nat) : Latin1 (Model.pad l n) :=
  latin1_append (latin1_take h n) (latin1_replicate (by decide))

theorem latin1_zzz (p : List Char) : ∀ (ds : List Nat) (sup : Bool), (∀ d ∈ ds, d < 10) →
    Latin1 (Model.zzz p ds sup) := by
  induction p with
  | nil => intro ds sup _; cases ds <;> simp [Model.zzz, Latin1]
  | cons c p ih =>
    intro ds sup h
    cases ds with
    | nil =>
      by_cases hc : c = ','
      · simp only [Model.zzz, if_pos hc]
        exact latin1_cons (by cases sup <;> decide) (ih [] sup h)
      · simp [Model.zzz, hc, Latin1]
    | cons d ds =>
      have hd : d < 10 := h d (List.mem_cons_self ..)
      have h' : ∀ e ∈ ds, e < 10 := fun e he => h e (List.mem_cons_of_mem _ he)
      by_cases hc : c = ','
      · simp only [Model.zzz, if_pos hc]
        exact latin1_cons (by cases sup <;> decide) (ih (d :: ds) sup h)
      · simp only [Model.zzz, if_neg hc]
        split
        · exact latin1_cons (by decide) (ih ds true h')
        · exact latin1_cons (by omega) (ih ds false h')

theorem latin1_editAmt (v : Int) (plus : Bool) : Latin1 (Model.editAmt v plus) := by
  simp only [Model.editAmt]
  split
  · exact latin1_replicate (by decide)
  · refine latin1_cons (by split; decide; split <;> decide)
      (latin1_append (latin1_zzz _ _ _ (fun d hd => toDigits_lt10 hd)) ?_)
    intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl <;> omega

/-! ## The total lines and the dashes -/

theorem totalLine_eq (lbl : String) (w n : Nat) {p : Int} (hp : p.natAbs < 100000000000)
    (hl : JStr.ofString lbl = jline (Model.txt lbl)) :
    totalLineJ (JStr.ofString lbl) w n (BitVec.ofInt 64 p) =
      jline (Model.pad (Model.txt lbl) w ++ List.replicate n 46 ++ Model.editAmt p true) := by
  rw [totalLineJ, hl, fixJ_eq, repJ_eq, trunc11_small (by omega), editJ_eq]
  simp only [jline_append, List.append_assoc]

theorem latin1_totalLine (lbl : String) (w n : Nat) (p : Int) (hl : Latin1 (Model.txt lbl)) :
    Latin1 (Model.to133 (Model.pad (Model.txt lbl) w ++ List.replicate n 46 ++
      Model.editAmt p true)) :=
  latin1_pad (latin1_append (latin1_append (latin1_pad hl w) (latin1_replicate (by decide)))
    (latin1_editAmt p true)) 133

theorem pageLine_eq {p : Int} (hp : p.natAbs < 100000000000) :
    fixJ (totalLineJ (JStr.ofString "Page Total") 11 86 (BitVec.ofInt 64 p)) 133 =
      Top.recLine (Model.pageTotalLine p) := by
  rw [Model.pageTotalLine,
    recLine_eq (latin1_totalLine "Page Total" 11 86 p (by unfold Latin1; decide)),
    totalLine_eq _ _ _ hp lit_pageTotal, Model.to133, fixJ_eq]

theorem acctLine_eq {p : Int} (hp : p.natAbs < 100000000000) :
    fixJ (totalLineJ (JStr.ofString "Account Total") 13 84 (BitVec.ofInt 64 p)) 133 =
      Top.recLine (Model.acctTotalLine p) := by
  rw [Model.acctTotalLine,
    recLine_eq (latin1_totalLine "Account Total" 13 84 p (by unfold Latin1; decide)),
    totalLine_eq _ _ _ hp lit_accountTotal, Model.to133, fixJ_eq]

theorem grandLine_eq {p : Int} (hp : p.natAbs < 100000000000) :
    fixJ (totalLineJ (JStr.ofString "Grand Total") 11 86 (BitVec.ofInt 64 p)) 133 =
      Top.recLine (Model.grandTotalLine p) := by
  rw [Model.grandTotalLine,
    recLine_eq (latin1_totalLine "Grand Total" 11 86 p (by unfold Latin1; decide)),
    totalLine_eq _ _ _ hp lit_grandTotal, Model.to133, fixJ_eq]

theorem dashLine_eq : fixJ dashJ 133 = Top.recLine Model.header2 := by
  rw [Model.header2, recLine_eq (latin1_replicate (n := 133) (u := 45) (by decide)), dashJ,
    repJ_eq, fixJ_eq]
  simp [Model.pad]

/-! ## Report records -/

theorem top_recsAt_append {σ : State} {a b : List Value} {c e : List JStr}
    (h1 : Top.RecsAt σ a c) (h2 : Top.RecsAt σ b e) : Top.RecsAt σ (a ++ b) (c ++ e) := by
  unfold Top.RecsAt at *
  rw [List.map_append, List.map_append, h1, h2]

theorem top_recsAt_one {σ : State} {y : Value} {t : JStr} (h : Top.recText σ y = some t) :
    Top.RecsAt σ [y] [t] := by
  simp [Top.RecsAt, h]

theorem top_recsAt_pair {σ : State} {y1 y2 : Value} {t1 t2 : JStr}
    (h1 : Top.recText σ y1 = some t1) (h2 : Top.recText σ y2 = some t2) :
    Top.RecsAt σ [y1, y2] [t1, t2] := by
  simp [Top.RecsAt, h1, h2]

/-! ## `WsRel` = fields + values -/

/-- The fields `v` of a working state hold the model state `s` (date parameters `d`). -/
def VRel (σ : State) (d : List EquivLean.Cobol.Rec.FVal) (v : WsV) (s : Model.St) : Prop :=
  v.first = (if s.first then 1 else 0) ∧
  (∃ c, v.cardRef = .ref c ∧ σ.heap c = some (.str (cp037Str s.card))) ∧
  (∃ rx, v.rsRef = .ref rx ∧ σ.heap rx = some (.str (cp037Str (Model.dStart d)))) ∧
  (∃ ex, v.reRef = .ref ex ∧ σ.heap ex = some (.str (cp037Str (Model.dEnd d)))) ∧
  v.acctId = BitVec.ofInt 64 (Model.xAcct s.xref) ∧ v.lc = BitVec.ofNat 64 s.lc ∧
  v.page = BitVec.ofInt 64 s.page ∧ v.acct = BitVec.ofInt 64 s.acct ∧
  v.grand = BitVec.ofInt 64 s.grand ∧
  StrsAt σ v.dsp (s.disp.map jline) ∧ Top.RecsAt σ v.wrs (s.writes.map Top.recLine) ∧
  (s.first = false → s.rs = Model.cps (Model.dStart d) ∧ s.re = Model.cps (Model.dEnd d)) ∧
  Top.StOk s

theorem wsRel_iff {σ : State} {w ld lr : Addr} {d : List EquivLean.Cobol.Rec.FVal} {s : Model.St} :
    Top.WsRel σ w ld lr d s ↔ ∃ v, WsAt σ w ld lr v ∧ VRel σ d v s := by
  constructor
  · rintro ⟨fs, dsp, wrs, dm, wm, c, rx, ex, hw, hd, hr, hf, hc, hrx, hex, ha, hl, hp, hac, hg,
      hld, hlr, h1, h2, h3, hS, hR, hcs, hrs, hes, hfirst, hok⟩
    exact ⟨⟨dsp, wrs, if s.first then 1 else 0, .ref c, .ref rx, .ref ex,
        BitVec.ofInt 64 (Model.xAcct s.xref), BitVec.ofNat 64 s.lc, BitVec.ofInt 64 s.page,
        BitVec.ofInt 64 s.acct, BitVec.ofInt 64 s.grand⟩,
      ⟨fs, dm, wm, hw, hd, hr, hf, hc, hrx, hex, ha, hl, hp, hac, hg, hld, hlr, h1, h2, h3⟩,
      rfl, ⟨c, rfl, hcs⟩, ⟨rx, rfl, hrs⟩, ⟨ex, rfl, hes⟩, rfl, rfl, rfl, rfl, rfl, hS, hR,
      hfirst, hok⟩
  · rintro ⟨v, ⟨fs, dm, wm, hw, hd, hr, hf, hc, hrx, hex, ha, hl, hp, hac, hg, hld, hlr, h1, h2,
      h3⟩, hfv, ⟨c, hcv, hcs⟩, ⟨rx, hrv, hrs⟩, ⟨ex, hev, hes⟩, hav, hlv, hpv, hacv, hgv, hS, hR,
      hfirst, hok⟩
    refine ⟨fs, v.dsp, v.wrs, dm, wm, c, rx, ex, hw, hd, hr, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      hld, hlr, h1, h2, h3, hS, hR, hcs, hrs, hes, hfirst, hok⟩
    · rw [← hfv]; exact hf
    · rw [← hcv]; exact hc
    · rw [← hrv]; exact hrx
    · rw [← hev]; exact hex
    · rw [← hav]; exact ha
    · rw [← hlv]; exact hl
    · rw [← hpv]; exact hp
    · rw [← hacv]; exact hac
    · rw [← hgv]; exact hg

theorem wsAt_wsVOf {σ : State} {w ld lr : Addr} {v : WsV} (h : WsAt σ w ld lr v) :
    wsVOf σ w = v ∧ ldOf σ w = ld ∧ lrOf σ w = lr := by
  obtain ⟨fs, dm, wm, hw, hd, hr, hf, hc, hrx, hex, ha, hl, hp, hac, hg, hld, hlr, -, -, -⟩ := h
  have e : ∀ f, wsF σ w f = (Fields.get fs (wsC, f)).getD .null := fun f => by simp [wsF, hw]
  refine ⟨?_, ?_, ?_⟩
  · cases v
    simp only [wsVOf, e, hd, hr, hf, hc, hrx, hex, ha, hl, hp, hac, hg, Option.getD_some, refOf,
      listVals, hld, hlr, intOf, longOf]
  · simp [ldOf, e, hd, refOf]
  · simp [lrOf, e, hr, refOf]

/-- A writer's effect on the values: the fields it keeps, the counters and totals it sets, the
report records it appends. -/
theorem vrel_of {σ σ' : State} {d : List EquivLean.Cobol.Rec.FVal} {v v' : WsV} {s s' : Model.St}
    (hV : VRel σ d v s) (hm : StrMono σ σ')
    (hfirst : s'.first = s.first) (hcard : s'.card = s.card) (hxref : s'.xref = s.xref)
    (hrs : s'.rs = s.rs) (hre : s'.re = s.re) (hdisp : s'.disp = s.disp)
    (vfirst : v'.first = v.first) (vcard : v'.cardRef = v.cardRef) (vrs : v'.rsRef = v.rsRef)
    (vre : v'.reRef = v.reRef) (vacctId : v'.acctId = v.acctId) (vdsp : v'.dsp = v.dsp)
    (hlc : v'.lc = BitVec.ofNat 64 s'.lc) (hpage : v'.page = BitVec.ofInt 64 s'.page)
    (hacct : v'.acct = BitVec.ofInt 64 s'.acct) (hgrand : v'.grand = BitVec.ofInt 64 s'.grand)
    (hwrs : Top.RecsAt σ' v'.wrs (s'.writes.map Top.recLine)) (hok : Top.StOk s') :
    VRel σ' d v' s' := by
  obtain ⟨h1, ⟨c, hc, hcs⟩, ⟨rx, hrx, hrxs⟩, ⟨ex, hex, hexs⟩, h5, -, -, -, -, h10, -, h12, -⟩ := hV
  refine ⟨by rw [vfirst, h1, hfirst], ⟨c, by rw [vcard, hc], by rw [hcard]; exact hm _ _ hcs⟩,
    ⟨rx, by rw [vrs, hrx], hm _ _ hrxs⟩, ⟨ex, by rw [vre, hex], hm _ _ hexs⟩,
    by rw [vacctId, h5, hxref], hlc, hpage, hacct, hgrand,
    by rw [vdsp, hdisp]; exact h10.mono hm, hwrs, by rw [hfirst, hrs, hre]; exact h12, hok⟩

end EquivLean.Modernize.Cbtrn03c.Java
