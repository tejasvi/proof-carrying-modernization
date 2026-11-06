import EquivLean.Modernize.Cbtrn03c.JavaW.WsM3

/-!
# CBTRN03C → Java: `writeDetail` on the model state

`writeDetailM_sat`: the detail line `Model.detailLine t s.xref y cc` written and counted, on
`WsRel`, for a valid transaction, type and category record and an account id of at most 11
digits; from `writeDetail_satG` at the ghost values the postcondition names.
-/

open Jimple EquivLean.Cobol.Rec EquivLean.Jimple

namespace EquivLean.Modernize.Cbtrn03c.Java

/-! ## Latin-1, field by field -/

theorem latin1_append_iff {a b : List Nat} : Latin1 (a ++ b) ↔ Latin1 a ∧ Latin1 b :=
  ⟨fun h => ⟨fun u hu => h u (List.mem_append.2 (Or.inl hu)),
    fun u hu => h u (List.mem_append.2 (Or.inr hu))⟩, fun h => latin1_append h.1 h.2⟩

theorem latin1_cons_iff {u : Nat} {l : List Nat} : Latin1 (u :: l) ↔ u < 256 ∧ Latin1 l :=
  ⟨fun h => ⟨h u (List.mem_cons_self ..), fun v hv => h v (List.mem_cons_of_mem _ hv)⟩,
    fun h => latin1_cons h.1 h.2⟩

theorem latin1_nil : Latin1 [] := fun _ h => absurd h (List.not_mem_nil)

theorem latin1_zpad (n v : Nat) : Latin1 (zpad n v) := by
  intro u hu
  obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hu
  have := toDigits_lt10 hd
  omega

/-! ## The detail line -/

theorem pad_take (L : List Nat) (n : Nat) : Model.pad (L.take n) n = Model.pad L n := by
  unfold Model.pad
  rw [List.take_take, Nat.min_self, List.length_take]
  have : n - min n L.length = n - L.length := by omega
  rw [this]

theorem cps_take (l : List UInt8) (n : Nat) : Model.cps (l.take n) = (Model.cps l).take n :=
  List.map_take ..

theorem space_eq : space = BitVec.ofNat 16 32 := rfl

theorem txt_sp4 : Model.txt "    " = List.replicate 4 32 := by decide
theorem txt_sp2 : Model.txt "  " = List.replicate 2 32 := by decide

set_option maxHeartbeats 2000000 in
theorem detailLine_eq {t x y cc : List EquivLean.Cobol.Rec.FVal} (ht : TranRecord.Valid t)
    (hx : (Model.xAcct x).natAbs < 100000000000) :
    fixJ (detailJ t (BitVec.ofInt 64 (Model.xAcct x)) (cp037Str (Model.yDesc y))
      (cp037Str (Model.cDesc cc))) 133 = Top.recLine (Model.detailLine t x y cc) := by
  obtain ⟨id, ty, cat, src, desc, amt, merch, mname, mcity, mzip, card, orig, proc, fill, rfl,
    hid, hty, hcat, -, hsrc, -, hamt, -⟩ := Glue.tran_shape ht
  have hL : Latin1 (Model.detailLine [.str id, .str ty, .num cat, .str src, .str desc, .num amt,
      .num merch, .str mname, .str mcity, .str mzip, .str card, .str orig, .str proc, .str fill]
      x y cc) := by
    simp only [Model.detailLine, Model.to133, Model.digs]
    refine latin1_pad ?_ 133
    simp only [latin1_append_iff, latin1_cons_iff, latin1_nil, latin1_cps, latin1_zpad,
      latin1_editAmt, latin1_pad, latin1_replicate, Nat.reduceLT, and_true, true_and]
  have e1 : (BitVec.ofInt 64 (Model.xAcct x)).toInt = Model.xAcct x :=
    trunc11_small (by omega)
  have e2 : (BitVec.ofInt 64 cat).toInt = cat := trunc11_small (by omega)
  have e3 : (BitVec.ofInt 64 amt).toInt = amt := trunc11_small (by omega)
  have p1 : Model.pad (Model.cps id) 16 = Model.cps id :=
    Glue.pad_of_length (by rw [Glue.length_cps]; exact hid)
  have p2 : Model.pad (Model.cps ty) 2 = Model.cps ty :=
    Glue.pad_of_length (by rw [Glue.length_cps]; exact hty)
  have p3 : Model.pad (Model.cps src) 10 = Model.cps src :=
    Glue.pad_of_length (by rw [Glue.length_cps]; exact hsrc)
  rw [recLine_eq hL, Model.detailLine, Model.to133, ← fixJ_eq]
  refine congrArg (fun z => fixJ z 133) ?_
  simp only [detailJ, detP2, detP1, Model.digs, Model.tId, Model.tType, Model.tCat,
    Model.tSource, Model.tAmt, Model.strOf, Model.numOf, List.getD_cons_zero,
    List.getD_cons_succ, cp037Str_eq, e1, e2, e3, editJ_eq, zpadJ_eq, lit_sp4, lit_sp2, txt_sp4,
    txt_sp2, fixJ_eq, p1, p2, p3, cps_take, pad_take, space_eq, jline_append, jline_cons,
    jline_nil, List.append_assoc, List.cons_append, List.singleton_append, List.nil_append]

/-! ## `writeDetail` on the model -/

def writeDetailSig : MethodSig :=
  ⟨"Cbtrn03c", .void, "writeDetail",
    [.cls "Cbtrn03c$Ws", .cls "Cbtrn03c$TranRecord", .cls "java.lang.String", .cls "java.lang.String"]⟩

/-- `writeDetail(ws, tran, typeDesc, catDesc)`: the detail line written and counted. -/
def writeDetailSpecM : Spec := Spec.of
  (fun args σ => ∃ w ld lr c ty ca d s t y cc, args = [.ref w, .ref c, .ref ty, .ref ca] ∧
     Top.WsRel σ w ld lr d s ∧ Top.TranFields σ c t ∧ TranRecord.Valid t ∧
     TranTypeRecord.Valid y ∧ TranCatRecord.Valid cc ∧
     (Model.xAcct s.xref).natAbs < 100000000000 ∧
     σ.heap ty = some (.str (cp037Str (Model.yDesc y))) ∧
     σ.heap ca = some (.str (cp037Str (Model.cDesc cc))) ∧
     σ.initOf "Cbtrn03c" = .done ∧ σ.initOf fdC = .done)
  (fun args σ r σ' => ∀ w ld lr c ty ca d s t y cc, args = [.ref w, .ref c, .ref ty, .ref ca] →
     Top.WsRel σ w ld lr d s → Top.TranFields σ c t → TranRecord.Valid t →
     TranTypeRecord.Valid y → TranCatRecord.Valid cc →
     (Model.xAcct s.xref).natAbs < 100000000000 →
     σ.heap ty = some (.str (cp037Str (Model.yDesc y))) →
     σ.heap ca = some (.str (cp037Str (Model.cDesc cc))) →
     r = none ∧ Top.WsRel σ' w ld lr d (Model.inc (Model.wr s (Model.detailLine t s.xref y cc))) ∧
     Top.KeepsNonWs σ σ' ∧ σ'.inits = σ.inits ∧ σ'.statics = σ.statics)

theorem writeDetailM_sat : Sat Gen.prog writeDetailRef writeDetailSpecM := by
  intro args σ o hpre hx
  obtain ⟨w0, ld0, lr0, c0, ty0, ca0, d0, s0, t0, y0, cc0, hargs0, hR0, hT0, ht0, hy0, hc0, hxa0,
    hty0, hca0, hi1, hi2⟩ := hpre
  have key : ∀ w ld lr c ty ca d s t y cc, args = [.ref w, .ref c, .ref ty, .ref ca] →
      Top.WsRel σ w ld lr d s → Top.TranFields σ c t → TranRecord.Valid t →
      TranTypeRecord.Valid y → TranCatRecord.Valid cc →
      (Model.xAcct s.xref).natAbs < 100000000000 →
      σ.heap ty = some (.str (cp037Str (Model.yDesc y))) →
      σ.heap ca = some (.str (cp037Str (Model.cDesc cc))) →
      ∃ v, WsAt σ w ld lr v ∧ VRel σ d v s ∧
        (writeDetailSpecG w ld lr v c ty ca t (cp037Str (Model.yDesc y))
          (cp037Str (Model.cDesc cc))).post args σ o := by
    intro w ld lr c ty ca d s t y cc h1 h2 h3 h4 h5 h6 h7 h8 h9
    obtain ⟨v, hA, hV⟩ := wsRel_iff.1 h2
    have hV0 := hV
    obtain ⟨-, -, -, -, ha, -⟩ := hV0
    obtain ⟨id, tty, cat, src, desc, amt, _, _, _, _, _, _, _, _, rfl, hid, htt, hcat, -, hsrc, -,
      hamt, -⟩ := Glue.tran_shape h4
    obtain ⟨_, ydesc, _, rfl, -, hyd, -⟩ := Glue.type_shape h5
    obtain ⟨_, _, cdesc, _, rfl, -, -, -, hcd, -⟩ := Glue.catg_shape h6
    refine ⟨v, hA, hV, writeDetail_satG w ld lr v c ty ca _ _ _ args σ o
      ⟨h1, hA, ?_, detailFields_of h3, ?_, ?_, ?_, ?_, ?_, h8, ?_, h9, ?_, hi1, hi2⟩ hx⟩
    · rw [ha, trunc11_small (by omega)]; omega
    · show id.length < 1000; omega
    · show tty.length < 1000; omega
    · show src.length < 1000; omega
    · show -9223372036854775808 < (BitVec.ofInt 64 cat).toInt
      rw [trunc11_small (by omega)]; omega
    · show -9223372036854775808 < (BitVec.ofInt 64 amt).toInt
      rw [trunc11_small (by omega)]; omega
    · show (cp037Str ydesc).length < 1000
      rw [cp037Str_length]; omega
    · show (cp037Str cdesc).length < 1000
      rw [cp037Str_length]; omega
  cases o with
  | normal r σ' =>
    intro w ld lr c ty ca d s t y cc hargs hR hT ht hy hc hxa hty hca
    obtain ⟨v, hA, hV, hpost⟩ := key w ld lr c ty ca d s t y cc hargs hR hT ht hy hc hxa hty hca
    obtain ⟨r1, hr, hA2, hR1, hfr, hi, hs⟩ := hpost
    obtain ⟨fs, dm, wm, hw0, -, -, -, -, -, -, -, -, -, -, -, hldh, hlrh, -, -, -⟩ := hA
    have hk := keepsNonWs_of_frame3 hfr hw0 hldh hlrh
    refine ⟨hr, wsRel_iff.2 ⟨_, hA2, ?_⟩, hk, hi, hs⟩
    have hV0 := hV
    obtain ⟨-, -, -, -, ha, hlc, hpg, hac, hgr, -, hW, -, hlck, hpk, hak, hgk, hxk⟩ := hV0
    refine vrel_of hV hk.2.1 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl ?_ hpg hac hgr ?_
      ⟨Nat.mod_lt _ (by decide), hpk, hak, hgk, hxk⟩
    · show incL v.lc = BitVec.ofNat 64 ((s.lc + 1) % 1000000000)
      rw [hlc, incL_ofNat _ hlck]
    · show Top.RecsAt σ' (v.wrs ++ [.ref r1])
        ((s.writes ++ [Model.detailLine t s.xref y cc]).map Top.recLine)
      simp only [List.map_append, List.map_cons, List.map_nil]
      rw [← detailLine_eq ht hxa, ← ha]
      exact top_recsAt_append (top_recsAt_mono hk hW) (top_recsAt_one (recT_text hR1))
  | exc e σ' =>
    obtain ⟨_, _, _, hpost⟩ := key w0 ld0 lr0 c0 ty0 ca0 d0 s0 t0 y0 cc0 hargs0 hR0 hT0 ht0 hy0 hc0
      hxa0 hty0 hca0
    exact hpost
  | wrong m =>
    obtain ⟨_, _, _, hpost⟩ := key w0 ld0 lr0 c0 ty0 ca0 d0 s0 t0 y0 cc0 hargs0 hR0 hT0 ht0 hy0 hc0
      hxa0 hty0 hca0
    exact hpost

set_option maxHeartbeats 0 in
theorem writeDetailM_ok : ContractOK Gen.prog writeDetailSig writeDetailSpecM := by
  jcontract_ok [writeDetailM_sat]

end EquivLean.Modernize.Cbtrn03c.Java

#print axioms EquivLean.Modernize.Cbtrn03c.Java.writeDetailM_ok
