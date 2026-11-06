import EquivLean.Modernize.Cbtrn03c.JavaW.W4v
import EquivLean.Modernize.Cbtrn03c.JavaW.WsM
import EquivLean.Modernize.Cbtrn03c.Glue

/-!
# CBTRN03C → Java: `writeHeaders` on the model state

`writeHeadersM_sat`: `Model.headers` on `WsRel`, for a state whose report dates are set
(`first = false`) and a valid date parameter record; from `writeHeaders_satG` at the ghost values
the postcondition names.
-/

open Jimple EquivLean.Cobol.Rec EquivLean.Jimple

namespace EquivLean.Modernize.Cbtrn03c.Java

open EquivLean.Modernize.GlueKit in
theorem dateparm_len {d : List EquivLean.Cobol.Rec.FVal} (hd : WsDateparmRecord.Valid d) :
    (Model.dStart d).length = 10 ∧ (Model.dEnd d).length = 10 := by
  have hl : d.length = 3 := hd.length_eq.symm
  match d, hl, hd with
  | [x0, x1, x2], _, .cons h0 (.cons h1 (.cons h2 .nil)) =>
    obtain ⟨a, rfl, ha⟩ := str_of_valid rfl h0
    obtain ⟨b, rfl, hb⟩ := str_of_valid rfl h1
    obtain ⟨e, rfl, he⟩ := str_of_valid rfl h2
    exact ⟨ha, he⟩

set_option maxRecDepth 100000 in
theorem cp037Code_lt_fin : ∀ n : Fin 256, cp037Code (UInt8.ofNat n.val) < 256 := by
  decide +kernel

theorem cp037Code_lt_all (b : UInt8) : cp037Code b < 256 := by
  have h := cp037Code_lt_fin ⟨b.toNat, b.toNat_lt⟩
  simpa using h

theorem latin1_cps (bs : List UInt8) : Latin1 (Model.cps bs) := by
  intro u hu
  obtain ⟨b, -, rfl⟩ := List.mem_map.1 hu
  exact cp037Code_lt_all b

theorem recT_text {σ : State} {r : Addr} {t : JStr} (h : RecT σ r t) :
    Top.recText σ (.ref r) = some t := by
  obtain ⟨f, z, h1, h2, h3⟩ := h
  exact top_recText_of_heap h1 h2 h3

/-! ## The header lines -/

theorem nameLine_eq (a b : List UInt8) :
    fixJ (nameHeaderJ (cp037Str a) (cp037Str b)) 133 =
      Top.recLine (Model.nameHeader (Model.cps a) (Model.cps b)) := by
  have hL : Latin1 (Model.nameHeader (Model.cps a) (Model.cps b)) := by
    unfold Model.nameHeader Model.to133
    refine latin1_pad (latin1_append (latin1_append (latin1_append (latin1_append
      (latin1_append (latin1_pad ?_ 38) (latin1_pad ?_ 41)) (latin1_pad ?_ 12)) (latin1_cps a)) ?_)
      (latin1_cps b)) 133
    all_goals (unfold Latin1; decide)
  have h12 : Model.pad (Model.txt "Date Range: ") 12 = Model.txt "Date Range: " := by decide
  rw [recLine_eq hL]
  unfold nameHeaderJ Model.nameHeader Model.to133
  rw [lit_dalyrept, lit_dailyReport, lit_dateRange, lit_to, cp037Str_eq, cp037Str_eq, fixJ_eq,
    fixJ_eq, h12]
  simp only [← jline_append]
  rw [fixJ_eq]
  simp only [List.append_assoc]

theorem blankLine_eq : fixJ (spJ 133) 133 = Top.recLine Model.blankLine := by
  rw [Model.blankLine, recLine_eq (latin1_replicate (n := 133) (u := 32) (by decide)), spJ_eq,
    fixJ_eq]
  simp [Model.pad]

theorem header1_eq : fixJ header1J 133 = Top.recLine Model.header1 := by
  decide +kernel

/-! ## `writeHeaders` on the model -/

def writeHeadersSig : MethodSig := ⟨"Cbtrn03c", .void, "writeHeaders", [.cls "Cbtrn03c$Ws"]⟩

/-- `writeHeaders`: `Model.headers`, once the report dates are set. -/
def writeHeadersSpecM : Spec := Spec.of
  (fun args σ => ∃ w ld lr d s, args = [.ref w] ∧ Top.WsRel σ w ld lr d s ∧ s.first = false ∧
     WsDateparmRecord.Valid d ∧ σ.initOf "Cbtrn03c" = .done ∧ σ.initOf fdC = .done)
  (fun args σ r σ' => ∀ w ld lr d s, args = [.ref w] → Top.WsRel σ w ld lr d s →
     s.first = false → WsDateparmRecord.Valid d →
     r = none ∧ Top.WsRel σ' w ld lr d (Model.headers s) ∧ Top.KeepsNonWs σ σ' ∧
     σ'.inits = σ.inits ∧ σ'.statics = σ.statics)

theorem writeHeadersM_sat : Sat Gen.prog writeHeadersRef writeHeadersSpecM := by
  intro args σ o hpre hx
  obtain ⟨w0, ld0, lr0, d0, s0, hargs0, hR0, -, hd0, hi1, hi2⟩ := hpre
  have key : ∀ w ld lr d s, args = [.ref w] → Top.WsRel σ w ld lr d s →
      WsDateparmRecord.Valid d →
      ∃ v rx ex, WsAt σ w ld lr v ∧ VRel σ d v s ∧
        (writeHeadersSpecG w ld lr v rx ex (cp037Str (Model.dStart d))
          (cp037Str (Model.dEnd d))).post args σ o := by
    intro w ld lr d s h1 h2 h3
    obtain ⟨v, hA, hV⟩ := wsRel_iff.1 h2
    have hV0 := hV
    obtain ⟨-, -, ⟨rx, hrx, hrxs⟩, ⟨ex, hex, hexs⟩, -⟩ := hV0
    obtain ⟨l1, l2⟩ := dateparm_len h3
    refine ⟨v, rx, ex, hA, hV, writeHeaders_satG w ld lr v rx ex _ _ args σ o
      ⟨h1, hA, hrx, hrxs, hex, hexs, ?_, ?_, hi1, hi2⟩ hx⟩
    · rw [cp037Str_length]; omega
    · rw [cp037Str_length]; omega
  cases o with
  | normal r σ' =>
    intro w ld lr d s hargs hR hf hd
    obtain ⟨v, rx, ex, hA, hV, hpost⟩ := key w ld lr d s hargs hR hd
    obtain ⟨r1, r2, r3, r4, hr, hA2, hR1, hR2, hR3, hR4, hfr, hi, hs⟩ := hpost
    obtain ⟨fs, dm, wm, hw0, -, -, -, -, -, -, -, -, -, -, -, hldh, hlrh, -, -, -⟩ := hA
    have hk := keepsNonWs_of_frame3 hfr hw0 hldh hlrh
    refine ⟨hr, wsRel_iff.2 ⟨_, hA2, ?_⟩, hk, hi, hs⟩
    have hV0 := hV
    obtain ⟨-, -, -, -, -, hlc, hpg, hac, hgr, -, hW, hrs, hlck, hpk, hak, hgk, hxk⟩ := hV0
    obtain ⟨hrs1, hre1⟩ := hrs hf
    refine vrel_of hV hk.2.1 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl ?_ hpg hac hgr ?_ ?_
    · show incL (incL (incL (incL v.lc))) = BitVec.ofNat 64
        (((((s.lc + 1) % 1000000000 + 1) % 1000000000 + 1) % 1000000000 + 1) % 1000000000)
      rw [hlc, incL_ofNat _ hlck, incL_ofNat _ (Nat.mod_lt _ (by decide)),
        incL_ofNat _ (Nat.mod_lt _ (by decide)), incL_ofNat _ (Nat.mod_lt _ (by decide))]
    · show Top.RecsAt σ' (v.wrs ++ [.ref r1] ++ [.ref r2] ++ [.ref r3] ++ [.ref r4])
        ((s.writes ++ [Model.nameHeader s.rs s.re] ++ [Model.blankLine] ++ [Model.header1] ++
          [Model.header2]).map Top.recLine)
      simp only [List.map_append, List.map_cons, List.map_nil]
      rw [hrs1, hre1, ← nameLine_eq, ← blankLine_eq, ← header1_eq, ← dashLine_eq]
      exact top_recsAt_append (top_recsAt_append (top_recsAt_append (top_recsAt_append
        (top_recsAt_mono hk hW) (top_recsAt_one (recT_text hR1))) (top_recsAt_one (recT_text hR2)))
        (top_recsAt_one (recT_text hR3))) (top_recsAt_one (recT_text hR4))
    · exact ⟨Nat.mod_lt _ (by decide), hpk, hak, hgk, hxk⟩
  | exc e σ' =>
    obtain ⟨_, _, _, _, _, hpost⟩ := key w0 ld0 lr0 d0 s0 hargs0 hR0 hd0
    exact hpost
  | wrong m =>
    obtain ⟨_, _, _, _, _, hpost⟩ := key w0 ld0 lr0 d0 s0 hargs0 hR0 hd0
    exact hpost

set_option maxHeartbeats 0 in
theorem writeHeadersM_ok : ContractOK Gen.prog writeHeadersSig writeHeadersSpecM := by
  jcontract_ok [writeHeadersM_sat]

end EquivLean.Modernize.Cbtrn03c.Java

#print axioms EquivLean.Modernize.Cbtrn03c.Java.writeHeadersM_ok
