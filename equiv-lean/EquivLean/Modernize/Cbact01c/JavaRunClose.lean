import EquivLean.Modernize.Cbact01c.JavaRunStep

/-!
# CBACT01C → Java: `run`, the loop invariant after a record

`read_close`: the facts the symbolic execution of one record leaves (the strings and records the
callees wrote, read in the state back at the loop head) give the loop invariant's `RunData` for
one record more.
-/

open Jimple EquivLean EquivLean.Jimple EquivLean.Jimple.Spec EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbact01c.Java

/-- The fifteen lines of a record, as the strings the record methods write. -/
theorem lines_glue {σ0 : Jimple.State} {c : Addr} {v : List EquivLean.Cobol.Rec.FVal}
    (hA : AcctAt σ0 c v) :
    (Model.lines v).map jline = [dispLine σ0 c 0, dispLine σ0 c 1, dispLine σ0 c 2,
      dispLine σ0 c 3, dispLine σ0 c 4, dispLine σ0 c 5, dispLine σ0 c 6, dispLine σ0 c 7,
      dispLine σ0 c 8, dispLine σ0 c 9, dispLine σ0 c 10, dispLine σ0 c 11,
      JStr.ofString "VBRC-REC1:" ++ vb1J σ0 c, JStr.ofString "VBRC-REC2:" ++ vb2J σ0 c,
      acctTextJ σ0 c] := by
  rw [dispLine_glue hA 0 (by decide), dispLine_glue hA 1 (by decide),
    dispLine_glue hA 2 (by decide), dispLine_glue hA 3 (by decide),
    dispLine_glue hA 4 (by decide), dispLine_glue hA 5 (by decide),
    dispLine_glue hA 6 (by decide), dispLine_glue hA 7 (by decide),
    dispLine_glue hA 8 (by decide), dispLine_glue hA 9 (by decide),
    dispLine_glue hA 10 (by decide), dispLine_glue hA 11 (by decide), vb1_glue hA, vb2_glue hA,
    acctText_glue hA, ← jline_txt "VBRC-REC1:" (by decide), ← jline_txt "VBRC-REC2:" (by decide),
    ← jline_append, ← jline_append]
  simp only [Model.lines, List.map_cons, List.map_nil, List.getD_cons_zero, List.getD_cons_succ]

/-- One record read, from the strings and records the callees wrote (`σF`: back at the loop
head; `cd'`: the cycle debit after the record, `252500` when the record's is zero). -/
theorem read_close {σ0 σ σF : Jimple.State} {vals : List (List EquivLean.Cobol.Rec.FVal)}
    {i : I32} {cd cd' dbt : I64} {s s7 : JStr} {ys1 ys2 ys3 ys4 : List Value} {c x7 : Addr}
    {fsc : List (FieldKey × Value)} {v : List EquivLean.Cobol.Rec.FVal}
    {w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 y1 y2 t o2 o3 u1 u2 : Addr}
    (hD : Hide (RunData σ0 vals σ i.toNat cd s ys1 ys2 ys3 ys4))
    (hv : Hide (vals[i.toNat]? = some v)) (hA : Hide (AcctAt σ0 c v))
    (hc : σ0.heap c = some (.plain acctCls fsc))
    (hf7 : Fields.get fsc (acctCls, "acctReissueDate") = some (.ref x7))
    (hx7 : σ0.heap x7 = some (.str s7))
    (hf9 : Fields.get fsc (acctCls, "acctCurrCycDebit") = some (.long dbt))
    (hi0 : 0 ≤ i.toInt)
    (hcd : cd' = if dbt = 0#64 then 252500#64 else cd)
    (hG : GrowsAbove (σ0.next + 4) σ σF)
    (h1 : σF.heap w1 = some (.str (dispLine σ0 c 0)))
    (h2 : σF.heap w2 = some (.str (dispLine σ0 c 1)))
    (h3 : σF.heap w3 = some (.str (dispLine σ0 c 2)))
    (h4 : σF.heap w4 = some (.str (dispLine σ0 c 3)))
    (h5 : σF.heap w5 = some (.str (dispLine σ0 c 4)))
    (h6 : σF.heap w6 = some (.str (dispLine σ0 c 5)))
    (h7 : σF.heap w7 = some (.str (dispLine σ0 c 6)))
    (h8 : σF.heap w8 = some (.str (dispLine σ0 c 7)))
    (h9 : σF.heap w9 = some (.str (dispLine σ0 c 8)))
    (h10 : σF.heap w10 = some (.str (dispLine σ0 c 9)))
    (h11 : σF.heap w11 = some (.str (dispLine σ0 c 10)))
    (h12 : σF.heap w12 = some (.str (dispLine σ0 c 11)))
    (hy1 : σF.heap y1 = some (.str (JStr.ofString "VBRC-REC1:" ++ vb1J σ0 c)))
    (hy2 : σF.heap y2 = some (.str (JStr.ofString "VBRC-REC2:" ++ vb2J σ0 c)))
    (ht : σF.heap t = some (.str (acctTextJ σ0 c)))
    (hR2 : OutRecJ σF o2 σ0 c (cobOut (fixStr s7 20) s) cd' (σ0.next + 5))
    (hR3 : ArrRecJ σF o3 σ0 c (σ0.next + 5))
    (hu1 : σF.heap u1 = some (.str (vb1J σ0 c)))
    (hu2 : σF.heap u2 = some (.str (vb2J σ0 c)))
    (hb1 : σ0.next + 4 < w1) (hb2 : σ0.next + 4 < w2) (hb3 : σ0.next + 4 < w3)
    (hb4 : σ0.next + 4 < w4) (hb5 : σ0.next + 4 < w5) (hb6 : σ0.next + 4 < w6)
    (hb7 : σ0.next + 4 < w7) (hb8 : σ0.next + 4 < w8) (hb9 : σ0.next + 4 < w9)
    (hb10 : σ0.next + 4 < w10) (hb11 : σ0.next + 4 < w11) (hb12 : σ0.next + 4 < w12)
    (hby1 : σ0.next + 4 < y1) (hby2 : σ0.next + 4 < y2) (hbt : σ0.next + 4 < t)
    (hbo2 : σ0.next + 4 < o2) (hbo3 : σ0.next + 4 < o3) (hbu1 : σ0.next + 4 < u1)
    (hbu2 : σ0.next + 4 < u2) :
    Hide (RunData σ0 vals σF ((BitVec.toInt i).toNat + 1) cd' (cobOut (fixStr s7 20) s)
      (ys1 ++ [.ref w1, .ref w2, .ref w3, .ref w4, .ref w5, .ref w6, .ref w7, .ref w8, .ref w9,
        .ref w10, .ref w11, .ref w12, .ref y1, .ref y2, .ref t]) (ys2 ++ [.ref o2])
      (ys3 ++ [.ref o3]) (ys4 ++ [.ref u1, .ref u2])) := by
  have hD' := Hide.elim hD
  have hv' := Hide.elim hv
  have hA' := Hide.elim hA
  have hik : i.toNat = (BitVec.toInt i).toNat :=
    toNat_of_toInt_eq (Int.toNat_of_nonneg hi0).symm
  rw [← hik]
  obtain ⟨hdbt, hdbtB⟩ := cycDebit_of hA' hc hf9
  obtain ⟨hcd0, hs1, hs2, -⟩ := hD'
  have hcdm : cd' = BitVec.ofInt 64
      (if Model.aCycDebit v = 0 then 252500 else (mst vals i.toNat).cd) := by
    rw [hcd]
    by_cases h0 : Model.aCycDebit v = 0
    · rw [if_pos (by rw [hdbt, h0]; rfl), if_pos h0]; rfl
    · rw [if_neg (fun h => h0 ((ofInt64_eq_zero hdbtB).1 (hdbt ▸ h))), if_neg h0, hcd0]
  obtain ⟨hl1, hl2⟩ := cobOut_date (i := fixStr s7 20) (by rw [fixStr_length]; decide) hs1 hs2
  obtain ⟨n0, n2, n3, n4, n8, n9, b1, b5, b6, b7, b10, b11, b12, hvv, -, -, -, -, -, -, -, -, -, -, e7, -, -,
    -, -, -, -, -, -, -, -, -, -, hl7, -, -, -⟩ := acctAt_flat hA'
  have hs7 : s7 = cp037Str b7 := by rw [← e7, sfJ_of hc hf7 hx7]
  have hdt : fixStr (cobOut (fixStr s7 20) s) 10 =
      cp037Str (Model.reissueOut (Model.aReissue v)) := by
    have hs : s = s.take 8 ++ fixStr [] 12 := by rw [← hs2, List.take_append_drop]
    rw [hs7, hs, reissue_glue hl7 (by simp [hs1]), hvv]
    rfl
  rw [hcdm] at hR2
  have hnb : σ0.next + 4 < σ0.next + 5 := by jomega
  refine Hide.intro (runData_step (Hide.elim hD) hv' hG hcdm hl1 hl2 ?_
    (outRec_glue hA' hR2 hnb hbo2 hdt) (arrRec_glue hA' hR3 hnb hbo3) ?_)
  · rw [lines_glue hA']
    exact .cons ⟨w1, rfl, hb1, h1⟩ (.cons ⟨w2, rfl, hb2, h2⟩ (.cons ⟨w3, rfl, hb3, h3⟩
      (.cons ⟨w4, rfl, hb4, h4⟩ (.cons ⟨w5, rfl, hb5, h5⟩ (.cons ⟨w6, rfl, hb6, h6⟩
      (.cons ⟨w7, rfl, hb7, h7⟩ (.cons ⟨w8, rfl, hb8, h8⟩ (.cons ⟨w9, rfl, hb9, h9⟩
      (.cons ⟨w10, rfl, hb10, h10⟩ (.cons ⟨w11, rfl, hb11, h11⟩ (.cons ⟨w12, rfl, hb12, h12⟩
      (.cons ⟨y1, rfl, hby1, hy1⟩ (.cons ⟨y2, rfl, hby2, hy2⟩ (.cons ⟨t, rfl, hbt, ht⟩
      .nil))))))))))))))
  · exact .cons ⟨u1, rfl, hbu1, by rw [hu1, vb1_glue hA']⟩
      (.cons ⟨u2, rfl, hbu2, by rw [hu2, vb2_glue hA']⟩ .nil)

/-! The records of `writeOutRecord` and `writeArrayRecord` from their parts: the field facts
first (they fix the field list and the field objects by `assumption`). -/

theorem outRecJ_of_parts {σ' σ : Jimple.State} {o c nb : Addr} {dt : JStr} {cd : I64}
    {fs : List (FieldKey × Value)} {x1 x5 x6 x7 x10 : Addr}
    (g0 : Fields.get fs (outCls, "outAcctId") = some (.long (fieldLong σ c "acctId")))
    (g1 : Fields.get fs (outCls, "outAcctActiveStatus") = some (.ref x1))
    (g2 : Fields.get fs (outCls, "outAcctCurrBal") = some (.long (fieldLong σ c "acctCurrBal")))
    (g3 : Fields.get fs (outCls, "outAcctCreditLimit") =
      some (.long (fieldLong σ c "acctCreditLimit")))
    (g4 : Fields.get fs (outCls, "outAcctCashCreditLimit") =
      some (.long (fieldLong σ c "acctCashCreditLimit")))
    (g5 : Fields.get fs (outCls, "outAcctOpenDate") = some (.ref x5))
    (g6 : Fields.get fs (outCls, "outAcctExpiraionDate") = some (.ref x6))
    (g7 : Fields.get fs (outCls, "outAcctReissueDate") = some (.ref x7))
    (g8 : Fields.get fs (outCls, "outAcctCurrCycCredit") =
      some (.long (fieldLong σ c "acctCurrCycCredit")))
    (g9 : Fields.get fs (outCls, "outAcctCurrCycDebit") = some (.long cd))
    (g10 : Fields.get fs (outCls, "outAcctGroupId") = some (.ref x10))
    (hfs : σ'.heap o = some (.plain outCls fs))
    (hb1 : nb ≤ x1) (hx1 : σ'.heap x1 = some (.str (fixStr (sfJ σ c "acctActiveStatus") 1)))
    (hb5 : nb ≤ x5) (hx5 : σ'.heap x5 = some (.str (fixStr (sfJ σ c "acctOpenDate") 10)))
    (hb6 : nb ≤ x6) (hx6 : σ'.heap x6 = some (.str (fixStr (sfJ σ c "acctExpiraionDate") 10)))
    (hb7 : nb ≤ x7) (hx7 : σ'.heap x7 = some (.str (fixStr dt 10)))
    (hb10 : nb ≤ x10) (hx10 : σ'.heap x10 = some (.str (fixStr (sfJ σ c "acctGroupId") 10))) :
    OutRecJ σ' o σ c dt cd nb :=
  ⟨fs, hfs, g0, ⟨x1, g1, hb1, hx1⟩, g2, g3, g4, ⟨x5, g5, hb5, hx5⟩, ⟨x6, g6, hb6, hx6⟩,
    ⟨x7, g7, hb7, hx7⟩, g8, g9, ⟨x10, g10, hb10, hx10⟩⟩

theorem arrRecJ_of_parts {σ' σ : Jimple.State} {o c nb : Addr}
    {fs : List (FieldKey × Value)} {b1 b2 x : Addr} {et1 et2 : JType}
    (g0 : Fields.get fs (arrCls, "arrAcctId") = some (.long (fieldLong σ c "acctId")))
    (g1 : Fields.get fs (arrCls, "arrAcctCurrBal") = some (.ref b1))
    (g2 : Fields.get fs (arrCls, "arrAcctCurrCycDebit") = some (.ref b2))
    (g3 : Fields.get fs (arrCls, "arrFiller") = some (.ref x))
    (hfs : σ'.heap o = some (.plain arrCls fs))
    (hb1 : nb ≤ b1) (ha1 : σ'.heap b1 = some (.array et1 (balArr (fieldLong σ c "acctCurrBal"))))
    (hb2 : nb ≤ b2) (ha2 : σ'.heap b2 = some (.array et2 debArr))
    (hbx : nb ≤ x) (hx : σ'.heap x = some (.str (fixStr [] 4))) :
    ArrRecJ σ' o σ c nb :=
  ⟨fs, hfs, g0, ⟨b1, et1, g1, hb1, ha1⟩, ⟨b2, et2, g2, hb2, ha2⟩, ⟨x, g3, hbx, hx⟩⟩

/-! The cycle debit after a record, in the three cases of the comparison with zero. -/

theorem cd_neg {dbt cd : I64} (h : dbt.toInt < 0) : cd = if dbt = 0#64 then 252500#64 else cd := by
  rw [if_neg]
  rintro rfl
  simp at h

theorem cd_zero {dbt cd : I64} (h : dbt = 0#64) :
    252500#64 = if dbt = 0#64 then 252500#64 else cd := by
  rw [if_pos h]

theorem cd_pos {dbt cd : I64} (h : ¬dbt = 0#64) : cd = if dbt = 0#64 then 252500#64 else cd := by
  rw [if_neg h]

end EquivLean.Modernize.Cbact01c.Java
