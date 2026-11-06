import EquivLean.Modernize.Cbtrn02c.Any.JavaRunO

/-!
# CBTRN02C → Java: the transaction record object `postTransaction` fills

`tranws_rec`: `tranWs` with fields 0–11 copied from the daily transaction object (holding `t`),
the processing timestamp of the clock and the `FILLER` of spaces holds `Model.tranVals t clk`.
-/

open Jimple EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbtrn02c.Java

set_option maxRecDepth 8000 in
theorem tranws_rec {σ : State} {w d : Addr} {fsT fsd : List (FieldKey × Value)} {t : List EquivLean.Cobol.Rec.FVal}
    {clk : List UInt8} {x : Addr} {sv : Value}
    (hd : JRecAt DalytranRecord "Cbtrn02c$DalytranRecord" σ (.ref d) t) (hdv : DalytranRecord.Valid t)
    (hdo : σ.heap d = some (.plain "Cbtrn02c$DalytranRecord" fsd))
    (hw : σ.heap w = some (.plain "Cbtrn02c$TranRecord" fsT))
    (e0 : Fields.get fsT ("Cbtrn02c$TranRecord", "tranId") = Fields.get fsd ("Cbtrn02c$DalytranRecord", "dalytranId"))
    (e1 : Fields.get fsT ("Cbtrn02c$TranRecord", "tranTypeCd") = Fields.get fsd ("Cbtrn02c$DalytranRecord", "dalytranTypeCd"))
    (e2 : Fields.get fsT ("Cbtrn02c$TranRecord", "tranCatCd") = Fields.get fsd ("Cbtrn02c$DalytranRecord", "dalytranCatCd"))
    (e3 : Fields.get fsT ("Cbtrn02c$TranRecord", "tranSource") = Fields.get fsd ("Cbtrn02c$DalytranRecord", "dalytranSource"))
    (e4 : Fields.get fsT ("Cbtrn02c$TranRecord", "tranDesc") = Fields.get fsd ("Cbtrn02c$DalytranRecord", "dalytranDesc"))
    (e5 : Fields.get fsT ("Cbtrn02c$TranRecord", "tranAmt") = Fields.get fsd ("Cbtrn02c$DalytranRecord", "dalytranAmt"))
    (e6 : Fields.get fsT ("Cbtrn02c$TranRecord", "tranMerchantId") = Fields.get fsd ("Cbtrn02c$DalytranRecord", "dalytranMerchantId"))
    (e7 : Fields.get fsT ("Cbtrn02c$TranRecord", "tranMerchantName") = Fields.get fsd ("Cbtrn02c$DalytranRecord", "dalytranMerchantName"))
    (e8 : Fields.get fsT ("Cbtrn02c$TranRecord", "tranMerchantCity") = Fields.get fsd ("Cbtrn02c$DalytranRecord", "dalytranMerchantCity"))
    (e9 : Fields.get fsT ("Cbtrn02c$TranRecord", "tranMerchantZip") = Fields.get fsd ("Cbtrn02c$DalytranRecord", "dalytranMerchantZip"))
    (e10 : Fields.get fsT ("Cbtrn02c$TranRecord", "tranCardNum") = Fields.get fsd ("Cbtrn02c$DalytranRecord", "dalytranCardNum"))
    (e11 : Fields.get fsT ("Cbtrn02c$TranRecord", "tranOrigTs") = Fields.get fsd ("Cbtrn02c$DalytranRecord", "dalytranOrigTs"))
    (hp : Fields.get fsT ("Cbtrn02c$TranRecord", "tranProcTs") = some (.ref x))
    (hx : σ.heap x = some (.str (cp037Str (CardDemo.Cbtrn02c.db2ts clk))))
    (hf : Fields.get fsT ("Cbtrn02c$TranRecord", "filler1") = some sv)
    (hsv : JStrAt σ sv (cp037Str (Model.sp 20))) :
    JRecAt TranRecord "Cbtrn02c$TranRecord" σ (.ref w) (Model.tranVals t clk) := by
  obtain ⟨⟨a, fs, s0, s1, s3, s4, s7, s8, s9, s10, s11, s12, s13, hae, hao, g0, t0, g1, t1, g2, g3, t3,
    g4, t4, g5, g6, g7, t7, g8, t8, g9, t9, g10, t10, g11, t11, g12, t12, g13, t13⟩, b0, b1, n2, b3, b4,
    n5, n6, b7, b8, b9, b10, b11, b12, b13, rfl, -, -, -⟩ := dalobj_of_rec hd hdv
  cases hae
  rw [hdo] at hao; cases hao
  simp only [bAt, nAt, Model.strOf, Model.numOf, List.getD_cons_zero, List.getD_cons_succ] at *
  refine ⟨w, fsT, rfl, hw, ?_⟩
  simp only [Model.tranVals, List.take_succ_cons, List.take_zero, List.cons_append, List.nil_append]
  refine .cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_
    (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ .nil)))))))))))))
  · exact ⟨_, by rw [e0, g0], _, rfl, t0⟩
  · exact ⟨_, by rw [e1, g1], _, rfl, t1⟩
  · show Fields.get fsT _ = _
    rw [e2, g2]
  · exact ⟨_, by rw [e3, g3], _, rfl, t3⟩
  · exact ⟨_, by rw [e4, g4], _, rfl, t4⟩
  · show Fields.get fsT _ = _
    rw [e5, g5]
  · show Fields.get fsT _ = _
    rw [e6, g6]
  · exact ⟨_, by rw [e7, g7], _, rfl, t7⟩
  · exact ⟨_, by rw [e8, g8], _, rfl, t8⟩
  · exact ⟨_, by rw [e9, g9], _, rfl, t9⟩
  · exact ⟨_, by rw [e10, g10], _, rfl, t10⟩
  · exact ⟨_, by rw [e11, g11], _, rfl, t11⟩
  · exact ⟨_, hp, x, rfl, hx⟩
  · exact ⟨_, hf, hsv⟩

end EquivLean.Modernize.Cbtrn02c.Java
