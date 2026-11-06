import EquivLean.Modernize.Cbact01c.JavaRunOuts

/-!
# CBACT01C → Java: the records written are the model's

The `OutAcctRec` of `writeOutRecord` holds `Model.outVals` (the reissue date through `cobdatft`
is `Model.reissueOut`), the `ArrArrayRec` of `writeArrayRecord` holds `Model.arrVals` (the
`OCCURS` items in arrays).
-/

open Jimple EquivLean EquivLean.Jimple EquivLean.Jimple.Spec EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbact01c.Java

/-! ## The date of `cobdatft` -/

/-- The eight characters `cobdatft` takes from its input (type 2). -/
def cob8 (i : JStr) : JStr := i.take 4 ++ (i.take 7).drop 5 ++ (i.take 10).drop 8

theorem cob8_length {i : JStr} (h : 10 ≤ i.length) : (cob8 i).length = 8 := by
  simp only [cob8, List.length_append, List.length_take, List.length_drop,
    Nat.min_eq_left (by omega : 4 ≤ i.length), Nat.min_eq_left (by omega : 7 ≤ i.length),
    Nat.min_eq_left (by omega : 10 ≤ i.length)]

/-- The output date after `cobdatft`: eight characters, then the twelve spaces it had. -/
theorem cobOut_spaces {i s8 : JStr} (hs8 : s8.length = 8) :
    cobOut i (s8 ++ fixStr [] 12) = cob8 i ++ fixStr [] 12 := by
  simp [cobOut, cob8, List.drop_append, hs8]

set_option maxRecDepth 20000 in
theorem cp037Unit_space : cp037Unit 64 = space := by decide

theorem cp037Str_sp (n : Nat) : cp037Str (Model.sp n) = fixStr [] n := by
  rw [cp037Str, Model.sp, List.map_replicate, cp037Unit_space, fixStr_nil]

theorem fixStr_of_le {s : JStr} {n : Nat} (h : n ≤ s.length) : fixStr s n = s.take n := by
  rw [fixStr_eq_map]
  apply List.ext_getElem (by simp; omega)
  intro i h1 h2
  simp at h1
  simp [List.getElem_take, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : i < s.length)]

theorem cp037Str_append (a b : List UInt8) : cp037Str (a ++ b) = cp037Str a ++ cp037Str b := by
  simp [cp037Str]

theorem cp037Str_take (a : List UInt8) (n : Nat) : cp037Str (a.take n) = (cp037Str a).take n := by
  simp [cp037Str, List.map_take]

theorem cp037Str_drop (a : List UInt8) (n : Nat) : cp037Str (a.drop n) = (cp037Str a).drop n := by
  simp [cp037Str, List.map_drop]

theorem fixStr_nil_take (n k : Nat) (h : k ≤ n) : (fixStr [] n).take k = fixStr [] k := by
  rw [fixStr_nil, fixStr_nil, List.take_replicate, Nat.min_eq_left h]

/-- A short text padded: itself, then spaces. -/
theorem fixStr_append_spaces {t : JStr} {n : Nat} (h : t.length ≤ n) :
    fixStr t n = t ++ fixStr [] (n - t.length) := by
  rw [fixStr_eq_map, fixStr_eq_map]
  apply List.ext_getElem (by simp; omega)
  intro k h1 h2
  simp only [List.getElem_map, List.getElem_range, List.getD_eq_getElem?_getD]
  by_cases hk : k < t.length
  · rw [List.getElem_append_left (by simpa using hk)]
    simp [List.getElem?_eq_getElem hk]
  · rw [List.getElem_append_right (by omega)]
    simp [List.getElem?_eq_none (by omega : t.length ≤ k)]

/-- The reissue date of the copy: `pad(cobdatft(…), 10)`. -/
theorem reissue_glue {b7 : List UInt8} (hl : b7.length = 10) {s8 : JStr} (hs8 : s8.length = 8) :
    fixStr (cobOut (fixStr (cp037Str b7) 20) (s8 ++ fixStr [] 12)) 10 =
      cp037Str (Model.reissueOut b7) := by
  have hA : (cp037Str b7).length = 10 := by rw [cp037Str_length, hl]
  have hT : fixStr (cp037Str b7) 20 = cp037Str b7 ++ fixStr [] 10 := by
    rw [fixStr_append_spaces (by omega), hA]
  have h8 : cob8 (cp037Str b7 ++ fixStr [] 10) =
      cp037Str (b7.take 4 ++ (b7.drop 5).take 2 ++ (b7.drop 8).take 2) := by
    have e1 : (cp037Str b7 ++ fixStr [] 10).take 4 = cp037Str (b7.take 4) := by
      rw [List.take_append_of_le_length (by rw [hA]; decide), cp037Str_take]
    have e2 : ((cp037Str b7 ++ fixStr [] 10).take 7).drop 5 = cp037Str ((b7.drop 5).take 2) := by
      rw [List.take_append_of_le_length (by rw [hA]; decide), ← cp037Str_take, ← cp037Str_drop,
        List.drop_take]
    have e3 : ((cp037Str b7 ++ fixStr [] 10).take 10).drop 8 = cp037Str ((b7.drop 8).take 2) := by
      rw [List.take_append_of_le_length (by rw [hA]; decide),
        List.take_of_length_le (by rw [hA]; exact Nat.le_refl _), ← cp037Str_drop,
        List.take_of_length_le (i := 2) (by rw [List.length_drop, hl]; decide)]
    rw [cob8, e1, e2, e3, cp037Str_append, cp037Str_append]
  have hl8 : (cob8 (cp037Str b7 ++ fixStr [] 10)).length = 8 := by
    rw [h8, cp037Str_length]
    simp only [List.length_append, List.length_take, List.length_drop, hl]
    decide
  rw [cobOut_spaces hs8, hT, fixStr_of_le (by rw [List.length_append, hl8, fixStr_length]; omega),
    List.take_append, List.take_of_length_le (by rw [hl8]; decide), hl8,
    fixStr_nil_take 12 (10 - 8) (by decide), h8]
  simp only [Model.reissueOut, cp037Str_append, cp037Str_sp, List.append_assoc]

/-! ## The records written -/

/-- The `OutAcctRec` of `writeOutRecord`: the model's copy `outVals v cd`. -/
theorem outRec_glue {σ' σ0 : Jimple.State} {o c B nb : Addr} {v : List EquivLean.Cobol.Rec.FVal}
    {dt : JStr} {cd : Int} (hA : AcctAt σ0 c v)
    (hR : OutRecJ σ' o σ0 c dt (BitVec.ofInt 64 cd) nb) (hB : B < nb) (ho : B < o)
    (hdt : fixStr dt 10 = cp037Str (Model.reissueOut (Model.aReissue v))) :
    JRecB OutAcctRec outCls σ' B (.ref o) (Model.outVals v cd) := by
  obtain ⟨n0, n2, n3, n4, n8, n9, b1, b5, b6, b7, b10, b11, b12, rfl, -, e0, e2, e3, e4, e8, e9,
    s1, s5, s6, s7, s10, s11, s12, h0, h2, h3, h4, h8, h9, hl1, hl5, hl6, hl7, hl10, hl11,
    hl12⟩ := acctAt_flat hA
  obtain ⟨fs, hfs, g0, ⟨x1, g1, hb1, hx1⟩, g2, g3, g4, ⟨x5, g5, hb5, hx5⟩, ⟨x6, g6, hb6, hx6⟩,
    ⟨x7, g7, hb7, hx7⟩, g8, g9, ⟨x10, g10, hb10, hx10⟩⟩ := hR
  rw [e0] at g0; rw [e2] at g2; rw [e3] at g3; rw [e4] at g4; rw [e8] at g8
  rw [s1, fixStr_eq_self (by rw [cp037Str_length, hl1])] at hx1
  rw [s5, fixStr_eq_self (by rw [cp037Str_length, hl5])] at hx5
  rw [s6, fixStr_eq_self (by rw [cp037Str_length, hl6])] at hx6
  rw [s11, fixStr_eq_self (by rw [cp037Str_length, hl11])] at hx10
  rw [hdt] at hx7
  refine ⟨o, fs, rfl, ho, hfs, ?_⟩
  try simp only [Model.outVals, Model.aReissue, Model.strOf, List.getD_cons_zero, List.getD_cons_succ]
  try simp only
  refine .cons g0 (.cons ⟨_, g1, x1, rfl, Nat.lt_of_lt_of_le hB hb1, hx1⟩ (.cons g2 (.cons g3 (.cons g4
    (.cons ⟨_, g5, x5, rfl, Nat.lt_of_lt_of_le hB hb5, hx5⟩ (.cons ⟨_, g6, x6, rfl, Nat.lt_of_lt_of_le hB hb6, hx6⟩
    (.cons ⟨_, g7, x7, rfl, Nat.lt_of_lt_of_le hB hb7, hx7⟩ (.cons g8 (.cons g9
    (.cons ⟨_, g10, x10, rfl, Nat.lt_of_lt_of_le hB hb10, hx10⟩ .nil))))))))))

/-- The `ArrArrayRec` of `writeArrayRecord`: the model's `arrVals v`. -/
theorem arrRec_glue {σ' σ0 : Jimple.State} {o c B nb : Addr} {v : List EquivLean.Cobol.Rec.FVal}
    (hA : AcctAt σ0 c v) (hR : ArrRecJ σ' o σ0 c nb) (hB : B < nb) (ho : B < o) :
    JRecOccB ArrArrayRec arrCls σ' B (.ref o) (Model.arrVals v) := by
  obtain ⟨n0, n2, n3, n4, n8, n9, b1, b5, b6, b7, b10, b11, b12, rfl, -, e0, e2, e3, e4, e8, e9,
    -⟩ := acctAt_flat hA
  obtain ⟨fs, hfs, g0, ⟨a1, et1, g1, hb1, ha1⟩, ⟨a2, et2, g2, hb2, ha2⟩, ⟨x, g3, hbx, hx⟩⟩ := hR
  rw [e0] at g0; rw [e2] at ha1
  rw [← cp037Str_sp] at hx
  refine ⟨o, fs, rfl, ho, hfs, ?_⟩
  try simp only [Model.arrVals, Model.aId, Model.aBal, Model.numOf, List.getD_cons_zero,
    List.getD_cons_succ]
  try simp only
  refine .cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_
    (.cons ?_ (.cons ?_ (.cons ?_ .nil)))))))))))
  all_goals simp only [jFieldOccB, jFieldB]
  all_goals first
    | exact g0
    | exact ⟨_, g3, x, rfl, Nat.lt_of_lt_of_le hB hbx, hx⟩
    | (refine ⟨a1, et1, _, g1, Nat.lt_of_lt_of_le hB hb1, ha1, ?_⟩; simp [jValB, balArr]; done)
    | (refine ⟨a2, et2, _, g2, Nat.lt_of_lt_of_le hB hb2, ha2, ?_⟩; simp [jValB, debArr]; done)
    | skip

end EquivLean.Modernize.Cbact01c.Java
