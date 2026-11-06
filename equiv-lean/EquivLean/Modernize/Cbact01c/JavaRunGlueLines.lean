import EquivLean.Modernize.Cbact01c.JavaRunGlueRec

/-!
# CBACT01C → Java: the helpers' texts of a record are the model's texts

For a record object holding valid values `v`: the lines `displayAcctRecord` adds, the text of
`accountRecordText` and the two variable-length records are those of `Model` (`jline`).
-/

open Jimple EquivLean EquivLean.Jimple EquivLean.Jimple.Spec EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbact01c.Java

theorem jline_cp037 (bs : List UInt8) : jline (bs.map cp037Code) = cp037Str bs := by
  simp [jline, cp037Str, cp037Unit, cp037Code, List.map_map, Function.comp_def]

theorem cp037Str_length (bs : List UInt8) : (cp037Str bs).length = bs.length := by
  simp [cp037Str]

/-- A text field of the field's length, padded: itself. -/
theorem fixStr_cp037 {bs : List UInt8} {n : Nat} (h : bs.length = n) :
    fixStr (cp037Str bs) n = jline (bs.map cp037Code) := by
  rw [fixStr_eq_self (by rw [cp037Str_length, h]), jline_cp037]

theorem zonedJ_ofInt_u {n : Int} {d : Nat} (k : Nat) (h : n.natAbs < 10 ^ d) (hd : d ≤ 18) :
    zonedJ (BitVec.ofInt 64 n).toInt k false = jline (zpad k n.natAbs) := by
  have : 10 ^ d ≤ 10 ^ 18 := Nat.pow_le_pow_right (by decide) hd
  rw [toInt_ofInt64 (by omega), zonedJ_unsigned]

theorem zonedJ_ofInt_s {n : Int} {d : Nat} (k : Nat) (h : n.natAbs < 10 ^ d) (hd : d ≤ 18)
    (hk : 1 ≤ k) :
    zonedJ (BitVec.ofInt 64 n).toInt k true =
      jline (zpad (k - 1) (n.natAbs / 10) ++ [overpunch (decide (n < 0)) (n.natAbs % 10)]) := by
  have : 10 ^ d ≤ 10 ^ 18 := Nat.pow_le_pow_right (by decide) hd
  rw [toInt_ofInt64 (by omega), zonedJ_signed _ _ hk]

/-- The text of `accountRecordText`: the record's text. -/
theorem acctText_glue {σ : Jimple.State} {c : Addr} {v : List EquivLean.Cobol.Rec.FVal}
    (h : AcctAt σ c v) : acctTextJ σ c = jline (Model.AccountRecord.textS v) := by
  obtain ⟨n0, n2, n3, n4, n8, n9, b1, b5, b6, b7, b10, b11, b12, rfl, -, e0, e2, e3, e4, e8, e9,
    s1, s5, s6, s7, s10, s11, s12, h0, h2, h3, h4, h8, h9, hl1, hl5, hl6, hl7, hl10, hl11,
    hl12⟩ := acctAt_flat h
  simp only [acctTextJ, zfJ, e0, e2, e3, e4, e8, e9, s1, s5, s6, s7, s10, s11, s12]
  simp only [Schema.textS, List.zip, List.zipWith, List.map, List.flatten,
    fieldTextS, ↓reduceIte, Bool.false_eq_true]
  rw [zonedJ_ofInt_u 11 h0 (by decide), zonedJ_ofInt_s 12 h2 (by decide) (by decide),
    zonedJ_ofInt_s 12 h3 (by decide) (by decide), zonedJ_ofInt_s 12 h4 (by decide) (by decide),
    zonedJ_ofInt_s 12 h8 (by decide) (by decide), zonedJ_ofInt_s 12 h9 (by decide) (by decide),
    fixStr_cp037 hl1, fixStr_cp037 hl5, fixStr_cp037 hl6, fixStr_cp037 hl7, fixStr_cp037 hl10,
    fixStr_cp037 hl11, fixStr_cp037 hl12]
  simp only [jline_append, List.append_assoc, List.append_nil, List.append_eq]

/-- A string literal of the BMP (every literal of CBACT01C) as a line. -/
theorem jline_txt (s : String) (h : s.toList.all (fun ch => decide (ch.toNat < 0x10000)) = true) :
    jline (Model.txt s) = JStr.ofString s := by
  unfold Model.txt jline JStr.ofString
  generalize s.toList = l at h ⊢
  induction l with
  | nil => rfl
  | cons ch t ih =>
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [List.map_cons, List.flatMap_cons, JStr.ofChar, if_pos h.1]
    rw [← ih h.2]; simp

/-- The lines `displayAcctRecord` adds: the first twelve lines of the record's in `Model`. -/
theorem dispLines_glue {σ : Jimple.State} {c : Addr} {v : List EquivLean.Cobol.Rec.FVal}
    (h : AcctAt σ c v) : dispLinesJ σ c = ((Model.lines v).take 12).map jline := by
  obtain ⟨n0, n2, n3, n4, n8, n9, b1, b5, b6, b7, b10, b11, b12, rfl, -, e0, e2, e3, e4, e8, e9,
    s1, s5, s6, s7, s10, s11, s12, h0, h2, h3, h4, h8, h9, -⟩ := acctAt_flat h
  simp only [dispLinesJ, zfJ, e0, e2, e3, e4, e8, e9, s1, s5, s6, s7, s10, s11, s12]
  simp only [Model.lines, Model.fld, List.take, List.map, List.getD_cons_zero, List.getD_cons_succ,
    Schema.fields, fieldTextS, ↓reduceIte, Bool.false_eq_true]
  rw [zonedJ_ofInt_u 11 h0 (by decide), zonedJ_ofInt_s 12 h2 (by decide) (by decide),
    zonedJ_ofInt_s 12 h3 (by decide) (by decide), zonedJ_ofInt_s 12 h4 (by decide) (by decide),
    zonedJ_ofInt_s 12 h8 (by decide) (by decide), zonedJ_ofInt_s 12 h9 (by decide) (by decide)]
  simp (disch := decide) only [jline_append, jline_cp037, jline_txt]

/-- VBRC-REC1 of the record. -/
theorem vb1_glue {σ : Jimple.State} {c : Addr} {v : List EquivLean.Cobol.Rec.FVal}
    (h : AcctAt σ c v) : vb1J σ c = jline (Model.VbrcRec1.textS (Model.vb1 v)) := by
  obtain ⟨n0, n2, n3, n4, n8, n9, b1, b5, b6, b7, b10, b11, b12, rfl, -, e0, e2, e3, e4, e8, e9,
    s1, s5, s6, s7, s10, s11, s12, h0, h2, h3, h4, h8, h9, hl1, hl5, hl6, hl7, -⟩ := acctAt_flat h
  simp only [vb1J, zfJ, e0, s1]
  simp only [Model.vb1, Model.aId, Model.aStatus, Model.numOf, Model.strOf, List.getD_cons_zero,
    List.getD_cons_succ, Schema.textS, List.zip, List.zipWith, List.map, List.flatten, fieldTextS,
    ↓reduceIte, Bool.false_eq_true]
  rw [zonedJ_ofInt_u 11 h0 (by decide), fixStr_cp037 hl1]
  simp [jline, List.append_eq, List.map_append]

/-- VBRC-REC2 of the record. -/
theorem vb2_glue {σ : Jimple.State} {c : Addr} {v : List EquivLean.Cobol.Rec.FVal}
    (h : AcctAt σ c v) : vb2J σ c = jline (Model.VbrcRec2.textS (Model.vb2 v)) := by
  obtain ⟨n0, n2, n3, n4, n8, n9, b1, b5, b6, b7, b10, b11, b12, rfl, -, e0, e2, e3, e4, e8, e9,
    s1, s5, s6, s7, s10, s11, s12, h0, h2, h3, h4, h8, h9, hl1, hl5, hl6, hl7, -⟩ := acctAt_flat h
  simp only [vb2J, zfJ, e0, e2, e3, s7]
  simp only [Model.vb2, Model.aId, Model.aBal, Model.aLimit, Model.aReissue, Model.numOf,
    Model.strOf, List.getD_cons_zero, List.getD_cons_succ, Schema.textS, List.zip, List.zipWith,
    List.map, List.flatten, fieldTextS, ↓reduceIte, Bool.false_eq_true]
  rw [zonedJ_ofInt_u 11 h0 (by decide), zonedJ_ofInt_s 12 h2 (by decide) (by decide),
    zonedJ_ofInt_s 12 h3 (by decide) (by decide), fixStr_cp037 hl7]
  simp [jline, List.append_eq, List.map_append, List.map_take]

end EquivLean.Modernize.Cbact01c.Java
