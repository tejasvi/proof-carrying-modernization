import EquivLean.Modernize.Cbtrn01c.JavaRunDefs

/-!
# CBTRN01C → Java: the record objects of the inputs

A transaction record object with valid field values is a record `formatDalytran` reads
(`DalOk`), its line is the model's record text (`dalLine_eq`), and it is a record area for the
lookups (`CurAt`).
-/

open Jimple EquivLean.Cobol.Rec EquivLean.Jimple

namespace EquivLean.Modernize.Cbtrn01c.Java

theorem jline_txt_append (s : String) (l : List Nat) :
    jline (Model.txt s ++ l) = jline (Model.txt s) ++ jline l := jline_append _ _

theorem szJ_of (n : Int) (h : n.natAbs < 10 ^ 18) :
    jline (zpad 10 (n.natAbs / 10) ++ [overpunch (decide (n < 0)) (n.natAbs % 10)]) =
      szJ (BitVec.ofInt 64 n) 11 := by
  rw [szJ, toInt_ofInt_of_natAbs h, jline_append, jline_zpad]
  rfl

theorem minval_lt {n : Int} (h : n.natAbs < 10 ^ 18) :
    -9223372036854775808 < (BitVec.ofInt 64 n).toInt := by
  rw [toInt_ofInt_of_natAbs h]; omega

set_option maxRecDepth 4000 in
/-- **A transaction record object**: `formatDalytran` reads it and builds the model's record text;
its card number and id are those of the field values. -/
theorem dal_of_rec {σ : State} {v : Value} {t : List EquivLean.Cobol.Rec.FVal}
    (hr : JRecAt DalytranRecord dalCls σ v t) (hv : DalytranRecord.Valid t) :
    ∃ c, v = .ref c ∧ DalOk σ c ∧ dalLine σ c = jline (Model.DalytranRecord.textS t) ∧
      CurAt σ v t := by
  obtain ⟨x, fs, rfl, hx, hf⟩ := hr
  have hl : t.length = 14 := hv.length_eq.symm
  match t, hl, hv, hf with
  | [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13], _,
    .cons h0 (.cons h1 (.cons h2 (.cons h3 (.cons h4 (.cons h5 (.cons h6 (.cons h7 (.cons h8
      (.cons h9 (.cons h10 (.cons h11 (.cons h12 (.cons h13 .nil))))))))))))),
    .cons j0 (.cons j1 (.cons j2 (.cons j3 (.cons j4 (.cons j5 (.cons j6 (.cons j7 (.cons j8
      (.cons j9 (.cons j10 (.cons j11 (.cons j12 (.cons j13 .nil))))))))))))) =>
    obtain ⟨b0, y0, rfl, g0, s0⟩ := str_field rfl h0 j0
    obtain ⟨b1, y1, rfl, g1, s1⟩ := str_field rfl h1 j1
    obtain ⟨n2, rfl, g2, hh2, -, hd2⟩ := num_field rfl h2 j2
    obtain ⟨b3, y3, rfl, g3, s3⟩ := str_field rfl h3 j3
    obtain ⟨b4, y4, rfl, g4, s4⟩ := str_field rfl h4 j4
    obtain ⟨n5, rfl, g5, hh5, -, hd5⟩ := num_field rfl h5 j5
    obtain ⟨n6, rfl, g6, hh6, -, hd6⟩ := num_field rfl h6 j6
    obtain ⟨b7, y7, rfl, g7, s7⟩ := str_field rfl h7 j7
    obtain ⟨b8, y8, rfl, g8, s8⟩ := str_field rfl h8 j8
    obtain ⟨b9, y9, rfl, g9, s9⟩ := str_field rfl h9 j9
    obtain ⟨b10, y10, rfl, g10, s10⟩ := str_field rfl h10 j10
    obtain ⟨b11, y11, rfl, g11, s11⟩ := str_field rfl h11 j11
    obtain ⟨b12, y12, rfl, g12, s12⟩ := str_field rfl h12 j12
    obtain ⟨b13, y13, rfl, g13, s13⟩ := str_field rfl h13 j13
    have a2 := natAbs_lt_of_holds rfl hh2 hd2
    have a5 := natAbs_lt_of_holds rfl hh5 hd5
    have a6 := natAbs_lt_of_holds rfl hh6 hd6
    dsimp only at g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13
    refine ⟨x, rfl, ⟨fs, hx, ⟨y0, _, g0, s0⟩, ⟨y1, _, g1, s1⟩, ⟨_, g2, minval_lt a2⟩,
      ⟨y3, _, g3, s3⟩, ⟨y4, _, g4, s4⟩, ⟨_, g5, minval_lt a5⟩, ⟨_, g6, minval_lt a6⟩,
      ⟨y7, _, g7, s7⟩, ⟨y8, _, g8, s8⟩, ⟨y9, _, g9, s9⟩, ⟨y10, _, g10, s10⟩, ⟨y11, _, g11, s11⟩,
      ⟨y12, _, g12, s12⟩, ⟨y13, _, g13, s13⟩⟩, ?_,
      ⟨x, fs, y10, y0, rfl, hx, g10, by simpa [Model.strOf] using s10, g0,
        by simpa [Model.strOf] using s0⟩⟩
    have e2 : (BitVec.ofInt 64 n2).toInt = n2 := toInt_ofInt_of_natAbs a2
    have e6 : (BitVec.ofInt 64 n6).toInt = n6 := toInt_ofInt_of_natAbs a6
    simp only [dalLine, fieldOf, fieldLong, argText, hx, g0, g1, g2, g3, g4, g5, g6, g7,
      g8, g9, g10, g11, g12, g13, Option.getD_some, strOf, s0, s1, s3, s4, s7, s8, s9, s10, s11,
      s12, s13, e2, e6]
    simp only [Schema.textS, List.zip_cons_cons, List.zip_nil_right,
      List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, fieldTextS,
      List.append_nil, jline_append, jline_cp037, jline_zpad, Bool.false_eq_true, ↓reduceIte,
      Nat.add_one_sub_one, List.append_assoc]
    rw [← szJ_of n5 a5]
    simp only [jline_append, List.append_assoc]
    rfl

def xrefCls : ClassName := "Cbtrn01c$CardXrefRecord"
def acctCls : ClassName := "Cbtrn01c$AccountRecord"

theorem natAbs_lt_of_holds' {fmt : Cobol.NumFmt} {n : Int} {d : Nat} (hu : fmt.usage = .display)
    (hh : fmt.Holds {} n) (hd : fmt.digits = d) : n.natAbs < 10 ^ d := by
  unfold Cobol.NumFmt.Holds at hh
  have hb : fmt.fullBinary {} = false := by
    unfold Cobol.NumFmt.fullBinary; simp [hu]
  rw [hb] at hh
  simp only [Bool.false_eq_true, ↓reduceIte] at hh
  rw [← hd]; exact hh.1

set_option maxRecDepth 4000 in
/-- **A cross-reference record object**: its card number string and its two ids. -/
theorem xref_of_rec {σ : State} {v : Value} {x : List EquivLean.Cobol.Rec.FVal}
    (hr : JRecAt CardXrefRecord xrefCls σ v x) (hv : CardXrefRecord.Valid x) :
    ∃ xr fs xc, v = .ref xr ∧ σ.heap xr = some (.plain xrefCls fs) ∧
      Fields.get fs (xrefCls, "xrefCardNum") = some (.ref xc) ∧
      σ.heap xc = some (.str (cp037Str (Model.strOf (x.getD 0 default)))) ∧
      Fields.get fs (xrefCls, "xrefCustId") =
        some (.long (BitVec.ofInt 64 (Model.numOf (x.getD 1 default)))) ∧
      Fields.get fs (xrefCls, "xrefAcctId") =
        some (.long (BitVec.ofInt 64 (Model.numOf (x.getD 2 default)))) ∧
      (Model.numOf (x.getD 1 default)).natAbs < 10 ^ 9 ∧
      (Model.numOf (x.getD 2 default)).natAbs < 10 ^ 11 := by
  obtain ⟨xr, fs, rfl, hx, hf⟩ := hr
  have hl : x.length = 4 := hv.length_eq.symm
  match x, hl, hv, hf with
  | [v0, v1, v2, v3], _, .cons h0 (.cons h1 (.cons h2 (.cons h3 .nil))),
    .cons j0 (.cons j1 (.cons j2 (.cons j3 .nil))) =>
    obtain ⟨b0, y0, rfl, g0, s0⟩ := str_field rfl h0 j0
    obtain ⟨n1, rfl, g1, hh1, -, -⟩ := num_field rfl h1 j1
    obtain ⟨n2, rfl, g2, hh2, -, -⟩ := num_field rfl h2 j2
    dsimp only at g0 g1 g2
    exact ⟨xr, fs, y0, rfl, hx, g0, by simpa [Model.strOf] using s0, by simpa [Model.numOf] using g1,
      by simpa [Model.numOf] using g2, by simpa [Model.numOf] using natAbs_lt_of_holds' rfl hh1 rfl,
      by simpa [Model.numOf] using natAbs_lt_of_holds' rfl hh2 rfl⟩

set_option maxRecDepth 4000 in
/-- **An account record object**: its account id. -/
theorem acct_of_rec {σ : State} {v : Value} {a : List EquivLean.Cobol.Rec.FVal}
    (hr : JRecAt AccountRecord acctCls σ v a) (hv : AccountRecord.Valid a) :
    ∃ ar fs, v = .ref ar ∧ σ.heap ar = some (.plain acctCls fs) ∧
      Fields.get fs (acctCls, "acctId") =
        some (.long (BitVec.ofInt 64 (Model.numOf (a.getD 0 default)))) ∧
      (Model.numOf (a.getD 0 default)).natAbs < 10 ^ 11 := by
  obtain ⟨ar, fs, rfl, hx, hf⟩ := hr
  cases a with
  | nil => cases hv
  | cons v0 rest =>
    cases hv with
    | cons h0 _ =>
      cases hf with
      | cons j0 _ =>
        obtain ⟨n0, rfl, g0, hh0, -, -⟩ := num_field rfl h0 j0
        dsimp only at g0
        exact ⟨ar, fs, rfl, hx, g0, natAbs_lt_of_holds' rfl hh0 rfl⟩

end EquivLean.Modernize.Cbtrn01c.Java
