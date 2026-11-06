import EquivLean.Modernize.Cbtrn02c.Any.JavaRunU
import EquivLean.Modernize.Cbtrn02c.Any.JavaRunB

/-!
# CBTRN02C → Java: record objects with the model's field values

`XObj σ v x`: `v` is a cross-reference object whose fields hold the field values `x` (CP037
strings, `long`s), spelled out field by field so that symbolic execution can read them.  Records of
the statement (`JRecAt` with valid values) are such objects, and the values are determined by the
object.
-/

open Jimple EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbtrn02c.Java

/-- The `i`-th field value as bytes / as an integer. -/
abbrev bAt (x : List EquivLean.Cobol.Rec.FVal) (i : Nat) : List UInt8 := Model.strOf (x.getD i default)
abbrev nAt (x : List EquivLean.Cobol.Rec.FVal) (i : Nat) : Int := Model.numOf (x.getD i default)

/-- A cross-reference object holding `x`. -/
def XObj (σ : State) (v : Value) (x : List EquivLean.Cobol.Rec.FVal) : Prop :=
  ∃ (a : Addr) (fs : List (FieldKey × Value)) (s0 s3 : Addr), v = .ref a ∧
    σ.heap a = some (.plain "Cbtrn02c$CardXrefRecord" fs) ∧
    Fields.get fs ("Cbtrn02c$CardXrefRecord", "xrefCardNum") = some (.ref s0) ∧
    σ.heap s0 = some (.str (cp037Str (bAt x 0))) ∧
    Fields.get fs ("Cbtrn02c$CardXrefRecord", "xrefCustId") = some (.long (BitVec.ofInt 64 (nAt x 1))) ∧
    Fields.get fs ("Cbtrn02c$CardXrefRecord", "xrefAcctId") = some (.long (BitVec.ofInt 64 (nAt x 2))) ∧
    Fields.get fs ("Cbtrn02c$CardXrefRecord", "filler1") = some (.ref s3) ∧
    σ.heap s3 = some (.str (cp037Str (bAt x 3)))

set_option maxRecDepth 4000 in
theorem xobj_of_rec {σ : State} {v : Value} {x : List EquivLean.Cobol.Rec.FVal}
    (hr : JRecAt CardXrefRecord "Cbtrn02c$CardXrefRecord" σ v x) (hv : CardXrefRecord.Valid x) :
    XObj σ v x ∧ ∃ (b0 : List UInt8) (n1 n2 : Int) (b3 : List UInt8),
      x = [.str b0, .num n1, .num n2, .str b3] ∧ n1.natAbs < 10 ^ 18 ∧ n2.natAbs < 10 ^ 18 ∧
      b0.length = 16 := by
  obtain ⟨a, fs, rfl, ha, hf⟩ := hr
  have hl : x.length = 4 := (forall2_length hv).symm
  match x, hl, hv, hf with
  | [v0, v1, v2, v3], _, .cons h0 (.cons h1 (.cons h2 (.cons h3 .nil))),
    .cons j0 (.cons j1 (.cons j2 (.cons j3 .nil))) =>
    obtain ⟨b0, y0, rfl, g0, s0, l0⟩ := str_field rfl h0 j0
    obtain ⟨n1, rfl, g1, hh1, -, hd1⟩ := num_field rfl h1 j1
    obtain ⟨n2, rfl, g2, hh2, -, hd2⟩ := num_field rfl h2 j2
    obtain ⟨b3, y3, rfl, g3, s3, l3⟩ := str_field rfl h3 j3
    exact ⟨⟨a, fs, y0, y3, rfl, ha, g0, s0, g1, g2, g3, s3⟩, b0, n1, n2, b3, rfl,
      natAbs_lt_of_holds rfl hh1 hd1, natAbs_lt_of_holds rfl hh2 hd2, l0⟩

theorem ofInt_inj {u w : Int} (hu : u.natAbs < 10 ^ 18) (hw : w.natAbs < 10 ^ 18)
    (h : BitVec.ofInt 64 u = BitVec.ofInt 64 w) : u = w := by
  have := congrArg BitVec.toInt h
  rwa [toInt_ofInt_of_natAbs hu, toInt_ofInt_of_natAbs hw] at this

/-- A `Cbtrn02c$AccountRecord` object holding `x`. -/
def AObj (σ : State) (v : Value) (x : List EquivLean.Cobol.Rec.FVal) : Prop :=
  ∃ (a : Addr) (fs : List (FieldKey × Value)) (s1 s5 s6 s7 s10 s11 s12 : Addr), v = .ref a ∧
    σ.heap a = some (.plain "Cbtrn02c$AccountRecord" fs) ∧
    Fields.get fs ("Cbtrn02c$AccountRecord", "acctId") = some (.long (BitVec.ofInt 64 (nAt x 0))) ∧
    Fields.get fs ("Cbtrn02c$AccountRecord", "acctActiveStatus") = some (.ref s1) ∧
    σ.heap s1 = some (.str (cp037Str (bAt x 1))) ∧
    Fields.get fs ("Cbtrn02c$AccountRecord", "acctCurrBal") = some (.long (BitVec.ofInt 64 (nAt x 2))) ∧
    Fields.get fs ("Cbtrn02c$AccountRecord", "acctCreditLimit") = some (.long (BitVec.ofInt 64 (nAt x 3))) ∧
    Fields.get fs ("Cbtrn02c$AccountRecord", "acctCashCreditLimit") = some (.long (BitVec.ofInt 64 (nAt x 4))) ∧
    Fields.get fs ("Cbtrn02c$AccountRecord", "acctOpenDate") = some (.ref s5) ∧
    σ.heap s5 = some (.str (cp037Str (bAt x 5))) ∧
    Fields.get fs ("Cbtrn02c$AccountRecord", "acctExpiraionDate") = some (.ref s6) ∧
    σ.heap s6 = some (.str (cp037Str (bAt x 6))) ∧
    Fields.get fs ("Cbtrn02c$AccountRecord", "acctReissueDate") = some (.ref s7) ∧
    σ.heap s7 = some (.str (cp037Str (bAt x 7))) ∧
    Fields.get fs ("Cbtrn02c$AccountRecord", "acctCurrCycCredit") = some (.long (BitVec.ofInt 64 (nAt x 8))) ∧
    Fields.get fs ("Cbtrn02c$AccountRecord", "acctCurrCycDebit") = some (.long (BitVec.ofInt 64 (nAt x 9))) ∧
    Fields.get fs ("Cbtrn02c$AccountRecord", "acctAddrZip") = some (.ref s10) ∧
    σ.heap s10 = some (.str (cp037Str (bAt x 10))) ∧
    Fields.get fs ("Cbtrn02c$AccountRecord", "acctGroupId") = some (.ref s11) ∧
    σ.heap s11 = some (.str (cp037Str (bAt x 11))) ∧
    Fields.get fs ("Cbtrn02c$AccountRecord", "filler1") = some (.ref s12) ∧
    σ.heap s12 = some (.str (cp037Str (bAt x 12)))

set_option maxRecDepth 4000 in
theorem acctobj_of_rec {σ : State} {v : Value} {x : List EquivLean.Cobol.Rec.FVal}
    (hr : JRecAt AccountRecord "Cbtrn02c$AccountRecord" σ v x) (hv : AccountRecord.Valid x) :
    AObj σ v x ∧ ∃ (n0 : Int) (b1 : List UInt8) (n2 : Int) (n3 : Int) (n4 : Int) (b5 : List UInt8) (b6 : List UInt8) (b7 : List UInt8) (n8 : Int) (n9 : Int) (b10 : List UInt8) (b11 : List UInt8) (b12 : List UInt8),
      x = [.num n0, .str b1, .num n2, .num n3, .num n4, .str b5, .str b6, .str b7, .num n8, .num n9, .str b10, .str b11, .str b12] ∧ n0.natAbs < 10 ^ 18 ∧ n2.natAbs < 10 ^ 18 ∧ n3.natAbs < 10 ^ 18 ∧ n4.natAbs < 10 ^ 18 ∧ n8.natAbs < 10 ^ 18 ∧ n9.natAbs < 10 ^ 18 := by
  obtain ⟨a, fs, rfl, ha, hf⟩ := hr
  have hl : x.length = 13 := (forall2_length hv).symm
  match x, hl, hv, hf with
  | [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12], _, .cons h0 (.cons h1 (.cons h2 (.cons h3 (.cons h4 (.cons h5 (.cons h6 (.cons h7 (.cons h8 (.cons h9 (.cons h10 (.cons h11 (.cons h12 (.nil))))))))))))),
    .cons j0 (.cons j1 (.cons j2 (.cons j3 (.cons j4 (.cons j5 (.cons j6 (.cons j7 (.cons j8 (.cons j9 (.cons j10 (.cons j11 (.cons j12 (.nil))))))))))))) =>
    obtain ⟨n0, rfl, g0, hh0, -, hd0⟩ := num_field rfl h0 j0
    obtain ⟨b1, y1, rfl, g1, t1, l1⟩ := str_field rfl h1 j1
    obtain ⟨n2, rfl, g2, hh2, -, hd2⟩ := num_field rfl h2 j2
    obtain ⟨n3, rfl, g3, hh3, -, hd3⟩ := num_field rfl h3 j3
    obtain ⟨n4, rfl, g4, hh4, -, hd4⟩ := num_field rfl h4 j4
    obtain ⟨b5, y5, rfl, g5, t5, l5⟩ := str_field rfl h5 j5
    obtain ⟨b6, y6, rfl, g6, t6, l6⟩ := str_field rfl h6 j6
    obtain ⟨b7, y7, rfl, g7, t7, l7⟩ := str_field rfl h7 j7
    obtain ⟨n8, rfl, g8, hh8, -, hd8⟩ := num_field rfl h8 j8
    obtain ⟨n9, rfl, g9, hh9, -, hd9⟩ := num_field rfl h9 j9
    obtain ⟨b10, y10, rfl, g10, t10, l10⟩ := str_field rfl h10 j10
    obtain ⟨b11, y11, rfl, g11, t11, l11⟩ := str_field rfl h11 j11
    obtain ⟨b12, y12, rfl, g12, t12, l12⟩ := str_field rfl h12 j12
    exact ⟨⟨a, fs, y1, y5, y6, y7, y10, y11, y12, rfl, ha, g0, g1, t1, g2, g3, g4, g5, t5, g6, t6, g7, t7, g8, g9, g10, t10, g11, t11, g12, t12⟩, n0, b1, n2, n3, n4, b5, b6, b7, n8, n9, b10, b11, b12, rfl,
      natAbs_lt_of_holds rfl hh0 hd0, natAbs_lt_of_holds rfl hh2 hd2, natAbs_lt_of_holds rfl hh3 hd3, natAbs_lt_of_holds rfl hh4 hd4, natAbs_lt_of_holds rfl hh8 hd8, natAbs_lt_of_holds rfl hh9 hd9⟩

/-- A `Cbtrn02c$TranCatBalRecord` object holding `x`. -/
def CObj (σ : State) (v : Value) (x : List EquivLean.Cobol.Rec.FVal) : Prop :=
  ∃ (a : Addr) (fs : List (FieldKey × Value)) (s1 s4 : Addr), v = .ref a ∧
    σ.heap a = some (.plain "Cbtrn02c$TranCatBalRecord" fs) ∧
    Fields.get fs ("Cbtrn02c$TranCatBalRecord", "trancatAcctId") = some (.long (BitVec.ofInt 64 (nAt x 0))) ∧
    Fields.get fs ("Cbtrn02c$TranCatBalRecord", "trancatTypeCd") = some (.ref s1) ∧
    σ.heap s1 = some (.str (cp037Str (bAt x 1))) ∧
    Fields.get fs ("Cbtrn02c$TranCatBalRecord", "trancatCd") = some (.long (BitVec.ofInt 64 (nAt x 2))) ∧
    Fields.get fs ("Cbtrn02c$TranCatBalRecord", "tranCatBal") = some (.long (BitVec.ofInt 64 (nAt x 3))) ∧
    Fields.get fs ("Cbtrn02c$TranCatBalRecord", "filler1") = some (.ref s4) ∧
    σ.heap s4 = some (.str (cp037Str (bAt x 4)))

set_option maxRecDepth 4000 in
theorem tcatobj_of_rec {σ : State} {v : Value} {x : List EquivLean.Cobol.Rec.FVal}
    (hr : JRecAt TranCatBalRecord "Cbtrn02c$TranCatBalRecord" σ v x) (hv : TranCatBalRecord.Valid x) :
    CObj σ v x ∧ ∃ (n0 : Int) (b1 : List UInt8) (n2 : Int) (n3 : Int) (b4 : List UInt8),
      x = [.num n0, .str b1, .num n2, .num n3, .str b4] ∧ n0.natAbs < 10 ^ 18 ∧ n2.natAbs < 10 ^ 18 ∧ n3.natAbs < 10 ^ 18 := by
  obtain ⟨a, fs, rfl, ha, hf⟩ := hr
  have hl : x.length = 5 := (forall2_length hv).symm
  match x, hl, hv, hf with
  | [v0, v1, v2, v3, v4], _, .cons h0 (.cons h1 (.cons h2 (.cons h3 (.cons h4 (.nil))))),
    .cons j0 (.cons j1 (.cons j2 (.cons j3 (.cons j4 (.nil))))) =>
    obtain ⟨n0, rfl, g0, hh0, -, hd0⟩ := num_field rfl h0 j0
    obtain ⟨b1, y1, rfl, g1, t1, l1⟩ := str_field rfl h1 j1
    obtain ⟨n2, rfl, g2, hh2, -, hd2⟩ := num_field rfl h2 j2
    obtain ⟨n3, rfl, g3, hh3, -, hd3⟩ := num_field rfl h3 j3
    obtain ⟨b4, y4, rfl, g4, t4, l4⟩ := str_field rfl h4 j4
    exact ⟨⟨a, fs, y1, y4, rfl, ha, g0, g1, t1, g2, g3, g4, t4⟩, n0, b1, n2, n3, b4, rfl,
      natAbs_lt_of_holds rfl hh0 hd0, natAbs_lt_of_holds rfl hh2 hd2, natAbs_lt_of_holds rfl hh3 hd3⟩

/-- A `Cbtrn02c$TranRecord` object holding `x`. -/
def TObj (σ : State) (v : Value) (x : List EquivLean.Cobol.Rec.FVal) : Prop :=
  ∃ (a : Addr) (fs : List (FieldKey × Value)) (s0 s1 s3 s4 s7 s8 s9 s10 s11 s12 s13 : Addr), v = .ref a ∧
    σ.heap a = some (.plain "Cbtrn02c$TranRecord" fs) ∧
    Fields.get fs ("Cbtrn02c$TranRecord", "tranId") = some (.ref s0) ∧
    σ.heap s0 = some (.str (cp037Str (bAt x 0))) ∧
    Fields.get fs ("Cbtrn02c$TranRecord", "tranTypeCd") = some (.ref s1) ∧
    σ.heap s1 = some (.str (cp037Str (bAt x 1))) ∧
    Fields.get fs ("Cbtrn02c$TranRecord", "tranCatCd") = some (.long (BitVec.ofInt 64 (nAt x 2))) ∧
    Fields.get fs ("Cbtrn02c$TranRecord", "tranSource") = some (.ref s3) ∧
    σ.heap s3 = some (.str (cp037Str (bAt x 3))) ∧
    Fields.get fs ("Cbtrn02c$TranRecord", "tranDesc") = some (.ref s4) ∧
    σ.heap s4 = some (.str (cp037Str (bAt x 4))) ∧
    Fields.get fs ("Cbtrn02c$TranRecord", "tranAmt") = some (.long (BitVec.ofInt 64 (nAt x 5))) ∧
    Fields.get fs ("Cbtrn02c$TranRecord", "tranMerchantId") = some (.long (BitVec.ofInt 64 (nAt x 6))) ∧
    Fields.get fs ("Cbtrn02c$TranRecord", "tranMerchantName") = some (.ref s7) ∧
    σ.heap s7 = some (.str (cp037Str (bAt x 7))) ∧
    Fields.get fs ("Cbtrn02c$TranRecord", "tranMerchantCity") = some (.ref s8) ∧
    σ.heap s8 = some (.str (cp037Str (bAt x 8))) ∧
    Fields.get fs ("Cbtrn02c$TranRecord", "tranMerchantZip") = some (.ref s9) ∧
    σ.heap s9 = some (.str (cp037Str (bAt x 9))) ∧
    Fields.get fs ("Cbtrn02c$TranRecord", "tranCardNum") = some (.ref s10) ∧
    σ.heap s10 = some (.str (cp037Str (bAt x 10))) ∧
    Fields.get fs ("Cbtrn02c$TranRecord", "tranOrigTs") = some (.ref s11) ∧
    σ.heap s11 = some (.str (cp037Str (bAt x 11))) ∧
    Fields.get fs ("Cbtrn02c$TranRecord", "tranProcTs") = some (.ref s12) ∧
    σ.heap s12 = some (.str (cp037Str (bAt x 12))) ∧
    Fields.get fs ("Cbtrn02c$TranRecord", "filler1") = some (.ref s13) ∧
    σ.heap s13 = some (.str (cp037Str (bAt x 13)))

set_option maxRecDepth 4000 in
theorem tranobj_of_rec {σ : State} {v : Value} {x : List EquivLean.Cobol.Rec.FVal}
    (hr : JRecAt TranRecord "Cbtrn02c$TranRecord" σ v x) (hv : TranRecord.Valid x) :
    TObj σ v x ∧ ∃ (b0 : List UInt8) (b1 : List UInt8) (n2 : Int) (b3 : List UInt8) (b4 : List UInt8) (n5 : Int) (n6 : Int) (b7 : List UInt8) (b8 : List UInt8) (b9 : List UInt8) (b10 : List UInt8) (b11 : List UInt8) (b12 : List UInt8) (b13 : List UInt8),
      x = [.str b0, .str b1, .num n2, .str b3, .str b4, .num n5, .num n6, .str b7, .str b8, .str b9, .str b10, .str b11, .str b12, .str b13] ∧ n2.natAbs < 10 ^ 18 ∧ n5.natAbs < 10 ^ 18 ∧ n6.natAbs < 10 ^ 18 := by
  obtain ⟨a, fs, rfl, ha, hf⟩ := hr
  have hl : x.length = 14 := (forall2_length hv).symm
  match x, hl, hv, hf with
  | [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13], _, .cons h0 (.cons h1 (.cons h2 (.cons h3 (.cons h4 (.cons h5 (.cons h6 (.cons h7 (.cons h8 (.cons h9 (.cons h10 (.cons h11 (.cons h12 (.cons h13 (.nil)))))))))))))),
    .cons j0 (.cons j1 (.cons j2 (.cons j3 (.cons j4 (.cons j5 (.cons j6 (.cons j7 (.cons j8 (.cons j9 (.cons j10 (.cons j11 (.cons j12 (.cons j13 (.nil)))))))))))))) =>
    obtain ⟨b0, y0, rfl, g0, t0, l0⟩ := str_field rfl h0 j0
    obtain ⟨b1, y1, rfl, g1, t1, l1⟩ := str_field rfl h1 j1
    obtain ⟨n2, rfl, g2, hh2, -, hd2⟩ := num_field rfl h2 j2
    obtain ⟨b3, y3, rfl, g3, t3, l3⟩ := str_field rfl h3 j3
    obtain ⟨b4, y4, rfl, g4, t4, l4⟩ := str_field rfl h4 j4
    obtain ⟨n5, rfl, g5, hh5, -, hd5⟩ := num_field rfl h5 j5
    obtain ⟨n6, rfl, g6, hh6, -, hd6⟩ := num_field rfl h6 j6
    obtain ⟨b7, y7, rfl, g7, t7, l7⟩ := str_field rfl h7 j7
    obtain ⟨b8, y8, rfl, g8, t8, l8⟩ := str_field rfl h8 j8
    obtain ⟨b9, y9, rfl, g9, t9, l9⟩ := str_field rfl h9 j9
    obtain ⟨b10, y10, rfl, g10, t10, l10⟩ := str_field rfl h10 j10
    obtain ⟨b11, y11, rfl, g11, t11, l11⟩ := str_field rfl h11 j11
    obtain ⟨b12, y12, rfl, g12, t12, l12⟩ := str_field rfl h12 j12
    obtain ⟨b13, y13, rfl, g13, t13, l13⟩ := str_field rfl h13 j13
    exact ⟨⟨a, fs, y0, y1, y3, y4, y7, y8, y9, y10, y11, y12, y13, rfl, ha, g0, t0, g1, t1, g2, g3, t3, g4, t4, g5, g6, g7, t7, g8, t8, g9, t9, g10, t10, g11, t11, g12, t12, g13, t13⟩, b0, b1, n2, b3, b4, n5, n6, b7, b8, b9, b10, b11, b12, b13, rfl,
      natAbs_lt_of_holds rfl hh2 hd2, natAbs_lt_of_holds rfl hh5 hd5, natAbs_lt_of_holds rfl hh6 hd6⟩

/-- A `Cbtrn02c$DalytranRecord` object holding `x`. -/
def DObj (σ : State) (v : Value) (x : List EquivLean.Cobol.Rec.FVal) : Prop :=
  ∃ (a : Addr) (fs : List (FieldKey × Value)) (s0 s1 s3 s4 s7 s8 s9 s10 s11 s12 s13 : Addr), v = .ref a ∧
    σ.heap a = some (.plain "Cbtrn02c$DalytranRecord" fs) ∧
    Fields.get fs ("Cbtrn02c$DalytranRecord", "dalytranId") = some (.ref s0) ∧
    σ.heap s0 = some (.str (cp037Str (bAt x 0))) ∧
    Fields.get fs ("Cbtrn02c$DalytranRecord", "dalytranTypeCd") = some (.ref s1) ∧
    σ.heap s1 = some (.str (cp037Str (bAt x 1))) ∧
    Fields.get fs ("Cbtrn02c$DalytranRecord", "dalytranCatCd") = some (.long (BitVec.ofInt 64 (nAt x 2))) ∧
    Fields.get fs ("Cbtrn02c$DalytranRecord", "dalytranSource") = some (.ref s3) ∧
    σ.heap s3 = some (.str (cp037Str (bAt x 3))) ∧
    Fields.get fs ("Cbtrn02c$DalytranRecord", "dalytranDesc") = some (.ref s4) ∧
    σ.heap s4 = some (.str (cp037Str (bAt x 4))) ∧
    Fields.get fs ("Cbtrn02c$DalytranRecord", "dalytranAmt") = some (.long (BitVec.ofInt 64 (nAt x 5))) ∧
    Fields.get fs ("Cbtrn02c$DalytranRecord", "dalytranMerchantId") = some (.long (BitVec.ofInt 64 (nAt x 6))) ∧
    Fields.get fs ("Cbtrn02c$DalytranRecord", "dalytranMerchantName") = some (.ref s7) ∧
    σ.heap s7 = some (.str (cp037Str (bAt x 7))) ∧
    Fields.get fs ("Cbtrn02c$DalytranRecord", "dalytranMerchantCity") = some (.ref s8) ∧
    σ.heap s8 = some (.str (cp037Str (bAt x 8))) ∧
    Fields.get fs ("Cbtrn02c$DalytranRecord", "dalytranMerchantZip") = some (.ref s9) ∧
    σ.heap s9 = some (.str (cp037Str (bAt x 9))) ∧
    Fields.get fs ("Cbtrn02c$DalytranRecord", "dalytranCardNum") = some (.ref s10) ∧
    σ.heap s10 = some (.str (cp037Str (bAt x 10))) ∧
    Fields.get fs ("Cbtrn02c$DalytranRecord", "dalytranOrigTs") = some (.ref s11) ∧
    σ.heap s11 = some (.str (cp037Str (bAt x 11))) ∧
    Fields.get fs ("Cbtrn02c$DalytranRecord", "dalytranProcTs") = some (.ref s12) ∧
    σ.heap s12 = some (.str (cp037Str (bAt x 12))) ∧
    Fields.get fs ("Cbtrn02c$DalytranRecord", "filler1") = some (.ref s13) ∧
    σ.heap s13 = some (.str (cp037Str (bAt x 13)))

set_option maxRecDepth 4000 in
theorem dalobj_of_rec {σ : State} {v : Value} {x : List EquivLean.Cobol.Rec.FVal}
    (hr : JRecAt DalytranRecord "Cbtrn02c$DalytranRecord" σ v x) (hv : DalytranRecord.Valid x) :
    DObj σ v x ∧ ∃ (b0 : List UInt8) (b1 : List UInt8) (n2 : Int) (b3 : List UInt8) (b4 : List UInt8) (n5 : Int) (n6 : Int) (b7 : List UInt8) (b8 : List UInt8) (b9 : List UInt8) (b10 : List UInt8) (b11 : List UInt8) (b12 : List UInt8) (b13 : List UInt8),
      x = [.str b0, .str b1, .num n2, .str b3, .str b4, .num n5, .num n6, .str b7, .str b8, .str b9, .str b10, .str b11, .str b12, .str b13] ∧ n2.natAbs < 10 ^ 18 ∧ n5.natAbs < 10 ^ 18 ∧ n6.natAbs < 10 ^ 18 := by
  obtain ⟨a, fs, rfl, ha, hf⟩ := hr
  have hl : x.length = 14 := (forall2_length hv).symm
  match x, hl, hv, hf with
  | [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13], _, .cons h0 (.cons h1 (.cons h2 (.cons h3 (.cons h4 (.cons h5 (.cons h6 (.cons h7 (.cons h8 (.cons h9 (.cons h10 (.cons h11 (.cons h12 (.cons h13 (.nil)))))))))))))),
    .cons j0 (.cons j1 (.cons j2 (.cons j3 (.cons j4 (.cons j5 (.cons j6 (.cons j7 (.cons j8 (.cons j9 (.cons j10 (.cons j11 (.cons j12 (.cons j13 (.nil)))))))))))))) =>
    obtain ⟨b0, y0, rfl, g0, t0, l0⟩ := str_field rfl h0 j0
    obtain ⟨b1, y1, rfl, g1, t1, l1⟩ := str_field rfl h1 j1
    obtain ⟨n2, rfl, g2, hh2, -, hd2⟩ := num_field rfl h2 j2
    obtain ⟨b3, y3, rfl, g3, t3, l3⟩ := str_field rfl h3 j3
    obtain ⟨b4, y4, rfl, g4, t4, l4⟩ := str_field rfl h4 j4
    obtain ⟨n5, rfl, g5, hh5, -, hd5⟩ := num_field rfl h5 j5
    obtain ⟨n6, rfl, g6, hh6, -, hd6⟩ := num_field rfl h6 j6
    obtain ⟨b7, y7, rfl, g7, t7, l7⟩ := str_field rfl h7 j7
    obtain ⟨b8, y8, rfl, g8, t8, l8⟩ := str_field rfl h8 j8
    obtain ⟨b9, y9, rfl, g9, t9, l9⟩ := str_field rfl h9 j9
    obtain ⟨b10, y10, rfl, g10, t10, l10⟩ := str_field rfl h10 j10
    obtain ⟨b11, y11, rfl, g11, t11, l11⟩ := str_field rfl h11 j11
    obtain ⟨b12, y12, rfl, g12, t12, l12⟩ := str_field rfl h12 j12
    obtain ⟨b13, y13, rfl, g13, t13, l13⟩ := str_field rfl h13 j13
    exact ⟨⟨a, fs, y0, y1, y3, y4, y7, y8, y9, y10, y11, y12, y13, rfl, ha, g0, t0, g1, t1, g2, g3, t3, g4, t4, g5, g6, g7, t7, g8, t8, g9, t9, g10, t10, g11, t11, g12, t12, g13, t13⟩, b0, b1, n2, b3, b4, n5, n6, b7, b8, b9, b10, b11, b12, b13, rfl,
      natAbs_lt_of_holds rfl hh2 hd2, natAbs_lt_of_holds rfl hh5 hd5, natAbs_lt_of_holds rfl hh6 hd6⟩

end EquivLean.Modernize.Cbtrn02c.Java
