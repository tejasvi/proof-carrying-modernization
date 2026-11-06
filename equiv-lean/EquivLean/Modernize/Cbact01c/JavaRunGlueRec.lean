import EquivLean.Modernize.Cbact01c.JavaRunGlueText

/-!
# CBACT01C → Java: an account record object with valid field values

`AcctAt σ c v`: the record object at `c` holds the field values `v` (as in the input array of
`run`), valid for the schema. Its fields one by one (`acctAt_flat`), the helpers' view of it
(`AcctOk`), and the texts the helpers build from it, as the model's texts (`jline`).
-/

open Jimple EquivLean EquivLean.Jimple EquivLean.Jimple.Spec EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbact01c.Java

/-- The record object at `c` holds the valid field values `v`. -/
def AcctAt (σ : Jimple.State) (c : Addr) (v : List EquivLean.Cobol.Rec.FVal) : Prop :=
  JRecAt AccountRecord acctCls σ (.ref c) v ∧ AccountRecord.Valid v

/-- A DISPLAY numeric field (signed or not): a `long` holding the value. -/
theorem jfield_numD {σ : Jimple.State} {cls : ClassName} {fs : List (FieldKey × Value)}
    {f : Field} {fmt : Cobol.NumFmt} {w : EquivLean.Cobol.Rec.FVal} (hk : f.desc.kind = .num fmt)
    (hu : fmt.usage = .display) (he : jFieldAt σ cls fs f w) (hv : f.Valid w) :
    ∃ n, w = .num n ∧ Fields.get fs (cls, f.jname) = some (.long (BitVec.ofInt 64 n)) ∧
      n.natAbs < 10 ^ fmt.digits ∧ fmt.digits ≤ 18 := by
  cases w with
  | str bs => obtain ⟨⟨j, hk'⟩, -⟩ := hv; rw [hk] at hk'; cases hk'
  | num n =>
    obtain ⟨fmt', hk', -, hd, hh, -⟩ := hv
    rw [hk] at hk'; cases hk'
    have hfb : fmt.fullBinary {} = false := by
      simp [Cobol.NumFmt.fullBinary, hu]
    simp only [Cobol.NumFmt.Holds, hfb, Bool.false_eq_true, ↓reduceIte] at hh
    exact ⟨n, rfl, he, hh.1, hd⟩

set_option hygiene false in
/-- One field of `acct_flat`. -/
macro "acct_flat_step" h:ident hv:ident : tactic => `(tactic| (
    have jrec_hstep := EquivLean.Jimple.Spec.jrec_step $h $hv
    clear $h:ident $hv:ident
    obtain ⟨_, _, rfl, jrec_e, jrec_ev, $h:ident, $hv:ident⟩ := jrec_hstep
    first
      | obtain ⟨_, _, rfl, _, _, _⟩ := EquivLean.Jimple.Spec.jfield_alnum rfl jrec_e jrec_ev
      | obtain ⟨_, rfl, _, _, _⟩ := jfield_numD rfl rfl jrec_e jrec_ev
    clear jrec_e jrec_ev))

set_option hygiene false in
/-- `jrec_flat` for records with signed DISPLAY fields. -/
macro "acct_flat" h:ident hv:ident : tactic => `(tactic| (
  simp only at $h:ident $hv:ident
  repeat acct_flat_step $h $hv
  have jrec_hnil := EquivLean.Jimple.Spec.jrec_nil $h
  subst jrec_hnil
  clear $h:ident $hv:ident
  try simp only at *))

theorem toInt_ofInt64 {n : Int} (h : n.natAbs < 10 ^ 18) : (BitVec.ofInt 64 n).toInt = n := by
  rw [BitVec.toInt_ofInt]; exact Jimple.bmod64_of_bounds (by omega) (by omega)

theorem natAbs_toInt_ofInt64 {n : Int} {d : Nat} (h : n.natAbs < 10 ^ d) (hd : d ≤ 18) :
    (BitVec.ofInt 64 n).toInt.natAbs < 10 ^ 18 := by
  have : 10 ^ d ≤ 10 ^ 18 := Nat.pow_le_pow_right (by decide) hd
  rw [toInt_ofInt64 (by omega)]; omega

theorem longField_of {fs : List (FieldKey × Value)} {f : String} {n : Int} {d : Nat}
    (h : Fields.get fs (acctCls, f) = some (.long (BitVec.ofInt 64 n))) (hn : n.natAbs < 10 ^ d)
    (hd : d ≤ 18 := by decide) : LongField fs f :=
  ⟨_, h, natAbs_toInt_ofInt64 hn hd⟩

theorem strField_of {σ : Jimple.State} {fs : List (FieldKey × Value)} {f : String} {x : Addr}
    {bs : List UInt8} (h : Fields.get fs (acctCls, f) = some (.ref x))
    (hx : σ.heap x = some (.str (cp037Str bs))) (hl : bs.length ≤ 178) : StrField σ fs f :=
  ⟨x, _, h, hx, by rw [cp037Str, List.length_map]; exact Nat.lt_of_le_of_lt hl (by decide)⟩

theorem fieldLong_of {σ : Jimple.State} {c : Addr} {fs : List (FieldKey × Value)} {f : String}
    {a : I64} (hc : σ.heap c = some (.plain acctCls fs))
    (h : Fields.get fs (acctCls, f) = some (.long a)) : fieldLong σ c f = a := by
  simp [fieldLong, fieldOf, hc, h]

theorem sfJ_of {σ : Jimple.State} {c : Addr} {fs : List (FieldKey × Value)} {f : String}
    {x : Addr} {s : JStr} (hc : σ.heap c = some (.plain acctCls fs))
    (h : Fields.get fs (acctCls, f) = some (.ref x)) (hx : σ.heap x = some (.str s)) :
    sfJ σ c f = s := by
  simp [sfJ, argText, fieldOf, hc, h, strOf, hx]

/-- The fields of a record object holding valid values, one by one. -/
theorem acctAt_flat {σ : Jimple.State} {c : Addr} {v : List EquivLean.Cobol.Rec.FVal}
    (h : AcctAt σ c v) :
    ∃ (n0 n2 n3 n4 n8 n9 : Int) (b1 b5 b6 b7 b10 b11 b12 : List UInt8),
      v = [.num n0, .str b1, .num n2, .num n3, .num n4, .str b5, .str b6, .str b7, .num n8,
        .num n9, .str b10, .str b11, .str b12] ∧
      AcctOk σ c ∧
      fieldLong σ c "acctId" = BitVec.ofInt 64 n0 ∧ fieldLong σ c "acctCurrBal" = BitVec.ofInt 64 n2 ∧
      fieldLong σ c "acctCreditLimit" = BitVec.ofInt 64 n3 ∧
      fieldLong σ c "acctCashCreditLimit" = BitVec.ofInt 64 n4 ∧
      fieldLong σ c "acctCurrCycCredit" = BitVec.ofInt 64 n8 ∧
      fieldLong σ c "acctCurrCycDebit" = BitVec.ofInt 64 n9 ∧
      sfJ σ c "acctActiveStatus" = cp037Str b1 ∧ sfJ σ c "acctOpenDate" = cp037Str b5 ∧
      sfJ σ c "acctExpiraionDate" = cp037Str b6 ∧ sfJ σ c "acctReissueDate" = cp037Str b7 ∧
      sfJ σ c "acctAddrZip" = cp037Str b10 ∧ sfJ σ c "acctGroupId" = cp037Str b11 ∧
      sfJ σ c "filler1" = cp037Str b12 ∧
      n0.natAbs < 10 ^ 11 ∧ n2.natAbs < 10 ^ 12 ∧ n3.natAbs < 10 ^ 12 ∧ n4.natAbs < 10 ^ 12 ∧
      n8.natAbs < 10 ^ 12 ∧ n9.natAbs < 10 ^ 12 ∧
      b1.length = 1 ∧ b5.length = 10 ∧ b6.length = 10 ∧ b7.length = 10 ∧ b10.length = 10 ∧
      b11.length = 10 ∧ b12.length = 178 := by
  obtain ⟨⟨x, fs, hx, hc, h2⟩, hv⟩ := h
  simp only [Value.ref.injEq] at hx
  subst hx
  unfold Schema.Valid at hv
  acct_flat h2 hv
  rename_i n0 hn0 hb0 _ b1 x1 hf1 hx1 hl1 n2 hn2 hb2 _ n3 hn3 hb3 _ n4 hn4 hb4 _ b5 x5 hf5 hx5 hl5
    b6 x6 hf6 hx6 hl6 b7 x7 hf7 hx7 hl7 n8 hn8 hb8 _ n9 hn9 hb9 _ b10 x10 hf10 hx10 hl10
    b11 x11 hf11 hx11 hl11 b12 x12 hf12 hx12 hl12
  refine ⟨n0, n2, n3, n4, n8, n9, b1, b5, b6, b7, b10, b11, b12, rfl,
    ⟨fs, hc, longField_of hn0 hb0, strField_of hf1 hx1 (by omega), longField_of hn2 hb2,
      longField_of hn3 hb3, longField_of hn4 hb4, strField_of hf5 hx5 (by omega),
      strField_of hf6 hx6 (by omega), strField_of hf7 hx7 (by omega), longField_of hn8 hb8,
      longField_of hn9 hb9, strField_of hf10 hx10 (by omega), strField_of hf11 hx11 (by omega),
      strField_of hf12 hx12 (by omega)⟩,
    fieldLong_of hc hn0, fieldLong_of hc hn2, fieldLong_of hc hn3, fieldLong_of hc hn4,
    fieldLong_of hc hn8, fieldLong_of hc hn9, sfJ_of hc hf1 hx1, sfJ_of hc hf5 hx5,
    sfJ_of hc hf6 hx6, sfJ_of hc hf7 hx7, sfJ_of hc hf10 hx10, sfJ_of hc hf11 hx11,
    sfJ_of hc hf12 hx12, hb0, hb2, hb3, hb4, hb8, hb9, hl1, hl5, hl6, hl7, hl10, hl11, hl12⟩

end EquivLean.Modernize.Cbact01c.Java
